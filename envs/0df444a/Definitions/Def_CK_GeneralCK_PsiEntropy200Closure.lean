-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEntropy200Closure
-- name    : CK_GeneralCK_PsiEntropy200Closure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:56:59.220894+00:00
-- url     : https://prove2.me/theorems/2bccf4fe-b3b4-4c52-8aed-27ff8b143673
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEntropy200Closure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEntropy200Closure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEntropy200Closure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEntropy200Closure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEntropy200Closure.lean)

import Definitions.Def_CK_GeneralCK_PsiOuterEntropy200
import Definitions.Def_CK_GeneralCK_PsiCentralAnalyticClosure

-- ===== source module GeneralCK.PsiEntropy200Closure =====
section

/-!
# Exact remaining opposite owners after the entropy-1/200 extension

The compact owner loses the full closed entropy interval E≤1/200, and
three proved parent exclusions supply additional ratio clipping rules.
The central owner loses all separated laws through the same cutoff.
-/

namespace GeneralCK.PsiEntropy200

/-- The three new ratio exclusions hold at every positive entropy. -/
theorem active_tail_bounds {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hb : 1 / 2 ≤ μ.b)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    (1 - μ.a - μ.b ≤ 1 / 4 → 1 - μ.a - μ.b < 16 * μ.meanEntropy) ∧
    (1 - μ.a - μ.b ≤ 2 / 5 → 1 - μ.a - μ.b < 40 * μ.meanEntropy) ∧
    (2 / 5 ≤ 1 - μ.a - μ.b → 1 - μ.a - μ.b < 75 * μ.meanEntropy) := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have heq : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have ha : phi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy ≤
      psi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy := by rwa [heq]
  constructor
  · intro hq
    by_contra hn
    have hr := le_of_not_gt hn
    exact (not_lt_of_ge ha)
      (PsiOuterEntropy200.parent_dominance_quarter (by linarith) hq hE hr)
  · constructor
    · intro hq
      by_contra hn
      have hr := le_of_not_gt hn
      exact (not_lt_of_ge ha)
        (PsiOuterEntropy200.parent_dominance_two_fifths (by linarith) hq hE hr)
    · intro hq
      by_contra hn
      exact (not_lt_of_ge ha)
        (PsiOuterEntropy200.parent_dominance_half hq
          (by linarith [μ.a_interior.1]) hE (le_of_not_gt hn))

/-- The old exact compact region, further clipped only by the new proved
entropy owner and parent-dominance tails. -/
def compactRegion (a b E : ℝ) : Prop :=
  PsiCompactAnalytic.compactRegion a b E ∧
  1 / 200 < E ∧
  (1 - a - b ≤ 1 / 4 → 1 - a - b < 16 * E) ∧
  (1 - a - b ≤ 2 / 5 → 1 - a - b < 40 * E) ∧
  (2 / 5 ≤ 1 - a - b → 1 - a - b < 75 * E)

def CompactOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), compactRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toCompactAnalyticOwner (h : CompactOwner) : PsiCompactAnalytic.CompactOwner := by
  intro k μ hregion hactive
  by_cases hE : μ.meanEntropy ≤ 1 / 200
  · exact PsiOuterEntropy200.law_gap_le_cost μ hregion.1.le hregion.2.2.2.1.le
      hregion.2.1 hE hactive.le
  · exact h k μ ⟨hregion, lt_of_not_ge hE, active_tail_bounds μ hregion.2.1 hactive.le⟩ hactive

/-- The affine-child contract remains sufficient on the newly clipped
three-variable chart. Both children and feasible entropy allocation remain. -/
theorem compactOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate compactRegion) : CompactOwner := by
  intro k μ hregion hactive
  have hab : μ.a < μ.b := by linarith [hregion.1.2.1, hregion.1.2.2.2.1]
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab hregion hactive.le

theorem extendedCompactOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate compactRegion) :
    OppositePsiExtendedCompactOwner :=
  PsiCompactAnalytic.toExtendedCompactOwner
    (toCompactAnalyticOwner (compactOwner_of_affineCertificate h))

/-- The exact complement of the new closed separated-law owner. -/
def centralRemainder (a b E : ℝ) : Prop := 1 / 200 < E ∨ b - a < 8 * E

def CentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    1 / 2 ≤ μ.b → 1 / 10 ≤ μ.a →
    (μ.a ≤ 1 / 10 → 1 / 32768 < μ.meanEntropy) →
    PsiCentralAnalytic.centralRemainder μ.a μ.b μ.meanEntropy →
    centralRemainder μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toCentralAnalyticOwner (h : CentralOwner) : PsiCentralAnalytic.CentralOwner := by
  intro k μ hab hsum hmean hinfo hE hb ha hface hregion hactive
  by_cases hl : μ.meanEntropy ≤ 1 / 200 ∧ 8 * μ.meanEntropy ≤ μ.b - μ.a
  · exact PsiOuterEntropy200.law_gap_le_cost_of_separation μ hsum.le hb hl.1 hl.2 hactive.le
  · apply h k μ hab hsum hmean hinfo hE hb ha hface hregion ?_ hactive
    by_contra hn
    change ¬(1 / 200 < μ.meanEntropy ∨ μ.b - μ.a < 8 * μ.meanEntropy) at hn
    push Not at hn
    exact hl hn

end GeneralCK.PsiEntropy200

namespace GeneralCK

/-- Both opposite charts consume the enlarged analytic entropy region;
the same-side owner retains its existing exact domain. -/
structure ResidualPsiEntropy200RemainingOwners : Prop where
  sameChart : SameSidePsiExtendedChartOwner
  oppositeCentral : PsiEntropy200.CentralOwner
  oppositeCompact : PsiEntropy200.CompactOwner

theorem ResidualPsiEntropy200RemainingOwners.toCentralCompact
    (h : ResidualPsiEntropy200RemainingOwners) : ResidualPsiCentralCompactRemainingOwners where
  sameChart := h.sameChart
  oppositeCentral := PsiEntropy200.toCentralAnalyticOwner h.oppositeCentral
  oppositeCompact := PsiEntropy200.toCompactAnalyticOwner h.oppositeCompact

theorem generalCourtadeKumar_of_entropy200_remaining_owners
    (hphi : CanonicalUnbalancedPhiOwner) (hpsi : ResidualPsiEntropy200RemainingOwners) :
    GeneralCourtadeKumar :=
  generalCourtadeKumar_of_central_compact_analytic_remaining_owners hphi hpsi.toCentralCompact

end GeneralCK

#print axioms GeneralCK.PsiEntropy200.active_tail_bounds
#print axioms GeneralCK.PsiEntropy200.toCompactAnalyticOwner
#print axioms GeneralCK.PsiEntropy200.compactOwner_of_affineCertificate
#print axioms GeneralCK.PsiEntropy200.extendedCompactOwner_of_affineCertificate
#print axioms GeneralCK.PsiEntropy200.toCentralAnalyticOwner
#print axioms GeneralCK.ResidualPsiEntropy200RemainingOwners.toCentralCompact
#print axioms GeneralCK.generalCourtadeKumar_of_entropy200_remaining_owners

end


