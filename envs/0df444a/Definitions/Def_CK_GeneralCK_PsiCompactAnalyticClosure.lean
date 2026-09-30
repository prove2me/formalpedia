-- Prove2me | Definitions.Def_CK_GeneralCK_PsiCompactAnalyticClosure
-- name    : CK_GeneralCK_PsiCompactAnalyticClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:29:49.699031+00:00
-- url     : https://prove2.me/theorems/6b6abab6-b350-4e94-b924-3079fe0b241e
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiCompactAnalyticClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiCompactAnalyticClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiCompactAnalyticClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiCompactAnalyticClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiCompactAnalyticClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiOuterEntropy2048
import Definitions.Def_CK_GeneralCK_PsiExtendedRegionClosure
import Definitions.Def_CK_GeneralCK_PsiAffineChildCertificate

-- ===== source module GeneralCK.PsiCompactAnalyticClosure =====
section

/-!
# Exact opposite compact remainder after the outer analytic owner

The entropy cutoff is raised to 1/2048 on the complete outer domain.
The already-proved endpoint theorem additionally removes the wedge
q≤1/10, E≤11/200. Both equality faces are assigned to proved owners.
The affine-child interface retains both hybrid children and their separate
feasible entropy caps; no mean-only scalar bound is asserted.
-/

namespace GeneralCK.PsiCompactAnalytic

/-- The wider low-bias wedge is an actual-law theorem. Its distance
condition is automatic on the outer means. -/
theorem outer_low_bias_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (ha : μ.a ≤ 1 / 10)
    (hq : 1 - μ.a - μ.b ≤ 1 / 10) (hE : μ.meanEntropy ≤ 11 / 200)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 50) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  exact PsiModerateEntropy.law_gap_margin_ceiling μ hsum hE (by linarith) hq hactive

theorem outer_low_bias_law {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (ha : μ.a ≤ 1 / 10)
    (hq : 1 - μ.a - μ.b ≤ 1 / 10) (hE : μ.meanEntropy ≤ 11 / 200)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hEpos : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hm : 0 ≤ (1 / 50) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  linarith only [outer_low_bias_margin μ hsum ha hq hE hactive, hm]

/-- Parent activity provides a further exact scalar clipping rule,
without any restriction on E beyond positivity. -/
theorem active_bias_lt_eight_entropy {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hq : 1 - μ.a - μ.b ≤ 1 / 8)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    1 - μ.a - μ.b < 8 * μ.meanEntropy := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  by_contra hn
  have hr : 8 * μ.meanEntropy ≤ 1 - μ.a - μ.b := le_of_not_gt hn
  have hh := PsiOuterEntropy2048.parent_dominance_ratio8 hE (by linarith) hq hr
  have heq : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  rw [heq] at hh
  exact (not_lt_of_ge hactive) hh

/-- The complete remaining scalar domain for the compact owner. Physical
means, entropy caps and parent activity are supplied by the certificate
contract, and are therefore not duplicated in this predicate. -/
def compactRegion (a b E : ℝ) : Prop :=
  a + b < 1 ∧ 1 / 2 ≤ b ∧
  1 / 268435456 < a ∧ a < 1 / 10 ∧
  1 / 8192 < a + 1 - b ∧
  1 / 100 < H ((a + b) / 2) - E ∧
  1 / 2048 < E ∧
  (1 - a - b ≤ 1 / 10 → 11 / 200 < E) ∧
  (1 - a - b ≤ 1 / 8 → 1 - a - b < 8 * E)

/-- Actual-law owner on precisely the remaining compact domain. -/
def CompactOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), compactRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

/-- No point of the extended compact chart is lost: the removed closed
regions are restored by established actual-law estimates. -/
theorem toExtendedCompactOwner (h : CompactOwner) : OppositePsiExtendedCompactOwner := by
  intro k μ _hab hsum _hmean hinfo hb ha0 ha1 hcorner _hE hactive
  by_cases hlow : μ.meanEntropy ≤ 1 / 2048
  · exact PsiOuterEntropy2048.law_gap_le_cost μ hsum.le ha1.le hb hlow hactive.le
  · by_cases hwedge : 1 - μ.a - μ.b ≤ 1 / 10 ∧ μ.meanEntropy ≤ 11 / 200
    · exact outer_low_bias_law μ hsum.le ha1.le hwedge.1 hwedge.2 hactive.le
    · apply h k μ ?_ hactive
      refine ⟨hsum, hb, ha0, ha1, hcorner, ?_, lt_of_not_ge hlow, ?_, ?_⟩
      · exact hinfo
      · intro hq
        by_contra hn
        exact hwedge ⟨hq, le_of_not_gt hn⟩
      · intro hq
        exact active_bias_lt_eight_entropy μ hq hactive.le

/-- A sound three-variable replacement certificate, retaining both child
maxima and minimizing affine supports over the exact entropy allocation.
This is a conditional consumer, not a claim that its premise is inhabited. -/
theorem compactOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate compactRegion) : CompactOwner := by
  intro k μ hregion hactive
  have hab : μ.a < μ.b := by linarith [hregion.2.1, hregion.2.2.2.1]
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab hregion hactive.le

theorem extendedCompactOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate compactRegion) :
    OppositePsiExtendedCompactOwner := toExtendedCompactOwner (compactOwner_of_affineCertificate h)

end GeneralCK.PsiCompactAnalytic

namespace GeneralCK

/-- Same-side and central owners are unchanged here. Only the opposite
compact field is replaced by its explicitly smaller analytic remainder. -/
structure ResidualPsiCompactAnalyticRemainingOwners : Prop where
  sameChart : SameSidePsiExtendedChartOwner
  oppositeCentral : OppositePsiExtendedCentralOwner
  oppositeCompact : PsiCompactAnalytic.CompactOwner

theorem ResidualPsiCompactAnalyticRemainingOwners.toExtended
    (h : ResidualPsiCompactAnalyticRemainingOwners) : ResidualPsiExtendedRemainingOwners where
  sameChart := h.sameChart
  oppositeCentral := h.oppositeCentral
  oppositeCompact := PsiCompactAnalytic.toExtendedCompactOwner h.oppositeCompact

theorem generalCourtadeKumar_of_compact_analytic_remaining_owners
    (hphi : CanonicalUnbalancedPhiOwner) (hpsi : ResidualPsiCompactAnalyticRemainingOwners) :
    GeneralCourtadeKumar := generalCourtadeKumar_of_extended_region_owners hphi hpsi.toExtended

end GeneralCK

#print axioms GeneralCK.PsiCompactAnalytic.outer_low_bias_margin
#print axioms GeneralCK.PsiCompactAnalytic.outer_low_bias_law
#print axioms GeneralCK.PsiCompactAnalytic.active_bias_lt_eight_entropy
#print axioms GeneralCK.PsiCompactAnalytic.toExtendedCompactOwner
#print axioms GeneralCK.PsiCompactAnalytic.compactOwner_of_affineCertificate
#print axioms GeneralCK.PsiCompactAnalytic.extendedCompactOwner_of_affineCertificate
#print axioms GeneralCK.ResidualPsiCompactAnalyticRemainingOwners.toExtended
#print axioms GeneralCK.generalCourtadeKumar_of_compact_analytic_remaining_owners

end


