-- Prove2me | Definitions.Def_CK_GeneralCK_PsiCentralAnalyticClosure
-- name    : CK_GeneralCK_PsiCentralAnalyticClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:52:48.211754+00:00
-- url     : https://prove2.me/theorems/b127bfc7-9904-467f-b2cf-5a4f7ee38bbe
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiCentralAnalyticClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiCentralAnalyticClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiCentralAnalyticClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiCentralAnalyticClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiCentralAnalyticClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiCompactAnalyticClosure
import Definitions.Def_CK_GeneralCK_PsiCentralEntropy1024

-- ===== source module GeneralCK.PsiCentralAnalyticClosure =====
section

/-!
# Exact opposite-central remainder after analytic owners

The retained-child endpoint theorem closes the closed wedge
`q <= 1/10`, `E <= 11/200`, `8E <= b-a`. The enlarged low-entropy theorem
additionally closes every opposite active law through `E = 1/1024`, without
a separation or outer-mean hypothesis. The predicate below records the
exact complement of these two proved regions inside the central chart.
-/

namespace GeneralCK.PsiCentralAnalytic

/-- The scalar conditions left after removing the two closed analytic
subregions.  The disjunctions deliberately use strict inequalities, so all
three wedge equality faces and the outer entropy equality face remain owned
by proved theorems. -/
def centralRemainder (a b E : ℝ) : Prop :=
  (11 / 200 < E ∨ b - a < 8 * E ∨ 1 / 10 < 1 - a - b) ∧
  1 / 1024 < E

/-- A replacement owner on precisely the residual part of the original
opposite-central chart. -/
def CentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    1 / 2 ≤ μ.b → 1 / 10 ≤ μ.a →
    (μ.a ≤ 1 / 10 → 1 / 32768 < μ.meanEntropy) →
    centralRemainder μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- The closed endpoint wedge, with no restriction on `a` beyond the physical
law assumptions required by the endpoint theorem. -/
theorem endpoint_wedge_law {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hE : μ.meanEntropy ≤ 11 / 200)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a)
    (hq : 1 - μ.a - μ.b ≤ 1 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  PsiModerateEntropy.law_gap_le_cost_ceiling μ hsum hE hd hq hactive

/-- In the central chart, parent activity turns the enlarged low-entropy
cutoff into the endpoint wedge's bias hypothesis.  Thus every sufficiently
separated central law is closed through `E = 1/2048`; no `a = 1/10`
assumption is needed. -/
theorem low_entropy_high_separation_law {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hsum : μ.a + μ.b ≤ 1)
    (hb : 1 / 2 ≤ μ.b) (ha : 1 / 10 ≤ μ.a)
    (hE : μ.meanEntropy ≤ 1 / 2048)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hEpos : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hmid : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have hq := PsiOuterEntropy2048.active_bias_lt_eight_entropy
    (q := 1 - μ.a - μ.b) (by linarith) (by linarith) hEpos hE (by rwa [hmid])
  exact endpoint_wedge_law μ hsum (by linarith) hd (by linarith) hactive

/-- No outer-mean or separation condition is required for the new complete
low-entropy slab. Both child profiles and actual-law cost are retained. -/
theorem low_entropy_law {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a < μ.b) (hsum : μ.a + μ.b ≤ 1) (hb : 1 / 2 ≤ μ.b)
    (hE : μ.meanEntropy ≤ 1 / 1024)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  PsiCentralEntropy1024.law_gap_le_cost μ hab hsum hb hE hactive

/-- No point is dropped in replacing the original central owner by
`CentralOwner`: failure of either strict residual clause lands on one of the
two established closed regions. -/
theorem toExtendedCentralOwner (h : CentralOwner) : OppositePsiExtendedCentralOwner := by
  intro k μ hab hsum hmean hinfo hE hb ha hface hactive
  by_cases hwedge :
      μ.meanEntropy ≤ 11 / 200 ∧
      8 * μ.meanEntropy ≤ μ.b - μ.a ∧
      1 - μ.a - μ.b ≤ 1 / 10
  · exact endpoint_wedge_law μ hsum.le hwedge.1 hwedge.2.1 hwedge.2.2 hactive.le
  · by_cases hlow : μ.meanEntropy ≤ 1 / 1024
    · exact low_entropy_law μ hab hsum.le hb hlow hactive.le
    · apply h k μ hab hsum hmean hinfo hE hb ha hface ?_ hactive
      constructor
      · by_contra hn
        push Not at hn
        exact hwedge ⟨hn.1, hn.2.1, hn.2.2⟩
      · exact lt_of_not_ge hlow

/-- Three scalar coordinates for the remaining central certificate family.
Physical mean bounds, the exact child entropy allocation interval, and both
hybrid child supports are supplied by `AffineChildCertificate`. -/
def centralRegion (a b E : ℝ) : Prop :=
  a + b < 1 ∧ 1 / 2 ≤ b ∧ 1 / 10 ≤ a ∧
  1 / 100 < H ((a + b) / 2) - E ∧ centralRemainder a b E ∧
  (1 - a - b ≤ 1 / 8 → 1 - a - b < 8 * E)

/-- This consumer preserves both actual hybrid child profiles and their
separate entropy caps. Its certificate premise remains an open obligation. -/
theorem centralOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate centralRegion) : CentralOwner := by
  intro k μ hab hsum _hmean hinfo _hE hb ha _hface hregion hactive
  apply PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab ?_ hactive.le
  refine ⟨hsum, hb, ha, hinfo, hregion, ?_⟩
  intro hq
  exact PsiCompactAnalytic.active_bias_lt_eight_entropy μ hq hactive.le

theorem extendedCentralOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate centralRegion) :
    OppositePsiExtendedCentralOwner :=
  toExtendedCentralOwner (centralOwner_of_affineCertificate h)

end GeneralCK.PsiCentralAnalytic

namespace GeneralCK

/-- The compact and central charts are both replaced by their exact analytic
remainders; the same-side chart is unchanged. -/
structure ResidualPsiCentralCompactRemainingOwners : Prop where
  sameChart : SameSidePsiExtendedChartOwner
  oppositeCentral : PsiCentralAnalytic.CentralOwner
  oppositeCompact : PsiCompactAnalytic.CompactOwner

theorem ResidualPsiCentralCompactRemainingOwners.toCompactAnalytic
    (h : ResidualPsiCentralCompactRemainingOwners) :
    ResidualPsiCompactAnalyticRemainingOwners where
  sameChart := h.sameChart
  oppositeCentral := PsiCentralAnalytic.toExtendedCentralOwner h.oppositeCentral
  oppositeCompact := h.oppositeCompact

theorem generalCourtadeKumar_of_central_compact_analytic_remaining_owners
    (hphi : CanonicalUnbalancedPhiOwner)
    (hpsi : ResidualPsiCentralCompactRemainingOwners) :
    GeneralCourtadeKumar :=
  generalCourtadeKumar_of_compact_analytic_remaining_owners hphi hpsi.toCompactAnalytic

end GeneralCK

#print axioms GeneralCK.PsiCentralAnalytic.endpoint_wedge_law
#print axioms GeneralCK.PsiCentralAnalytic.low_entropy_high_separation_law
#print axioms GeneralCK.PsiCentralAnalytic.low_entropy_law
#print axioms GeneralCK.PsiCentralAnalytic.toExtendedCentralOwner
#print axioms GeneralCK.PsiCentralAnalytic.centralOwner_of_affineCertificate
#print axioms GeneralCK.PsiCentralAnalytic.extendedCentralOwner_of_affineCertificate
#print axioms GeneralCK.ResidualPsiCentralCompactRemainingOwners.toCompactAnalytic
#print axioms GeneralCK.generalCourtadeKumar_of_central_compact_analytic_remaining_owners

end


