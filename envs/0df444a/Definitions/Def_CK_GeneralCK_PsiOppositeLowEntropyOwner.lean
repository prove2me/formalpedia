-- Prove2me | Definitions.Def_CK_GeneralCK_PsiOppositeLowEntropyOwner
-- name    : CK_GeneralCK_PsiOppositeLowEntropyOwner
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:07:13.049644+00:00
-- url     : https://prove2.me/theorems/bef9fc9c-06aa-4886-85b8-ad1019df3ea2
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiOppositeLowEntropyOwner` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiOppositeLowEntropyOwner` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiOppositeLowEntropyOwner` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiOppositeLowEntropyOwner (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiOppositeLowEntropyOwner.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointBellman
import Definitions.Def_CK_GeneralCK_PsiLowEntropyBias
import Definitions.Def_CK_GeneralCK_PsiSmallDistanceLowEntropy
import Definitions.Def_CK_GeneralCK_PsiFourRatioBridge

-- ===== source module GeneralCK.PsiOppositeLowEntropyOwner =====
section

/-!
# The complete opposite low-entropy owner

The active-parent bias estimate and all three separation regimes are proved
for actual laws. This joins them at the exact ratio-four and ratio-eight
boundaries, retaining the original hybrid child maximum throughout.
-/

namespace GeneralCK.PsiOppositeLowEntropy

theorem coordinate_domain {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a < μ.b) (hsum : μ.a + μ.b ≤ 1) (hside : 1 / 2 ≤ μ.b) :
    0 < μ.b - μ.a ∧ μ.b - μ.a ≤ 1 ∧
      0 ≤ 1 - μ.a - μ.b ∧ 1 - μ.a - μ.b ≤ μ.b - μ.a ∧
      1 - μ.a - μ.b < 1 / 2 ∧ 0 < μ.meanEntropy := by
  have ha := μ.a_interior.1
  have hb := μ.b_interior.2
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, hE⟩

theorem high_ratio_branch {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hE : μ.meanEntropy ≤ 1 / 1000000)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a)
    (hq : 1 - μ.a - μ.b ≤ 1 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  PsiEndpointBellman.law_gap_le_cost μ hsum (by linarith) hd hq hactive.le

theorem active_bias_bounds {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hside : 1 / 2 ≤ μ.b) (hEs : μ.meanEntropy ≤ 1 / 1000000)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    1 - μ.a - μ.b < 1 / 10 ∧ 1 - μ.a - μ.b < 8 * μ.meanEntropy := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hqi : 1 - μ.a - μ.b ≤ 15 / 16 := by linarith [μ.a_interior.1]
  have hmid : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have ha : phi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy ≤
      psi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy := by rwa [hmid]
  exact ⟨PsiLowEntropyBias.active_bias_lt_tenth hqi hE hEs ha,
    PsiLowEntropyBias.active_bias_lt_eight_entropy hqi hE hEs ha⟩

theorem small_distance_branch {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a < μ.b) (hsum : μ.a + μ.b ≤ 1) (hside : 1 / 2 ≤ μ.b)
    (hEs : μ.meanEntropy ≤ 1 / 1000000) (hd : μ.b - μ.a ≤ 4 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  PsiSmallDistance.law_gap_le_cost μ hab hsum
    (active_bias_bounds μ hside hEs hactive).2.le hEs hd hactive

/-- Every positive separation is covered, including both dividing equalities. -/
theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a < μ.b) (hsum : μ.a + μ.b ≤ 1) (hside : 1 / 2 ≤ μ.b)
    (hEs : μ.meanEntropy ≤ 1 / 1000000)
    (hactive : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  by_cases h4 : μ.b - μ.a ≤ 4 * μ.meanEntropy
  · exact small_distance_branch μ hab hsum hside hEs h4 hactive.le
  · by_cases h8 : μ.b - μ.a ≤ 8 * μ.meanEntropy
    · exact PsiFourRatioBridge.law_gap_le_cost μ hsum hside hEs
        (lt_of_not_ge h4).le h8 hactive.le
    · exact high_ratio_branch μ hsum hEs (lt_of_not_ge h8).le
        (active_bias_bounds μ hside hEs hactive.le).1.le hactive

end GeneralCK.PsiOppositeLowEntropy

namespace GeneralCK

/-- The full original opposite-side low-average-entropy owner. There is no
scalar-owner hypothesis, endpoint-cost premise, or uncovered distance regime. -/
theorem oppositePsiLowEntropyOwner : OppositePsiLowEntropyOwner := by
  intro k μ hab hsum _hmean _hinfo hside hEs hactive
  exact PsiOppositeLowEntropy.law_gap_le_cost μ hab hsum hside hEs hactive

end GeneralCK

#print axioms GeneralCK.PsiOppositeLowEntropy.coordinate_domain
#print axioms GeneralCK.PsiOppositeLowEntropy.high_ratio_branch
#print axioms GeneralCK.PsiOppositeLowEntropy.active_bias_bounds
#print axioms GeneralCK.PsiOppositeLowEntropy.small_distance_branch
#print axioms GeneralCK.PsiOppositeLowEntropy.law_gap_le_cost
#print axioms GeneralCK.oppositePsiLowEntropyOwner

end


