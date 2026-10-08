-- Prove2me | Definitions.Def_CK_CKLaneA1_FEFinal
-- name    : CK_CKLaneA1_FEFinal
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T04:23:54.485069+00:00
-- url     : https://prove2.me/theorems/80a99611-0295-4085-8916-b2453b21f3b3
-- title:
--   Courtade–Kumar proof module `CKLaneA1.FEFinal` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.FEFinal` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.FEFinal` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.FEFinal (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/FEFinal.lean)

import Definitions.Def_CK_CKLaneA1_FEFinal_q02

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace CKLaneA1
open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU
/-- Pointwise positivity on the fixed-edge rectangle `0 < u ≤ 1/50`, `1/40 ≤ w < 1/2`. -/
theorem fixedEdge_pointwise : ∀ u w : ℝ, 0 < u → u ≤ 1/50 → 1/40 ≤ w → w < 1/2 →
    0 < (1 / jn u) * actualDetGapCoefficient u w ∧ 0 < m11 u w :=
  fe_pointwise_of_cover feCover_ok

/-- **`ChartOwners.fixedEdge`**, with the exact field type. -/
theorem fixedEdge_field : ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 → u ≤ 1 / 50 →
    1 / 40 ≤ u + rho * (1 / 2 - u) → GeneralCK.Correction.Complement.RatioSigns u rho := by
  intro u rho hu hu2 hr hr1 hu50 hw40
  have hw : u + rho * (1 / 2 - u) < 1 / 2 := by
    have : rho * (1 / 2 - u) < 1 * (1 / 2 - u) := mul_lt_mul_of_pos_right hr1 (by linarith)
    linarith
  obtain ⟨hc, hm⟩ := fixedEdge_pointwise u _ hu hu50 hw40 hw
  have hJ : 0 < jn u := jn_pos hu hu2
  have hcoef : 0 < actualDetGapCoefficient u (u + rho * (1 / 2 - u)) :=
    (mul_pos_iff_of_pos_left (one_div_pos.mpr hJ)).mp hc
  exact ratioSigns_of_pos hu hu2 hr hr1 hcoef.le hm

/-- Machine check that `fixedEdge_field` has exactly the `ChartOwners.fixedEdge` field type:
this structure update typechecks only if the types agree. -/
theorem withFixedEdge (c : GeneralCK.Correction.Complement.ChartOwners) :
    GeneralCK.Correction.Complement.ChartOwners :=
  { c with fixedEdge := fixedEdge_field }

#print axioms feCover_ok
#print axioms fixedEdge_pointwise
#print axioms fixedEdge_field

end CKLaneA1


