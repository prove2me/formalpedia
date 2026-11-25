-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:44.821548+00:00
-- url     : https://prove2.me/theorems/930c3d6c-0639-5d0c-9a23-598e7e088545
-- title:
--   Reg Line
-- statement:
--   Definitions and structural lemmas for Reg Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegLine.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSectionOn_coordinate_plane_191de7224ed6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_bsmul_of_isMultiHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
section Objects
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def secNorm (E : HermLine ι) (t : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  ‖eval z (map (Int.castRingHom ℂ) t)‖ / E.h z
theorem secNorm_smul {E : HermLine ι} {t : MRing ι} {a : K → ℕ} (hE : ∀ k, E.a k = a k)
    (ht : IsMultiHomog t a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    secNorm E t (fun p => c p.1 * z p) = secNorm E t z := by
  have he := eval_bsmul_of_isMultiHomog ht c z
  have hh : E.h (bsmul c z) = (∏ k, ‖c k‖ ^ E.a k) * E.h z := E.smul c z hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ E.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  have hn : ‖∏ k, c k ^ a k‖ = ∏ k, ‖c k‖ ^ E.a k := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, hE k, zpow_natCast]
  change ‖eval (bsmul c z) (map (Int.castRingHom ℂ) t)‖ / E.h (bsmul c z) = _
  rw [he, hh, norm_mul, hn, mul_div_mul_left _ _ hpos.ne']
  rfl
def regLine (E : HermLine ι) (t : MRing ι) (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a)
    (ε : ℝ) : HermLine ι :=
  HermLine.ofWeight (fun z => -(Real.log (secNorm E t z ^ 2 + ε) / 2)) (by
    intro c z hc
    obtain ⟨a, hE, hta⟩ := ht
    simp only [secNorm_smul hE hta hc z])
variable {E : HermLine ι} {t : MRing ι} {ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a}
  {ε : ℝ}
end Objects
theorem isMultiHomog_planeCoordinate (i : Fin 3) : ∃ a : Unit → ℕ, (∀ k, (fsLine 3).a k = a k) ∧ IsMultiHomog (Xc 3 i) a := by
  obtain ⟨a, ha, hm, -⟩ := isSectionOn_coordinate_plane i
  exact ⟨a, ha, hm⟩
end GroundTheory.Heights₂.Heights.Inter


