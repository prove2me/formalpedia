-- Prove2me | solution 1 for AutomorphicForm.prod_norm_pow_mult_mul_lintegral_comp_linearMap_tensor_infiniteAdeleRing_eq_lintegral_of_det_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/4bee6707-c780-5cbd-9480-3ce2a2d9a41e

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_NumberField_InfiniteAdeleRing_map_linearMap_eq_inv_prod_norm_archEval_det_pow_mult_smul_of_isAddHaarMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_prod_norm_pow_mult_mul_lintegral_comp_linearMap_tensor_infiniteAdeleRing_eq_lintegral_of_det_eq

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (T : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K))
    (d : (InfiniteAdeleRing K)ˣ) (hT : LinearMap.det T = (d : InfiniteAdeleRing K))
    (G : (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞) (hG : Measurable G) :
    ENNReal.ofReal (∏ v : InfinitePlace K, ‖(d : InfiniteAdeleRing K) v‖ ^ v.mult) * ∫⁻ ξ, G (T ξ) ∂lam =
      ∫⁻ ξ, G ξ ∂lam := by
  classical
  have hunit : IsUnit (LinearMap.det T) := by rw [hT]; exact Units.isUnit d
  have hmap :=
    NumberField.InfiniteAdeleRing.map_linearMap_eq_inv_prod_norm_archEval_det_pow_mult_smul_of_isAddHaarMeasure
      K (L ⊗[K] InfiniteAdeleRing K) lam T hunit
  have hTc : Continuous T := IsModuleTopology.continuous_of_linearMap T
  have hTm : Measurable T := hTc.measurable
  have hP : (∏ w : InfinitePlace K, ‖NumberField.AdelicLevel.archEval K w (LinearMap.det T)‖ ^ w.mult) =
      ∏ v : InfinitePlace K, ‖(d : InfiniteAdeleRing K) v‖ ^ v.mult := by
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [hT]
    rfl
  have hpos : 0 < ∏ v : InfinitePlace K, ‖(d : InfiniteAdeleRing K) v‖ ^ v.mult := by
    refine Finset.prod_pos (fun v _ => pow_pos (norm_pos_iff.mpr ?_) _)
    exact ((Units.isUnit d).map (NumberField.AdelicLevel.archEval K v)).ne_zero
  rw [← lintegral_map hG hTm, hmap, lintegral_smul_measure, hP, smul_eq_mul, ← mul_assoc,
    ENNReal.ofReal_inv_of_pos hpos, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top,
    one_mul]

end S_AutomorphicForm_prod_norm_pow_mult_mul_lintegral_comp_linearMap_tensor_infiniteAdeleRing_eq_lintegral_of_det_eq
end P2MW
export P2MW.S_AutomorphicForm_prod_norm_pow_mult_mul_lintegral_comp_linearMap_tensor_infiniteAdeleRing_eq_lintegral_of_det_eq (solution)
