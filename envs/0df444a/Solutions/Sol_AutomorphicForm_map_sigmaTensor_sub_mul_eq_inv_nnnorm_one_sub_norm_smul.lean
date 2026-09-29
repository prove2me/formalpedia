-- Prove2me | solution 1 for AutomorphicForm.map_sigmaTensor_sub_mul_eq_inv_nnnorm_one_sub_norm_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2b9bfd01-3972-51a3-a39a-fac5043a612d

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_AutomorphicForm_map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_map_sigmaTensor_sub_mul_eq_inv_nnnorm_one_sub_norm_smul
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct
open LanglandsTunnell.CubicInduction (diagUnits2)
open MeasureTheory
open AutomorphicForm

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (r : (L ⊗[K] v.adicCompletion K)) (hr : Algebra.norm (v.adicCompletion K) r ≠ 1) :
    Measure.map (fun y : (L ⊗[K] v.adicCompletion K) => AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ y - r * y) ν =
      ((‖(1 : (v.adicCompletion K)) - Algebra.norm (v.adicCompletion K) r‖₊)⁻¹ : NNReal) • ν := by
  have hab : Algebra.norm (v.adicCompletion K) (1 : L ⊗[K] v.adicCompletion K) ≠ Algebra.norm (v.adicCompletion K) r := by
    rw [map_one]; exact fun h => hr h.symm
  have h := AutomorphicForm.map_mul_sigmaTensor_sub_mul_eq_norm_algebraNorm_sub_inv_smul K L σ hgen v ν 1 r hab
  have hfun : (fun y : L ⊗[K] v.adicCompletion K => AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ y - r * y) =
      (fun x : L ⊗[K] v.adicCompletion K => 1 * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ x - r * x) := by
    funext x; rw [one_mul]
  rw [hfun, h, map_one]
  have hpos : 0 < ‖(1 : v.adicCompletion K) - Algebra.norm (v.adicCompletion K) r‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hr))
  have hne : ‖(1 : v.adicCompletion K) - Algebra.norm (v.adicCompletion K) r‖₊ ≠ 0 := by
    rw [← NNReal.coe_ne_zero, coe_nnnorm]; exact hpos.ne'
  have hscal : ENNReal.ofReal ‖(1 : v.adicCompletion K) - Algebra.norm (v.adicCompletion K) r‖⁻¹ =
      (((‖(1 : v.adicCompletion K) - Algebra.norm (v.adicCompletion K) r‖₊)⁻¹ : NNReal) : ENNReal) := by
    rw [ENNReal.ofReal_inv_of_pos hpos, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal, ENNReal.coe_inv hne]
  ext s hs
  simp only [Measure.smul_apply, hscal, ENNReal.smul_def, smul_eq_mul]

end S_AutomorphicForm_map_sigmaTensor_sub_mul_eq_inv_nnnorm_one_sub_norm_smul
end P2MW
export P2MW.S_AutomorphicForm_map_sigmaTensor_sub_mul_eq_inv_nnnorm_one_sub_norm_smul (solution)
