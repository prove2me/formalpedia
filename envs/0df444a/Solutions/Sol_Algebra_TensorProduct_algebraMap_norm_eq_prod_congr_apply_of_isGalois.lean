-- Prove2me | solution 1 for Algebra.TensorProduct.algebraMap_norm_eq_prod_congr_apply_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b8ba0a18-5e9e-5bc3-af2f-b782f8e3c907

import Mathlib
import Definitions.Def_Mathlib_RightActionInstances
import Theorems.Thm_Algebra_TensorProduct_map_norm_eq_norm_map_of_rightAlgebra
import Theorems.Thm_Algebra_TensorProduct_bijective_productMap_pi_comp_of_isGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_TensorProduct_algebraMap_norm_eq_prod_congr_apply_of_isGalois
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk"

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

namespace NormGal

open scoped TensorProduct.RightActions

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem norm_pi {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] (c : ι → F) :
    Algebra.norm F c = ∏ i, c i := by
  classical
  rw [Algebra.norm_eq_matrix_det (Pi.basisFun F ι)]
  have h : Algebra.leftMulMatrix (Pi.basisFun F ι) c = Matrix.diagonal c := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.diagonal_apply]
    simp only [Pi.basisFun_apply, Pi.basisFun_repr, Pi.mul_apply, Pi.single_apply]
    split_ifs with hij
    · subst hij; simp
    · simp [Ne.symm hij]
  rw [h, Matrix.det_diagonal]

section WithF

variable {K L} (F : Type*) [Field F] [Algebra K F] (σ₀ : L →ₐ[K] F)

def Φ : L ⊗[K] F →ₐ[K] ((L ≃ₐ[K] L) → F) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom K (fun _ : L ≃ₐ[K] L => F) (fun τ : L ≃ₐ[K] L => σ₀.comp (τ : L →ₐ[K] L)))
    (Pi.algHom K (fun _ : L ≃ₐ[K] L => F) (fun _ : L ≃ₐ[K] L => AlgHom.id K F))

theorem Φ_tmul (ℓ : L) (f : F) (τ : L ≃ₐ[K] L) : Φ F σ₀ (ℓ ⊗ₜ f) τ = σ₀ (τ ℓ) * f := by
  simp [Φ, Algebra.TensorProduct.productMap_apply_tmul]

theorem Φ_algebraMap (f : F) : Φ F σ₀ (algebraMap F (L ⊗[K] F) f) = algebraMap F ((L ≃ₐ[K] L) → F) f := by
  funext τ
  rw [show algebraMap F (L ⊗[K] F) f = (1 : L) ⊗ₜ[K] f from rfl, Φ_tmul, map_one, map_one, one_mul,
    Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem Φ_congr (τ' : L ≃ₐ[K] L) (z : L ⊗[K] F) (τ : L ≃ₐ[K] L) :
    Φ F σ₀ (Algebra.TensorProduct.congr τ' (AlgEquiv.refl : F ≃ₐ[K] F) z) τ = Φ F σ₀ z (τ * τ') := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul ℓ f =>
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    simp only [AlgHom.coe_coe, AlgEquiv.coe_refl, Φ_tmul, AlgEquiv.mul_apply]
    rfl
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

def ΦF : (L ⊗[K] F) ≃ₐ[F] ((L ≃ₐ[K] L) → F) :=
  AlgEquiv.ofBijective
    ({ toFun := Φ F σ₀
       map_one' := map_one _
       map_mul' := map_mul _
       map_zero' := map_zero _
       map_add' := map_add _
       commutes' := fun f => Φ_algebraMap F σ₀ f } : (L ⊗[K] F) →ₐ[F] ((L ≃ₐ[K] L) → F))
    (Algebra.TensorProduct.bijective_productMap_pi_comp_of_isGalois K L F σ₀)

theorem ΦF_apply (z : L ⊗[K] F) : ΦF F σ₀ z = Φ F σ₀ z := rfl

theorem norm_eq_prod_Φ (z : L ⊗[K] F) : Algebra.norm F z = ∏ τ : L ≃ₐ[K] L, Φ F σ₀ z τ := by
  classical
  rw [← Algebra.norm_eq_of_algEquiv (ΦF F σ₀) z, ΦF_apply, norm_pi]

end WithF

theorem map_id_congr {E F : Type*} [Field E] [Algebra K E] [Field F] [Algebra K F] (ι : E →ₐ[K] F)
    (τ' : L ≃ₐ[K] L) (z : L ⊗[K] E) :
    Algebra.TensorProduct.map (AlgHom.id K L) ι (Algebra.TensorProduct.congr τ' (AlgEquiv.refl : E ≃ₐ[K] E) z) =
      Algebra.TensorProduct.congr τ' (AlgEquiv.refl : F ≃ₐ[K] F) (Algebra.TensorProduct.map (AlgHom.id K L) ι z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul ℓ e =>
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_coe,
      AlgEquiv.coe_refl, AlgHom.id_apply]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem main (E : Type*) [Field E] [Algebra K E] (x : L ⊗[K] E) :
    algebraMap E (L ⊗[K] E) (Algebra.norm E x) =
      ∏ τ : L ≃ₐ[K] L, Algebra.TensorProduct.congr τ (AlgEquiv.refl : E ≃ₐ[K] E) x := by
  classical

  haveI : Nontrivial (L ⊗[K] E) := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K L E
    (algebraMap K L).injective (algebraMap K E).injective
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (L ⊗[K] E)
  let F : Type _ := (L ⊗[K] E) ⧸ 𝔪
  letI : Field F := Ideal.Quotient.field 𝔪
  let π : L ⊗[K] E →ₐ[K] F := Ideal.Quotient.mkₐ K 𝔪
  let σ₀ : L →ₐ[K] F := π.comp Algebra.TensorProduct.includeLeft
  let ι : E →ₐ[K] F := π.comp Algebra.TensorProduct.includeRight
  let j : L ⊗[K] E →ₐ[K] L ⊗[K] F := Algebra.TensorProduct.map (AlgHom.id K L) ι

  have hι : Function.Injective ι := ι.toRingHom.injective
  have hj : Function.Injective j := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := L) ι.toLinearMap hι
    exact h

  have hΦ := (Algebra.TensorProduct.bijective_productMap_pi_comp_of_isGalois K L F σ₀).1
  apply hj
  apply hΦ
  change Φ F σ₀ (j (algebraMap E (L ⊗[K] E) (Algebra.norm E x))) =
    Φ F σ₀ (j (∏ τ : L ≃ₐ[K] L, Algebra.TensorProduct.congr τ (AlgEquiv.refl : E ≃ₐ[K] E) x))

  have hjalg : j (algebraMap E (L ⊗[K] E) (Algebra.norm E x)) = algebraMap F (L ⊗[K] F) (ι (Algebra.norm E x)) := by
    show j ((1 : L) ⊗ₜ[K] Algebra.norm E x) = (1 : L) ⊗ₜ[K] ι (Algebra.norm E x)
    rw [show j ((1 : L) ⊗ₜ[K] Algebra.norm E x) = (AlgHom.id K L (1 : L)) ⊗ₜ[K] ι (Algebra.norm E x) from
      Algebra.TensorProduct.map_tmul _ _ _ _]
    rfl
  rw [hjalg, Algebra.TensorProduct.map_norm_eq_norm_map_of_rightAlgebra K L E F ι x, Φ_algebraMap,
    norm_eq_prod_Φ F σ₀, map_prod j, map_prod (Φ F σ₀)]
  funext τ
  rw [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, Finset.prod_apply]
  have hjc : ∀ τ' : L ≃ₐ[K] L, Φ F σ₀ (j (Algebra.TensorProduct.congr τ' (AlgEquiv.refl : E ≃ₐ[K] E) x)) τ =
      Φ F σ₀ (j x) (τ * τ') := by
    intro τ'
    show Φ F σ₀ (Algebra.TensorProduct.map (AlgHom.id K L) ι
      (Algebra.TensorProduct.congr τ' (AlgEquiv.refl : E ≃ₐ[K] E) x)) τ = _
    rw [map_id_congr K L ι τ' x, Φ_congr]
  simp_rw [hjc]
  exact (Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)).symm

end NormGal

end

open scoped TensorProduct.RightActions in
theorem solution
    (K L E : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Field E] [Algebra K E] (x : L ⊗[K] E) :
    algebraMap E (L ⊗[K] E) (Algebra.norm E x) =
      ∏ τ : L ≃ₐ[K] L, Algebra.TensorProduct.congr τ (AlgEquiv.refl : E ≃ₐ[K] E) x :=
  NormGal.main K L E x

end S_Algebra_TensorProduct_algebraMap_norm_eq_prod_congr_apply_of_isGalois
end P2MW
export P2MW.S_Algebra_TensorProduct_algebraMap_norm_eq_prod_congr_apply_of_isGalois (solution)
