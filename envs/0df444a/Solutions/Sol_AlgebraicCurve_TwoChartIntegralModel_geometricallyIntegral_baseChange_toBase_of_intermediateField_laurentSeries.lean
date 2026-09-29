-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.geometricallyIntegral_baseChange_toBase_of_intermediateField_laurentSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f26a38a5-d495-504d-adc5-81f7697eb627

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral_pullback_toBase_of_isDomain_tensorProduct_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_geometricallyIntegral_baseChange_toBase_of_intermediateField_laurentSeries

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_geometricallyIntegral_baseChange_toBase_of_intermediateField_laurentSeries.AlgebraicCurve"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel.chartAlgFin TwoChartIntegralModel.chartAlgInf TwoChartIntegralModel.chartAlgMid TwoChartIntegralModel TwoChartIntegralModel.toBase TwoChartIntegralModel.isIntegral_pullback_toBase_of_isDomain_tensorProduct_chartAlg"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlgFin chartAlgInf chartAlgMid toBase baseChange fibre isIntegral_pullback_toBase_of_isDomain_tensorProduct_chartAlg"
namespace HGIL
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_geometricallyIntegral_baseChange_toBase_of_intermediateField_laurentSeries.AlgebraicCurve"

section LinDisj

variable (L : Type) [Field L] (E : Type) [Field E] [Algebra L E]

theorem linearIndependent_coeffMap {ι : Type*} {v : ι → LaurentSeries L} (hv : LinearIndependent L v) :
    LinearIndependent E (fun i => ModularCurve.coeffMap (algebraMap L E) (v i)) := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  let b := Module.Free.chooseBasis L E
  refine b.forall_coord_eq_zero_iff.mp fun k => ?_
  have hk : ∑ j ∈ s, (b.coord k (g j)) • v j = 0 := by
    ext n
    have hn := congrArg (fun x : LaurentSeries E => b.coord k (x.coeff n)) hg
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, ModularCurve.coeffMap_coeff, smul_eq_mul,
      HahnSeries.coeff_zero, map_zero] at hn
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_zero]
    rw [← hn, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (g j), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  exact hv s (fun j => b.coord k (g j)) hk i hi

variable (K : IntermediateField L (LaurentSeries L))

theorem algebraMap_mul_eq_smul (F : Type) [Field F] (c : F) (y : LaurentSeries F) :
    algebraMap F (LaurentSeries F) c * y = c • y := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul]

noncomputable def valLinear : ↥K →ₗ[L] LaurentSeries L where
  toFun f := (f : LaurentSeries L)
  map_add' _ _ := rfl
  map_smul' c f := by
    rw [RingHom.id_apply, ← algebraMap_mul_eq_smul]
    rfl

theorem valLinear_apply (f : ↥K) : valLinear L K f = (f : LaurentSeries L) := rfl

theorem algebraMap_laurentSeries_eq_single' (c : L) :
    algebraMap L (LaurentSeries E) c = HahnSeries.single 0 (algebraMap L E c) := by
  have h1 : algebraMap L (PowerSeries E) c = PowerSeries.C (algebraMap L E c) := by
    rw [IsScalarTower.algebraMap_apply L E (PowerSeries E) c]
    simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

noncomputable def constHom : E →ₐ[L] LaurentSeries E :=
  { algebraMap E (LaurentSeries E) with
    commutes' := fun c => by
      change algebraMap E (LaurentSeries E) (algebraMap L E c) = algebraMap L (LaurentSeries E) c
      rw [ModularCurve.algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single'] }

noncomputable def coeffHom : ↥K →ₐ[L] LaurentSeries E :=
  { (ModularCurve.coeffMap (algebraMap L E)).comp (K.val : ↥K →+* LaurentSeries L) with
    commutes' := fun c => by
      change ModularCurve.coeffMap (algebraMap L E) (algebraMap L (LaurentSeries L) c) = algebraMap L (LaurentSeries E) c
      rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.coeffMap_single, algebraMap_laurentSeries_eq_single'] }

theorem coeffHom_apply (f : ↥K) : coeffHom L E K f = ModularCurve.coeffMap (algebraMap L E) (f : LaurentSeries L) := rfl

noncomputable def θ : E ⊗[L] ↥K →ₐ[L] LaurentSeries E :=
  Algebra.TensorProduct.productMap (constHom L E) (coeffHom L E K)

theorem θ_tmul (c : E) (f : ↥K) :
    θ L E K (c ⊗ₜ f) = algebraMap E (LaurentSeries E) c * ModularCurve.coeffMap (algebraMap L E) (f : LaurentSeries L) :=
  Algebra.TensorProduct.productMap_apply_tmul _ _ c f

theorem θ_one_tmul (f : ↥K) : θ L E K (1 ⊗ₜ f) = ModularCurve.coeffMap (algebraMap L E) (f : LaurentSeries L) := by
  rw [θ_tmul, map_one, one_mul]

theorem θ_algebraMap (c : E) : θ L E K (algebraMap E (E ⊗[L] ↥K) c) = algebraMap E (LaurentSeries E) c := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, θ_tmul, OneMemClass.coe_one,
    map_one, mul_one]

noncomputable def θL : E ⊗[L] ↥K →ₗ[E] LaurentSeries E where
  toFun := θ L E K
  map_add' := map_add _
  map_smul' c x := by
    rw [RingHom.id_apply, ← algebraMap_mul_eq_smul, ← θ_algebraMap L E K c, ← map_mul, ← Algebra.smul_def]

theorem θL_apply (x : E ⊗[L] ↥K) : θL L E K x = θ L E K x := rfl

theorem θL_injective : Function.Injective (θL L E K) := by
  classical
  let bK := Module.Free.chooseBasis L ↥K
  let B := Algebra.TensorProduct.basis E bK
  have hli : LinearIndependent E (θL L E K ∘ B) := by
    have h : (θL L E K ∘ B : _ → LaurentSeries E) =
        fun i => ModularCurve.coeffMap (algebraMap L E) (valLinear L K (bK i)) := by
      funext i
      rw [Function.comp_apply, θL_apply, Algebra.TensorProduct.basis_apply, θ_one_tmul, valLinear_apply]
    rw [h]
    refine linearIndependent_coeffMap L E ?_
    exact bK.linearIndependent.map' (valLinear L K) (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hrepr : Finsupp.linearCombination E (θL L E K ∘ B) (B.repr x) = 0 := by
    rw [← Finsupp.apply_linearCombination, B.linearCombination_repr]
    exact hx
  have h0 : B.repr x = 0 := linearIndependent_iff.mp hli (B.repr x) hrepr
  rw [← B.linearCombination_repr x, h0, map_zero]

theorem θ_injective : Function.Injective (θ L E K) := θL_injective L E K

theorem isDomain_tensor : IsDomain (E ⊗[L] ↥K) :=
  Function.Injective.isDomain (θ L E K).toRingHom (θ_injective L E K)

end LinDisj

section Charts

variable (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
  (A : Type) [CommRing A] [Algebra A L] [IsFractionRing A L]
  [Algebra A ↥K] [IsScalarTower A L ↥K]
  (E : Type) [Field E] [Algebra L E] [Algebra A E] [IsScalarTower A L E]

theorem isDomain_tensor_subalgebra (𝒪 : Subalgebra A ↥K) : IsDomain (E ⊗[A] ↥𝒪) := by
  haveI : Module.Flat A L := IsLocalization.flat L (nonZeroDivisors A)
  haveI : Module.Flat A E := Module.Flat.trans A L E
  haveI : IsDomain (E ⊗[L] ↥K) := isDomain_tensor L E K

  haveI hdom : IsDomain (E ⊗[A] ↥K) :=
    (IsLocalization.algebraTensorEquiv (nonZeroDivisors A) L E ↥K).symm.injective.isDomain
      (IsLocalization.algebraTensorEquiv (nonZeroDivisors A) L E ↥K).symm.toAlgHom.toRingHom

  let ι := Algebra.TensorProduct.map (AlgHom.id A E) 𝒪.val
  have hlt : ∀ z, LinearMap.lTensor E 𝒪.val.toLinearMap z = ι z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ι, Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  have hι : Function.Injective ι := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := E) 𝒪.val.toLinearMap Subtype.val_injective
    intro x y hxy
    exact h ((hlt x).trans (hxy.trans (hlt y).symm))
  exact hι.isDomain ι

end Charts

end AlgebraicCurve.TwoChartIntegralModel.HGIL

open AlgebraicCurve.TwoChartIntegralModel.HGIL in
open scoped TensorProduct in
theorem solution
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)] :
    GeometricallyIntegral (SmoothProperCurve.baseChange A (TwoChartIntegralModel.toBase A (↥K) j) L) := by
  refine ⟨fun E _ y Z fst snd h => ?_⟩

  obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of L ⟶ CommRingCat.of E, Spec.map φ = y := ⟨Spec.preimage y, Spec.map_preimage y⟩
  letI : Algebra L E := φ.hom.toAlgebra
  letI : Algebra A E := (φ.hom.comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L E := IsScalarTower.of_algebraMap_eq fun _ => rfl

  have hcomp : Spec.map φ ≫ SmoothProperCurve.specMap A L = Spec.map (CommRingCat.ofHom (algebraMap A E)) := by
    rw [SmoothProperCurve.specMap, ← Spec.map_comp]
    rfl
  let e₁ : pullback (SmoothProperCurve.baseChange A (TwoChartIntegralModel.toBase A (↥K) j) L) (Spec.map φ) ≅
      pullback (TwoChartIntegralModel.toBase A (↥K) j) (Spec.map φ ≫ SmoothProperCurve.specMap A L) :=
    pullbackLeftPullbackSndIso _ _ _
  let e₂ : pullback (TwoChartIntegralModel.toBase A (↥K) j) (Spec.map φ ≫ SmoothProperCurve.specMap A L) ≅
      pullback (TwoChartIntegralModel.toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A E))) :=
    pullback.congrHom rfl hcomp

  haveI := isDomain_tensor_subalgebra L K A E (TwoChartIntegralModel.chartAlgFin A (↥K) j)
  haveI := isDomain_tensor_subalgebra L K A E (TwoChartIntegralModel.chartAlgInf A (↥K) j)
  haveI : Nontrivial (E ⊗[A] ↥(TwoChartIntegralModel.chartAlgMid A (↥K) j)) :=
    (isDomain_tensor_subalgebra L K A E (TwoChartIntegralModel.chartAlgMid A (↥K) j)).toNontrivial
  haveI hint : IsIntegral ↑(pullback (TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A E)))) :=
    AlgebraicCurve.TwoChartIntegralModel.isIntegral_pullback_toBase_of_isDomain_tensorProduct_chartAlg A (↥K) j E
  exact IsIntegral.of_isIso ((e₁ ≪≫ e₂).inv ≫ h.isoPullback.inv)

end S_AlgebraicCurve_TwoChartIntegralModel_geometricallyIntegral_baseChange_toBase_of_intermediateField_laurentSeries
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_geometricallyIntegral_baseChange_toBase_of_intermediateField_laurentSeries (solution)
