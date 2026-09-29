-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.smooth_tensorProduct_chartAlgFin_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b55e6220-d36e-50ef-8935-bbe72c740bfd

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isLocalization_chartAlg
import Theorems.Thm_Algebra_Smooth_of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_smooth_tensorProduct_chartAlgFin_of_charZero

set_option autoImplicit false

open scoped TensorProduct
open AlgebraicCurve.TwoChartIntegralModel

universe u

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]
    (K₀ : Type u) [Field K₀] [CharZero K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F) :
    Algebra.Smooth K₀ (K₀ ⊗[R] ↥(chartAlgFin R F j)) := by
  classical

  have htj' : Transcendental K₀ j := fun h => htj ((IsFractionRing.isAlgebraic_iff R K₀ F).mpr h)
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F := Algebra.IsAlgebraic.of_finite _ _
  haveI : PerfectField K₀ := PerfectField.ofCharZero
  have hRF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  have hRC : Function.Injective (algebraMap R ↥(chartAlgFin R F j)) := by
    intro a b h
    apply hRF
    have := congrArg (fun x : ↥(chartAlgFin R F j) => (x : F)) h
    simpa [Subalgebra.coe_algebraMap] using this

  haveI hFT : Algebra.FiniteType R ↥(chartAlgFin R F j) :=
    (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf R K₀ F j htj hFD hsep).1
  haveI : Algebra.FiniteType K₀ (K₀ ⊗[R] ↥(chartAlgFin R F j)) := inferInstance

  haveI hfrac : IsFractionRing ↥(chartAlgFin R F j) F :=
    AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg R K₀ F ({j} : Set F)
  haveI hIC : IsIntegrallyClosed ↥(chartAlgFin R F j) := by
    rw [isIntegrallyClosed_iff F]
    intro x hx
    have hle : Algebra.adjoin R ({j} : Set F) ≤ chartAlgFin R F j := adjoin_le_chartAlg R F {j}
    letI : Algebra ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) := (Subalgebra.inclusion hle).toRingHom.toAlgebra
    haveI : IsScalarTower ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) F := IsScalarTower.of_algebraMap_eq (fun a => rfl)
    haveI : Algebra.IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) := ⟨fun b => by
      have hb : IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) ((b : ↥(chartAlgFin R F j)) : F) := (mem_chartAlg_iff R F).mp b.2
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) F)
        (fun a b h => Subtype.ext h)).mp hb⟩
    have hx' : IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) x := isIntegral_trans x hx
    exact ⟨⟨x, (mem_chartAlg_iff R F).mpr hx'⟩, rfl⟩

  letI : Algebra ↥(chartAlgFin R F j) (K₀ ⊗[R] ↥(chartAlgFin R F j)) := Algebra.TensorProduct.rightAlgebra
  haveI hlocT : IsLocalization (Algebra.algebraMapSubmonoid ↥(chartAlgFin R F j) (nonZeroDivisors R)) (K₀ ⊗[R] ↥(chartAlgFin R F j)) :=
    IsLocalization.tensorRight K₀ (nonZeroDivisors R)
  have hM' : Algebra.algebraMapSubmonoid ↥(chartAlgFin R F j) (nonZeroDivisors R) ≤ nonZeroDivisors ↥(chartAlgFin R F j) := by
    rintro x ⟨m, hm, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    apply nonZeroDivisors.ne_zero hm
    exact hRC (by rw [h0, map_zero])
  haveI : IsDomain (K₀ ⊗[R] ↥(chartAlgFin R F j)) := IsLocalization.isDomain_of_le_nonZeroDivisors (K₀ ⊗[R] ↥(chartAlgFin R F j)) hM'
  haveI : IsIntegrallyClosed (K₀ ⊗[R] ↥(chartAlgFin R F j)) := isIntegrallyClosed_of_isLocalization (K₀ ⊗[R] ↥(chartAlgFin R F j)) _ hM'

  have hfin := (AlgebraicCurve.TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf K₀ K₀ F j htj' hFD hsep).1
  haveI hK1 : Ring.KrullDimLE 1 ↥(chartAlgFin K₀ F j) := by
    letI algP : Algebra (Polynomial K₀) ↥(chartAlgFin K₀ F j) := (polynomialToChartFin K₀ F j).toRingHom.toAlgebra
    haveI : Module.Finite (Polynomial K₀) ↥(chartAlgFin K₀ F j) := hfin
    haveI : Algebra.IsIntegral (Polynomial K₀) ↥(chartAlgFin K₀ F j) := inferInstance
    rw [Ring.krullDimLE_one_iff_of_isPrime_bot]
    intro P hP hPp
    haveI := hPp
    have h1 : P.comap (algebraMap (Polynomial K₀) ↥(chartAlgFin K₀ F j)) ≠ ⊥ := fun h => hP (Ideal.eq_bot_of_comap_eq_bot h)
    haveI : (P.comap (algebraMap (Polynomial K₀) ↥(chartAlgFin K₀ F j))).IsPrime := Ideal.comap_isPrime _ P
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P (IsPrime.to_maximal_ideal h1)
  letI algCB : Algebra ↥(chartAlgFin R F j) ↥(chartAlgFin K₀ F j) := (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F K₀ ({j} : Set F)).toAlgebra
  haveI hlocB : IsLocalization (Algebra.algebraMapSubmonoid ↥(chartAlgFin R F j) (nonZeroDivisors R)) ↥(chartAlgFin K₀ F j) :=
    AlgebraicCurve.TwoChartIntegralModel.isLocalization_chartAlg R F K₀ (nonZeroDivisors R) ({j} : Set F)
  have e₀ : (K₀ ⊗[R] ↥(chartAlgFin R F j)) ≃ₐ[↥(chartAlgFin R F j)] ↥(chartAlgFin K₀ F j) :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid ↥(chartAlgFin R F j) (nonZeroDivisors R)) (K₀ ⊗[R] ↥(chartAlgFin R F j)) ↥(chartAlgFin K₀ F j)
  haveI : Ring.KrullDimLE 1 (K₀ ⊗[R] ↥(chartAlgFin R F j)) := by
    rw [Ring.krullDimLE_iff] at hK1 ⊢
    rw [ringKrullDim_eq_of_ringEquiv e₀.toRingEquiv]
    exact hK1
  exact Algebra.Smooth.of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField K₀ (K₀ ⊗[R] ↥(chartAlgFin R F j))

end S_AlgebraicCurve_TwoChartIntegralModel_smooth_tensorProduct_chartAlgFin_of_charZero
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_smooth_tensorProduct_chartAlgFin_of_charZero (solution)
