-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_sub_algebraMap_mem_of_isMaximal_chartAlgFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2c639760-8745-5c7e-99c5-8c0ea5292811

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_sub_algebraMap_mem_of_isMaximal_chartAlgFin

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 4000000

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel IsLocalRing

namespace H34RF

variable {R F : Type} [CommRing R] [IsLocalRing R] [Field F] [Algebra R F]

theorem exists_sub_algebraMap_mem (hres : IsAlgClosed (ResidueField R)) (j : F)
    (y : Ideal ↥(chartAlgFin R F j)) (hy : y.IsMaximal)
    (hmy : ∀ r ∈ maximalIdeal R, algebraMap R ↥(chartAlgFin R F j) r ∈ y)
    (b : ↥(chartAlgFin R F j)) : ∃ c : R, b - algebraMap R ↥(chartAlgFin R F j) c ∈ y := by
  classical
  haveI : y.IsMaximal := hy
  letI : Field (↥(chartAlgFin R F j) ⧸ y) := Ideal.Quotient.field y

  set φ : R →+* ↥(chartAlgFin R F j) ⧸ y := (Ideal.Quotient.mk y).comp (algebraMap R ↥(chartAlgFin R F j)) with hφ
  have hφm : ∀ r ∈ maximalIdeal R, φ r = 0 := fun r hr =>
    (Ideal.Quotient.eq_zero_iff_mem).mpr (hmy r hr)
  set φκ : ResidueField R →+* ↥(chartAlgFin R F j) ⧸ y := Ideal.Quotient.lift (maximalIdeal R) φ hφm with hφκ
  letI algκ : Algebra (ResidueField R) (↥(chartAlgFin R F j) ⧸ y) := φκ.toAlgebra

  set A₁ : Subalgebra R F := Algebra.adjoin R {j} with hA₁
  have hle : A₁ ≤ chartAlgFin R F j := fun x hx => by
    show IsIntegral (↥(Algebra.adjoin R ({j} : Set F))) x
    exact ⟨Polynomial.X - Polynomial.C ⟨x, hx⟩, Polynomial.monic_X_sub_C _, by simp⟩
  letI algA : Algebra ↥A₁ ↥(chartAlgFin R F j) := (Subalgebra.inclusion hle).toAlgebra
  haveI : IsScalarTower ↥A₁ ↥(chartAlgFin R F j) F := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI hint : Algebra.IsIntegral ↥A₁ ↥(chartAlgFin R F j) := by
    refine ⟨fun x => ?_⟩
    have hx : IsIntegral ↥A₁ (x : F) := x.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥A₁ ↥(chartAlgFin R F j) F) Subtype.val_injective).mp hx

  set 𝔭 : Ideal ↥A₁ := y.comap (algebraMap ↥A₁ ↥(chartAlgFin R F j)) with h𝔭
  letI algQ : Algebra (↥A₁ ⧸ 𝔭) (↥(chartAlgFin R F j) ⧸ y) := inferInstance
  haveI : Algebra.IsIntegral (↥A₁ ⧸ 𝔭) (↥(chartAlgFin R F j) ⧸ y) := Algebra.IsIntegral.quotient
  have hinj : Function.Injective (algebraMap (↥A₁ ⧸ 𝔭) (↥(chartAlgFin R F j) ⧸ y)) := Ideal.algebraMap_quotient_injective
  have hF1 : IsField (↥A₁ ⧸ 𝔭) := isField_of_isIntegral_of_isField hinj (Field.toIsField _)
  letI : Field (↥A₁ ⧸ 𝔭) := hF1.toField

  have h𝔭m : ∀ r ∈ maximalIdeal R, algebraMap R ↥A₁ r ∈ 𝔭 := by
    intro r hr
    rw [h𝔭, Ideal.mem_comap]
    exact hmy r hr
  set φ₁ : R →+* ↥A₁ ⧸ 𝔭 := (Ideal.Quotient.mk 𝔭).comp (algebraMap R ↥A₁) with hφ₁
  have hφ₁m : ∀ r ∈ maximalIdeal R, φ₁ r = 0 := fun r hr =>
    (Ideal.Quotient.eq_zero_iff_mem).mpr (h𝔭m r hr)
  set φ₁κ : ResidueField R →+* ↥A₁ ⧸ 𝔭 := Ideal.Quotient.lift (maximalIdeal R) φ₁ hφ₁m with hφ₁κ
  letI alg₁ : Algebra (ResidueField R) (↥A₁ ⧸ 𝔭) := φ₁κ.toAlgebra
  haveI : IsScalarTower R (ResidueField R) (↥A₁ ⧸ 𝔭) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Algebra.FiniteType R ↥A₁ := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton j)
  haveI : Algebra.FiniteType R (↥A₁ ⧸ 𝔭) := inferInstance
  haveI : Algebra.FiniteType (ResidueField R) (↥A₁ ⧸ 𝔭) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (ResidueField R) (↥A₁ ⧸ 𝔭)

  haveI : Module.Finite (ResidueField R) (↥A₁ ⧸ 𝔭) := finite_of_finite_type_of_isJacobsonRing (ResidueField R) (↥A₁ ⧸ 𝔭)
  haveI : Algebra.IsIntegral (ResidueField R) (↥A₁ ⧸ 𝔭) := Algebra.IsIntegral.of_finite (ResidueField R) (↥A₁ ⧸ 𝔭)

  haveI : IsScalarTower (ResidueField R) (↥A₁ ⧸ 𝔭) (↥(chartAlgFin R F j) ⧸ y) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    rfl
  haveI : Algebra.IsIntegral (ResidueField R) (↥(chartAlgFin R F j) ⧸ y) := Algebra.IsIntegral.trans (↥A₁ ⧸ 𝔭)
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField R) (K := ↥(chartAlgFin R F j) ⧸ y)).2
    (Ideal.Quotient.mk y b)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨r, ?_⟩
  rw [← Ideal.Quotient.eq, ← hc]
  rfl

end H34RF

theorem solution
    {R F : Type} [CommRing R] [IsLocalRing R] [Field F] [Algebra R F]
    (hres : IsAlgClosed (ResidueField R)) (j : F)
    (y : Ideal ↥(chartAlgFin R F j)) (hy : y.IsMaximal)
    (hmy : ∀ r ∈ maximalIdeal R, algebraMap R ↥(chartAlgFin R F j) r ∈ y)
    (b : ↥(chartAlgFin R F j)) : ∃ c : R, b - algebraMap R ↥(chartAlgFin R F j) c ∈ y :=
  H34RF.exists_sub_algebraMap_mem hres j y hy hmy b

end S_AlgebraicCurve_TwoChartIntegralModel_exists_sub_algebraMap_mem_of_isMaximal_chartAlgFin
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_sub_algebraMap_mem_of_isMaximal_chartAlgFin (solution)
