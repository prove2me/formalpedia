-- Prove2me | solution 1 for AlgebraicGeometry.germToFunctionField_trace_eq_traceFunAlong_germToFunctionField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/562e495b-e9a5-56ee-b30e-ee9acb20b5d3

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Theorems.Thm_AlgebraicCurve_germToFunctionField_app_eq_of_fromSpecStalk_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_germToFunctionField_trace_eq_traceFunAlong_germToFunctionField

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem solution
    {K : Type u} [Field K] {X Y : Scheme.{u}} (cX : X ⟶ Spec (.of K)) (cY : Y ⟶ Spec (.of K))
    [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) [IsAffineHom π] (hπ : π ≫ cX = cY)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (π ⁻¹ᵁ U : Y.Opens)] :
    letI := (AlgebraicCurve.baseToFunctionField cX).toAlgebra
    letI := (AlgebraicCurve.baseToFunctionField cY).toAlgebra
    letI : Algebra Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
    ∀ [Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U)] [Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U)]
      (φ : X.functionField →ₐ[K] Y.functionField)
      (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
      (g : Γ(Y, π ⁻¹ᵁ U)),
      (X.germToFunctionField U).hom (Algebra.trace Γ(X, U) Γ(Y, π ⁻¹ᵁ U) g) =
        AlgebraicCurve.traceFunAlong φ ((Y.germToFunctionField (π ⁻¹ᵁ U)).hom g) := by
  intro _ _ φ hφπ g
  letI := (AlgebraicCurve.baseToFunctionField cX).toAlgebra
  letI := (AlgebraicCurve.baseToFunctionField cY).toAlgebra
  letI iAB : Algebra Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra

  letI : Algebra X.functionField Y.functionField := AlgebraicCurve.algebraAlong φ
  have hUaff : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  haveI : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  haveI : IsFractionRing Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ hUaff

  have hnat : ∀ a : Γ(X, U), (Y.germToFunctionField (π ⁻¹ᵁ U)).hom (π.app U a) =
      φ ((X.germToFunctionField U).hom a) := fun a =>
    AlgebraicCurve.germToFunctionField_app_eq_of_fromSpecStalk_comp_eq π φ.toRingHom hφπ U a

  letI : Algebra Γ(X, U) Y.functionField :=
    ((algebraMap Γ(Y, π ⁻¹ᵁ U) Y.functionField).comp (algebraMap Γ(X, U) Γ(Y, π ⁻¹ᵁ U))).toAlgebra
  haveI : IsScalarTower Γ(X, U) Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a => hnat a)

  haveI : FaithfulSMul Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h := congrArg (fun t => (Y.germToFunctionField (π ⁻¹ᵁ U)).hom t) hab
    change (Y.germToFunctionField (π ⁻¹ᵁ U)).hom (π.app U a) =
      (Y.germToFunctionField (π ⁻¹ᵁ U)).hom (π.app U b) at h
    rw [hnat, hnat] at h
    exact X.germToFunctionField_injective U (φ.toRingHom.injective h)
  haveI : Algebra.IsIntegral Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsAlgebraic Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := Algebra.IsIntegral.isAlgebraic
  have key : Algebra.trace X.functionField Y.functionField (algebraMap Γ(Y, π ⁻¹ᵁ U) Y.functionField g) =
      algebraMap Γ(X, U) X.functionField (Algebra.trace Γ(X, U) Γ(Y, π ⁻¹ᵁ U) g) :=
    Algebra.trace_localization Γ(X, U) (nonZeroDivisors Γ(X, U)) g
  rw [AlgebraicCurve.traceFunAlong_apply]
  exact key.symm

end S_AlgebraicGeometry_germToFunctionField_trace_eq_traceFunAlong_germToFunctionField
end P2MW
export P2MW.S_AlgebraicGeometry_germToFunctionField_trace_eq_traceFunAlong_germToFunctionField (solution)
