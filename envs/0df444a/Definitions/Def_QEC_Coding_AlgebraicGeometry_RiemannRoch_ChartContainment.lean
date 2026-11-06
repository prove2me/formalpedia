-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ChartContainment
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_ChartContainment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:51:50.49877+00:00
-- url     : https://prove2.me/theorems/f57238fb-f6d2-4cc3-a743-7350bd234bae
-- title:
--   Chart Containment
-- statement:
--   Definitions and structural lemmas for Chart Containment, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ChartContainment.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
variable [τ : IsScalarTower k[X] k⟮X⟯ F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable k⟮X⟯ F]
theorem affineGlobalPlace_injective :
    Function.Injective (AffinePlace.globalPlace k F) := by
  letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  intro P Q h
  apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F)
  exact Valuation.IsEquiv.of_eq (congrArg (fun V : GlobalPlace k F => V.valuation) h)
noncomputable def GlobalPlace.directChartDivisor
    (G : Divisor (@GlobalPlace k F _ _ _ (@AffinePlace.constantAlgebra k F _ _ π))) :
    Divisor (AffinePlace.carrier k F) :=
  Finsupp.comapDomain (AffinePlace.globalPlace k F) G
    (affineGlobalPlace_injective k F).injOn
noncomputable def InverseAffinePlace.asGlobalPlace
    (P : InverseAffinePlace.carrier k F) :
    let directConstantAlgebra : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    @GlobalPlace k F _ _ _ directConstantAlgebra := by
  let directConstantAlgebra : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  letI : Algebra k F := directConstantAlgebra
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  exact ⟨P.valuation F, P.valuation_surjective F⟩
theorem inverseAffineAsGlobalPlace_injective :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    Function.Injective (InverseAffinePlace.asGlobalPlace (π := π) (ρ := ρ)
      (φ := φ) (s := s) k F) := by
  let directConstantAlgebra : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  letI : Algebra k F := directConstantAlgebra
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  intro P Q h
  apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F)
  exact Valuation.IsEquiv.of_eq (congrArg (fun V : GlobalPlace k F => V.valuation) h)
noncomputable def GlobalPlace.inverseChartDivisor
    (G : Divisor (@GlobalPlace k F _ _ _ (@AffinePlace.constantAlgebra k F _ _ π))) :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    Divisor (AffinePlace.carrier k F) := by
  let directConstantAlgebra : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  letI : Algebra k F := directConstantAlgebra
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  exact Finsupp.comapDomain (InverseAffinePlace.asGlobalPlace (π := π) (ρ := ρ)
    (φ := φ) (s := s) k F) G
    (inverseAffineAsGlobalPlace_injective (π := π) (ρ := ρ) (φ := φ) (s := s) k F).injOn
end QEC.Coding.AlgebraicGeometry


