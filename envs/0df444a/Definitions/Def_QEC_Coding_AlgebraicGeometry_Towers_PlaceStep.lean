-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceStep
-- name    : QEC_Coding_AlgebraicGeometry_Towers_PlaceStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:45:10.043556+00:00
-- url     : https://prove2.me/theorems/b0727a6c-76cd-45d9-b1cd-0b4be63a9d1d
-- title:
--   Place Step
-- statement:
--   Definitions and structural lemmas for Place Step, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceStep.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.GoingUp
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing

set_option autoImplicit false
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
instance stepFieldValuationRingScalarTower
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsScalarTower P.valuationRing K (StepField P x hx) :=
  IsScalarTower.of_algebraMap_eq' rfl
instance stepFieldConstantScalarTower
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsScalarTower F256 K (StepField P x hx) :=
  IsScalarTower.of_algebraMap_eq' rfl
noncomputable instance stepFieldFiniteDimensional
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    FiniteDimensional K (StepField P x hx) :=
  (AdjoinRoot.powerBasis (stepPolynomial_monic P x hx).ne_zero).finite
abbrev StepIntegralClosure (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :=
  integralClosure P.valuationRing (StepField P x hx)
noncomputable instance stepIntegralClosureIsTorsionFree
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Module.IsTorsionFree P.valuationRing (StepIntegralClosure P x hx) := by
  letI : Module.IsTorsionFree P.valuationRing (StepField P x hx) :=
    Module.IsTorsionFree.trans_faithfulSMul
      P.valuationRing K (StepField P x hx)
  exact IsIntegralClosure.isTorsionFree
    P.valuationRing (StepField P x hx)
noncomputable instance stepIntegralClosureFinite
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Module.Finite P.valuationRing (StepIntegralClosure P x hx) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite P.valuationRing K (StepField P x hx)
    (StepIntegralClosure P x hx)
noncomputable instance stepIntegralClosureIsFractionRing
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsFractionRing (StepIntegralClosure P x hx) (StepField P x hx) :=
  integralClosure.isFractionRing_of_finite_extension K (StepField P x hx)
noncomputable instance stepIntegralClosureIsDedekindDomain
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsDedekindDomain (StepIntegralClosure P x hx) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain P.valuationRing K (StepField P x hx)
noncomputable def stepIntegralRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    StepIntegralClosure P x hx := by
  refine ⟨stepReciprocalRoot P x hx, ?_⟩
  refine ⟨reciprocalPolynomial P x hx,
    reciprocalPolynomial_monic P x hx, ?_⟩
  change eval₂
      ((AdjoinRoot.of (stepPolynomial P x hx)).comp
        (algebraMap P.valuationRing K))
      (stepReciprocalRoot P x hx) (reciprocalPolynomial P x hx) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root (stepPolynomial P x hx)
noncomputable def stepIntegralUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    StepIntegralClosure P x hx := by
  refine ⟨stepFieldEmbedding P x hx x⁻¹, ?_⟩
  change IsIntegral P.valuationRing
    (algebraMap P.valuationRing (StepField P x hx)
      (reciprocalUniformizer P x hx))
  exact isIntegral_algebraMap
theorem exists_stepUpperIdeal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    ∃ Q : Ideal (StepIntegralClosure P x hx),
      Q.IsMaximal ∧
        Q.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := StepIntegralClosure P x hx)
    (IsLocalRing.maximalIdeal P.valuationRing)
noncomputable def stepUpperIdeal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Ideal (StepIntegralClosure P x hx) :=
  Classical.choose (exists_stepUpperIdeal P x hx)
theorem stepUpperIdeal_isMaximal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (stepUpperIdeal P x hx).IsMaximal :=
  (Classical.choose_spec (exists_stepUpperIdeal P x hx)).1
theorem stepUpperIdeal_liesOver
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (stepUpperIdeal P x hx).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
  (Classical.choose_spec (exists_stepUpperIdeal P x hx)).2
noncomputable def stepUpperHeightOne
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsDedekindDomain.HeightOneSpectrum (StepIntegralClosure P x hx) :=
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : (stepUpperIdeal P x hx).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
    stepUpperIdeal_liesOver P x hx
  { asIdeal := stepUpperIdeal P x hx
    isPrime := (stepUpperIdeal_isMaximal P x hx).isPrime
    ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
      (IsDiscreteValuationRing.not_a_field P.valuationRing)
      (stepUpperIdeal P x hx) }
noncomputable def stepAbovePlace
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    GlobalPlace F256 (StepField P x hx) where
  valuation := (stepUpperHeightOne P x hx).valuation (StepField P x hx)
  normalized := (stepUpperHeightOne P x hx).valuation_surjective
    (StepField P x hx)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


