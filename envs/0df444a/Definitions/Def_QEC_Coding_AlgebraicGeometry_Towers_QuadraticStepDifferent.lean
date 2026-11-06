-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
-- name    : QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:45:59.811191+00:00
-- url     : https://prove2.me/theorems/f91705b7-8fba-418a-a31e-3c94276da022
-- title:
--   Quadratic Step Different
-- statement:
--   Definitions and structural lemmas for Quadratic Step Different, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStepDifferent.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing

set_option autoImplicit false
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
instance quadraticArtinSchreierValuationRingScalarTower
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    IsScalarTower P.valuationRing K (QuadraticArtinSchreierField P a ha) :=
  IsScalarTower.of_algebraMap_eq' rfl
abbrev QuadraticArtinSchreierIntegralClosure
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :=
  integralClosure P.valuationRing (QuadraticArtinSchreierField P a ha)
noncomputable instance quadraticArtinSchreierIntegralClosureIsTorsionFree
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Module.IsTorsionFree P.valuationRing
      (QuadraticArtinSchreierIntegralClosure P a ha) := by
  letI : Module.IsTorsionFree P.valuationRing
      (QuadraticArtinSchreierField P a ha) :=
    Module.IsTorsionFree.trans_faithfulSMul
      P.valuationRing K (QuadraticArtinSchreierField P a ha)
  exact IsIntegralClosure.isTorsionFree
    P.valuationRing (QuadraticArtinSchreierField P a ha)
noncomputable instance quadraticArtinSchreierIntegralClosureFinite
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Module.Finite P.valuationRing
      (QuadraticArtinSchreierIntegralClosure P a ha) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite P.valuationRing K
    (QuadraticArtinSchreierField P a ha)
    (QuadraticArtinSchreierIntegralClosure P a ha)
noncomputable instance quadraticArtinSchreierIntegralClosureIsFractionRing
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    IsFractionRing (QuadraticArtinSchreierIntegralClosure P a ha)
      (QuadraticArtinSchreierField P a ha) :=
  integralClosure.isFractionRing_of_finite_extension K
    (QuadraticArtinSchreierField P a ha)
noncomputable instance quadraticArtinSchreierIntegralClosureIsDedekindDomain
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    IsDedekindDomain (QuadraticArtinSchreierIntegralClosure P a ha) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain P.valuationRing K
    (QuadraticArtinSchreierField P a ha)
noncomputable def quadraticArtinSchreierIntegralRoot
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    QuadraticArtinSchreierIntegralClosure P a ha := by
  refine ⟨quadraticArtinSchreierReciprocalRoot P a ha, ?_⟩
  refine ⟨quadraticArtinSchreierReciprocalPolynomial P a ha,
    quadraticArtinSchreierReciprocalPolynomial_monic P a ha, ?_⟩
  change eval₂
      ((AdjoinRoot.of (quadraticArtinSchreierPolynomial P a ha)).comp
        (algebraMap P.valuationRing K))
      (quadraticArtinSchreierReciprocalRoot P a ha)
      (quadraticArtinSchreierReciprocalPolynomial P a ha) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root (quadraticArtinSchreierPolynomial P a ha)
noncomputable def quadraticArtinSchreierIntegralUniformizer
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    QuadraticArtinSchreierIntegralClosure P a ha := by
  refine ⟨quadraticArtinSchreierEmbedding P a ha a⁻¹, ?_⟩
  change IsIntegral P.valuationRing
    (algebraMap P.valuationRing (QuadraticArtinSchreierField P a ha)
      (reciprocalUniformizer P a ha))
  exact isIntegral_algebraMap
theorem exists_quadraticArtinSchreierUpperIdeal
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    ∃ Q : Ideal (QuadraticArtinSchreierIntegralClosure P a ha),
      Q.IsMaximal ∧
        Q.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := QuadraticArtinSchreierIntegralClosure P a ha)
    (IsLocalRing.maximalIdeal P.valuationRing)
noncomputable def quadraticArtinSchreierUpperIdeal
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Ideal (QuadraticArtinSchreierIntegralClosure P a ha) :=
  Classical.choose (exists_quadraticArtinSchreierUpperIdeal P a ha)
theorem quadraticArtinSchreierUpperIdeal_isMaximal
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierUpperIdeal P a ha).IsMaximal :=
  (Classical.choose_spec
    (exists_quadraticArtinSchreierUpperIdeal P a ha)).1
theorem quadraticArtinSchreierUpperIdeal_liesOver
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierUpperIdeal P a ha).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
  (Classical.choose_spec
    (exists_quadraticArtinSchreierUpperIdeal P a ha)).2
noncomputable def quadraticArtinSchreierUpperHeightOne
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    IsDedekindDomain.HeightOneSpectrum
      (QuadraticArtinSchreierIntegralClosure P a ha) :=
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : (quadraticArtinSchreierUpperIdeal P a ha).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
    quadraticArtinSchreierUpperIdeal_liesOver P a ha
  { asIdeal := quadraticArtinSchreierUpperIdeal P a ha
    isPrime := (quadraticArtinSchreierUpperIdeal_isMaximal P a ha).isPrime
    ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
      (IsDiscreteValuationRing.not_a_field P.valuationRing)
      (quadraticArtinSchreierUpperIdeal P a ha) }
noncomputable def quadraticArtinSchreierAbovePlace
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    GlobalPlace F256 (QuadraticArtinSchreierField P a ha) where
  valuation := (quadraticArtinSchreierUpperHeightOne P a ha).valuation
    (QuadraticArtinSchreierField P a ha)
  normalized :=
    (quadraticArtinSchreierUpperHeightOne P a ha).valuation_surjective
      (QuadraticArtinSchreierField P a ha)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


