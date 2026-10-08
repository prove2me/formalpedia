-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralModelContraction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralModelContraction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:06:59.432604+00:00
-- url     : https://prove2.me/theorems/54342f10-5e36-4cd4-903b-a5aeb87e6a16
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralModelContraction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralModelContraction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralModelContraction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicCoordinateBaseChange_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13Infinity_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordRepresentative_p0
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Ideal

set_option autoImplicit false




/-!
# Vertical localization and ideal contraction for the N13 integral model

The affine coordinate ring of the N13 generic fibre is obtained from the
integral good-model coordinate ring by inverting only the nonzero scalars of
`ℤ₂`.  The proof uses the rank-two normal form `p(x) + q(x)y`: a common
scalar denominator clears the two coefficient polynomials simultaneously.

Consequently every ideal on the generic affine fibre has a canonical
contraction to the integral model, and extending this contraction recovers
the original ideal exactly.  The contraction is vertically saturated.  This
is the algebraic integral-model layer needed before taking a reflexive hull
or lifting a section; it does not assert that the contracted ideal is already
invertible on the two-dimensional integral surface.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13IntegralModelContraction

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13TwoAdicCoordinateBaseChange.R₂

abbrev Q₂ : Type :=
  N13TwoAdicCoordinateBaseChange.Q₂

abbrev IntegralRing : Type :=
  N13TwoAdicCoordinateBaseChange.IntegralRing

abbrev GoodRing : Type :=
  N13TwoAdicCoordinateBaseChange.GoodRing

abbrev RationalRing : Type :=
  N13GoodSexticCoordinateEquiv.SexticRing (K := Q₂)

abbrev Pic : Type :=
  SexticMumford.ConcretePic
    (N13Mumford.model Q₂)
    (N13Infinity.positiveInfinityOrder Q₂)

abbrev IntegralOrientedRep : Type :=
  SexticMumford.IntegralOrientedRep
    (N13Mumford.model Q₂)

/-- The integral good model maps to its generalized generic fibre. -/
def integralToGood : IntegralRing →+* GoodRing :=
  N13TwoAdicCoordinateBaseChange.extendCoordinate

local instance integralGoodAlgebra :
    Algebra IntegralRing GoodRing :=
  integralToGood.toAlgebra

/-- The vertical multiplicative set consists exactly of nonzero `ℤ₂`
scalars inside the integral coordinate ring. -/
def verticalScalars : Submonoid IntegralRing :=
  (nonZeroDivisors R₂).map
    (algebraMap R₂ IntegralRing)

local instance polynomialAlgebra :
    Algebra R₂[X] Q₂[X] :=
  Polynomial.algebra R₂ Q₂

local instance polynomialLocalization :
    IsLocalization
      ((nonZeroDivisors R₂).map
        (Polynomial.C : R₂ →+* R₂[X]).toMonoidHom)
      Q₂[X] :=
  Polynomial.isLocalization (nonZeroDivisors R₂) Q₂

@[simp] theorem integralToGood_algebraMap
    (a : R₂) :
    integralToGood (algebraMap R₂ IntegralRing a) =
      algebraMap Q₂ GoodRing
        (N13TwoAdicCoordinateBaseChange.coeffMap a) := by
  change
    N13TwoAdicCoordinateBaseChange.extendCoordinate
        (N13GeneralizedMumfordIntegral.xClass (C a)) =
      N13GeneralizedMumfordIntegral.xClass
        (C (N13TwoAdicCoordinateBaseChange.coeffMap a))
  rw [N13TwoAdicCoordinateBaseChange.extend_xClass]
  simp [N13TwoAdicCoordinateBaseChange.mapPoly,
    N13TwoAdicCoordinateBaseChange.coeffMap]

/-- Inverting the vertical nonzero scalars produces the generalized generic
fibre coordinate ring. -/
theorem goodRing_isLocalization :
    IsLocalization verticalScalars GoodRing := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have hs := s.property
    change
      ∃ r : R₂, r ∈ nonZeroDivisors R₂ ∧
        algebraMap R₂ IntegralRing r =
          (s : IntegralRing) at hs
    obtain ⟨r, hr, hs⟩ := hs
    change IsUnit (integralToGood (s : IntegralRing))
    rw [← hs, integralToGood_algebraMap]
    have hr0 :
        N13TwoAdicCoordinateBaseChange.coeffMap r ≠ 0 := by
      change algebraMap R₂ Q₂ r ≠ 0
      simpa using
        (IsFractionRing.injective R₂ Q₂).ne
          (mem_nonZeroDivisors_iff_ne_zero.mp hr)
    exact IsUnit.map (algebraMap Q₂ GoodRing)
      (isUnit_iff_ne_zero.mpr hr0)
  · intro z
    obtain ⟨p, q, d, hp, hq⟩ :=
      IsLocalization.surj₂
        ((nonZeroDivisors R₂).map
          (Polynomial.C : R₂ →+* R₂[X]).toMonoidHom)
        Q₂[X]
        (N13GeneralizedMumfordIntegral.coeff0 z)
        (N13GeneralizedMumfordIntegral.coeffY z)
    obtain ⟨r, hr, hd⟩ := d.property
    change C r = (d : R₂[X]) at hd
    rw [← hd] at hp hq
    rw [Polynomial.algebraMap_def] at hp hq
    have hp0 :
        N13GeneralizedMumfordIntegral.coeff0 z *
            C (N13TwoAdicCoordinateBaseChange.coeffMap r) =
          N13TwoAdicCoordinateBaseChange.mapPoly p := by
      simpa [N13TwoAdicCoordinateBaseChange.mapPoly,
        N13TwoAdicCoordinateBaseChange.coeffMap,
        N13TwoAdicMumfordTransport.mapPoly,
        N13TwoAdicMumfordTransport.coeffMap] using hp
    have hq0 :
        N13GeneralizedMumfordIntegral.coeffY z *
            C (N13TwoAdicCoordinateBaseChange.coeffMap r) =
          N13TwoAdicCoordinateBaseChange.mapPoly q := by
      simpa [N13TwoAdicCoordinateBaseChange.mapPoly,
        N13TwoAdicCoordinateBaseChange.coeffMap,
        N13TwoAdicMumfordTransport.mapPoly,
        N13TwoAdicMumfordTransport.coeffMap] using hq
    let numerator : IntegralRing :=
      N13GeneralizedMumfordIntegral.xClass p +
        N13GeneralizedMumfordIntegral.xClass q *
          N13GeneralizedMumfordIntegral.yClass
    let denominator : verticalScalars :=
      ⟨algebraMap R₂ IntegralRing r,
        ⟨r, hr, rfl⟩⟩
    refine ⟨⟨numerator, denominator⟩, ?_⟩
    change
      z * integralToGood (denominator : IntegralRing) =
        integralToGood numerator
    dsimp only [denominator, numerator]
    rw [← N13GeneralizedMumfordIntegral.recompose z]
    rw [integralToGood_algebraMap]
    unfold integralToGood
    simp only [map_add, map_mul,
      N13TwoAdicCoordinateBaseChange.extend_xClass,
      N13TwoAdicCoordinateBaseChange.extend_yClass]
    have hscalar :
        algebraMap Q₂ GoodRing
            (N13TwoAdicCoordinateBaseChange.coeffMap r) =
          N13GeneralizedMumfordIntegral.xClass
            (C (N13TwoAdicCoordinateBaseChange.coeffMap r)) :=
      rfl
    rw [hscalar]
    have hp' := congrArg
      (N13GeneralizedMumfordIntegral.xClass (R := Q₂)) hp0
    have hq' := congrArg
      (N13GeneralizedMumfordIntegral.xClass (R := Q₂)) hq0
    simp only [
      N13GeneralizedMumfordIntegral.xClass_mul] at hp' hq'
    calc
      (N13GeneralizedMumfordIntegral.xClass
              (N13GeneralizedMumfordIntegral.coeff0 z) +
            N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeffY z) *
              N13GeneralizedMumfordIntegral.yClass) *
            N13GeneralizedMumfordIntegral.xClass
              (C (N13TwoAdicCoordinateBaseChange.coeffMap r)) =
          N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeff0 z) *
              N13GeneralizedMumfordIntegral.xClass
                (C (N13TwoAdicCoordinateBaseChange.coeffMap r)) +
            (N13GeneralizedMumfordIntegral.xClass
                  (N13GeneralizedMumfordIntegral.coeffY z) *
                N13GeneralizedMumfordIntegral.xClass
                  (C (N13TwoAdicCoordinateBaseChange.coeffMap r))) *
              N13GeneralizedMumfordIntegral.yClass := by ring
      _ =
          N13GeneralizedMumfordIntegral.xClass
              (N13TwoAdicCoordinateBaseChange.mapPoly p) +
            N13GeneralizedMumfordIntegral.xClass
                (N13TwoAdicCoordinateBaseChange.mapPoly q) *
              N13GeneralizedMumfordIntegral.yClass := by
            rw [hp', hq']
  · intro x y hxy
    exact
      ⟨1, by
        simpa using
          N13TwoAdicCoordinateBaseChange.extendCoordinate_injective hxy⟩

local instance goodRingLocalization :
    IsLocalization verticalScalars GoodRing :=
  goodRing_isLocalization

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

/-- Completion of the square is an equivalence over the integral model. -/
def goodToSextic :
    GoodRing ≃ₐ[IntegralRing] RationalRing where
  __ :=
    N13GoodSexticCoordinateEquiv.coordinateRingEquiv
      (K := Q₂)
  commutes' _ := rfl

/-- The standard sextic generic-fibre coordinate ring is the same vertical
localization. -/
theorem rationalRing_isLocalization :
    IsLocalization verticalScalars RationalRing :=
  IsLocalization.isLocalization_of_algEquiv
    verticalScalars goodToSextic

local instance rationalRingLocalization :
    IsLocalization verticalScalars RationalRing :=
  rationalRing_isLocalization

/-- Canonical contraction of a generic-fibre ideal to the integral model. -/
def contractIdeal
    (J : Ideal RationalRing) :
    Ideal IntegralRing :=
  J.under IntegralRing

/-- Extending the canonical contraction recovers the generic-fibre ideal
exactly. -/
theorem map_contractIdeal
    (J : Ideal RationalRing) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (contractIdeal J) =
      J := by
  exact IsLocalization.map_under
    verticalScalars RationalRing J

/-- Contraction loses no nonzero ideal. -/
theorem contractIdeal_ne_bot
    {J : Ideal RationalRing}
    (hJ : J ≠ ⊥) :
    contractIdeal J ≠ ⊥ := by
  intro hbot
  apply hJ
  rw [← map_contractIdeal J, hbot, Ideal.map_bot]

/-- The contracted ideal is saturated with respect to every nonzero
vertical scalar. -/
theorem contractIdeal_vertical_saturated
    (J : Ideal RationalRing)
    {a : IntegralRing}
    (r : R₂) (hr : r ≠ 0)
    (ha :
      algebraMap R₂ IntegralRing r * a ∈
        contractIdeal J) :
    a ∈ contractIdeal J := by
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic a ∈ J
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic
        (algebraMap R₂ IntegralRing r * a) ∈ J at ha
  rw [map_mul] at ha
  let s : verticalScalars :=
    ⟨algebraMap R₂ IntegralRing r,
      ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr, rfl⟩⟩
  have hs :
      IsUnit
        (algebraMap IntegralRing RationalRing s) :=
    IsLocalization.map_units RationalRing s
  exact (Ideal.unit_mul_mem_iff_mem J hs).mp ha

/-- Every local oriented Picard class therefore has a canonical integral
model ideal whose generic fibre is exactly an integral ideal representative
of that class.  This statement does not yet promote the contraction to an
invertible ideal on the integral surface. -/
theorem exists_integralModelIdeal
    (c : Pic) :
    ∃ J₀ : Ideal IntegralRing,
      ∃ R : IntegralOrientedRep,
        J₀ ≠ ⊥ ∧
          Ideal.map
              N13TwoAdicCoordinateBaseChange.integralToSextic
              J₀ =
            R.ideal ∧
          R.picClass
              (N13Mumford.model Q₂)
              (N13Infinity.positiveInfinityOrder Q₂) =
            c := by
  obtain ⟨R, hR⟩ :=
    SexticMumford.exists_integralRepresentative
      (N13Mumford.model Q₂)
      (N13Infinity.positiveInfinityOrder Q₂)
      c
  exact
    ⟨contractIdeal R.ideal, R,
      contractIdeal_ne_bot
        (R.ideal_ne_bot (N13Mumford.model Q₂)),
      map_contractIdeal R.ideal, hR⟩

end

end MazurProof.N13IntegralModelContraction


