-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13PrimitiveAffineComparison_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13PrimitiveAffineComparison_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:49:20.740001+00:00
-- url     : https://prove2.me/theorems/723ada14-b755-41c9-9648-8658400ff29f
-- title:
--   FLT.Assumptions.MazurProof.N13PrimitiveAffineComparison source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13PrimitiveAffineComparison

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13PrimitiveAffineComparison
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13PrincipalBranchIdeals_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InvertibleReductionSaturation_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

A principal equality on the generic affine chart descends to the exact
primitive integral numerator/denominator equation. Powers of two removed
from a field presentation contribute unit ideals only on the generic fibre.
The integral descent uses proved saturation, not cancellation of integral
nonunits.
-/

namespace MazurProof.N13PrimitiveAffineComparison

noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InvertibleReductionSaturation
open scoped nonZeroDivisors
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev R₂ := N13IntegralModelContraction.R₂
abbrev Frac := N13IntegralFractionalHull.RationalFractionalIdeal

local instance instAlgebraAR : Algebra A R := N13IntegralFractionalHull.integralToRational.toAlgebra
local instance instIsFractionRingAF : IsFractionRing A F := N13IntegralFractionalHull.functionField_isFractionRing
local instance instIsLocalizationIntegralRingVerticalScalarsR : IsLocalization N13IntegralModelContraction.verticalScalars R :=
  N13IntegralModelContraction.rationalRing_isLocalization

private theorem coe_principal_isUnit (a : A) (ha : a ≠ 0) :
    IsUnit ((Ideal.span ({a} : Set A) : Ideal A) : FractionalIdeal A⁰ F) := by
  refine ⟨Units.mkOfMulEqOne
    ((Ideal.span ({a} : Set A) : Ideal A) : FractionalIdeal A⁰ F)
    (((Ideal.span ({a} : Set A) : Ideal A) : FractionalIdeal A⁰ F)⁻¹) ?_, rfl⟩
  exact FractionalIdeal.coe_ideal_span_singleton_mul_inv F ha

private theorem scalar_span_eq_one (n : ℕ) :
    FractionalIdeal.spanSingleton R⁰ ((2 : F) ^ n) = (1 : Frac) := by
  have hu : IsUnit ((2 : R) ^ n) := by
    have hq : IsUnit ((2 : Q₂) ^ n) :=
      isUnit_iff_ne_zero.mpr (pow_ne_zero n (by norm_num))
    simpa only [map_pow, map_ofNat] using hq.map (algebraMap Q₂ R)
  calc
    FractionalIdeal.spanSingleton R⁰ ((2 : F) ^ n) =
        ((Ideal.span ({(2 : R) ^ n} : Set R) : Ideal R) : Frac) := by
          rw [FractionalIdeal.coeIdeal_span_singleton]
          simp only [map_pow, map_ofNat]
    _ = 1 := by rw [Ideal.span_singleton_eq_top.mpr hu]; exact FractionalIdeal.coeIdeal_top R⁰

theorem generic_cleared_equation
    (L M : Line) (f : Fˣ) (n m : ℕ) (a b : A)
    (hf : (2 : F) ^ m * (f : F) * algebraMap A F b =
      (2 : F) ^ n * algebraMap A F a)
    (hprincipal : genericIdealUnit L * toPrincipalIdeal R F f = genericIdealUnit M) :
    Ideal.map N13IntegralFractionalHull.integralToRational
        (Ideal.span ({a} : Set A) * L.affineIdeal) =
      Ideal.map N13IntegralFractionalHull.integralToRational
        (Ideal.span ({b} : Set A) * M.affineIdeal) := by
  have hfrac := congrArg (fun U : Fracˣ => (U : Frac)) hprincipal
  simp only [Units.val_mul, coe_genericIdealUnit, coe_toPrincipalIdeal] at hfrac
  have hsp := congrArg (FractionalIdeal.spanSingleton R⁰) hf
  simp only [← FractionalIdeal.spanSingleton_mul_spanSingleton] at hsp
  rw [scalar_span_eq_one, scalar_span_eq_one, one_mul, one_mul] at hsp
  apply FractionalIdeal.coeIdeal_injective (K := F)
  simp only [Ideal.map_mul, Ideal.map_span, Set.image_singleton,
    FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  change FractionalIdeal.spanSingleton R⁰ (algebraMap A F a) *
      ((Ideal.map N13IntegralFractionalHull.integralToRational L.affineIdeal : Ideal R) : Frac) =
    FractionalIdeal.spanSingleton R⁰ (algebraMap A F b) *
      ((Ideal.map N13IntegralFractionalHull.integralToRational M.affineIdeal : Ideal R) : Frac)
  rw [← hsp, ← hfrac]
  ac_rfl

theorem affine_two_ne_zero : algebraMap R₂ A (2 : R₂) ≠ 0 := by
  change (2 : A) ≠ 0
  have h2 : (2 : R) ≠ 0 := by
    have hq : (2 : Q₂) ≠ 0 := by norm_num
    simpa only [map_ofNat, map_zero] using (algebraMap Q₂ R).injective.ne hq
  intro h
  apply h2
  simpa only [map_ofNat, map_zero] using congrArg N13IntegralFractionalHull.integralToRational h

theorem primitive_principal_saturated (a : A)
    (ha : N13GeneralizedMumfordReduction.reduceCoordinate a ≠ 0) :
    ∀ r : R₂, r ≠ 0 → ∀ x : A,
      algebraMap R₂ A r * x ∈ Ideal.span ({a} : Set A) → x ∈ Ideal.span ({a} : Set A) := by
  have ha0 : a ≠ 0 := fun h => ha (by rw [h, map_zero])
  have har : Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
      (Ideal.span ({a} : Set A)) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton]
    intro h
    apply ha
    have hm : N13GeneralizedMumfordReduction.reduceCoordinate a ∈
        Ideal.span ({N13GeneralizedMumfordReduction.reduceCoordinate a} :
          Set N13GeneralizedMumfordReduction.SpecialRing) :=
      Ideal.subset_span (Set.mem_singleton _)
    rw [h, Ideal.mem_bot] at hm
    exact hm
  exact twoAdic_scalar_saturated_of_reduction_ne_bot (K := F)
    N13GeneralizedMumfordReduction.reduceCoordinate affine_two_ne_zero
    N13GeneralizedMumfordReduction.ker_reduceCoordinate _
    (coe_principal_isUnit a ha0) har

theorem integral_cleared_equation
    (L M : Line)
    (hL : AffineVerticallySaturated L) (hM : AffineVerticallySaturated M)
    (f : Fˣ) (n m : ℕ) (a b : A)
    (ha : N13GeneralizedMumfordReduction.reduceCoordinate a ≠ 0)
    (hb : N13GeneralizedMumfordReduction.reduceCoordinate b ≠ 0)
    (hf : (2 : F) ^ m * (f : F) * algebraMap A F b =
      (2 : F) ^ n * algebraMap A F a)
    (hprincipal : genericIdealUnit L * toPrincipalIdeal R F f = genericIdealUnit M) :
    Ideal.span ({a} : Set A) * L.affineIdeal =
      Ideal.span ({b} : Set A) * M.affineIdeal := by
  have hg := generic_cleared_equation L M f n m a b hf hprincipal
  have hs (c : A) (hc : N13GeneralizedMumfordReduction.reduceCoordinate c ≠ 0)
      (N : Line) (hN : AffineVerticallySaturated N) :=
    N13QuadraticTwoChartSpreadSaturation.mul_scalar_saturated_of_left_isUnit
      (Ideal.span ({c} : Set A)) N.affineIdeal
      (coe_principal_isUnit c (fun h => hc (by simp [h])))
      (primitive_principal_saturated c hc) hN
  have descend (I J : Ideal A)
      (hJ : ∀ r : R₂, r ≠ 0 → ∀ x : A, algebraMap R₂ A r * x ∈ J → x ∈ J)
      (heq : Ideal.map N13IntegralFractionalHull.integralToRational I =
        Ideal.map N13IntegralFractionalHull.integralToRational J) : I ≤ J := by
    intro x hx
    have hm := Ideal.mem_map_of_mem N13IntegralFractionalHull.integralToRational hx
    rw [heq] at hm
    change algebraMap A R x ∈ Ideal.map (algebraMap A R) J at hm
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
      N13IntegralModelContraction.verticalScalars] at hm
    obtain ⟨s, hs, hsx⟩ := hm
    obtain ⟨r, hr, hrs⟩ := hs
    rw [← hrs] at hsx
    exact hJ r (mem_nonZeroDivisors_iff_ne_zero.mp hr) x hsx
  exact le_antisymm (descend _ _ (hs b hb M hM) hg)
    (descend _ _ (hs a ha L hL) hg.symm)

end
end MazurProof.N13PrimitiveAffineComparison


