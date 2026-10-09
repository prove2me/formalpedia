-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13PrincipalBranchIdeals_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13PrincipalBranchIdeals_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:43:56.559419+00:00
-- url     : https://prove2.me/theorems/15b8c6a6-4c38-40e4-bcf2-77d3b3944b30
-- title:
--   FLT.Assumptions.MazurProof.N13PrincipalBranchIdeals source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13PrincipalBranchIdeals

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13PrincipalBranchIdeals
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13OverlapBranchCompatibility_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13PrimitiveVerticalPresentation_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13PrincipalBranchBalance_p0
import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Primitive presentations retain powers of two. These are Laurent-order-zero
scalars, so the SAME transported infinity numerator/denominator has the
prescribed difference of orders at both branches. Power-series division by
X^order turns the order equations into actual principal ideal equations.
-/

namespace MazurProof.N13PrincipalBranchIdeals

noncomputable section
open N13OverlapBranchCompatibility
open scoped nonZeroDivisors LaurentSeries
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev R := N13IntegralFractionalHull.RationalRing
abbrev F := N13IntegralFractionalHull.FunctionField

local instance instAlgebraAR : Algebra A R := N13IntegralFractionalHull.integralToRational.toAlgebra

private theorem includePower_injective : Function.Injective includePower :=
  HahnSeries.ofPowerSeries_injective

private theorem includePower_ne_zero {f : QP} (hf : f ≠ 0) : includePower f ≠ 0 :=
  (map_ne_zero_iff includePower includePower_injective).mpr hf

private theorem two_eq_C : (2 : L) = HahnSeries.C (2 : Q₂) := (map_ofNat _ 2).symm

theorem includePower_order (f : QP) (hf : f ≠ 0) :
    (includePower f).order = (f.order.toNat : ℤ) := by
  have hinc : includePower f ≠ 0 := includePower_ne_zero hf
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    change (HahnSeries.ofPowerSeries ℤ Q₂ f).coeff (f.order.toNat : ℤ) ≠ 0
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    exact PowerSeries.coeff_order hf
  · rw [HahnSeries.le_order_iff_forall hinc]
    intro j hj
    change ((f : LaurentSeries Q₂).coeff j) = 0
    rw [PowerSeries.coeff_coe]
    split_ifs with hneg
    · rfl
    · apply PowerSeries.coeff_of_lt_order_toNat
      have hj0 : 0 ≤ j := le_of_not_gt hneg
      have hjabs : (j.natAbs : ℤ) = j := Int.natAbs_of_nonneg hj0
      omega

theorem span_eq_order_power (f : QP) (hf : f ≠ 0) :
    Ideal.span ({f} : Set QP) = Ideal.span ({PowerSeries.X ^ f.order.toNat} : Set QP) := by
  conv_lhs => rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f)]
  exact Ideal.span_singleton_mul_right_unit
    (PowerSeries.isUnit_divided_by_X_pow_order hf) _

theorem principal_power_ideal_eq_of_orders (f g : QP) (hf : f ≠ 0) (hg : g ≠ 0)
    (p q : ℕ)
    (h : (includePower f).order + (p : ℤ) = (includePower g).order + (q : ℤ)) :
    Ideal.span ({f} : Set QP) * Ideal.span ({PowerSeries.X ^ p} : Set QP) =
      Ideal.span ({g} : Set QP) * Ideal.span ({PowerSeries.X ^ q} : Set QP) := by
  rw [includePower_order f hf, includePower_order g hg] at h
  have hn : f.order.toNat + p = g.order.toNat + q := by omega
  rw [span_eq_order_power f hf, span_eq_order_power g hg,
    Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_mul_span_singleton, ← pow_add, ← pow_add, hn]

private theorem scalar_order (n : ℕ) : ((2 : L) ^ n).order = 0 := by
  rw [two_eq_C, ← map_pow, HahnSeries.order_C]

private theorem clear_cross
    (χ : F →+* L) (f a b : F) (c d : L) (n m : ℕ)
    (hb : b ≠ 0)
    (hf : (2 : F) ^ m * f * b = (2 : F) ^ n * a)
    (hcross : χ a * d = χ b * c) :
    (2 : L) ^ m * χ f * d = (2 : L) ^ n * c := by
  have hbχ : χ b ≠ 0 := by simpa only [map_zero] using χ.injective.ne hb
  apply mul_right_cancel₀ hbχ
  have hm := congrArg χ hf
  simp only [map_mul, map_pow, map_ofNat] at hm
  calc
    ((2 : L) ^ m * χ f * d) * χ b = ((2 : L) ^ m * χ f * χ b) * d := by ring
    _ = ((2 : L) ^ n * χ a) * d := by rw [hm]
    _ = (2 : L) ^ n * (χ a * d) := by ring
    _ = ((2 : L) ^ n * c) * χ b := by rw [hcross]; ring

private theorem order_of_scaled_cross
    (f : Fˣ) (χ : F →+* L) (c d : QP) (hc : c ≠ 0) (hd : d ≠ 0)
    (n m : ℕ)
    (h : (2 : L) ^ m * χ (f : F) * includePower d = (2 : L) ^ n * includePower c) :
    (includePower c).order = (χ (f : F)).order + (includePower d).order := by
  have h2 : (2 : L) ≠ 0 := by rw [two_eq_C]; exact HahnSeries.C_ne_zero (by norm_num)
  have hf : χ (f : F) ≠ 0 := by simpa only [map_zero] using χ.injective.ne f.ne_zero
  have hc' : includePower c ≠ 0 := includePower_ne_zero hc
  have hd' : includePower d ≠ 0 := includePower_ne_zero hd
  have ho := congrArg HahnSeries.order h
  rw [HahnSeries.order_mul (mul_ne_zero (pow_ne_zero m h2) hf) hd',
    HahnSeries.order_mul (pow_ne_zero m h2) hf,
    HahnSeries.order_mul (pow_ne_zero n h2) hc', scalar_order, scalar_order] at ho
  omega

/-- The exact common primitive fraction determines both branch order
differences, even before any line ideal is considered. -/
theorem branch_orders_of_primitive_presentation
    (f : Fˣ) (n m : ℕ) (a b : A) (c d : B)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hf : (2 : F) ^ m * (f : F) * algebraMap A F b =
      (2 : F) ^ n * algebraMap A F a)
    (hcross : N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap B O c) :
    (includePower (N13InfinityChartMarking.positiveExpansion c)).order =
        Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder Q₂).ordPlus f) +
          (includePower (N13InfinityChartMarking.positiveExpansion d)).order ∧
    (includePower (N13InfinityChartMarking.negativeExpansion c)).order =
        Multiplicative.toAdd ((N13InfinityMinus.negativeInfinityOrder Q₂).ordPlus f) +
          (includePower (N13InfinityChartMarking.negativeExpansion d)).order := by
  have hbF : algebraMap A F b ≠ 0 := by
    change algebraMap R F (N13IntegralFractionalHull.integralToRational b) ≠ 0
    have hbr : N13IntegralFractionalHull.integralToRational b ≠ 0 := by
      simpa only [map_zero] using N13IntegralFractionalHull.integralToRational_injective.ne hb
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hbr
  obtain ⟨hp, hm⟩ := branch_cross_relations a b c d hcross
  have hp' : N13Infinity.functionFieldToLaurent Q₂ (algebraMap A F a) *
      includePower (N13InfinityChartMarking.positiveExpansion d) =
    N13Infinity.functionFieldToLaurent Q₂ (algebraMap A F b) *
      includePower (N13InfinityChartMarking.positiveExpansion c) := by
    change N13Infinity.functionFieldToLaurent Q₂
        (algebraMap R F (N13IntegralFractionalHull.integralToRational a)) * _ =
      N13Infinity.functionFieldToLaurent Q₂
        (algebraMap R F (N13IntegralFractionalHull.integralToRational b)) * _
    simpa only [N13Infinity.functionFieldToLaurent_algebraMap] using hp
  have hm' : N13InfinityMinus.functionFieldToLaurentMinus Q₂ (algebraMap A F a) *
      includePower (N13InfinityChartMarking.negativeExpansion d) =
    N13InfinityMinus.functionFieldToLaurentMinus Q₂ (algebraMap A F b) *
      includePower (N13InfinityChartMarking.negativeExpansion c) := by
    change N13InfinityMinus.functionFieldToLaurentMinus Q₂
        (algebraMap R F (N13IntegralFractionalHull.integralToRational a)) * _ =
      N13InfinityMinus.functionFieldToLaurentMinus Q₂
        (algebraMap R F (N13IntegralFractionalHull.integralToRational b)) * _
    simpa only [N13InfinityMinus.functionFieldToLaurentMinus_algebraMap] using hm
  constructor
  · exact order_of_scaled_cross f (N13Infinity.functionFieldToLaurent Q₂) _ _
      (by simpa only [map_zero] using positiveExpansion_injective.ne hc)
      (by simpa only [map_zero] using positiveExpansion_injective.ne hd) n m
      (clear_cross _ _ _ _ _ _ n m hbF hf hp')
  · exact order_of_scaled_cross f (N13InfinityMinus.functionFieldToLaurentMinus Q₂) _ _
      (by simpa only [map_zero] using negativeExpansion_injective.ne hc)
      (by simpa only [map_zero] using negativeExpansion_injective.ne hd) n m
      (clear_cross _ _ _ _ _ _ n m hbF hf hm')

open N13InfinityChartMarking hiding B QP
open N13EffectiveInfinityRepair

/-- The affine principal relation and its positive orientation force BOTH
actual branch ideal equations for the transported common numerator and
denominator. The negative equation is derived from the norm/degree theorem;
it is not an additional compatibility hypothesis. -/
theorem tensor_branch_ideal_equations
    (E₀ E₁ E₂ E₃ : N13Mumford.SemiMumford Q₂)
    (h₀ : EffectiveChamber E₀) (h₁ : EffectiveChamber E₁)
    (h₂ : EffectiveChamber E₂) (h₃ : EffectiveChamber E₃)
    (L₀ L₁ L₂ L₃ : N13TwoChartPicardRealization.Line)
    (hL₀ : HasInfinityMultiplicities L₀ (positiveMultiplicity E₀) (negativeMultiplicity E₀))
    (hL₁ : HasInfinityMultiplicities L₁ (positiveMultiplicity E₁) (negativeMultiplicity E₁))
    (hL₂ : HasInfinityMultiplicities L₂ (positiveMultiplicity E₂) (negativeMultiplicity E₂))
    (hL₃ : HasInfinityMultiplicities L₃ (positiveMultiplicity E₃) (negativeMultiplicity E₃))
    (f : Fˣ) (n m : ℕ) (a b : A) (c d : B)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hf : (2 : F) ^ m * (f : F) * algebraMap A F b =
      (2 : F) ^ n * algebraMap A F a)
    (hcross : N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap B O d =
      N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap B O c)
    (hprincipal :
      SexticMumford.mumfordIdealUnit (N13Mumford.model Q₂) E₀ *
        SexticMumford.mumfordIdealUnit (N13Mumford.model Q₂) E₁ *
        toPrincipalIdeal R F f =
      SexticMumford.mumfordIdealUnit (N13Mumford.model Q₂) E₂ *
        SexticMumford.mumfordIdealUnit (N13Mumford.model Q₂) E₃)
    (horientation : E₀.nInf + E₁.nInf +
      Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder Q₂).ordPlus f) =
        E₂.nInf + E₃.nInf) :
    Ideal.map positiveExpansion
        (Ideal.span ({c} : Set B) * (L₀.infinityIdeal * L₁.infinityIdeal)) =
      Ideal.map positiveExpansion
        (Ideal.span ({d} : Set B) * (L₂.infinityIdeal * L₃.infinityIdeal)) ∧
    Ideal.map negativeExpansion
        (Ideal.span ({c} : Set B) * (L₀.infinityIdeal * L₁.infinityIdeal)) =
      Ideal.map negativeExpansion
        (Ideal.span ({d} : Set B) * (L₂.infinityIdeal * L₃.infinityIdeal)) := by
  obtain ⟨hplus, hminus⟩ :=
    branch_orders_of_primitive_presentation f n m a b c d hb hc hd hf hcross
  have hbalance := N13PrincipalBranchBalance.principal_branch_orders_sum
    E₀ E₁ E₂ E₃ f hprincipal
  have hp₀ := positiveMultiplicity_cast E₀ h₀
  have hp₁ := positiveMultiplicity_cast E₁ h₁
  have hp₂ := positiveMultiplicity_cast E₂ h₂
  have hp₃ := positiveMultiplicity_cast E₃ h₃
  have hm₀ := negativeMultiplicity_cast E₀ h₀
  have hm₁ := negativeMultiplicity_cast E₁ h₁
  have hm₂ := negativeMultiplicity_cast E₂ h₂
  have hm₃ := negativeMultiplicity_cast E₃ h₃
  constructor
  · have he := principal_power_ideal_eq_of_orders
      (positiveExpansion c) (positiveExpansion d)
      (by simpa only [map_zero] using positiveExpansion_injective.ne hc)
      (by simpa only [map_zero] using positiveExpansion_injective.ne hd)
      (positiveMultiplicity E₀ + positiveMultiplicity E₁)
      (positiveMultiplicity E₂ + positiveMultiplicity E₃) (by push_cast; omega)
    simpa only [Ideal.map_mul, Ideal.map_span, Set.image_singleton,
      hL₀.1, hL₁.1, hL₂.1, hL₃.1,
      Ideal.span_singleton_mul_span_singleton, ← pow_add] using he
  · have he := principal_power_ideal_eq_of_orders
      (negativeExpansion c) (negativeExpansion d)
      (by simpa only [map_zero] using negativeExpansion_injective.ne hc)
      (by simpa only [map_zero] using negativeExpansion_injective.ne hd)
      (negativeMultiplicity E₀ + negativeMultiplicity E₁)
      (negativeMultiplicity E₂ + negativeMultiplicity E₃) (by push_cast; omega)
    simpa only [Ideal.map_mul, Ideal.map_span, Set.image_singleton,
      hL₀.2, hL₁.2, hL₂.2, hL₃.2,
      Ideal.span_singleton_mul_span_singleton, ← pow_add] using he

end
end MazurProof.N13PrincipalBranchIdeals


