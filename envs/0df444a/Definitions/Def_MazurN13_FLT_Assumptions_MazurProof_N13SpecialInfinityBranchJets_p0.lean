-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinityBranchJets_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinityBranchJets_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:55:32.911326+00:00
-- url     : https://prove2.me/theorems/1945d92f-db8a-450e-b1c7-eb506509828b
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialInfinityBranchJets source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialInfinityBranchJets

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialInfinityBranchJets
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityBranchJets_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

The actual characteristic-two infinity chart has two power-series branches
obtained by reducing the integral Hensel roots. Both n-jets vanish exactly
on the principal ideal (t^n). This is special-fibre geometry, independent of
the unreviewed calibrated chooser and of the missing special-code theorem.
-/

namespace MazurProof.N13SpecialInfinityBranchJets

noncomputable section
open Polynomial
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev K := N13GoodModelTwo.F2
abbrev B := N13SpecialInfinityChart.CoordinateRing
abbrev P := PowerSeries K

def powerReduce : N13FormalInfinityChart.Power →+* P := PowerSeries.map PadicInt.toZMod
def r₀ : P := powerReduce N13FormalInfinityBranches.branchZero
def r₁ : P := powerReduce N13FormalInfinityBranches.branchOne
def h : P := 1 + PowerSeries.X ^ 2 + PowerSeries.X ^ 3
def rhs : P := PowerSeries.X + PowerSeries.X ^ 2

theorem reduce_h : powerReduce N13FormalInfinityChart.hPower = h := by
  simp [powerReduce, N13FormalInfinityChart.hPower, h]

theorem reduce_rhs : powerReduce N13FormalInfinityChart.rhsPower = rhs := by
  simp [powerReduce, N13FormalInfinityChart.rhsPower, rhs]

theorem r₀_relation : r₀ ^ 2 + h * r₀ - rhs = 0 := by
  have he := congrArg powerReduce N13FormalInfinityBranches.branchZero_relation
  simp only [map_sub, map_add, map_pow, map_mul, map_zero, reduce_h, reduce_rhs] at he
  exact he

theorem r₁_eq : r₁ = -h - r₀ := by
  simp [r₁, N13FormalInfinityBranches.branchOne, reduce_h, r₀]

theorem r₁_relation : r₁ ^ 2 + h * r₁ - rhs = 0 := by
  rw [r₁_eq]
  linear_combination r₀_relation

theorem r₀_constant : PowerSeries.constantCoeff r₀ = 0 := by
  change PowerSeries.constantCoeff (PowerSeries.map PadicInt.toZMod
    N13FormalInfinityBranches.branchZero) = 0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    N13FormalInfinityBranches.branchZero_constantCoeff, map_zero]

theorem r₁_constant : PowerSeries.constantCoeff r₁ = 1 := by
  rw [r₁_eq]
  norm_num [h, r₀_constant]

theorem root_difference_unit : IsUnit (r₀ - r₁) := by
  have hu := N13FormalInfinityBranches.branch_difference_isUnit.map powerReduce
  simp only [map_sub] at hu
  exact hu

def beta : K[X] →+* P := Polynomial.eval₂RingHom PowerSeries.C PowerSeries.X

theorem beta_eq_coe (p : K[X]) : beta p = (p : P) := by
  simpa [beta] using p.eval₂_C_X_eq_coe

private theorem root_eval (r : P) (hr : r ^ 2 + h * r - rhs = 0) :
    N13SpecialInfinityChart.curvePoly.eval₂ beta r = 0 := by
  simpa [N13SpecialInfinityChart.curvePoly, N13SpecialInfinityChart.hPoly,
    N13SpecialInfinityChart.rhsPoly, beta, h, rhs, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using hr

def plus : B →+* P := AdjoinRoot.lift beta r₀ (root_eval r₀ r₀_relation)
def minus : B →+* P := AdjoinRoot.lift beta r₁ (root_eval r₁ r₁_relation)

@[simp] theorem plus_base (p : K[X]) :
    plus (N13IntegralInfinityReduction.specialBaseClass p) = beta p :=
  AdjoinRoot.lift_of _

@[simp] theorem minus_base (p : K[X]) :
    minus (N13IntegralInfinityReduction.specialBaseClass p) = beta p :=
  AdjoinRoot.lift_of _

@[simp] theorem plus_t : plus N13SpecialInfinityChart.tClass = PowerSeries.X := by
  exact (plus_base X).trans (by simp [beta])

@[simp] theorem minus_t : minus N13SpecialInfinityChart.tClass = PowerSeries.X := by
  exact (minus_base X).trans (by simp [beta])

@[simp] theorem plus_v : plus N13SpecialInfinityChart.vClass = r₀ :=
  AdjoinRoot.lift_root _

@[simp] theorem minus_v : minus N13SpecialInfinityChart.vClass = r₁ :=
  AdjoinRoot.lift_root _

theorem plus_normal_form (z : B) :
    plus z = beta (N13IntegralInfinityReduction.specialCoeff0 z) +
      beta (N13IntegralInfinityReduction.specialCoeffV z) * r₀ := by
  calc
    plus z = plus
        (N13IntegralInfinityReduction.specialBaseClass (N13IntegralInfinityReduction.specialCoeff0 z) +
          N13IntegralInfinityReduction.specialBaseClass (N13IntegralInfinityReduction.specialCoeffV z) *
            N13SpecialInfinityChart.vClass) :=
      congrArg plus (N13IntegralInfinityReduction.special_recompose z).symm
    _ = _ := by rw [map_add, map_mul, plus_base, plus_base, plus_v]

theorem minus_normal_form (z : B) :
    minus z = beta (N13IntegralInfinityReduction.specialCoeff0 z) +
      beta (N13IntegralInfinityReduction.specialCoeffV z) * r₁ := by
  calc
    minus z = minus
        (N13IntegralInfinityReduction.specialBaseClass (N13IntegralInfinityReduction.specialCoeff0 z) +
          N13IntegralInfinityReduction.specialBaseClass (N13IntegralInfinityReduction.specialCoeffV z) *
            N13SpecialInfinityChart.vClass) :=
      congrArg minus (N13IntegralInfinityReduction.special_recompose z).symm
    _ = _ := by rw [map_add, map_mul, minus_base, minus_base, minus_v]

private theorem polynomial_dvd_of_beta_dvd (p : K[X]) (n : ℕ)
    (hp : (PowerSeries.X : P) ^ n ∣ beta p) : (X : K[X]) ^ n ∣ p := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro i hi
  have hc := PowerSeries.X_pow_dvd_iff.mp hp i hi
  simpa only [beta_eq_coe, Polynomial.coeff_coe] using hc

/-- A literal geometric finite-jet kernel statement on the special chart. -/
theorem branch_jets_detect_t_power (z : B) (n : ℕ) :
    N13SpecialInfinityChart.tClass ^ n ∣ z ↔
      (PowerSeries.X : P) ^ n ∣ plus z ∧ (PowerSeries.X : P) ^ n ∣ minus z := by
  constructor
  · rintro ⟨w, rfl⟩
    constructor
    · refine ⟨plus w, ?_⟩; simp
    · refine ⟨minus w, ?_⟩; simp
  · rintro ⟨hp, hm⟩
    rw [plus_normal_form] at hp
    rw [minus_normal_form] at hm
    let u := N13IntegralInfinityReduction.specialCoeff0 z
    let v := N13IntegralInfinityReduction.specialCoeffV z
    have hdiff : (PowerSeries.X : P) ^ n ∣ beta v * (r₀ - r₁) := by
      convert dvd_sub hp hm using 1 <;> dsimp [u, v] <;> ring
    have hv : (PowerSeries.X : P) ^ n ∣ beta v := by
      obtain ⟨w, hw⟩ := root_difference_unit
      rw [← hw] at hdiff
      obtain ⟨q, hq⟩ := hdiff
      refine ⟨q * (↑(w⁻¹) : P), ?_⟩
      calc
        beta v = (beta v * (w : P)) * (↑(w⁻¹) : P) := by simp [mul_assoc]
        _ = (PowerSeries.X : P) ^ n * (q * (↑(w⁻¹) : P)) := by rw [hq]; ring
    have hu : (PowerSeries.X : P) ^ n ∣ beta u := by
      have hvr : (PowerSeries.X : P) ^ n ∣ beta v * r₀ := dvd_mul_of_dvd_left hv _
      convert dvd_sub hp hvr using 1 <;> dsimp [u, v] <;> ring
    obtain ⟨a, ha⟩ := polynomial_dvd_of_beta_dvd u n hu
    obtain ⟨b, hb⟩ := polynomial_dvd_of_beta_dvd v n hv
    refine ⟨N13IntegralInfinityReduction.specialBaseClass a +
      N13IntegralInfinityReduction.specialBaseClass b * N13SpecialInfinityChart.vClass, ?_⟩
    calc
      z = N13IntegralInfinityReduction.specialBaseClass u +
          N13IntegralInfinityReduction.specialBaseClass v * N13SpecialInfinityChart.vClass :=
        (N13IntegralInfinityReduction.special_recompose z).symm
      _ = _ := by
        rw [ha, hb]
        simp only [N13IntegralInfinityReduction.specialBaseClass, map_mul, map_pow]
        change (N13SpecialInfinityChart.tClass ^ n * algebraMap K[X] B a) +
          (N13SpecialInfinityChart.tClass ^ n * algebraMap K[X] B b) * N13SpecialInfinityChart.vClass = _
        ring

private theorem span_pair_eq_top_of_right_unit (x y : P) (hy : IsUnit y) :
    Ideal.span ({x, y} : Set P) = ⊤ := by
  obtain ⟨u, hu⟩ := hy
  rw [← hu, Ideal.eq_top_iff_one]
  have hm : (u : P) ∈ Ideal.span ({x, (u : P)} : Set P) := Ideal.subset_span (by simp)
  have hh := Ideal.mul_mem_left (Ideal.span ({x, (u : P)} : Set P)) (↑(u⁻¹) : P) hm
  simpa using hh

/-- The positive special point has order one on its own branch. -/
theorem plus_positive_point :
    Ideal.map plus (N13SpecialDivisorCharts.infinityPointIdeal 0 0) =
      Ideal.span ({PowerSeries.X} : Set P) := by
  simp only [N13SpecialDivisorCharts.infinityPointIdeal, Polynomial.C_0,
    map_zero, sub_zero, Ideal.map_span, Set.image_pair, plus_t, plus_v]
  apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
  exact PowerSeries.X_dvd_iff.mpr r₀_constant

/-- The positive special point is absent from the other branch. -/
theorem minus_positive_point :
    Ideal.map minus (N13SpecialDivisorCharts.infinityPointIdeal 0 0) = ⊤ := by
  simp only [N13SpecialDivisorCharts.infinityPointIdeal, Polynomial.C_0,
    map_zero, sub_zero, Ideal.map_span, Set.image_pair, minus_t, minus_v]
  apply span_pair_eq_top_of_right_unit
  rw [PowerSeries.isUnit_iff_constantCoeff, r₁_constant]
  exact isUnit_one

/-- The negative special point is absent from the positive branch. -/
theorem plus_negative_point :
    Ideal.map plus (N13SpecialDivisorCharts.infinityPointIdeal 0 1) = ⊤ := by
  simp only [N13SpecialDivisorCharts.infinityPointIdeal, Polynomial.C_0, Polynomial.C_1,
    map_zero, map_one, sub_zero, Ideal.map_span, Set.image_pair, map_sub, plus_t, plus_v]
  apply span_pair_eq_top_of_right_unit
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp only [map_sub, map_one, r₀_constant, zero_sub]
  exact isUnit_neg_one

/-- The negative special point has order one on its own branch. -/
theorem minus_negative_point :
    Ideal.map minus (N13SpecialDivisorCharts.infinityPointIdeal 0 1) =
      Ideal.span ({PowerSeries.X} : Set P) := by
  simp only [N13SpecialDivisorCharts.infinityPointIdeal, Polynomial.C_0, Polynomial.C_1,
    map_zero, map_one, sub_zero, Ideal.map_span, Set.image_pair, map_sub, minus_t, minus_v]
  apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
  apply PowerSeries.X_dvd_iff.mpr
  simp only [map_sub, map_one, r₁_constant, sub_self]

end
end MazurProof.N13SpecialInfinityBranchJets


