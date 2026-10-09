-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityBranchJets_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InfinityBranchJets_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:49:58.842245+00:00
-- url     : https://prove2.me/theorems/6c6342b5-6564-4897-aba6-6654ee0eafba
-- title:
--   FLT.Assumptions.MazurProof.N13InfinityBranchJets source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InfinityBranchJets

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InfinityBranchJets
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityChartMarking_p0
import Mathlib.RingTheory.PowerSeries.Trunc

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Finite-jet geometry for the actual ordinary N13 infinity chart and its two
named Hensel branch maps. The two roots differ by a unit. Consequently both
branch jets vanish exactly when the ordinary element is divisible by t^n.
-/

namespace MazurProof.N13InfinityBranchJets

noncomputable section
open Polynomial
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev R₂ := N13IntegralInfinityChart.R₂
abbrev B := N13IntegralInfinityChart.InfinityCurve
abbrev P := N13FormalInfinityChart.Power
abbrev QP := N13TwoAdicInfinityCompatibility.RationalPower
abbrev base := N13IntegralInfinityReduction.integralBaseClass
abbrev beta := N13IntegralInfinityChart.baseToPower
abbrev plus := N13InfinityChartMarking.positiveIntegralExpansion
abbrev minus := N13InfinityChartMarking.negativeIntegralExpansion
abbrev r₀ := N13FormalInfinityBranches.branchZero
abbrev r₁ := N13FormalInfinityBranches.branchOne

theorem beta_eq_coe (p : R₂[X]) : beta p = (p : P) := by
  simpa [beta, N13IntegralInfinityChart.baseToPower] using p.eval₂_C_X_eq_coe

theorem plus_base (p : R₂[X]) : plus (base p) = beta p := by
  simp [plus, base, N13InfinityChartMarking.positiveIntegralExpansion,
    N13IntegralInfinityReduction.integralBaseClass,
    N13IntegralInfinityChart.toFormalInfinity, N13FormalInfinitySplit.evalBranchZero]

theorem minus_base (p : R₂[X]) : minus (base p) = beta p := by
  simp [minus, base, N13InfinityChartMarking.negativeIntegralExpansion,
    N13IntegralInfinityReduction.integralBaseClass,
    N13IntegralInfinityChart.toFormalInfinity, N13FormalInfinitySplit.evalBranchOne]

theorem plus_v : plus N13IntegralInfinityChart.vClass = r₀ := by
  simp [plus, N13InfinityChartMarking.positiveIntegralExpansion]

theorem minus_v : minus N13IntegralInfinityChart.vClass = r₁ := by
  simp [minus, N13InfinityChartMarking.negativeIntegralExpansion]

theorem plus_normal_form (z : B) :
    plus z = beta (N13IntegralInfinityReduction.integralCoeff0 z) +
      beta (N13IntegralInfinityReduction.integralCoeffV z) * r₀ := by
  calc
    plus z = plus (base (N13IntegralInfinityReduction.integralCoeff0 z) +
        base (N13IntegralInfinityReduction.integralCoeffV z) *
          N13IntegralInfinityChart.vClass) :=
      congrArg plus (N13IntegralInfinityReduction.integral_recompose z).symm
    _ = _ := by rw [map_add, map_mul, plus_base, plus_base, plus_v]

theorem minus_normal_form (z : B) :
    minus z = beta (N13IntegralInfinityReduction.integralCoeff0 z) +
      beta (N13IntegralInfinityReduction.integralCoeffV z) * r₁ := by
  calc
    minus z = minus (base (N13IntegralInfinityReduction.integralCoeff0 z) +
        base (N13IntegralInfinityReduction.integralCoeffV z) *
          N13IntegralInfinityChart.vClass) :=
      congrArg minus (N13IntegralInfinityReduction.integral_recompose z).symm
    _ = _ := by rw [map_add, map_mul, minus_base, minus_base, minus_v]

theorem polynomial_dvd_of_beta_dvd (p : R₂[X]) (n : ℕ)
    (h : (PowerSeries.X : P) ^ n ∣ beta p) : (X : R₂[X]) ^ n ∣ p := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro i hi
  have hh := PowerSeries.X_pow_dvd_iff.mp h i hi
  simpa only [beta_eq_coe, Polynomial.coeff_coe] using hh

/-- Both actual integral branch jets detect the t-adic kernel on the
ordinary chart, by its rank-two normal form and the unit root difference. -/
theorem integral_branch_dvd_iff (z : B) (n : ℕ) :
    N13IntegralInfinityChart.tClass ^ n ∣ z ↔
      (PowerSeries.X : P) ^ n ∣ plus z ∧ (PowerSeries.X : P) ^ n ∣ minus z := by
  constructor
  · rintro ⟨w, rfl⟩
    constructor
    · refine ⟨plus w, ?_⟩
      simp [plus, N13InfinityChartMarking.positiveIntegralExpansion]
    · refine ⟨minus w, ?_⟩
      simp [minus, N13InfinityChartMarking.negativeIntegralExpansion]
  · rintro ⟨hp, hm⟩
    rw [plus_normal_form] at hp
    rw [minus_normal_form] at hm
    let u := N13IntegralInfinityReduction.integralCoeff0 z
    let v := N13IntegralInfinityReduction.integralCoeffV z
    have hdiff : (PowerSeries.X : P) ^ n ∣ beta v * (r₀ - r₁) := by
      convert dvd_sub hp hm using 1 <;> dsimp [u, v] <;> ring
    have hv : (PowerSeries.X : P) ^ n ∣ beta v := by
      obtain ⟨w, hw⟩ := N13FormalInfinityBranches.branch_difference_isUnit
      rw [← hw] at hdiff
      obtain ⟨c, hc⟩ := hdiff
      refine ⟨c * (↑(w⁻¹) : P), ?_⟩
      calc
        beta v = (beta v * (w : P)) * (↑(w⁻¹) : P) := by simp [mul_assoc]
        _ = (PowerSeries.X : P) ^ n * (c * (↑(w⁻¹) : P)) := by rw [hc]; ring
    have hu : (PowerSeries.X : P) ^ n ∣ beta u := by
      have hvm : (PowerSeries.X : P) ^ n ∣ beta v * r₀ :=
        hv.trans (dvd_mul_right _ _)
      have h := dvd_sub hp hvm
      simpa only [u, v, add_sub_cancel_right] using h
    obtain ⟨a, ha⟩ := polynomial_dvd_of_beta_dvd u n hu
    obtain ⟨b, hb⟩ := polynomial_dvd_of_beta_dvd v n hv
    refine ⟨base a + base b * N13IntegralInfinityChart.vClass, ?_⟩
    calc
      z = base u + base v * N13IntegralInfinityChart.vClass :=
        (N13IntegralInfinityReduction.integral_recompose z).symm
      _ = base ((X : R₂[X]) ^ n * a) +
          base ((X : R₂[X]) ^ n * b) * N13IntegralInfinityChart.vClass := by rw [ha, hb]
      _ = N13IntegralInfinityChart.tClass ^ n *
          (base a + base b * N13IntegralInfinityChart.vClass) := by
        simp only [base, N13IntegralInfinityReduction.integralBaseClass, map_mul, map_pow]
        change N13IntegralInfinityChart.tClass ^ n * base a +
          (N13IntegralInfinityChart.tClass ^ n * base b) * N13IntegralInfinityChart.vClass = _
        simp only [base, N13IntegralInfinityReduction.integralBaseClass]
        ring

theorem powerMap_reflects_X_pow_dvd (f : P) (n : ℕ) :
    (PowerSeries.X : QP) ^ n ∣ N13TwoAdicInfinityCompatibility.powerMap f ↔
      (PowerSeries.X : P) ^ n ∣ f := by
  rw [PowerSeries.X_pow_dvd_iff, PowerSeries.X_pow_dvd_iff]
  constructor
  · intro h i hi
    have hh := h i hi
    rw [N13TwoAdicInfinityCompatibility.powerMap_coeff] at hh
    apply N13TwoAdicInfinityCompatibility.coeffMap_injective
    simpa only [map_zero] using hh
  · intro h i hi
    rw [N13TwoAdicInfinityCompatibility.powerMap_coeff, h i hi, map_zero]

/-- The SAME finite-jet kernel is detected by the generic branch maps used
in HasInfinityMultiplicities. Coefficient injection prevents losing a
nonzero low-order term when passing from Z2 to Q2. -/
theorem generic_branch_dvd_iff (z : B) (n : ℕ) :
    N13IntegralInfinityChart.tClass ^ n ∣ z ↔
      (PowerSeries.X : QP) ^ n ∣ N13InfinityChartMarking.positiveExpansion z ∧
      (PowerSeries.X : QP) ^ n ∣ N13InfinityChartMarking.negativeExpansion z := by
  change N13IntegralInfinityChart.tClass ^ n ∣ z ↔
    (PowerSeries.X : QP) ^ n ∣ N13TwoAdicInfinityCompatibility.powerMap (plus z) ∧
    (PowerSeries.X : QP) ^ n ∣ N13TwoAdicInfinityCompatibility.powerMap (minus z)
  rw [powerMap_reflects_X_pow_dvd, powerMap_reflects_X_pow_dvd]
  exact integral_branch_dvd_iff z n

end
end MazurProof.N13InfinityBranchJets


