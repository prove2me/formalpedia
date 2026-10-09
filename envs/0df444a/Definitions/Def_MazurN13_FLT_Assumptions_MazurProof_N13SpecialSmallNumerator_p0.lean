-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallNumerator_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialSmallNumerator_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T23:12:17.028275+00:00
-- url     : https://prove2.me/theorems/e3a5cd76-7adb-4559-b2a7-899b16bcae61
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialSmallNumerator source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialSmallNumerator

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialSmallNumerator
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialDivisorBranchOrders_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

An arbitrary degree-four SpecialComparison actually supplies a numerator
p+q*y with deg(p)<=4 and deg(q)<=1. Its nonzero norm is supported only over
x=0 and x=1. The two-infinity bounds are derived from the input chart ideal
equations and the common overlap fraction, not assumed as a replacement
for the principal-comparison target.
-/

namespace MazurProof.N13SpecialSmallNumerator

noncomputable section
open Polynomial N13SpecialDivisorCharts N13SpecialOverlapBranches
open N13SpecialLaurentBranches hiding K R
open N13SpecialComparisonFactorPair N13SpecialDivisorBranchOrders N13SpecialBranchFaithfulness

private theorem include_X : includeSeries (PowerSeries.X : N13SpecialLaurentBranches.P) = t :=
  HahnSeries.ofPowerSeries_X

private theorem include_unit_order (u : N13SpecialLaurentBranches.Pˣ) :
    (includeSeries (u : N13SpecialLaurentBranches.P)).order = 0 := by
  have hp : includeSeries (u : N13SpecialLaurentBranches.P) * includeSeries (↑(u⁻¹) : N13SpecialLaurentBranches.P) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have ho := HahnSeries.order_mul (u.isUnit.map includeSeries).ne_zero ((u⁻¹).isUnit.map includeSeries).ne_zero
  rw [hp, HahnSeries.order_one] at ho
  have hu := include_order_nonnegative (u : N13SpecialLaurentBranches.P)
  have hv := include_order_nonnegative (↑(u⁻¹) : N13SpecialLaurentBranches.P)
  omega

private theorem t_pow_order (n : ℕ) : (t ^ n).order = (n : ℤ) := by
  rw [HahnSeries.order_pow, N13LaurentPolynomialOrder.order_parameter]
  simp

theorem order_balance_of_principal_power_eq
    (f g : N13SpecialLaurentBranches.P) (hf : f ≠ 0) (hg : g ≠ 0) (n m : ℕ)
    (h : Ideal.span ({f} : Set N13SpecialLaurentBranches.P) * Ideal.span ({PowerSeries.X ^ n} : Set N13SpecialLaurentBranches.P) =
      Ideal.span ({g} : Set N13SpecialLaurentBranches.P) * Ideal.span ({PowerSeries.X ^ m} : Set N13SpecialLaurentBranches.P)) :
    (includeSeries f).order + (n : ℤ) = (includeSeries g).order + (m : ℤ) := by
  rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton] at h
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  have he := congrArg includeSeries hu
  simp only [map_mul, map_pow, include_X] at he
  have hf' : includeSeries f ≠ 0 :=
    (map_ne_zero_iff includeSeries HahnSeries.ofPowerSeries_injective).mpr hf
  have hg' : includeSeries g ≠ 0 :=
    (map_ne_zero_iff includeSeries HahnSeries.ofPowerSeries_injective).mpr hg
  have ho := congrArg HahnSeries.order he
  rw [HahnSeries.order_mul (mul_ne_zero hf' (pow_ne_zero n t_ne_zero)) (u.isUnit.map includeSeries).ne_zero,
    HahnSeries.order_mul hf' (pow_ne_zero n t_ne_zero),
    HahnSeries.order_mul hg' (pow_ne_zero m t_ne_zero),
    include_unit_order, t_pow_order, t_pow_order, add_zero] at ho
  exact ho

theorem comparison_infinity_order_balance
    (negative : Bool) (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H))) :
    (includeSeries (infinityBranch negative h.iNum)).order + (tensorOrder negative D E : ℤ) =
      (includeSeries (infinityBranch negative h.iDen)).order + (tensorOrder negative F H : ℤ) := by
  have he := congrArg (Ideal.map (infinityBranch negative)) h.infinity_eq
  simp only [Ideal.map_mul, Ideal.map_span, Set.image_singleton, tensor_branch_ideal] at he
  exact order_balance_of_principal_power_eq _ _
    (infinityBranch_ne_zero negative _ h.iNum_ne) (infinityBranch_ne_zero negative _ h.iDen_ne) _ _ he

private theorem affineBranch_ne_zero (negative : Bool) (z : R) (hz : z ≠ 0) : affineBranch negative z ≠ 0 := by
  simpa only [map_zero] using (affineBranch_injective negative).ne hz

private theorem affineBranch_xClass (negative : Bool) (p : K[X]) :
    affineBranch negative (N13GoodCoordinateRingTwo.xClass p) = base p := by
  cases negative <;> simp [affineBranch]

/-- The previously missing two-infinity bounds for the ACTUAL cleared
numerator extracted from a special comparison. -/
theorem cleared_numerator_pole_bound
    (negative : Bool) (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H)))
    (z : R) (hz : z ≠ 0)
    (hcross : h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) = h.aDen * z) :
    (-4 : ℤ) ≤ (affineBranch negative z).order := by
  have ha := affineBranch_ne_zero negative _ h.aNum_ne
  have hb := affineBranch_ne_zero negative _ h.aDen_ne
  have hc : includeSeries (infinityBranch negative h.iNum) ≠ 0 :=
    (map_ne_zero_iff includeSeries HahnSeries.ofPowerSeries_injective).mpr
      (infinityBranch_ne_zero negative _ h.iNum_ne)
  have hd : includeSeries (infinityBranch negative h.iDen) ≠ 0 :=
    (map_ne_zero_iff includeSeries HahnSeries.ofPowerSeries_injective).mpr
      (infinityBranch_ne_zero negative _ h.iDen_ne)
  have he := congrArg HahnSeries.order (cross_relation negative _ _ _ _ h.overlap_eq)
  rw [HahnSeries.order_mul ha hd, HahnSeries.order_mul hb hc] at he
  have hi := comparison_infinity_order_balance negative D E F H h
  have hn := congrArg (affineBranch negative) hcross
  simp only [map_mul, affineBranch_xClass] at hn
  have hq := (tensorPolynomial_monic D E).ne_zero
  have ho := congrArg HahnSeries.order hn
  rw [HahnSeries.order_mul ha (N13BranchNorm.evalPoly_ne_zero K hq),
    HahnSeries.order_mul hb (affineBranch_ne_zero negative z hz),
    N13BranchNorm.evalPoly_order K _ hq] at ho
  have hdegree : (tensorPolynomial D E).natDegree + tensorOrder negative D E ≤ 4 := by
    have hh := tensor_degree_balance D E
    cases negative <;> omega
  have hr : 0 ≤ (tensorOrder negative F H : ℤ) := Nat.cast_nonneg _
  omega

/-- Reduction to the genuine 32-by-4 polynomial search space over F2.
The small numerator retains the input fraction and has supported norm. -/
theorem exists_small_supported_numerator
    (D E F H : EffectiveDivisorTwo)
    (h : N13CoherentChartComparison.SpecialComparison
      (tensor (ofDivisor D) (ofDivisor E)) (tensor (ofDivisor F) (ofDivisor H))) :
    ∃ p q : K[X], ∃ i j : ℕ,
      p.natDegree ≤ 4 ∧ q.natDegree ≤ 1 ∧ i + j ≤ 16 ∧
      N13SpecialAffineNorm.linear p q ≠ 0 ∧
      h.aNum * N13GoodCoordinateRingTwo.xClass (tensorPolynomial D E) =
        h.aDen * N13SpecialAffineNorm.linear p q ∧
      N13SpecialAffineNorm.normPolynomial p q ≠ 0 ∧
      N13SpecialAffineNorm.normPolynomial p q ∣ X ^ i * (X - 1) ^ j := by
  obtain ⟨z, w, i, j, hij, hz, _, hcross, _, _, hnorm⟩ :=
    N13SpecialAffineNorm.exists_factor_pair_with_supported_norm D E F H h
  have hrepr : N13SpecialAffineNorm.linear
      (N13GoodCoordinateRingTwo.coeff0 z) (N13GoodCoordinateRingTwo.coeffY z) = z :=
    N13GoodCoordinateRingTwo.recompose z
  have hp := cleared_numerator_pole_bound false D E F H h z hz hcross
  have hm := cleared_numerator_pole_bound true D E F H h z hz hcross
  change (-4 : ℤ) ≤ (plus z).order at hp
  change (-4 : ℤ) ≤ (minus z).order at hm
  have hbounds := degree_four_polynomial_bounds
    (N13GoodCoordinateRingTwo.coeff0 z) (N13GoodCoordinateRingTwo.coeffY z)
    (by rw [hrepr]; exact hp) (by rw [hrepr]; exact hm)
  refine ⟨_, _, i, j, hbounds.1, hbounds.2, hij, ?_, ?_, ?_, hnorm⟩
  · rw [hrepr]; exact hz
  · rw [hrepr]; exact hcross
  · exact N13SpecialAffineNorm.norm_ne_zero z hz

end
end MazurProof.N13SpecialSmallNumerator


