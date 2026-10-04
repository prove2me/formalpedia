-- Prove2me | Definitions.Def_ZetaNine_CoefficientMapKernelBridge
-- name    : ZetaNine_CoefficientMapKernelBridge
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-04T10:12:26.773745+00:00
-- url     : https://prove2.me/theorems/c7863012-af24-4701-9c51-6a46db9af05b
-- title:
--   Actual rational quartic aggregate equivalence and inverse multiplier
-- statement:
--   Define the original positive/negative products and shift factors, the actual five-dimensional rational quartic aggregate equivalence, its actual inverse multiplier and prescribed real linear form. The equivalence constructor's bijective proof is closed from the genuine source proof closure, without an added kernel/bijection/inverse premise. All seven actual data functions and original Even n, n>=2 domain remain fixed. No integer inverse, denominator height, small linear form or irrationality claim is made.
-- source:
--   Zeta(9) actual original five-dimensional coefficient map kernel and rational inverse: missions/zeta9/research/coefficient-map-kernel-2026-10-04.md. Frozen source SHA256 1ec15a46ae656bb0be0de0eb44afeca3144a7223a84eecf161693be25205bedb. The actual kernel, polynomial relation, bijection, inverse and sum are derived from genuine data and source proofs.

import Definitions.Def_ZetaNine_CoefficientMapTelescoper
import Definitions.Def_ZetaNine_CoefficientMapShiftDegree
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Order.Interval.Set.Infinite

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Topology
open Finset Polynomial Filter
open ZetaNine ZetaNine.CoefficientMap ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapTelescoper ZetaNine.CoefficientMapShiftDegree
open scoped BigOperators
open Finset
open Polynomial
open Finset Polynomial
open CoefficientMapInjectivity
open CoefficientMapInjectivity CoefficientMapPartialFractions
open HarmonicStability CoefficientMapInjectivity CoefficientMapPartialFractions
open scoped BigOperators Topology
open Finset Polynomial Filter
open HarmonicStability CoefficientMapInjectivity CoefficientMapReflection
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection CoefficientMapAggregate
open CoefficientMapAggregate CoefficientMapTelescoper

namespace ZetaNine.CoefficientMapKernelBridge

def positiveProduct (n : ℕ) (t : ℚ) : ℚ := ∏ k ∈ range n, (t - ((k : ℚ) + 1))

def negativeProduct (n : ℕ) (t : ℚ) : ℚ := ∏ k ∈ range n, (t + (n : ℚ) + ((k : ℚ) + 1))

def aValue (n : ℕ) (t : ℚ) : ℚ := (t - (n : ℚ) - 1) * (t + (n : ℚ)) ^ 10

def bValue (n : ℕ) (t : ℚ) : ℚ := t ^ 10 * (t + 2 * (n : ℚ) + 1)

def actualAggregateEquiv (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    (Fin 5 → ℚ) ≃ₗ[ℚ] (Fin 5 → ℚ) :=
  LinearEquiv.ofBijective (quarticAggregateLinearMap n) (((by
    have embedded_ZetaNine__CoefficientMap__poleProduct_ne_zero (n : ℕ) (t : ℚ)
        (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) : ZetaNine.CoefficientMap.poleProduct n t ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      exact ht k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    have embedded_ZetaNine__CoefficientMap__clearedPoleProduct_ne_zero (n j : ℕ) :
        ZetaNine.CoefficientMap.clearedPoleProduct n j (-(j : ℚ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      have hkj := (Finset.mem_erase.mp hk).1
      intro hz
      have he : (k : ℚ) = (j : ℚ) := by linarith
      exact hkj (Nat.cast_inj.mp he)
    have embedded_ZetaNine__CoefficientMapJet__shiftedVariable_eval (j : ℕ) (z : ℚ) :
        (ZetaNine.CoefficientMapJet.shiftedVariable j).eval z = -(j : ℚ) + z := by
      simp [ZetaNine.CoefficientMapJet.shiftedVariable]
      ring
    have embedded_ZetaNine__CoefficientMapJet__shiftedClearedDenominator_eval (n j : ℕ) (z : ℚ) :
        (ZetaNine.CoefficientMapJet.shiftedClearedDenominator n j).eval z = ZetaNine.CoefficientMap.clearedPoleProduct n j (-(j : ℚ) + z) := by
      simp only [ZetaNine.CoefficientMapJet.shiftedClearedDenominator, Polynomial.eval_prod, Polynomial.eval_add,
        Polynomial.eval_C, embedded_ZetaNine__CoefficientMapJet__shiftedVariable_eval]
      rfl
    have embedded_ZetaNine__CoefficientMapJet__shiftedClearedDenominator_constant (n j : ℕ) :
        PowerSeries.constantCoeff (ZetaNine.CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) =
          ZetaNine.CoefficientMap.clearedPoleProduct n j (-(j : ℚ)) := by
      rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
        embedded_ZetaNine__CoefficientMapJet__shiftedClearedDenominator_eval]
      simp
    have embedded_ZetaNine__CoefficientMapJet__shiftedClearedDenominator_constant_ne_zero (n j : ℕ) :
        PowerSeries.constantCoeff (ZetaNine.CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ≠ 0 := by
      rw [embedded_ZetaNine__CoefficientMapJet__shiftedClearedDenominator_constant]
      exact embedded_ZetaNine__CoefficientMap__clearedPoleProduct_ne_zero n j
    have embedded_ZetaNine__CoefficientMapJet__clearedSeries_denominator_identity (n j : ℕ) :
        ZetaNine.CoefficientMapJet.clearedSeries n j * (ZetaNine.CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
          (ZetaNine.CoefficientMapJet.shiftedNumerator n j : PowerSeries ℚ) := by
      have h : PowerSeries.constantCoeff ((ZetaNine.CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9) ≠ 0 := by
        rw [map_pow]
        exact pow_ne_zero _ (embedded_ZetaNine__CoefficientMapJet__shiftedClearedDenominator_constant_ne_zero n j)
      unfold ZetaNine.CoefficientMapJet.clearedSeries
      rw [mul_assoc, PowerSeries.inv_mul_cancel _ h, mul_one]
    have embedded_ZetaNine__CoefficientMapJet__weightedClearedSeries_denominator_identity (n j : ℕ) (W : ℚ[X]) :
        ZetaNine.CoefficientMapJet.weightedClearedSeries n j W * (ZetaNine.CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
          (ZetaNine.CoefficientMapJet.shiftedNumerator n j * W.comp (ZetaNine.CoefficientMapJet.localU n j) : ℚ[X]) := by
      unfold ZetaNine.CoefficientMapJet.weightedClearedSeries
      rw [mul_right_comm, embedded_ZetaNine__CoefficientMapJet__clearedSeries_denominator_identity, Polynomial.coe_mul]
    have embedded_ZetaNine__CoefficientMapInjectivity__baseNumerator_eval (n : ℕ) (t : ℚ) :
        (ZetaNine.CoefficientMapInjectivity.baseNumerator n).eval t = ZetaNine.CoefficientMap.numerator n t := by
      simp only [ZetaNine.CoefficientMapInjectivity.baseNumerator, Polynomial.eval_mul, Polynomial.eval_prod,
        Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      rfl
    have embedded_ZetaNine__CoefficientMapInjectivity__weightedNumerator_shift (n j : ℕ) (W : ℚ[X]) :
        (ZetaNine.CoefficientMapInjectivity.weightedNumerator n W).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) =
          ZetaNine.CoefficientMapJet.shiftedNumerator n j * W.comp (ZetaNine.CoefficientMapJet.localU n j) := by
      simp only [ZetaNine.CoefficientMapInjectivity.weightedNumerator, ZetaNine.CoefficientMapInjectivity.baseNumerator, ZetaNine.CoefficientMapInjectivity.baseU, ZetaNine.CoefficientMapJet.shiftedNumerator,
        ZetaNine.CoefficientMapJet.localU, Polynomial.mul_comp, Polynomial.prod_comp,
        Polynomial.sub_comp, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp,
        Polynomial.comp_assoc]
    have embedded_ZetaNine__CoefficientMapInjectivity__pole_factors_coprime (a b : ℕ) (hab : a ≠ b) :
        IsCoprime ((X + C (a : ℚ)) ^ 9) ((X + C (b : ℚ)) ^ 9) := by
      have hneq : (-(a : ℚ)) ≠ -(b : ℚ) := by
        intro h
        exact hab (Nat.cast_inj.mp (neg_inj.mp h))
      have hc := Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero_of_ne hneq).isUnit
      have hp := hc.pow (m := 9) (n := 9)
      simpa only [map_neg, sub_neg_eq_add] using hp
    have embedded_ZetaNine__CoefficientMapInjectivity__polePolynomial_natDegree (n : ℕ) : (ZetaNine.CoefficientMapInjectivity.polePolynomial n).natDegree = n + 1 := by
      unfold ZetaNine.CoefficientMapInjectivity.polePolynomial
      rw [Polynomial.natDegree_prod_of_monic (range (n + 1))
        (fun j : ℕ => X + C (j : ℚ)) (fun j hj => Polynomial.monic_X_add_C (j : ℚ))]
      simp only [Polynomial.natDegree_X_add_C]
      simp
    have embedded_ZetaNine__CoefficientMapInjectivity__polePolynomial_pow_natDegree (n : ℕ) : (ZetaNine.CoefficientMapInjectivity.polePolynomial n ^ 9).natDegree = 9 * (n + 1) := by
      rw [Polynomial.natDegree_pow, embedded_ZetaNine__CoefficientMapInjectivity__polePolynomial_natDegree]
    have embedded_ZetaNine__CoefficientMapInjectivity__baseU_natDegree (n : ℕ) : (ZetaNine.CoefficientMapInjectivity.baseU n).natDegree = 2 := by
      unfold ZetaNine.CoefficientMapInjectivity.baseU
      rw [Polynomial.natDegree_mul (Polynomial.X_ne_zero) (Polynomial.X_add_C_ne_zero _)]
      simp only [Polynomial.natDegree_X, Polynomial.natDegree_X_add_C]
    have embedded_ZetaNine__CoefficientMapInjectivity__baseNumerator_ne_zero (n : ℕ) : ZetaNine.CoefficientMapInjectivity.baseNumerator n ≠ 0 := by
      unfold ZetaNine.CoefficientMapInjectivity.baseNumerator
      apply mul_ne_zero
      · apply mul_ne_zero
        · apply Polynomial.C_ne_zero.mpr
          apply pow_ne_zero
          exact_mod_cast n.factorial_ne_zero
        · apply Finset.prod_ne_zero_iff.mpr
          intro i hi
          exact Polynomial.X_sub_C_ne_zero _
      · apply Finset.prod_ne_zero_iff.mpr
        intro i hi
        rw [add_assoc, ← map_add]
        exact Polynomial.X_add_C_ne_zero _
    have embedded_ZetaNine__CoefficientMapInjectivity__baseNumerator_natDegree_le (n : ℕ) : (ZetaNine.CoefficientMapInjectivity.baseNumerator n).natDegree ≤ 2 * n := by
      have hL : (∏ i ∈ range n, (X - C ((i : ℚ) + 1))).natDegree ≤ n := by
        calc
          _ ≤ ∑ i ∈ range n, (X - C ((i : ℚ) + 1)).natDegree := Polynomial.natDegree_prod_le _ _
          _ = n := by
            simp only [Polynomial.natDegree_X_sub_C]
            simp
      have hR : (∏ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1))).natDegree ≤ n := by
        calc
          _ ≤ ∑ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1)).natDegree := Polynomial.natDegree_prod_le _ _
          _ = n := by
            simp only [add_assoc, ← map_add, Polynomial.natDegree_X_add_C]
            simp
      have h1 := Polynomial.natDegree_mul_le (p := C ((n.factorial : ℚ) ^ 7))
        (q := ∏ i ∈ range n, (X - C ((i : ℚ) + 1)))
      have h2 := Polynomial.natDegree_mul_le
        (p := C ((n.factorial : ℚ) ^ 7) * (∏ i ∈ range n, (X - C ((i : ℚ) + 1))))
        (q := ∏ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1)))
      simp only [Polynomial.natDegree_C, zero_add] at h1
      unfold ZetaNine.CoefficientMapInjectivity.baseNumerator
      omega
    have embedded_ZetaNine__CoefficientMapInjectivity__weightedNumerator_natDegree_le (n : ℕ) (W : ℚ[X]) :
        (ZetaNine.CoefficientMapInjectivity.weightedNumerator n W).natDegree ≤ 2 * n + 2 * W.natDegree := by
      have hmul := Polynomial.natDegree_mul_le (p := ZetaNine.CoefficientMapInjectivity.baseNumerator n) (q := W.comp (ZetaNine.CoefficientMapInjectivity.baseU n))
      have hcomp := Polynomial.natDegree_comp_le (p := W) (q := ZetaNine.CoefficientMapInjectivity.baseU n)
      rw [embedded_ZetaNine__CoefficientMapInjectivity__baseU_natDegree] at hcomp
      have hbase := embedded_ZetaNine__CoefficientMapInjectivity__baseNumerator_natDegree_le n
      unfold ZetaNine.CoefficientMapInjectivity.weightedNumerator
      omega
    have embedded_ZetaNine__CoefficientMapInjectivity__weightedNumerator_zero_implies_multiplier_zero (n : ℕ) (W : ℚ[X])
        (h : ZetaNine.CoefficientMapInjectivity.weightedNumerator n W = 0) : W = 0 := by
      have hcomp : W.comp (ZetaNine.CoefficientMapInjectivity.baseU n) = 0 :=
        (mul_eq_zero.mp h).resolve_left (embedded_ZetaNine__CoefficientMapInjectivity__baseNumerator_ne_zero n)
      rcases Polynomial.comp_eq_zero_iff.mp hcomp with hW | hconstant
      · exact hW
      · have hdeg := congrArg Polynomial.natDegree hconstant.2
        rw [embedded_ZetaNine__CoefficientMapInjectivity__baseU_natDegree, Polynomial.natDegree_C] at hdeg
        omega
    have embedded_ZetaNine__CoefficientMapPartialFractions__clearedPolePolynomial_comp_shift (n j : ℕ) :
        (ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial n j).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) =
          ZetaNine.CoefficientMapJet.shiftedClearedDenominator n j := by
      simp only [ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial, ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
        Polynomial.prod_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
    have embedded_ZetaNine__CoefficientMapPartialFractions__localTruncation_comp_eq_sum (n j : ℕ) (W : ℚ[X]) :
        (ZetaNine.CoefficientMapPartialFractions.localTruncation n j W).comp (X + C (j : ℚ)) =
          ∑ s ∈ Icc 1 9, C (ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W) *
            (X + C (j : ℚ)) ^ (9 - s) := by
      unfold ZetaNine.CoefficientMapPartialFractions.localTruncation Polynomial.comp
      rw [PowerSeries.eval₂_trunc_eq_sum_range]
      apply Finset.sum_nbij' (fun k : ℕ => 9 - k) (fun s : ℕ => 9 - s)
      · intro k hk
        have hk' := Finset.mem_range.mp hk
        rw [Finset.mem_Icc]
        omega
      · intro s hs
        have hs' := Finset.mem_Icc.mp hs
        rw [Finset.mem_range]
        omega
      · intro k hk
        have hk' := Finset.mem_range.mp hk
        omega
      · intro s hs
        have hs' := Finset.mem_Icc.mp hs
        omega
      · intro k hk
        have hk' := Finset.mem_range.mp hk
        have he : 9 - (9 - k) = k := by omega
        simp only [ZetaNine.CoefficientMapJet.weightedLocalCoefficient, he]
    have embedded_ZetaNine__CoefficientMapPartialFractions__partialNumerator_eq_sum_blocks (n : ℕ) (W : ℚ[X]) :
        ZetaNine.CoefficientMapPartialFractions.partialNumerator n W = ∑ j ∈ range (n + 1), ZetaNine.CoefficientMapPartialFractions.partialBlock n j W := by
      unfold ZetaNine.CoefficientMapPartialFractions.partialNumerator ZetaNine.CoefficientMapPartialFractions.partialBlock
      apply Finset.sum_congr rfl
      intro j hj
      rw [embedded_ZetaNine__CoefficientMapPartialFractions__localTruncation_comp_eq_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    have embedded_ZetaNine__CoefficientMapPartialFractions__partialBlock_comp_own_shift (n j : ℕ) (W : ℚ[X]) :
        (ZetaNine.CoefficientMapPartialFractions.partialBlock n j W).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) =
          ZetaNine.CoefficientMapJet.shiftedClearedDenominator n j ^ 9 * ZetaNine.CoefficientMapPartialFractions.localTruncation n j W := by
      rw [ZetaNine.CoefficientMapPartialFractions.partialBlock, Polynomial.mul_comp, Polynomial.pow_comp, embedded_ZetaNine__CoefficientMapPartialFractions__clearedPolePolynomial_comp_shift]
      simp only [Polynomial.comp_assoc, Polynomial.add_comp,
        Polynomial.X_comp, Polynomial.C_comp, ZetaNine.CoefficientMapJet.shiftedVariable,
        sub_add_cancel, Polynomial.comp_X]
    have embedded_ZetaNine__CoefficientMapPartialFractions__truncation_remainder_X_pow_dvd (S : PowerSeries ℚ) :
        (PowerSeries.X : PowerSeries ℚ) ^ 9 ∣ S - (PowerSeries.trunc 9 S : PowerSeries ℚ) := by
      apply PowerSeries.X_pow_dvd_iff.mpr
      intro k hk
      simp only [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hk, sub_self]
    have embedded_ZetaNine__CoefficientMapPartialFractions__polynomial_X_pow_dvd_of_series (P : ℚ[X])
        (h : (PowerSeries.X : PowerSeries ℚ) ^ 9 ∣ (P : PowerSeries ℚ)) :
        (X : ℚ[X]) ^ 9 ∣ P := by
      apply Polynomial.X_pow_dvd_iff.mpr
      intro k hk
      simpa only [Polynomial.coeff_coe] using PowerSeries.X_pow_dvd_iff.mp h k hk
    have embedded_ZetaNine__CoefficientMapPartialFractions__own_block_matches_nine_jets (n j : ℕ) (W : ℚ[X]) :
        (X : ℚ[X]) ^ 9 ∣
          (ZetaNine.CoefficientMapInjectivity.weightedNumerator n W).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) -
            (ZetaNine.CoefficientMapPartialFractions.partialBlock n j W).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) := by
      apply embedded_ZetaNine__CoefficientMapPartialFractions__polynomial_X_pow_dvd_of_series
      have h := dvd_mul_of_dvd_left
        (embedded_ZetaNine__CoefficientMapPartialFractions__truncation_remainder_X_pow_dvd (ZetaNine.CoefficientMapJet.weightedClearedSeries n j W))
        ((ZetaNine.CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)
      have he : ((ZetaNine.CoefficientMapInjectivity.weightedNumerator n W).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) -
          (ZetaNine.CoefficientMapPartialFractions.partialBlock n j W).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) : ℚ[X]) =
          ZetaNine.CoefficientMapJet.shiftedNumerator n j * W.comp (ZetaNine.CoefficientMapJet.localU n j) -
            ZetaNine.CoefficientMapJet.shiftedClearedDenominator n j ^ 9 * ZetaNine.CoefficientMapPartialFractions.localTruncation n j W := by
        rw [embedded_ZetaNine__CoefficientMapInjectivity__weightedNumerator_shift, embedded_ZetaNine__CoefficientMapPartialFractions__partialBlock_comp_own_shift]
      rw [he]
      convert h using 1
      rw [sub_mul, embedded_ZetaNine__CoefficientMapJet__weightedClearedSeries_denominator_identity]
      simp only [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow, ZetaNine.CoefficientMapPartialFractions.localTruncation]
      ring
    have embedded_ZetaNine__CoefficientMapPartialFractions__different_block_pole_divisibility (n i j : ℕ) (W : ℚ[X])
        (hj : j ≤ n) (hji : j ≠ i) :
        (X + C (j : ℚ)) ^ 9 ∣ ZetaNine.CoefficientMapPartialFractions.partialBlock n i W := by
      have hjmem : j ∈ (range (n + 1)).erase i := by
        simp only [Finset.mem_erase, Finset.mem_range]
        exact ⟨hji, Nat.lt_succ_of_le hj⟩
      have hbase : X + C (j : ℚ) ∣ ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial n i :=
        Finset.dvd_prod_of_mem (fun k : ℕ => X + C (k : ℚ)) hjmem
      exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hbase 9) _
    have embedded_ZetaNine__CoefficientMapPartialFractions__different_block_shift_X_pow_dvd (n i j : ℕ) (W : ℚ[X])
        (hj : j ≤ n) (hji : j ≠ i) :
        (X : ℚ[X]) ^ 9 ∣ (ZetaNine.CoefficientMapPartialFractions.partialBlock n i W).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) := by
      obtain ⟨q, hq⟩ := embedded_ZetaNine__CoefficientMapPartialFractions__different_block_pole_divisibility n i j W hj hji
      refine ⟨q.comp (ZetaNine.CoefficientMapJet.shiftedVariable j), ?_⟩
      have he := congrArg (fun p : ℚ[X] => p.comp (ZetaNine.CoefficientMapJet.shiftedVariable j)) hq
      simpa only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.add_comp,
        Polynomial.X_comp, Polynomial.C_comp, ZetaNine.CoefficientMapJet.shiftedVariable, sub_add_cancel] using he
    have embedded_ZetaNine__CoefficientMapPartialFractions__full_candidate_matches_nine_jets (n j : ℕ) (W : ℚ[X]) (hj : j ≤ n) :
        (X : ℚ[X]) ^ 9 ∣
          (ZetaNine.CoefficientMapInjectivity.weightedNumerator n W - ZetaNine.CoefficientMapPartialFractions.partialNumerator n W).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) := by
      have hjmem : j ∈ range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
      have hsplit : (ZetaNine.CoefficientMapPartialFractions.partialNumerator n W).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) =
          (ZetaNine.CoefficientMapPartialFractions.partialBlock n j W).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) +
            ∑ i ∈ (range (n + 1)).erase j,
              (ZetaNine.CoefficientMapPartialFractions.partialBlock n i W).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) := by
        rw [embedded_ZetaNine__CoefficientMapPartialFractions__partialNumerator_eq_sum_blocks, Polynomial.sum_comp]
        exact (Finset.add_sum_erase (range (n + 1))
          (fun i => (ZetaNine.CoefficientMapPartialFractions.partialBlock n i W).comp (ZetaNine.CoefficientMapJet.shiftedVariable j)) hjmem).symm
      have hoff : (X : ℚ[X]) ^ 9 ∣
          ∑ i ∈ (range (n + 1)).erase j,
            (ZetaNine.CoefficientMapPartialFractions.partialBlock n i W).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) := by
        apply Finset.dvd_sum
        intro i hi
        exact embedded_ZetaNine__CoefficientMapPartialFractions__different_block_shift_X_pow_dvd n i j W hj (Finset.ne_of_mem_erase hi).symm
      rw [Polynomial.sub_comp, hsplit, sub_add_eq_sub_sub]
      exact dvd_sub (embedded_ZetaNine__CoefficientMapPartialFractions__own_block_matches_nine_jets n j W) hoff
    have embedded_ZetaNine__CoefficientMapPartialFractions__shifted_divisibility_implies_pole_divisibility (P : ℚ[X]) (j : ℕ)
        (h : (X : ℚ[X]) ^ 9 ∣ P.comp (ZetaNine.CoefficientMapJet.shiftedVariable j)) :
        (X + C (j : ℚ)) ^ 9 ∣ P := by
      obtain ⟨q, hq⟩ := h
      refine ⟨q.comp (X + C (j : ℚ)), ?_⟩
      have he := congrArg (fun p : ℚ[X] => p.comp (X + C (j : ℚ))) hq
      simpa only [Polynomial.comp_assoc, ZetaNine.CoefficientMapJet.shiftedVariable,
        Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, add_sub_cancel_right,
        Polynomial.comp_X, Polynomial.mul_comp, Polynomial.pow_comp] using he
    have embedded_ZetaNine__CoefficientMapPartialFractions__denominator_divides_actual_candidate_difference (n : ℕ) (W : ℚ[X]) :
        ZetaNine.CoefficientMapInjectivity.polePolynomial n ^ 9 ∣ ZetaNine.CoefficientMapInjectivity.weightedNumerator n W - ZetaNine.CoefficientMapPartialFractions.partialNumerator n W := by
      unfold ZetaNine.CoefficientMapInjectivity.polePolynomial
      rw [← Finset.prod_pow]
      apply Finset.prod_dvd_of_coprime
      · intro a ha b hb hab
        exact embedded_ZetaNine__CoefficientMapInjectivity__pole_factors_coprime a b hab
      · intro j hj
        apply embedded_ZetaNine__CoefficientMapPartialFractions__shifted_divisibility_implies_pole_divisibility
        exact embedded_ZetaNine__CoefficientMapPartialFractions__full_candidate_matches_nine_jets n j W (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    have embedded_ZetaNine__CoefficientMapPartialFractions__clearedPolePolynomial_natDegree (n j : ℕ) (hj : j ≤ n) :
        (ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial n j).natDegree = n := by
      unfold ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial
      rw [Polynomial.natDegree_prod_of_monic ((range (n + 1)).erase j)
        (fun k : ℕ => X + C (k : ℚ)) (fun k hk => Polynomial.monic_X_add_C (k : ℚ))]
      simp only [Polynomial.natDegree_X_add_C]
      simp [Nat.lt_succ_of_le hj]
    have embedded_ZetaNine__CoefficientMapPartialFractions__localTruncation_natDegree_le (n j : ℕ) (W : ℚ[X]) :
        (ZetaNine.CoefficientMapPartialFractions.localTruncation n j W).natDegree ≤ 8 := by
      have h := PowerSeries.natDegree_trunc_lt (ZetaNine.CoefficientMapJet.weightedClearedSeries n j W) 8
      exact Nat.le_of_lt_succ h
    have embedded_ZetaNine__CoefficientMapPartialFractions__partialBlock_natDegree_le (n j : ℕ) (W : ℚ[X]) (hj : j ≤ n) :
        (ZetaNine.CoefficientMapPartialFractions.partialBlock n j W).natDegree ≤ 9 * n + 8 := by
      have hm := Polynomial.natDegree_mul_le (p := ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial n j ^ 9)
        (q := (ZetaNine.CoefficientMapPartialFractions.localTruncation n j W).comp (X + C (j : ℚ)))
      have hc := Polynomial.natDegree_comp_le (p := ZetaNine.CoefficientMapPartialFractions.localTruncation n j W) (q := X + C (j : ℚ))
      rw [Polynomial.natDegree_X_add_C, mul_one] at hc
      rw [Polynomial.natDegree_pow, embedded_ZetaNine__CoefficientMapPartialFractions__clearedPolePolynomial_natDegree n j hj] at hm
      have ht := embedded_ZetaNine__CoefficientMapPartialFractions__localTruncation_natDegree_le n j W
      unfold ZetaNine.CoefficientMapPartialFractions.partialBlock
      omega
    have embedded_ZetaNine__CoefficientMapPartialFractions__partialNumerator_natDegree_le (n : ℕ) (W : ℚ[X]) :
        (ZetaNine.CoefficientMapPartialFractions.partialNumerator n W).natDegree ≤ 9 * n + 8 := by
      rw [embedded_ZetaNine__CoefficientMapPartialFractions__partialNumerator_eq_sum_blocks]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j hj
      exact embedded_ZetaNine__CoefficientMapPartialFractions__partialBlock_natDegree_le n j W (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    have embedded_ZetaNine__CoefficientMapPartialFractions__actual_global_polynomial_partial_fractions (n : ℕ) (W : ℚ[X])
        (hproper : ZetaNine.CoefficientMapInjectivity.ProperMultiplier n W) : ZetaNine.CoefficientMapInjectivity.weightedNumerator n W = ZetaNine.CoefficientMapPartialFractions.partialNumerator n W := by
      have hdvd := embedded_ZetaNine__CoefficientMapPartialFractions__denominator_divides_actual_candidate_difference n W
      have hzero : ZetaNine.CoefficientMapInjectivity.weightedNumerator n W - ZetaNine.CoefficientMapPartialFractions.partialNumerator n W = 0 := by
        by_contra hne
        have hdeg := Polynomial.natDegree_le_of_dvd hdvd hne
        rw [embedded_ZetaNine__CoefficientMapInjectivity__polePolynomial_pow_natDegree] at hdeg
        have hw := embedded_ZetaNine__CoefficientMapInjectivity__weightedNumerator_natDegree_le n W
        have hp := embedded_ZetaNine__CoefficientMapPartialFractions__partialNumerator_natDegree_le n W
        have hdiff := Polynomial.natDegree_sub_le (ZetaNine.CoefficientMapInjectivity.weightedNumerator n W) (ZetaNine.CoefficientMapPartialFractions.partialNumerator n W)
        unfold ZetaNine.CoefficientMapInjectivity.ProperMultiplier at hproper
        rcases le_total (ZetaNine.CoefficientMapInjectivity.weightedNumerator n W).natDegree (ZetaNine.CoefficientMapPartialFractions.partialNumerator n W).natDegree with h | h
        · rw [max_eq_right h] at hdiff
          omega
        · rw [max_eq_left h] at hdiff
          omega
      exact sub_eq_zero.mp hzero
    have embedded_ZetaNine__CoefficientMapPartialFractions__polePolynomial_eval (n : ℕ) (t : ℚ) :
        (ZetaNine.CoefficientMapInjectivity.polePolynomial n).eval t = ZetaNine.CoefficientMap.poleProduct n t := by
      simp only [ZetaNine.CoefficientMapInjectivity.polePolynomial, Polynomial.eval_prod, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_C]
      rfl
    have embedded_ZetaNine__CoefficientMapPartialFractions__polePolynomial_eval_ne_zero (n : ℕ) (t : ℚ)
        (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) : (ZetaNine.CoefficientMapInjectivity.polePolynomial n).eval t ≠ 0 := by
      rw [embedded_ZetaNine__CoefficientMapPartialFractions__polePolynomial_eval]
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      exact hregular k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    have embedded_ZetaNine__CoefficientMapPartialFractions__polePolynomial_eval_factor (n j : ℕ) (t : ℚ) (hj : j ≤ n) :
        (ZetaNine.CoefficientMapInjectivity.polePolynomial n).eval t = (t + (j : ℚ)) * (ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial n j).eval t := by
      simp only [ZetaNine.CoefficientMapInjectivity.polePolynomial, ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial, Polynomial.eval_prod,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      exact (Finset.mul_prod_erase (range (n + 1)) (fun k => t + (k : ℚ))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).symm
    have embedded_ZetaNine__CoefficientMapPartialFractions__actual_weighted_rational_representation (n : ℕ) (W : ℚ[X]) (t : ℚ) :
        ZetaNine.CoefficientMap.weightedR n W t =
          (ZetaNine.CoefficientMapInjectivity.weightedNumerator n W).eval t / ((ZetaNine.CoefficientMapInjectivity.polePolynomial n).eval t) ^ 9 := by
      simp only [ZetaNine.CoefficientMapInjectivity.weightedNumerator, Polynomial.eval_mul, Polynomial.eval_comp,
        embedded_ZetaNine__CoefficientMapInjectivity__baseNumerator_eval, ZetaNine.CoefficientMapInjectivity.baseU, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_C,
        embedded_ZetaNine__CoefficientMapPartialFractions__polePolynomial_eval, ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR]
      ring
    have embedded_ZetaNine__CoefficientMapPartialFractions__partial_term_division (n j s : ℕ) (W : ℚ[X]) (t : ℚ) (hj : j ≤ n)
        (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
        (ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W *
          (ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial n j).eval t ^ 9 * (t + (j : ℚ)) ^ (9 - s)) /
            (ZetaNine.CoefficientMapInjectivity.polePolynomial n).eval t ^ 9 =
          ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s := by
      apply (div_eq_div_iff (pow_ne_zero _ (embedded_ZetaNine__CoefficientMapPartialFractions__polePolynomial_eval_ne_zero n t hregular))
        (pow_ne_zero _ (hregular j hj))).mpr
      rw [embedded_ZetaNine__CoefficientMapPartialFractions__polePolynomial_eval_factor n j t hj, mul_pow]
      have he : (t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s = (t + (j : ℚ)) ^ 9 := by
        rw [← pow_add]
        congr 1
        omega
      calc
        _ = ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W *
            (ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial n j).eval t ^ 9 *
            ((t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s) := by ring
        _ = _ := by rw [he]; ring
    have embedded_ZetaNine__CoefficientMapPartialFractions__actual_global_partial_fractions (n : ℕ) (W : ℚ[X])
        (hproper : ZetaNine.CoefficientMapInjectivity.ProperMultiplier n W) (t : ℚ)
        (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
        ZetaNine.CoefficientMap.weightedR n W t =
          ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
            ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s := by
      rw [embedded_ZetaNine__CoefficientMapPartialFractions__actual_weighted_rational_representation, embedded_ZetaNine__CoefficientMapPartialFractions__actual_global_polynomial_partial_fractions n W hproper]
      simp only [ZetaNine.CoefficientMapPartialFractions.partialNumerator, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro s hs
      exact embedded_ZetaNine__CoefficientMapPartialFractions__partial_term_division n j s W t (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
        (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2 hregular
    have embedded_ZetaNine__CoefficientMapReflection__product_reverse_erased_range (n j : ℕ) (hj : j ≤ n) (f : ℕ → ℚ[X]) :
        ∏ k ∈ (range (n + 1)).erase (n - j), f (n - k) =
          ∏ k ∈ (range (n + 1)).erase j, f k := by
      apply Finset.prod_nbij' (fun k : ℕ => n - k) (fun k : ℕ => n - k)
      · intro k hk
        have h := Finset.mem_erase.mp hk
        have hr := Finset.mem_range.mp h.2
        rw [Finset.mem_erase, Finset.mem_range]
        constructor <;> omega
      · intro k hk
        have h := Finset.mem_erase.mp hk
        have hr := Finset.mem_range.mp h.2
        rw [Finset.mem_erase, Finset.mem_range]
        constructor <;> omega
      · intro k hk
        have h := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
        omega
      · intro k hk
        have h := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
        omega
      · intro k hk
        rfl
    have embedded_ZetaNine__CoefficientMapReflection__sum_reverse_range (n : ℕ) (f : ℕ → ℚ) :
        ∑ k ∈ range (n + 1), f (n - k) = ∑ k ∈ range (n + 1), f k := by
      apply Finset.sum_nbij' (fun k : ℕ => n - k) (fun k : ℕ => n - k)
      · intro k hk
        have h := Finset.mem_range.mp hk
        rw [Finset.mem_range]
        omega
      · intro k hk
        have h := Finset.mem_range.mp hk
        rw [Finset.mem_range]
        omega
      · intro k hk
        have h := Finset.mem_range.mp hk
        omega
      · intro k hk
        have h := Finset.mem_range.mp hk
        omega
      · intro k hk
        rfl
    have embedded_ZetaNine__CoefficientMapReflection__baseNumerator_reflection (n : ℕ) :
        (ZetaNine.CoefficientMapInjectivity.baseNumerator n).comp (ZetaNine.CoefficientMapReflection.reflectionVariable n) = ZetaNine.CoefficientMapInjectivity.baseNumerator n := by
      have hleft : (∏ i ∈ range n, (ZetaNine.CoefficientMapReflection.reflectionVariable n - C ((i : ℚ) + 1))) =
          (-1 : ℚ[X]) ^ n * ∏ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1)) := by
        calc
          _ = ∏ i ∈ range n, -(X + C (n : ℚ) + C ((i : ℚ) + 1)) := by
            apply Finset.prod_congr rfl
            intro i hi
            unfold ZetaNine.CoefficientMapReflection.reflectionVariable
            ring
          _ = _ := by rw [Finset.prod_neg, Finset.card_range]
      have hright : (∏ i ∈ range n, (ZetaNine.CoefficientMapReflection.reflectionVariable n + C (n : ℚ) + C ((i : ℚ) + 1))) =
          (-1 : ℚ[X]) ^ n * ∏ i ∈ range n, (X - C ((i : ℚ) + 1)) := by
        calc
          _ = ∏ i ∈ range n, -(X - C ((i : ℚ) + 1)) := by
            apply Finset.prod_congr rfl
            intro i hi
            unfold ZetaNine.CoefficientMapReflection.reflectionVariable
            ring
          _ = _ := by rw [Finset.prod_neg, Finset.card_range]
      simp only [ZetaNine.CoefficientMapInjectivity.baseNumerator, Polynomial.mul_comp, Polynomial.prod_comp, Polynomial.C_comp,
        Polynomial.sub_comp, Polynomial.add_comp, Polynomial.X_comp]
      rw [hleft, hright]
      have hsign : (-1 : ℚ[X]) ^ n * (-1 : ℚ[X]) ^ n = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        _ = C ((n.factorial : ℚ) ^ 7) * ((-1 : ℚ[X]) ^ n * (-1 : ℚ[X]) ^ n) *
            (∏ i ∈ range n, (X - C ((i : ℚ) + 1))) *
            (∏ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1))) := by ring
        _ = _ := by rw [hsign, mul_one]
    have embedded_ZetaNine__CoefficientMapReflection__baseU_reflection (n : ℕ) : (ZetaNine.CoefficientMapInjectivity.baseU n).comp (ZetaNine.CoefficientMapReflection.reflectionVariable n) = ZetaNine.CoefficientMapInjectivity.baseU n := by
      simp only [ZetaNine.CoefficientMapInjectivity.baseU, Polynomial.mul_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
        ZetaNine.CoefficientMapReflection.reflectionVariable]
      ring
    have embedded_ZetaNine__CoefficientMapReflection__weightedNumerator_reflection (n : ℕ) (W : ℚ[X]) :
        (ZetaNine.CoefficientMapInjectivity.weightedNumerator n W).comp (ZetaNine.CoefficientMapReflection.reflectionVariable n) = ZetaNine.CoefficientMapInjectivity.weightedNumerator n W := by
      simp only [ZetaNine.CoefficientMapInjectivity.weightedNumerator, Polynomial.mul_comp, embedded_ZetaNine__CoefficientMapReflection__baseNumerator_reflection,
        Polynomial.comp_assoc, embedded_ZetaNine__CoefficientMapReflection__baseU_reflection]
    have embedded_ZetaNine__CoefficientMapReflection__clearedPolePolynomial_reflection (n j : ℕ) (hj : j ≤ n) :
        (ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial n (n - j)).comp (ZetaNine.CoefficientMapReflection.reflectionVariable n) =
          C ((-1 : ℚ) ^ n) * ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial n j := by
      simp only [ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial, Polynomial.prod_comp, Polynomial.add_comp,
        Polynomial.X_comp, Polynomial.C_comp]
      calc
        _ = ∏ k ∈ (range (n + 1)).erase (n - j), -(X + C ((n - k : ℕ) : ℚ)) := by
          apply Finset.prod_congr rfl
          intro k hk
          have hk' := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_erase.mp hk).2)
          rw [Nat.cast_sub hk', map_sub]
          unfold ZetaNine.CoefficientMapReflection.reflectionVariable
          ring
        _ = (-1 : ℚ[X]) ^ n * ∏ k ∈ (range (n + 1)).erase j, (X + C (k : ℚ)) := by
          rw [Finset.prod_neg,
            embedded_ZetaNine__CoefficientMapReflection__product_reverse_erased_range n j hj (fun k : ℕ => (X : ℚ[X]) + C (k : ℚ))]
          congr 1
          simp [Nat.lt_succ_of_le (Nat.sub_le n j)]
        _ = _ := by simp only [map_pow, map_neg, map_one]
    have embedded_ZetaNine__CoefficientMapReflection__local_shift_reflection (n j : ℕ) (hj : j ≤ n) :
        (ZetaNine.CoefficientMapJet.shiftedVariable (n - j)).comp (-X) =
          (ZetaNine.CoefficientMapReflection.reflectionVariable n).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) := by
      simp only [ZetaNine.CoefficientMapJet.shiftedVariable, ZetaNine.CoefficientMapReflection.reflectionVariable, Polynomial.sub_comp,
        Polynomial.neg_comp, Polynomial.X_comp, Polynomial.C_comp, Nat.cast_sub hj, map_sub]
      ring
    have embedded_ZetaNine__CoefficientMapReflection__shiftedWeightedNumerator_reflection (n j : ℕ) (W : ℚ[X]) (hj : j ≤ n) :
        ((ZetaNine.CoefficientMapInjectivity.weightedNumerator n W).comp (ZetaNine.CoefficientMapJet.shiftedVariable (n - j))).comp (-X) =
          (ZetaNine.CoefficientMapInjectivity.weightedNumerator n W).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) := by
      rw [Polynomial.comp_assoc, embedded_ZetaNine__CoefficientMapReflection__local_shift_reflection n j hj, ← Polynomial.comp_assoc,
        embedded_ZetaNine__CoefficientMapReflection__weightedNumerator_reflection]
    have embedded_ZetaNine__CoefficientMapReflection__shiftedClearedDenominator_reflection (n j : ℕ) (hj : j ≤ n) :
        (ZetaNine.CoefficientMapJet.shiftedClearedDenominator n (n - j)).comp (-X) =
          C ((-1 : ℚ) ^ n) * ZetaNine.CoefficientMapJet.shiftedClearedDenominator n j := by
      rw [← embedded_ZetaNine__CoefficientMapPartialFractions__clearedPolePolynomial_comp_shift, Polynomial.comp_assoc, embedded_ZetaNine__CoefficientMapReflection__local_shift_reflection n j hj,
        ← Polynomial.comp_assoc, embedded_ZetaNine__CoefficientMapReflection__clearedPolePolynomial_reflection n j hj,
        Polynomial.mul_comp, Polynomial.C_comp, embedded_ZetaNine__CoefficientMapPartialFractions__clearedPolePolynomial_comp_shift]
    have embedded_ZetaNine__CoefficientMapReflection__rescale_neg_one_C (a : ℚ) :
        PowerSeries.rescale (-1 : ℚ) (PowerSeries.C a) = PowerSeries.C a := by
      ext k
      by_cases hk : k = 0 <;> simp [PowerSeries.coeff_rescale, PowerSeries.coeff_C, hk]
    have embedded_ZetaNine__CoefficientMapReflection__rescale_neg_one_polynomial (P : ℚ[X]) :
        PowerSeries.rescale (-1 : ℚ) (P : PowerSeries ℚ) = (P.comp (-X) : PowerSeries ℚ) := by
      induction P using Polynomial.induction_on' with
      | add P Q hP hQ =>
          simp only [Polynomial.coe_add, map_add, hP, hQ, Polynomial.add_comp]
      | monomial k a =>
          rw [← Polynomial.C_mul_X_pow_eq_monomial]
          simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X,
            map_mul, map_pow, embedded_ZetaNine__CoefficientMapReflection__rescale_neg_one_C, PowerSeries.rescale_neg_one_X,
            Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp,
            Polynomial.coe_neg]
    have embedded_ZetaNine__CoefficientMapReflection__actual_local_series_reflection (n j : ℕ) (hn : Even n) (W : ℚ[X]) (hj : j ≤ n) :
        PowerSeries.rescale (-1 : ℚ) (ZetaNine.CoefficientMapJet.weightedClearedSeries n (n - j) W) =
          ZetaNine.CoefficientMapJet.weightedClearedSeries n j W := by
      have hD : PowerSeries.rescale (-1 : ℚ)
          (ZetaNine.CoefficientMapJet.shiftedClearedDenominator n (n - j) : PowerSeries ℚ) =
          (ZetaNine.CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) := by
        rw [embedded_ZetaNine__CoefficientMapReflection__rescale_neg_one_polynomial, embedded_ZetaNine__CoefficientMapReflection__shiftedClearedDenominator_reflection n j hj, hn.neg_one_pow]
        simp
      have hP : PowerSeries.rescale (-1 : ℚ)
          ((ZetaNine.CoefficientMapJet.shiftedNumerator n (n - j) *
            W.comp (ZetaNine.CoefficientMapJet.localU n (n - j)) : ℚ[X]) : PowerSeries ℚ) =
          ((ZetaNine.CoefficientMapJet.shiftedNumerator n j * W.comp (ZetaNine.CoefficientMapJet.localU n j) : ℚ[X]) : PowerSeries ℚ) := by
        rw [embedded_ZetaNine__CoefficientMapReflection__rescale_neg_one_polynomial, ← embedded_ZetaNine__CoefficientMapInjectivity__weightedNumerator_shift, embedded_ZetaNine__CoefficientMapReflection__shiftedWeightedNumerator_reflection n j W hj,
          embedded_ZetaNine__CoefficientMapInjectivity__weightedNumerator_shift]
      have he := congrArg (PowerSeries.rescale (-1 : ℚ))
        (embedded_ZetaNine__CoefficientMapJet__weightedClearedSeries_denominator_identity n (n - j) W)
      rw [map_mul, map_pow, hD, hP] at he
      have hnonzero : (ZetaNine.CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 ≠ 0 := by
        intro hz
        have hc := pow_ne_zero 9 (embedded_ZetaNine__CoefficientMapJet__shiftedClearedDenominator_constant_ne_zero n j)
        apply hc
        rw [← map_pow, hz, map_zero]
      apply mul_right_cancel₀ hnonzero
      exact he.trans (embedded_ZetaNine__CoefficientMapJet__weightedClearedSeries_denominator_identity n j W).symm
    have embedded_ZetaNine__CoefficientMapReflection__local_coefficient_reflection (n j s : ℕ) (hn : Even n) (W : ℚ[X])
        (hj : j ≤ n) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
        ZetaNine.CoefficientMapJet.weightedLocalCoefficient n (n - j) s W =
          (-1 : ℚ) ^ (s + 1) * ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W := by
      have he := congrArg (PowerSeries.coeff (9 - s)) (embedded_ZetaNine__CoefficientMapReflection__actual_local_series_reflection n j hn W hj)
      rw [PowerSeries.coeff_rescale] at he
      have hsign : (-1 : ℚ) ^ (9 - s) * (-1 : ℚ) ^ (9 - s) = 1 := by
        rw [← mul_pow]
        norm_num
      have hparity : (-1 : ℚ) ^ (9 - s) = (-1 : ℚ) ^ (s + 1) := by
        interval_cases s <;> norm_num
      unfold ZetaNine.CoefficientMapJet.weightedLocalCoefficient
      calc
        _ = ((-1 : ℚ) ^ (9 - s) * (-1 : ℚ) ^ (9 - s)) *
            PowerSeries.coeff (9 - s) (ZetaNine.CoefficientMapJet.weightedClearedSeries n (n - j) W) := by rw [hsign, one_mul]
        _ = (-1 : ℚ) ^ (9 - s) *
            (((-1 : ℚ) ^ (9 - s)) *
              PowerSeries.coeff (9 - s) (ZetaNine.CoefficientMapJet.weightedClearedSeries n (n - j) W)) := by ring
        _ = _ := by rw [he, hparity]
    have embedded_ZetaNine__CoefficientMapReflection__rho_even_order_zero (n s : ℕ) (hn : Even n) (W : ℚ[X])
        (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hs : Even s) : ZetaNine.CoefficientMapReflection.rho n s W = 0 := by
      have he : ZetaNine.CoefficientMapReflection.rho n s W = (-1 : ℚ) ^ (s + 1) * ZetaNine.CoefficientMapReflection.rho n s W := by
        calc
          _ = ∑ j ∈ range (n + 1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n (n - j) s W :=
            (embedded_ZetaNine__CoefficientMapReflection__sum_reverse_range n _).symm
          _ = ∑ j ∈ range (n + 1), (-1 : ℚ) ^ (s + 1) *
              ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W := by
            apply Finset.sum_congr rfl
            intro j hj
            exact embedded_ZetaNine__CoefficientMapReflection__local_coefficient_reflection n j s hn W (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hs1 hs9
          _ = _ := by rw [← Finset.mul_sum]; rfl
      rw [pow_succ, hs.neg_one_pow, one_mul, neg_one_mul] at he
      linarith
    have embedded_ZetaNine__CoefficientMapReflection__strong_proper_implies_proper (n : ℕ) (W : ℚ[X])
        (h : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) : ZetaNine.CoefficientMapInjectivity.ProperMultiplier n W := by
      unfold ZetaNine.CoefficientMapReflection.StrongProperMultiplier at h
      unfold ZetaNine.CoefficientMapInjectivity.ProperMultiplier
      omega
    have embedded_ZetaNine__CoefficientMapReflection__quartic_is_strong_proper (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
        ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W := by
      unfold ZetaNine.CoefficientMapReflection.StrongProperMultiplier
      omega
    have embedded_ZetaNine__CoefficientMapReflection__clearedPolePolynomial_monic (n j : ℕ) : (ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial n j).Monic := by
      unfold ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial
      apply Polynomial.monic_prod_of_monic
      intro k hk
      exact Polynomial.monic_X_add_C _
    have embedded_ZetaNine__CoefficientMapReflection__partialBasis_monic (n j s : ℕ) : (ZetaNine.CoefficientMapReflection.partialBasis n j s).Monic := by
      exact ((embedded_ZetaNine__CoefficientMapReflection__clearedPolePolynomial_monic n j).pow 9).mul ((Polynomial.monic_X_add_C (j : ℚ)).pow (9 - s))
    have embedded_ZetaNine__CoefficientMapReflection__partialBasis_natDegree (n j s : ℕ) (hj : j ≤ n) :
        (ZetaNine.CoefficientMapReflection.partialBasis n j s).natDegree = 9 * n + (9 - s) := by
      unfold ZetaNine.CoefficientMapReflection.partialBasis
      rw [Polynomial.natDegree_mul ((embedded_ZetaNine__CoefficientMapReflection__clearedPolePolynomial_monic n j).pow 9).ne_zero
        ((Polynomial.monic_X_add_C (j : ℚ)).pow (9 - s)).ne_zero,
        Polynomial.natDegree_pow, Polynomial.natDegree_pow,
        embedded_ZetaNine__CoefficientMapPartialFractions__clearedPolePolynomial_natDegree n j hj, Polynomial.natDegree_X_add_C]
      omega
    have embedded_ZetaNine__CoefficientMapReflection__partialBasis_simple_pole_top_coefficient (n j : ℕ) (hj : j ≤ n) :
        (ZetaNine.CoefficientMapReflection.partialBasis n j 1).coeff (9 * n + 8) = 1 := by
      have h := (embedded_ZetaNine__CoefficientMapReflection__partialBasis_monic n j 1).coeff_natDegree
      simpa only [embedded_ZetaNine__CoefficientMapReflection__partialBasis_natDegree n j 1 hj, Nat.reduceSub] using h
    have embedded_ZetaNine__CoefficientMapReflection__partialBasis_higher_pole_top_coefficient (n j s : ℕ) (hj : j ≤ n)
        (hs : 2 ≤ s) (hs9 : s ≤ 9) : (ZetaNine.CoefficientMapReflection.partialBasis n j s).coeff (9 * n + 8) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [embedded_ZetaNine__CoefficientMapReflection__partialBasis_natDegree n j s hj]
      omega
    have embedded_ZetaNine__CoefficientMapReflection__partialNumerator_top_coefficient_is_rho_one (n : ℕ) (W : ℚ[X]) :
        (ZetaNine.CoefficientMapPartialFractions.partialNumerator n W).coeff (9 * n + 8) = ZetaNine.CoefficientMapReflection.rho n 1 W := by
      simp only [ZetaNine.CoefficientMapPartialFractions.partialNumerator, Polynomial.finsetSum_coeff, ZetaNine.CoefficientMapReflection.rho]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [Finset.sum_eq_single_of_mem 1 (by simp)]
      · rw [mul_assoc, Polynomial.coeff_C_mul]
        change ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j 1 W *
          (ZetaNine.CoefficientMapReflection.partialBasis n j 1).coeff (9 * n + 8) = _
        rw [embedded_ZetaNine__CoefficientMapReflection__partialBasis_simple_pole_top_coefficient n j hj', mul_one]
      · intro s hs hsne
        have hs' := Finset.mem_Icc.mp hs
        have hs2 : 2 ≤ s := by omega
        rw [mul_assoc, Polynomial.coeff_C_mul]
        change ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W *
          (ZetaNine.CoefficientMapReflection.partialBasis n j s).coeff (9 * n + 8) = 0
        rw [embedded_ZetaNine__CoefficientMapReflection__partialBasis_higher_pole_top_coefficient n j s hj' hs2 hs'.2, mul_zero]
    have embedded_ZetaNine__CoefficientMapReflection__rho_one_zero_of_strong_proper (n : ℕ) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) : ZetaNine.CoefficientMapReflection.rho n 1 W = 0 := by
      have hpoly := embedded_ZetaNine__CoefficientMapPartialFractions__actual_global_polynomial_partial_fractions n W (embedded_ZetaNine__CoefficientMapReflection__strong_proper_implies_proper n W hstrong)
      have hcoeff := congrArg (fun P : ℚ[X] => P.coeff (9 * n + 8)) hpoly
      rw [embedded_ZetaNine__CoefficientMapReflection__partialNumerator_top_coefficient_is_rho_one] at hcoeff
      have hzero : (ZetaNine.CoefficientMapInjectivity.weightedNumerator n W).coeff (9 * n + 8) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hbound := embedded_ZetaNine__CoefficientMapInjectivity__weightedNumerator_natDegree_le n W
        unfold ZetaNine.CoefficientMapReflection.StrongProperMultiplier at hstrong
        omega
      rw [hzero] at hcoeff
      exact hcoeff.symm
    have embedded_ZetaNine__CoefficientMapFiniteSum__harmonicPower_succ (s T : ℕ) :
        ZetaNine.HarmonicStability.harmonicPower s (T + 1) = ZetaNine.HarmonicStability.harmonicPower s T + 1 / ((T + 1 : ℕ) : ℚ) ^ s := by
      unfold ZetaNine.HarmonicStability.harmonicPower
      exact Finset.sum_Icc_succ_top (by omega) _
    have embedded_ZetaNine__CoefficientMapFiniteSum__shifted_harmonic_sum (s T j : ℕ) :
        (∑ t ∈ Icc 1 T, 1 / ((t : ℚ) + (j : ℚ)) ^ s) =
          ZetaNine.HarmonicStability.harmonicPower s (T + j) - ZetaNine.HarmonicStability.harmonicPower s j := by
      induction T with
      | zero => simp [ZetaNine.HarmonicStability.harmonicPower]
      | succ T ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih]
        have he : T + 1 + j = (T + j) + 1 := by omega
        rw [he, embedded_ZetaNine__CoefficientMapFiniteSum__harmonicPower_succ]
        simp only [Nat.cast_add, Nat.cast_one]
        ring
    have embedded_ZetaNine__CoefficientMapFiniteSum__actual_finite_harmonic_identity (n T : ℕ) (W : ℚ[X])
        (hproper : ZetaNine.CoefficientMapInjectivity.ProperMultiplier n W) :
        ZetaNine.CoefficientMapFiniteSum.finiteL n T W = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
          ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W *
            (ZetaNine.HarmonicStability.harmonicPower s (T + j) - ZetaNine.HarmonicStability.harmonicPower s j) := by
      unfold ZetaNine.CoefficientMapFiniteSum.finiteL
      calc
        _ = ∑ t ∈ Icc 1 T, ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
            ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s := by
          apply Finset.sum_congr rfl
          intro t ht
          apply embedded_ZetaNine__CoefficientMapPartialFractions__actual_global_partial_fractions n W hproper
          intro k hk
          have htpos : (0 : ℚ) < (t : ℚ) := by exact_mod_cast (Finset.mem_Icc.mp ht).1
          exact ne_of_gt (add_pos_of_pos_of_nonneg htpos (Nat.cast_nonneg k))
        _ = ∑ j ∈ range (n + 1), ∑ t ∈ Icc 1 T, ∑ s ∈ Icc 1 9,
            ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s :=
          Finset.sum_comm
        _ = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9, ∑ t ∈ Icc 1 T,
            ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s := by
          apply Finset.sum_congr rfl
          intro j hj
          exact Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro s hs
          have hterm : (∑ t ∈ Icc 1 T,
              ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s) =
              ∑ t ∈ Icc 1 T,
              ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W * (1 / ((t : ℚ) + (j : ℚ)) ^ s) := by
            apply Finset.sum_congr rfl
            intro t ht
            ring
          rw [hterm]
          rw [← Finset.mul_sum, embedded_ZetaNine__CoefficientMapFiniteSum__shifted_harmonic_sum]
    have embedded_ZetaNine__CoefficientMapFiniteSum__actual_grouped_finite_identity (n T : ℕ) (W : ℚ[X])
        (hproper : ZetaNine.CoefficientMapInjectivity.ProperMultiplier n W) :
        ZetaNine.CoefficientMapFiniteSum.finiteL n T W = ZetaNine.CoefficientMapFiniteSum.constantTerm n W +
          (∑ s ∈ Icc 1 9, ZetaNine.CoefficientMapFiniteSum.rho n s W * ZetaNine.HarmonicStability.harmonicPower s T) + ZetaNine.CoefficientMapFiniteSum.shiftedTail n T W := by
      rw [embedded_ZetaNine__CoefficientMapFiniteSum__actual_finite_harmonic_identity n T W hproper]
      have hmain : (∑ s ∈ Icc 1 9, ZetaNine.CoefficientMapFiniteSum.rho n s W * ZetaNine.HarmonicStability.harmonicPower s T) =
          ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
            ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W * ZetaNine.HarmonicStability.harmonicPower s T := by
        unfold ZetaNine.CoefficientMapFiniteSum.rho
        simp only [Finset.sum_mul]
        exact Finset.sum_comm
      rw [hmain]
      unfold ZetaNine.CoefficientMapFiniteSum.constantTerm ZetaNine.CoefficientMapFiniteSum.shiftedTail
      simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro s hs
      ring
    have embedded_ZetaNine__CoefficientMapFiniteSum__actual_grouped_finite_identity_no_simple_pole (n T : ℕ) (W : ℚ[X])
        (hproper : ZetaNine.CoefficientMapInjectivity.ProperMultiplier n W) (hcancel : ZetaNine.CoefficientMapFiniteSum.rho n 1 W = 0) :
        ZetaNine.CoefficientMapFiniteSum.finiteL n T W = ZetaNine.CoefficientMapFiniteSum.constantTerm n W +
          (∑ s ∈ Icc 2 9, ZetaNine.CoefficientMapFiniteSum.rho n s W * ZetaNine.HarmonicStability.harmonicPower s T) + ZetaNine.CoefficientMapFiniteSum.shiftedTail n T W := by
      rw [embedded_ZetaNine__CoefficientMapFiniteSum__actual_grouped_finite_identity n T W hproper]
      have hsplit : (∑ s ∈ Icc 1 9, ZetaNine.CoefficientMapFiniteSum.rho n s W * ZetaNine.HarmonicStability.harmonicPower s T) =
          ZetaNine.CoefficientMapFiniteSum.rho n 1 W * ZetaNine.HarmonicStability.harmonicPower 1 T + ∑ s ∈ Icc 2 9, ZetaNine.CoefficientMapFiniteSum.rho n s W * ZetaNine.HarmonicStability.harmonicPower s T := by
        rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
        rfl
      rw [hsplit, hcancel, zero_mul, zero_add]
    have embedded_ZetaNine__CoefficientMapFiniteSum__actual_grouped_finite_identity_odd (n T : ℕ) (W : ℚ[X])
        (hproper : ZetaNine.CoefficientMapInjectivity.ProperMultiplier n W) (h1 : ZetaNine.CoefficientMapFiniteSum.rho n 1 W = 0)
        (h2 : ZetaNine.CoefficientMapFiniteSum.rho n 2 W = 0) (h4 : ZetaNine.CoefficientMapFiniteSum.rho n 4 W = 0)
        (h6 : ZetaNine.CoefficientMapFiniteSum.rho n 6 W = 0) (h8 : ZetaNine.CoefficientMapFiniteSum.rho n 8 W = 0) :
        ZetaNine.CoefficientMapFiniteSum.finiteL n T W = ZetaNine.CoefficientMapFiniteSum.constantTerm n W +
          (ZetaNine.CoefficientMapFiniteSum.rho n 3 W * ZetaNine.HarmonicStability.harmonicPower 3 T + ZetaNine.CoefficientMapFiniteSum.rho n 5 W * ZetaNine.HarmonicStability.harmonicPower 5 T +
           ZetaNine.CoefficientMapFiniteSum.rho n 7 W * ZetaNine.HarmonicStability.harmonicPower 7 T + ZetaNine.CoefficientMapFiniteSum.rho n 9 W * ZetaNine.HarmonicStability.harmonicPower 9 T) +
          ZetaNine.CoefficientMapFiniteSum.shiftedTail n T W := by
      rw [embedded_ZetaNine__CoefficientMapFiniteSum__actual_grouped_finite_identity_no_simple_pole n T W hproper h1]
      have hs : (∑ s ∈ Icc 2 9, ZetaNine.CoefficientMapFiniteSum.rho n s W * ZetaNine.HarmonicStability.harmonicPower s T) =
          ZetaNine.CoefficientMapFiniteSum.rho n 3 W * ZetaNine.HarmonicStability.harmonicPower 3 T + ZetaNine.CoefficientMapFiniteSum.rho n 5 W * ZetaNine.HarmonicStability.harmonicPower 5 T +
          ZetaNine.CoefficientMapFiniteSum.rho n 7 W * ZetaNine.HarmonicStability.harmonicPower 7 T + ZetaNine.CoefficientMapFiniteSum.rho n 9 W * ZetaNine.HarmonicStability.harmonicPower 9 T := by
        norm_num [Finset.sum_Icc_succ_top, h2, h4, h6, h8]
      rw [hs]
    have embedded_ZetaNine__CoefficientMapFiniteSum__harmonic_difference_eq_shifted (s T j : ℕ) :
        ZetaNine.HarmonicStability.harmonicPower s (T + j) - ZetaNine.HarmonicStability.harmonicPower s T =
          ∑ k ∈ Icc 1 j, 1 / ((T : ℚ) + (k : ℚ)) ^ s := by
      simpa only [Nat.add_comm j T, add_comm] using (embedded_ZetaNine__CoefficientMapFiniteSum__shifted_harmonic_sum s j T).symm
    have embedded_ZetaNine__CoefficientMapSummation__actual_finite_odd_identity (n T : ℕ) (hn : Even n) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) :
        ZetaNine.CoefficientMapFiniteSum.finiteL n T W = ZetaNine.CoefficientMapFiniteSum.constantTerm n W +
          (ZetaNine.CoefficientMapFiniteSum.rho n 3 W * ZetaNine.HarmonicStability.harmonicPower 3 T +
           ZetaNine.CoefficientMapFiniteSum.rho n 5 W * ZetaNine.HarmonicStability.harmonicPower 5 T +
           ZetaNine.CoefficientMapFiniteSum.rho n 7 W * ZetaNine.HarmonicStability.harmonicPower 7 T +
           ZetaNine.CoefficientMapFiniteSum.rho n 9 W * ZetaNine.HarmonicStability.harmonicPower 9 T) +
          ZetaNine.CoefficientMapFiniteSum.shiftedTail n T W := by
      exact embedded_ZetaNine__CoefficientMapFiniteSum__actual_grouped_finite_identity_odd n T W
        (embedded_ZetaNine__CoefficientMapReflection__strong_proper_implies_proper n W hstrong) (embedded_ZetaNine__CoefficientMapReflection__rho_one_zero_of_strong_proper n W hstrong)
        (embedded_ZetaNine__CoefficientMapReflection__rho_even_order_zero n 2 hn W (by norm_num) (by norm_num) (by norm_num))
        (embedded_ZetaNine__CoefficientMapReflection__rho_even_order_zero n 4 hn W (by norm_num) (by norm_num) (by norm_num))
        (embedded_ZetaNine__CoefficientMapReflection__rho_even_order_zero n 6 hn W (by norm_num) (by norm_num) (by norm_num))
        (embedded_ZetaNine__CoefficientMapReflection__rho_even_order_zero n 8 hn W (by norm_num) (by norm_num) (by norm_num))
    have embedded_ZetaNine__CoefficientMapSummation__sum_Icc_eq_sum_range_successor (T : ℕ) (f : ℕ → ℝ) :
        ∑ t ∈ Icc 1 T, f t = ∑ t ∈ range T, f (t + 1) := by
      apply Finset.sum_nbij' (fun t : ℕ => t - 1) (fun t : ℕ => t + 1)
      · intro t ht
        have h := Finset.mem_Icc.mp ht
        rw [Finset.mem_range]
        omega
      · intro t ht
        have h := Finset.mem_range.mp ht
        rw [Finset.mem_Icc]
        omega
      · intro t ht
        have h := Finset.mem_Icc.mp ht
        omega
      · intro t ht
        omega
      · intro t ht
        have h := Finset.mem_Icc.mp ht
        have he : t - 1 + 1 = t := by omega
        rw [he]
    have embedded_ZetaNine__CoefficientMapSummation__harmonicPower_cast (s T : ℕ) :
        (ZetaNine.HarmonicStability.harmonicPower s T : ℝ) = ∑ t ∈ Icc 1 T, 1 / (t : ℝ) ^ s := by
      unfold ZetaNine.HarmonicStability.harmonicPower
      push_cast
      rfl
    have embedded_ZetaNine__CoefficientMapSummation__harmonicPower_cast_eq_range (s T : ℕ) (hs : 1 ≤ s) :
        (ZetaNine.HarmonicStability.harmonicPower s T : ℝ) = ∑ t ∈ range (T + 1), 1 / (t : ℝ) ^ s := by
      rw [embedded_ZetaNine__CoefficientMapSummation__harmonicPower_cast, embedded_ZetaNine__CoefficientMapSummation__sum_Icc_eq_sum_range_successor, Finset.sum_range_succ']
      simp [show s ≠ 0 by omega]
    have embedded_ZetaNine__CoefficientMapSummation__zetaReal_eq_tsum (s : ℕ) (hs : 1 < s) :
        ZetaNine.CoefficientMapSummation.zetaReal s = ∑' t : ℕ, 1 / (t : ℝ) ^ s := by
      have he : ((∑' t : ℕ, 1 / (t : ℝ) ^ s : ℝ) : ℂ) = riemannZeta (s : ℂ) := by
        rw [Complex.ofReal_tsum, zeta_nat_eq_tsum_of_gt_one hs]
        apply tsum_congr
        intro t
        simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_natCast]
      have hr := congrArg Complex.re he
      simpa only [Complex.ofReal_re, ZetaNine.CoefficientMapSummation.zetaReal] using hr.symm
    have embedded_ZetaNine__CoefficientMapSummation__harmonicPower_tendsto_zeta (s : ℕ) (hs : 1 < s) :
        Tendsto (fun T : ℕ => (ZetaNine.HarmonicStability.harmonicPower s T : ℝ)) atTop (𝓝 (ZetaNine.CoefficientMapSummation.zetaReal s)) := by
      have h := ((Real.summable_one_div_nat_pow.mpr hs).hasSum.tendsto_sum_nat).comp
        (tendsto_add_atTop_nat 1)
      rw [← embedded_ZetaNine__CoefficientMapSummation__zetaReal_eq_tsum s hs] at h
      simpa only [Function.comp_def, ← embedded_ZetaNine__CoefficientMapSummation__harmonicPower_cast_eq_range s _ (by omega)] using h
    have embedded_ZetaNine__CoefficientMapSummation__shifted_reciprocal_tendsto_zero (s k : ℕ) (hs : 1 ≤ s) :
        Tendsto (fun T : ℕ => 1 / ((T : ℝ) + (k : ℝ)) ^ s) atTop (𝓝 0) := by
      have hbase : Tendsto (fun T : ℕ => (((T + k : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat k))
      simpa only [one_div, inv_pow, Nat.cast_add, zero_pow (show s ≠ 0 by omega)] using hbase.pow s
    have embedded_ZetaNine__CoefficientMapSummation__harmonic_fixed_tail_tendsto_zero (s j : ℕ) (hs : 1 ≤ s) :
        Tendsto (fun T : ℕ => ((ZetaNine.HarmonicStability.harmonicPower s (T + j) - ZetaNine.HarmonicStability.harmonicPower s T : ℚ) : ℝ)) atTop (𝓝 0) := by
      have h := tendsto_finsetSum (Icc 1 j) (fun k hk => embedded_ZetaNine__CoefficientMapSummation__shifted_reciprocal_tendsto_zero s k hs)
      have he : (fun T : ℕ => ((ZetaNine.HarmonicStability.harmonicPower s (T + j) - ZetaNine.HarmonicStability.harmonicPower s T : ℚ) : ℝ)) =
          (fun T : ℕ => ∑ k ∈ Icc 1 j, 1 / ((T : ℝ) + (k : ℝ)) ^ s) := by
        funext T
        rw [embedded_ZetaNine__CoefficientMapFiniteSum__harmonic_difference_eq_shifted]
        push_cast
        rfl
      rw [he]
      simpa only [Finset.sum_const_zero] using h
    have embedded_ZetaNine__CoefficientMapSummation__actual_shiftedTail_tendsto_zero (n : ℕ) (W : ℚ[X]) :
        Tendsto (fun T : ℕ => (ZetaNine.CoefficientMapFiniteSum.shiftedTail n T W : ℝ)) atTop (𝓝 0) := by
      have h := tendsto_finsetSum (range (n + 1)) (fun j hj =>
        tendsto_finsetSum (Icc 1 9) (fun s hs =>
          (embedded_ZetaNine__CoefficientMapSummation__harmonic_fixed_tail_tendsto_zero s j (Finset.mem_Icc.mp hs).1).const_mul
            (ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ)))
      have he : (fun T : ℕ => (ZetaNine.CoefficientMapFiniteSum.shiftedTail n T W : ℝ)) =
          (fun T : ℕ => ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
            (ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ) *
              ((ZetaNine.HarmonicStability.harmonicPower s (T + j) - ZetaNine.HarmonicStability.harmonicPower s T : ℚ) : ℝ)) := by
        funext T
        unfold ZetaNine.CoefficientMapFiniteSum.shiftedTail
        push_cast
        rfl
      rw [he]
      simpa only [mul_zero, Finset.sum_const_zero] using h
    have embedded_ZetaNine__CoefficientMapSummation__actual_finiteL_tendsto_exactL (n : ℕ) (hn : Even n) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) :
        Tendsto (fun T : ℕ => (ZetaNine.CoefficientMapFiniteSum.finiteL n T W : ℝ)) atTop (𝓝 (ZetaNine.CoefficientMapSummation.exactL n W)) := by
      have hB : Tendsto (fun _ : ℕ => (ZetaNine.CoefficientMapFiniteSum.constantTerm n W : ℝ)) atTop
          (𝓝 (ZetaNine.CoefficientMapFiniteSum.constantTerm n W : ℝ)) := tendsto_const_nhds
      have hmain := (((embedded_ZetaNine__CoefficientMapSummation__harmonicPower_tendsto_zeta 3 (by omega)).const_mul (ZetaNine.CoefficientMapFiniteSum.rho n 3 W : ℝ)).add
        ((embedded_ZetaNine__CoefficientMapSummation__harmonicPower_tendsto_zeta 5 (by omega)).const_mul (ZetaNine.CoefficientMapFiniteSum.rho n 5 W : ℝ))).add
        ((embedded_ZetaNine__CoefficientMapSummation__harmonicPower_tendsto_zeta 7 (by omega)).const_mul (ZetaNine.CoefficientMapFiniteSum.rho n 7 W : ℝ))
      have hmain' := hmain.add ((embedded_ZetaNine__CoefficientMapSummation__harmonicPower_tendsto_zeta 9 (by omega)).const_mul
        (ZetaNine.CoefficientMapFiniteSum.rho n 9 W : ℝ))
      have h := (hB.add hmain').add (embedded_ZetaNine__CoefficientMapSummation__actual_shiftedTail_tendsto_zero n W)
      convert h using 1
      · funext T
        rw [embedded_ZetaNine__CoefficientMapSummation__actual_finite_odd_identity n T hn W hstrong]
        push_cast
        rfl
      · simp only [ZetaNine.CoefficientMapSummation.exactL, add_zero]
    have embedded_ZetaNine__CoefficientMapAggregate__actual_local_coefficient_add (n j s : ℕ) (W V : ℚ[X]) :
        ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s (W + V) =
          ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W + ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s V := by
      simp [ZetaNine.CoefficientMapJet.weightedLocalCoefficient, ZetaNine.CoefficientMapJet.weightedClearedSeries, add_comp, mul_add]
    have embedded_ZetaNine__CoefficientMapAggregate__actual_local_coefficient_smul (n j s : ℕ) (a : ℚ) (W : ℚ[X]) :
        ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s (a • W) = a * ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W := by
      simp [ZetaNine.CoefficientMapJet.weightedLocalCoefficient, ZetaNine.CoefficientMapJet.weightedClearedSeries, smul_comp, smul_eq_mul]
    have embedded_ZetaNine__CoefficientMapAggregate__actual_rho_add (n s : ℕ) (W V : ℚ[X]) :
        ZetaNine.CoefficientMapFiniteSum.rho n s (W + V) =
          ZetaNine.CoefficientMapFiniteSum.rho n s W + ZetaNine.CoefficientMapFiniteSum.rho n s V := by
      simp [ZetaNine.CoefficientMapFiniteSum.rho, embedded_ZetaNine__CoefficientMapAggregate__actual_local_coefficient_add, Finset.sum_add_distrib]
    have embedded_ZetaNine__CoefficientMapAggregate__actual_rho_smul (n s : ℕ) (a : ℚ) (W : ℚ[X]) :
        ZetaNine.CoefficientMapFiniteSum.rho n s (a • W) = a * ZetaNine.CoefficientMapFiniteSum.rho n s W := by
      simp [ZetaNine.CoefficientMapFiniteSum.rho, embedded_ZetaNine__CoefficientMapAggregate__actual_local_coefficient_smul, Finset.mul_sum]
    have embedded_ZetaNine__CoefficientMapAggregate__actual_constant_add (n : ℕ) (W V : ℚ[X]) :
        ZetaNine.CoefficientMapFiniteSum.constantTerm n (W + V) =
          ZetaNine.CoefficientMapFiniteSum.constantTerm n W + ZetaNine.CoefficientMapFiniteSum.constantTerm n V := by
      simp only [ZetaNine.CoefficientMapFiniteSum.constantTerm, embedded_ZetaNine__CoefficientMapAggregate__actual_local_coefficient_add, add_mul,
        Finset.sum_add_distrib]
      ring
    have embedded_ZetaNine__CoefficientMapAggregate__actual_constant_smul (n : ℕ) (a : ℚ) (W : ℚ[X]) :
        ZetaNine.CoefficientMapFiniteSum.constantTerm n (a • W) = a * ZetaNine.CoefficientMapFiniteSum.constantTerm n W := by
      simp [ZetaNine.CoefficientMapFiniteSum.constantTerm, embedded_ZetaNine__CoefficientMapAggregate__actual_local_coefficient_smul, mul_assoc,
        Finset.mul_sum]
    have embedded_ZetaNine__CoefficientMapAggregate__aggregate_add (n : ℕ) (W V : ℚ[X]) :
        ZetaNine.CoefficientMapAggregate.aggregate n (W + V) = ZetaNine.CoefficientMapAggregate.aggregate n W + ZetaNine.CoefficientMapAggregate.aggregate n V := by
      funext i
      fin_cases i <;> simp [ZetaNine.CoefficientMapAggregate.aggregate, embedded_ZetaNine__CoefficientMapAggregate__actual_constant_add, embedded_ZetaNine__CoefficientMapAggregate__actual_rho_add]
    have embedded_ZetaNine__CoefficientMapAggregate__aggregate_smul (n : ℕ) (a : ℚ) (W : ℚ[X]) :
        ZetaNine.CoefficientMapAggregate.aggregate n (a • W) = a • ZetaNine.CoefficientMapAggregate.aggregate n W := by
      funext i
      fin_cases i <;> simp [ZetaNine.CoefficientMapAggregate.aggregate, embedded_ZetaNine__CoefficientMapAggregate__actual_constant_smul, embedded_ZetaNine__CoefficientMapAggregate__actual_rho_smul, smul_eq_mul]
    have embedded_ZetaNine__CoefficientMapAggregate__coordinatePolynomial_add (a b : Fin 5 → ℚ) :
        ZetaNine.CoefficientMapAggregate.coordinatePolynomial (a + b) = ZetaNine.CoefficientMapAggregate.coordinatePolynomial a + ZetaNine.CoefficientMapAggregate.coordinatePolynomial b := by
      simp [ZetaNine.CoefficientMapAggregate.coordinatePolynomial, C_add, add_mul, Finset.sum_add_distrib]
    have embedded_ZetaNine__CoefficientMapAggregate__coordinatePolynomial_smul (c : ℚ) (a : Fin 5 → ℚ) :
        ZetaNine.CoefficientMapAggregate.coordinatePolynomial (c • a) = c • ZetaNine.CoefficientMapAggregate.coordinatePolynomial a := by
      simp [ZetaNine.CoefficientMapAggregate.coordinatePolynomial, smul_eq_mul, C_mul, mul_assoc, smul_eq_C_mul,
        Finset.mul_sum]
    have embedded_ZetaNine__CoefficientMapAggregate__coordinatePolynomial_coeff (a : Fin 5 → ℚ) (i : Fin 5) :
        (ZetaNine.CoefficientMapAggregate.coordinatePolynomial a).coeff i.val = a i := by
      classical
      simp only [ZetaNine.CoefficientMapAggregate.coordinatePolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        have h : i.val ≠ j.val := by intro he; exact hji (Fin.ext he.symm)
        simp [h]
      · simp
    have embedded_ZetaNine__CoefficientMapAggregate__coordinatePolynomial_natDegree_le (a : Fin 5 → ℚ) :
        (ZetaNine.CoefficientMapAggregate.coordinatePolynomial a).natDegree ≤ 4 := by
      unfold ZetaNine.CoefficientMapAggregate.coordinatePolynomial
      apply natDegree_sum_le_of_forall_le
      intro i hi
      have h : (C (a i) * X ^ i.val : ℚ[X]).natDegree ≤
          (C (a i) : ℚ[X]).natDegree + (X ^ i.val : ℚ[X]).natDegree := natDegree_mul_le
      simp only [natDegree_C, natDegree_X_pow, zero_add] at h
      exact h.trans (by have := i.isLt; omega)
    have embedded_ZetaNine__CoefficientMapAggregate__coordinates_restore (a : Fin 5 → ℚ) :
        ZetaNine.CoefficientMapAggregate.polynomialCoordinates (ZetaNine.CoefficientMapAggregate.coordinatePolynomial a) = a := by
      funext i
      exact embedded_ZetaNine__CoefficientMapAggregate__coordinatePolynomial_coeff a i
    have embedded_ZetaNine__CoefficientMapAggregate__coordinatePolynomial_injective : Function.Injective ZetaNine.CoefficientMapAggregate.coordinatePolynomial := by
      intro a b hab
      simpa only [embedded_ZetaNine__CoefficientMapAggregate__coordinates_restore] using congrArg ZetaNine.CoefficientMapAggregate.polynomialCoordinates hab
    have embedded_ZetaNine__CoefficientMapAggregate__aggregate_zero_iff (n : ℕ) (W : ℚ[X]) :
        ZetaNine.CoefficientMapAggregate.aggregate n W = 0 ↔ ZetaNine.CoefficientMapFiniteSum.constantTerm n W = 0 ∧
          ZetaNine.CoefficientMapFiniteSum.rho n 3 W = 0 ∧ ZetaNine.CoefficientMapFiniteSum.rho n 5 W = 0 ∧
          ZetaNine.CoefficientMapFiniteSum.rho n 7 W = 0 ∧ ZetaNine.CoefficientMapFiniteSum.rho n 9 W = 0 := by
      constructor
      · intro h
        exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3, congrFun h 4⟩
      · rintro ⟨hB, h3, h5, h7, h9⟩
        funext i
        fin_cases i <;> simp [ZetaNine.CoefficientMapAggregate.aggregate, hB, h3, h5, h7, h9]
    have embedded_ZetaNine__CoefficientMapAggregate__aggregate_zero_all_rho (n : ℕ) (hn : Even n) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0)
        (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) : ZetaNine.CoefficientMapFiniteSum.rho n s W = 0 := by
      obtain ⟨hB, h3, h5, h7, h9⟩ := (embedded_ZetaNine__CoefficientMapAggregate__aggregate_zero_iff n W).mp hzero
      have h1 : ZetaNine.CoefficientMapFiniteSum.rho n 1 W = 0 := embedded_ZetaNine__CoefficientMapReflection__rho_one_zero_of_strong_proper n W hstrong
      have h2 : ZetaNine.CoefficientMapFiniteSum.rho n 2 W = 0 := embedded_ZetaNine__CoefficientMapReflection__rho_even_order_zero n 2 hn W (by omega) (by omega) (by norm_num)
      have h4 : ZetaNine.CoefficientMapFiniteSum.rho n 4 W = 0 := embedded_ZetaNine__CoefficientMapReflection__rho_even_order_zero n 4 hn W (by omega) (by omega) (by norm_num)
      have h6 : ZetaNine.CoefficientMapFiniteSum.rho n 6 W = 0 := embedded_ZetaNine__CoefficientMapReflection__rho_even_order_zero n 6 hn W (by omega) (by omega) (by norm_num)
      have h8 : ZetaNine.CoefficientMapFiniteSum.rho n 8 W = 0 := embedded_ZetaNine__CoefficientMapReflection__rho_even_order_zero n 8 hn W (by omega) (by omega) (by norm_num)
      interval_cases s <;> assumption
    have embedded_ZetaNine__CoefficientMapAggregate__aggregate_zero_exactL (n : ℕ) (W : ℚ[X]) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0) :
        ZetaNine.CoefficientMapSummation.exactL n W = 0 := by
      obtain ⟨hB, h3, h5, h7, h9⟩ := (embedded_ZetaNine__CoefficientMapAggregate__aggregate_zero_iff n W).mp hzero
      simp [ZetaNine.CoefficientMapSummation.exactL, hB, h3, h5, h7, h9]
    have embedded_ZetaNine__CoefficientMapTelescoper__prefixSum_succ (c : ℕ → ℚ) (j : ℕ) :
        ZetaNine.CoefficientMapTelescoper.prefixSum c (j + 1) = ZetaNine.CoefficientMapTelescoper.prefixSum c j + c (j + 1) := by
      unfold ZetaNine.CoefficientMapTelescoper.prefixSum
      exact Finset.sum_range_succ _ _
    have embedded_ZetaNine__CoefficientMapTelescoper__finite_cumulative_difference (n : ℕ) (c f : ℕ → ℚ) :
        (∑ j ∈ range n, ZetaNine.CoefficientMapTelescoper.prefixSum c j * (f j - f (j + 1))) =
          (∑ j ∈ range (n + 1), c j * f j) - ZetaNine.CoefficientMapTelescoper.prefixSum c n * f n := by
      induction n with
      | zero => simp [ZetaNine.CoefficientMapTelescoper.prefixSum]
      | succ n ih =>
        rw [Finset.sum_range_succ (fun j => ZetaNine.CoefficientMapTelescoper.prefixSum c j * (f j - f (j + 1))) n, ih,
          Finset.sum_range_succ (fun j => c j * f j) (n + 1), embedded_ZetaNine__CoefficientMapTelescoper__prefixSum_succ]
        ring
    have embedded_ZetaNine__CoefficientMapTelescoper__cumulativeCoefficient_succ (n j s : ℕ) (W : ℚ[X]) :
        ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient n (j + 1) s W = ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient n j s W +
          ZetaNine.CoefficientMapJet.weightedLocalCoefficient n (j + 1) s W := embedded_ZetaNine__CoefficientMapTelescoper__prefixSum_succ _ j
    have embedded_ZetaNine__CoefficientMapTelescoper__cumulativeCoefficient_last_zero (n : ℕ) (hn : Even n) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0)
        (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) : ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient n n s W = 0 :=
      embedded_ZetaNine__CoefficientMapAggregate__aggregate_zero_all_rho n hn W hstrong hzero s hs1 hs9
    have embedded_ZetaNine__CoefficientMapTelescoper__telescoper_as_sum_over_orders (n : ℕ) (W : ℚ[X]) (t : ℚ) :
        ZetaNine.CoefficientMapTelescoper.telescoper n W t = ∑ s ∈ Icc 1 9, ∑ j ∈ range n,
          ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient n j s W / (t + (j : ℚ)) ^ s := Finset.sum_comm
    have embedded_ZetaNine__CoefficientMapTelescoper__telescoper_difference_principal_parts (n : ℕ) (hn : Even n) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0) (t : ℚ) :
        ZetaNine.CoefficientMapTelescoper.telescoper n W t - ZetaNine.CoefficientMapTelescoper.telescoper n W (t + 1) =
          ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
            ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s := by
      rw [embedded_ZetaNine__CoefficientMapTelescoper__telescoper_as_sum_over_orders, embedded_ZetaNine__CoefficientMapTelescoper__telescoper_as_sum_over_orders, ← Finset.sum_sub_distrib]
      calc
        _ = ∑ s ∈ Icc 1 9, ∑ j ∈ range n, ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient n j s W *
            (1 / (t + (j : ℚ)) ^ s - 1 / (t + ((j + 1 : ℕ) : ℚ)) ^ s) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          have hshift : (t + 1) + (j : ℚ) = t + ((j + 1 : ℕ) : ℚ) := by push_cast; ring
          rw [hshift]
          ring
        _ = ∑ s ∈ Icc 1 9, ∑ j ∈ range (n + 1),
            ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s := by
          apply Finset.sum_congr rfl
          intro s hs
          have h := embedded_ZetaNine__CoefficientMapTelescoper__finite_cumulative_difference n (fun j => ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W)
            (fun j => 1 / (t + (j : ℚ)) ^ s)
          change (∑ j ∈ range n, ZetaNine.CoefficientMapTelescoper.prefixSum (fun j => ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W) j *
            (1 / (t + (j : ℚ)) ^ s - 1 / (t + ((j + 1 : ℕ) : ℚ)) ^ s)) = _
          rw [h]
          have htotal : ZetaNine.CoefficientMapTelescoper.prefixSum (fun j => ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W) n = 0 :=
            embedded_ZetaNine__CoefficientMapTelescoper__cumulativeCoefficient_last_zero n hn W hstrong hzero s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
          simp only [htotal, mul_one_div, zero_div, sub_zero]
        _ = _ := Finset.sum_comm
    have embedded_ZetaNine__CoefficientMapTelescoper__actual_weightedR_is_difference (n : ℕ) (hn : Even n) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0) (t : ℚ)
        (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
        ZetaNine.CoefficientMap.weightedR n W t = ZetaNine.CoefficientMapTelescoper.telescoper n W t - ZetaNine.CoefficientMapTelescoper.telescoper n W (t + 1) := by
      rw [embedded_ZetaNine__CoefficientMapTelescoper__telescoper_difference_principal_parts n hn W hstrong hzero t]
      exact embedded_ZetaNine__CoefficientMapPartialFractions__actual_global_partial_fractions n W
        (embedded_ZetaNine__CoefficientMapReflection__strong_proper_implies_proper n W hstrong) t hregular
    have embedded_ZetaNine__CoefficientMapTelescoper__telescoper_positive_tendsto_zero (n : ℕ) (W : ℚ[X]) :
        Tendsto (fun T : ℕ => (ZetaNine.CoefficientMapTelescoper.telescoper n W ((T + 1 : ℕ) : ℚ) : ℝ)) atTop (𝓝 0) := by
      have h := tendsto_finsetSum (range n) (fun j hj => tendsto_finsetSum (Icc 1 9) (fun s hs =>
        (embedded_ZetaNine__CoefficientMapSummation__shifted_reciprocal_tendsto_zero s (j + 1) (Finset.mem_Icc.mp hs).1).const_mul
          (ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient n j s W : ℝ)))
      have he : (fun T : ℕ => (ZetaNine.CoefficientMapTelescoper.telescoper n W ((T + 1 : ℕ) : ℚ) : ℝ)) =
          (fun T : ℕ => ∑ j ∈ range n, ∑ s ∈ Icc 1 9,
            (ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient n j s W : ℝ) * (1 / ((T : ℝ) + ((j + 1 : ℕ) : ℝ)) ^ s)) := by
        funext T
        unfold ZetaNine.CoefficientMapTelescoper.telescoper
        push_cast
        simp only [mul_one_div, add_left_comm, add_comm]
      rw [he]
      simpa only [mul_zero, Finset.sum_const_zero] using h
    have embedded_ZetaNine__CoefficientMapTelescoper__finite_sum_is_telescoper_boundary (n T : ℕ) (hn : Even n) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0) :
        ZetaNine.CoefficientMapFiniteSum.finiteL n T W = ZetaNine.CoefficientMapTelescoper.telescoper n W 1 - ZetaNine.CoefficientMapTelescoper.telescoper n W ((T + 1 : ℕ) : ℚ) := by
      induction T with
      | zero => simp [ZetaNine.CoefficientMapFiniteSum.finiteL]
      | succ T ih =>
        have hstep : ZetaNine.CoefficientMapFiniteSum.finiteL n (T + 1) W =
            ZetaNine.CoefficientMapFiniteSum.finiteL n T W + ZetaNine.CoefficientMap.weightedR n W ((T + 1 : ℕ) : ℚ) := by
          unfold ZetaNine.CoefficientMapFiniteSum.finiteL
          exact Finset.sum_Icc_succ_top (by omega) _
        rw [hstep, ih, embedded_ZetaNine__CoefficientMapTelescoper__actual_weightedR_is_difference n hn W hstrong hzero]
        · have he : ((T + 1 : ℕ) : ℚ) + 1 = ((T + 1 + 1 : ℕ) : ℚ) := by push_cast; ring
          rw [he]
          ring
        · intro k hk
          exact ne_of_gt (add_pos_of_pos_of_nonneg (by positivity) (Nat.cast_nonneg k))
    have embedded_ZetaNine__CoefficientMapTelescoper__telescoper_at_one_zero (n : ℕ) (hn : Even n) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0) : ZetaNine.CoefficientMapTelescoper.telescoper n W 1 = 0 := by
      have hfinite := embedded_ZetaNine__CoefficientMapSummation__actual_finiteL_tendsto_exactL n hn W hstrong
      rw [embedded_ZetaNine__CoefficientMapAggregate__aggregate_zero_exactL n W hzero] at hfinite
      have hboundary := (tendsto_const_nhds (x := (ZetaNine.CoefficientMapTelescoper.telescoper n W 1 : ℝ))).sub
        (embedded_ZetaNine__CoefficientMapTelescoper__telescoper_positive_tendsto_zero n W)
      have he : (fun T : ℕ => (ZetaNine.CoefficientMapFiniteSum.finiteL n T W : ℝ)) =
          (fun T : ℕ => (ZetaNine.CoefficientMapTelescoper.telescoper n W 1 : ℝ) - (ZetaNine.CoefficientMapTelescoper.telescoper n W ((T + 1 : ℕ) : ℚ) : ℝ)) := by
        funext T
        rw [embedded_ZetaNine__CoefficientMapTelescoper__finite_sum_is_telescoper_boundary n T hn W hstrong hzero]
        push_cast
        rfl
      rw [he] at hfinite
      have h := tendsto_nhds_unique hfinite hboundary
      simp only [sub_zero] at h
      exact_mod_cast h.symm
    have embedded_ZetaNine__CoefficientMapTelescoper__actual_weightedR_positive_zero (n k : ℕ) (W : ℚ[X]) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
        ZetaNine.CoefficientMap.weightedR n W (k : ℚ) = 0 := by
      have hprod : (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_range.mpr (show k - 1 < n by omega))
        have he : k - 1 + 1 = k := by omega
        exact sub_eq_zero.mpr (by exact_mod_cast he.symm)
      simp [ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR, ZetaNine.CoefficientMap.numerator, hprod]
    have embedded_ZetaNine__CoefficientMapTelescoper__telescoper_positive_zeros (n k : ℕ) (hn : Even n) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0)
        (hk1 : 1 ≤ k) (hkn : k ≤ n + 1) : ZetaNine.CoefficientMapTelescoper.telescoper n W (k : ℚ) = 0 := by
      have hzeros : ∀ l ≤ n, ZetaNine.CoefficientMapTelescoper.telescoper n W ((l + 1 : ℕ) : ℚ) = 0 := by
        intro l
        induction l with
        | zero => intro hl; exact embedded_ZetaNine__CoefficientMapTelescoper__telescoper_at_one_zero n hn W hstrong hzero
        | succ l ih =>
          intro hl
          have hprev := ih (by omega)
          have hdiff := embedded_ZetaNine__CoefficientMapTelescoper__actual_weightedR_is_difference n hn W hstrong hzero ((l + 1 : ℕ) : ℚ)
            (by intro k hk; exact ne_of_gt (add_pos_of_pos_of_nonneg (by positivity) (Nat.cast_nonneg k)))
          rw [embedded_ZetaNine__CoefficientMapTelescoper__actual_weightedR_positive_zero n (l + 1) W (by omega) (by omega), hprev] at hdiff
          have he : ((l + 1 : ℕ) : ℚ) + 1 = ((l + 1 + 1 : ℕ) : ℚ) := by push_cast; ring
          rw [he] at hdiff
          linarith
      have he : k - 1 + 1 = k := by omega
      simpa only [he] using hzeros (k - 1) (by omega)
    have embedded_ZetaNine__CoefficientMapTelescoper__cumulativeCoefficient_reflection (n j s : ℕ) (hn : Even n) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0)
        (hj : j < n) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
        ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient n (n - 1 - j) s W = (-1 : ℚ) ^ s * ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient n j s W := by
      induction j with
      | zero =>
        have hn1 : 1 ≤ n := by omega
        have hlast := embedded_ZetaNine__CoefficientMapTelescoper__cumulativeCoefficient_last_zero n hn W hstrong hzero s hs1 hs9
        have hstep := embedded_ZetaNine__CoefficientMapTelescoper__cumulativeCoefficient_succ n (n - 1) s W
        rw [show n - 1 + 1 = n by omega, hlast] at hstep
        have hreflection := embedded_ZetaNine__CoefficientMapReflection__local_coefficient_reflection n 0 s hn W (by omega) hs1 hs9
        simp only [Nat.sub_zero, pow_succ] at hreflection
        simp only [Nat.sub_zero]
        have hfirst : ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient n 0 s W = ZetaNine.CoefficientMapJet.weightedLocalCoefficient n 0 s W := by
          simp [ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient, ZetaNine.CoefficientMapTelescoper.prefixSum]
        rw [hfirst]
        rw [hreflection] at hstep
        nlinarith
      | succ j ih =>
        have hprev := ih (by omega)
        have hstep := embedded_ZetaNine__CoefficientMapTelescoper__cumulativeCoefficient_succ n (n - 1 - (j + 1)) s W
        rw [show n - 1 - (j + 1) + 1 = n - 1 - j by omega, hprev] at hstep
        have hreflection := embedded_ZetaNine__CoefficientMapReflection__local_coefficient_reflection n (j + 1) s hn W (by omega) hs1 hs9
        rw [show n - (j + 1) = n - 1 - j by omega] at hreflection
        rw [hreflection, pow_succ] at hstep
        rw [embedded_ZetaNine__CoefficientMapTelescoper__cumulativeCoefficient_succ]
        nlinarith
    have embedded_ZetaNine__CoefficientMapTelescoper__telescoper_reflection (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0) (t : ℚ) :
        ZetaNine.CoefficientMapTelescoper.telescoper n W (1 - (n : ℚ) - t) = ZetaNine.CoefficientMapTelescoper.telescoper n W t := by
      have hreverse := embedded_ZetaNine__CoefficientMapReflection__sum_reverse_range (n - 1)
        (fun j => ∑ s ∈ Icc 1 9,
          ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient n j s W / ((1 - (n : ℚ) - t) + (j : ℚ)) ^ s)
      rw [show n - 1 + 1 = n by omega] at hreverse
      unfold ZetaNine.CoefficientMapTelescoper.telescoper
      rw [← hreverse]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn := Finset.mem_range.mp hj
      apply Finset.sum_congr rfl
      intro s hs
      rw [embedded_ZetaNine__CoefficientMapTelescoper__cumulativeCoefficient_reflection n j s hn W hstrong hzero hjn
        (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2]
      have he : (1 - (n : ℚ) - t) + ((n - 1 - j : ℕ) : ℚ) = -(t + (j : ℚ)) := by
        have hnsub : (n - 1 - j : ℕ) + (j + 1) = n := by omega
        have hc : ((n - 1 - j : ℕ) : ℚ) + ((j : ℚ) + 1) = (n : ℚ) := by exact_mod_cast hnsub
        linarith
      rw [he, neg_pow (t + (j : ℚ))]
      exact mul_div_mul_left _ _ (pow_ne_zero s (by norm_num : (-1 : ℚ) ≠ 0))
    have embedded_ZetaNine__CoefficientMapTelescoper__telescoper_negative_zeros (n k : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0) (hk : k ≤ n) :
        ZetaNine.CoefficientMapTelescoper.telescoper n W (-(n : ℚ) - (k : ℚ)) = 0 := by
      have hreflection := embedded_ZetaNine__CoefficientMapTelescoper__telescoper_reflection n hn1 hn W hstrong hzero (-(n : ℚ) - (k : ℚ))
      have he : 1 - (n : ℚ) - (-(n : ℚ) - (k : ℚ)) = ((k + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [he, embedded_ZetaNine__CoefficientMapTelescoper__telescoper_positive_zeros n (k + 1) hn W hstrong hzero (by omega) (by omega)] at hreflection
      exact hreflection.symm
    have embedded_ZetaNine__CoefficientMapTelescoper__cleared_term_division (n j s : ℕ) (a t : ℚ) (hj : j ≤ n)
        (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
        (a * (ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial n j).eval t ^ 9 *
          (t + (j : ℚ)) ^ (9 - s)) / (ZetaNine.CoefficientMapInjectivity.polePolynomial n).eval t ^ 9 = a / (t + (j : ℚ)) ^ s := by
      apply (div_eq_div_iff
        (pow_ne_zero _ (embedded_ZetaNine__CoefficientMapPartialFractions__polePolynomial_eval_ne_zero n t hregular))
        (pow_ne_zero _ (hregular j hj))).mpr
      rw [embedded_ZetaNine__CoefficientMapPartialFractions__polePolynomial_eval_factor n j t hj, mul_pow]
      have he : (t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s = (t + (j : ℚ)) ^ 9 := by
        rw [← pow_add]
        congr 1
        omega
      calc
        _ = a * (ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial n j).eval t ^ 9 *
          ((t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s) := by ring
        _ = _ := by rw [he]; ring
    have embedded_ZetaNine__CoefficientMapTelescoper__telescoper_actual_rational_representation (n : ℕ) (hn1 : 1 ≤ n) (W : ℚ[X]) (t : ℚ)
        (hregular : ∀ k < n, t + (k : ℚ) ≠ 0) :
        ZetaNine.CoefficientMapTelescoper.telescoper n W t = (ZetaNine.CoefficientMapTelescoper.telescoperNumerator n W).eval t / (ZetaNine.CoefficientMapInjectivity.polePolynomial (n - 1)).eval t ^ 9 := by
      symm
      simp only [ZetaNine.CoefficientMapTelescoper.telescoperNumerator, ZetaNine.CoefficientMapReflection.partialBasis, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro s hs
      simpa only [mul_assoc] using embedded_ZetaNine__CoefficientMapTelescoper__cleared_term_division (n - 1) j s (ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient n j s W) t
        (by have := Finset.mem_range.mp hj; omega) (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
        (by intro k hk; exact hregular k (by omega))
    have embedded_ZetaNine__CoefficientMapTelescoper__telescoperNumerator_natDegree_le (n : ℕ) (hn1 : 1 ≤ n) (W : ℚ[X]) :
        (ZetaNine.CoefficientMapTelescoper.telescoperNumerator n W).natDegree ≤ 9 * n - 1 := by
      unfold ZetaNine.CoefficientMapTelescoper.telescoperNumerator
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j hj
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro s hs
      have h : (C (ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient n j s W) * ZetaNine.CoefficientMapReflection.partialBasis (n - 1) j s).natDegree ≤
          (C (ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient n j s W)).natDegree + (ZetaNine.CoefficientMapReflection.partialBasis (n - 1) j s).natDegree :=
        Polynomial.natDegree_mul_le
      rw [Polynomial.natDegree_C, zero_add,
        embedded_ZetaNine__CoefficientMapReflection__partialBasis_natDegree (n - 1) j s (by have := Finset.mem_range.mp hj; omega)] at h
      have horder := Finset.mem_Icc.mp hs
      omega
    have embedded_ZetaNine__CoefficientMapTelescoper__rootNode_injective (n : ℕ) : Function.Injective (ZetaNine.CoefficientMapTelescoper.rootNode n) := by
      intro a b h
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          congr 1
          apply Fin.ext
          have he : (a.val : ℚ) = (b.val : ℚ) := by simpa [ZetaNine.CoefficientMapTelescoper.rootNode] using h
          exact_mod_cast he
        | inr b =>
          have ha : (0 : ℚ) ≤ (a.val : ℚ) := Nat.cast_nonneg _
          have hb : (0 : ℚ) ≤ (b.val : ℚ) := Nat.cast_nonneg _
          have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg _
          simp only [ZetaNine.CoefficientMapTelescoper.rootNode] at h
          linarith
      | inr a =>
        cases b with
        | inl b =>
          have ha : (0 : ℚ) ≤ (a.val : ℚ) := Nat.cast_nonneg _
          have hb : (0 : ℚ) ≤ (b.val : ℚ) := Nat.cast_nonneg _
          have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg _
          simp only [ZetaNine.CoefficientMapTelescoper.rootNode] at h
          linarith
        | inr b =>
          congr 1
          apply Fin.ext
          have he : (a.val : ℚ) = (b.val : ℚ) := by simp only [ZetaNine.CoefficientMapTelescoper.rootNode] at h; linarith
          exact_mod_cast he
    have embedded_ZetaNine__CoefficientMapTelescoper__rootPolynomial_monic (n : ℕ) : (ZetaNine.CoefficientMapTelescoper.rootPolynomial n).Monic := by
      unfold ZetaNine.CoefficientMapTelescoper.rootPolynomial
      apply Polynomial.monic_prod_of_monic
      intro i hi
      exact Polynomial.monic_X_sub_C _
    have embedded_ZetaNine__CoefficientMapTelescoper__rootPolynomial_eq_explicit_products (n : ℕ) :
        ZetaNine.CoefficientMapTelescoper.rootPolynomial n =
          (∏ k ∈ range (n + 1), (X - C ((k : ℚ) + 1))) *
          (∏ k ∈ range (n + 1), (X + C (n : ℚ) + C (k : ℚ))) := by
      unfold ZetaNine.CoefficientMapTelescoper.rootPolynomial
      rw [Fintype.prod_sum_type]
      simp only [ZetaNine.CoefficientMapTelescoper.rootNode]
      rw [Fin.prod_univ_eq_prod_range (fun k : ℕ => (X - C ((k : ℚ) + 1) : ℚ[X])) (n + 1),
        Fin.prod_univ_eq_prod_range (fun k : ℕ => (X - C (-(n : ℚ) - (k : ℚ)) : ℚ[X])) (n + 1)]
      congr 1
      apply Finset.prod_congr rfl
      intro k hk
      simp only [map_sub, map_neg]
      ring
    have embedded_ZetaNine__CoefficientMapTelescoper__rootPolynomial_natDegree (n : ℕ) : (ZetaNine.CoefficientMapTelescoper.rootPolynomial n).natDegree = 2 * n + 2 := by
      unfold ZetaNine.CoefficientMapTelescoper.rootPolynomial
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun i hi => Polynomial.monic_X_sub_C _)]
      simp only [Polynomial.natDegree_X_sub_C]
      simp
      omega
    have embedded_ZetaNine__CoefficientMapTelescoper__telescoperNumerator_zero_at_nodes (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0)
        (i : Fin (n + 1) ⊕ Fin (n + 1)) : (ZetaNine.CoefficientMapTelescoper.telescoperNumerator n W).eval (ZetaNine.CoefficientMapTelescoper.rootNode n i) = 0 := by
      have hregular : ∀ k < n, ZetaNine.CoefficientMapTelescoper.rootNode n i + (k : ℚ) ≠ 0 := by
        intro k hk
        cases i with
        | inl l =>
          simp only [ZetaNine.CoefficientMapTelescoper.rootNode]
          exact ne_of_gt (by positivity)
        | inr l =>
          simp only [ZetaNine.CoefficientMapTelescoper.rootNode]
          have hkn : (k : ℚ) < (n : ℚ) := by exact_mod_cast hk
          have hl : (0 : ℚ) ≤ (l.val : ℚ) := Nat.cast_nonneg _
          exact ne_of_lt (by linarith)
      have hvalue : ZetaNine.CoefficientMapTelescoper.telescoper n W (ZetaNine.CoefficientMapTelescoper.rootNode n i) = 0 := by
        cases i with
        | inl k =>
          simpa only [ZetaNine.CoefficientMapTelescoper.rootNode, Nat.cast_add, Nat.cast_one] using
            embedded_ZetaNine__CoefficientMapTelescoper__telescoper_positive_zeros n (k.val + 1) hn W hstrong hzero (by omega) (by have := k.isLt; omega)
        | inr k =>
          exact embedded_ZetaNine__CoefficientMapTelescoper__telescoper_negative_zeros n k.val hn1 hn W hstrong hzero (by have := k.isLt; omega)
      have hrep := embedded_ZetaNine__CoefficientMapTelescoper__telescoper_actual_rational_representation n hn1 W (ZetaNine.CoefficientMapTelescoper.rootNode n i) hregular
      have hden : (ZetaNine.CoefficientMapInjectivity.polePolynomial (n - 1)).eval (ZetaNine.CoefficientMapTelescoper.rootNode n i) ^ 9 ≠ 0 :=
        pow_ne_zero _ (embedded_ZetaNine__CoefficientMapPartialFractions__polePolynomial_eval_ne_zero (n - 1) _
          (by intro k hk; exact hregular k (by omega)))
      rw [hvalue] at hrep
      have hmult := congrArg (fun x : ℚ => x * (ZetaNine.CoefficientMapInjectivity.polePolynomial (n - 1)).eval (ZetaNine.CoefficientMapTelescoper.rootNode n i) ^ 9) hrep
      rw [div_mul_cancel₀ _ hden] at hmult
      simpa only [zero_mul] using hmult.symm
    have embedded_ZetaNine__CoefficientMapTelescoper__all_kernel_nodes_divide_telescoperNumerator (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0) :
        ZetaNine.CoefficientMapTelescoper.rootPolynomial n ∣ ZetaNine.CoefficientMapTelescoper.telescoperNumerator n W := by
      unfold ZetaNine.CoefficientMapTelescoper.rootPolynomial
      apply Finset.prod_dvd_of_coprime
      · intro a ha b hb hab
        exact Polynomial.pairwise_coprime_X_sub_C (embedded_ZetaNine__CoefficientMapTelescoper__rootNode_injective n) hab
      · intro i hi
        rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
        exact embedded_ZetaNine__CoefficientMapTelescoper__telescoperNumerator_zero_at_nodes n hn1 hn W hstrong hzero i
    have embedded_ZetaNine__CoefficientMapTelescoper__actual_polynomial_quotient_degree_bound (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0) :
        ∃ H : ℚ[X], ZetaNine.CoefficientMapTelescoper.telescoperNumerator n W = ZetaNine.CoefficientMapTelescoper.rootPolynomial n * H ∧ H.natDegree ≤ 7 * n - 3 := by
      obtain ⟨H, hH⟩ := embedded_ZetaNine__CoefficientMapTelescoper__all_kernel_nodes_divide_telescoperNumerator n hn1 hn W hstrong hzero
      refine ⟨H, hH, ?_⟩
      by_cases hH0 : H = 0
      · simp [hH0]
      · have hdegree := congrArg Polynomial.natDegree hH
        rw [Polynomial.natDegree_mul (embedded_ZetaNine__CoefficientMapTelescoper__rootPolynomial_monic n).ne_zero hH0, embedded_ZetaNine__CoefficientMapTelescoper__rootPolynomial_natDegree] at hdegree
        have hbound := embedded_ZetaNine__CoefficientMapTelescoper__telescoperNumerator_natDegree_le n hn1 W
        omega
    have embedded_ZetaNine__CoefficientMapShiftDegree__actual_nextCoeff_mul (P H : ℚ[X]) :
        (P * H).nextCoeff = P.nextCoeff * H.leadingCoeff + P.leadingCoeff * H.nextCoeff := by
      rw [← coeff_one_reverse, reverse_mul_of_domain, mul_coeff_one]
      simp only [coeff_zero_reverse, coeff_one_reverse]
      ring
    have embedded_ZetaNine__CoefficientMapShiftDegree__actual_shift_nextCoeff (H : ℚ[X]) :
        (H.comp (X + C 1)).nextCoeff = H.nextCoeff + (H.natDegree : ℚ) * H.leadingCoeff := by
      change (taylor 1 H).nextCoeff = _
      by_cases hd : H.natDegree = 0
      · rw [eq_C_of_natDegree_eq_zero hd]
        simp
      have hdpos : 0 < H.natDegree := Nat.pos_of_ne_zero hd
      rw [nextCoeff_of_natDegree_pos (by simpa using hdpos), natDegree_taylor, taylor_coeff]
      have hdeg : (hasseDeriv (H.natDegree - 1) H).natDegree < 2 := by
        have h := natDegree_hasseDeriv_le H (H.natDegree - 1)
        omega
      rw [eval_eq_sum_range' hdeg 1]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, one_pow, mul_one,
        hasseDeriv_coeff]
      have hadd : 1 + (H.natDegree - 1) = H.natDegree := by omega
      have hchoose : H.natDegree.choose (H.natDegree - 1) = H.natDegree := by
        have h := Nat.choose_succ_self_right (H.natDegree - 1)
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ H.natDegree)] using h
      rw [hadd, Nat.choose_self, hchoose, Nat.cast_one, one_mul,
        ← nextCoeff_of_natDegree_pos hdpos, coeff_natDegree]
    have embedded_ZetaNine__CoefficientMapShiftDegree__shiftA_monic (n : ℕ) : (ZetaNine.CoefficientMapShiftDegree.shiftA n).Monic :=
      (monic_X_sub_C _).mul ((monic_X_add_C _).pow 10)
    have embedded_ZetaNine__CoefficientMapShiftDegree__shiftB_monic (n : ℕ) : (ZetaNine.CoefficientMapShiftDegree.shiftB n).Monic :=
      (monic_X.pow 10).mul (monic_X_add_C _)
    have embedded_ZetaNine__CoefficientMapShiftDegree__shiftA_natDegree (n : ℕ) : (ZetaNine.CoefficientMapShiftDegree.shiftA n).natDegree = 11 := by
      rw [ZetaNine.CoefficientMapShiftDegree.shiftA, natDegree_mul (monic_X_sub_C _).ne_zero ((monic_X_add_C _).pow 10).ne_zero]
      simp only [natDegree_X_sub_C, natDegree_pow, natDegree_X_add_C]
    have embedded_ZetaNine__CoefficientMapShiftDegree__shiftB_natDegree (n : ℕ) : (ZetaNine.CoefficientMapShiftDegree.shiftB n).natDegree = 11 := by
      rw [ZetaNine.CoefficientMapShiftDegree.shiftB, natDegree_mul (monic_X.pow 10).ne_zero (monic_X_add_C _).ne_zero]
      simp only [natDegree_pow, natDegree_X, natDegree_X_add_C]
    have embedded_ZetaNine__CoefficientMapShiftDegree__shiftA_nextCoeff (n : ℕ) : (ZetaNine.CoefficientMapShiftDegree.shiftA n).nextCoeff = 9 * (n : ℚ) - 1 := by
      unfold ZetaNine.CoefficientMapShiftDegree.shiftA
      rw [Monic.nextCoeff_mul (monic_X_sub_C _) ((monic_X_add_C _).pow 10),
        Monic.nextCoeff_pow (monic_X_add_C _) 10, nextCoeff_X_sub_C, nextCoeff_X_add_C]
      simp only [nsmul_eq_mul]
      ring
    have embedded_ZetaNine__CoefficientMapShiftDegree__shiftB_nextCoeff (n : ℕ) : (ZetaNine.CoefficientMapShiftDegree.shiftB n).nextCoeff = 2 * (n : ℚ) + 1 := by
      have hX : (X : ℚ[X]).nextCoeff = 0 := by norm_num [nextCoeff]
      unfold ZetaNine.CoefficientMapShiftDegree.shiftB
      rw [Monic.nextCoeff_mul (monic_X.pow 10) (monic_X_add_C _),
        Monic.nextCoeff_pow monic_X 10, hX, nextCoeff_X_add_C]
      simp
    have embedded_ZetaNine__CoefficientMapShiftDegree__actual_shift_difference_coefficient (n : ℕ) (H : ℚ[X]) (hH : H ≠ 0) :
        (ZetaNine.CoefficientMapShiftDegree.shiftDifference n H).coeff (H.natDegree + 10) =
          (7 * (n : ℚ) - 2 - (H.natDegree : ℚ)) * H.leadingCoeff := by
      have hAH : (ZetaNine.CoefficientMapShiftDegree.shiftA n * H).natDegree = 11 + H.natDegree := by
        rw [(embedded_ZetaNine__CoefficientMapShiftDegree__shiftA_monic n).natDegree_mul' hH, embedded_ZetaNine__CoefficientMapShiftDegree__shiftA_natDegree]
      have hHs : H.comp (X + C 1) ≠ 0 := by
        intro h
        exact hH ((taylor_eq_zero (r := (1 : ℚ)) (f := H)).mp h)
      have hHsdeg : (H.comp (X + C 1)).natDegree = H.natDegree := natDegree_taylor H 1
      have hHslead : (H.comp (X + C 1)).leadingCoeff = H.leadingCoeff := leadingCoeff_taylor 1 H
      have hBH : (ZetaNine.CoefficientMapShiftDegree.shiftB n * H.comp (X + C 1)).natDegree = 11 + H.natDegree := by
        rw [(embedded_ZetaNine__CoefficientMapShiftDegree__shiftB_monic n).natDegree_mul' hHs, embedded_ZetaNine__CoefficientMapShiftDegree__shiftB_natDegree, hHsdeg]
      have hfirst : (ZetaNine.CoefficientMapShiftDegree.shiftA n * H).coeff (H.natDegree + 10) =
          (9 * (n : ℚ) - 1) * H.leadingCoeff + H.nextCoeff := by
        have hnext := nextCoeff_of_natDegree_pos (p := ZetaNine.CoefficientMapShiftDegree.shiftA n * H) (by omega)
        rw [hAH] at hnext
        rw [show 11 + H.natDegree - 1 = H.natDegree + 10 by omega] at hnext
        rw [← hnext, embedded_ZetaNine__CoefficientMapShiftDegree__actual_nextCoeff_mul, embedded_ZetaNine__CoefficientMapShiftDegree__shiftA_nextCoeff, (embedded_ZetaNine__CoefficientMapShiftDegree__shiftA_monic n).leadingCoeff,
          one_mul]
      have hsecond : (ZetaNine.CoefficientMapShiftDegree.shiftB n * H.comp (X + C 1)).coeff (H.natDegree + 10) =
          (2 * (n : ℚ) + 1) * H.leadingCoeff +
            (H.nextCoeff + (H.natDegree : ℚ) * H.leadingCoeff) := by
        have hnext := nextCoeff_of_natDegree_pos (p := ZetaNine.CoefficientMapShiftDegree.shiftB n * H.comp (X + C 1)) (by omega)
        rw [hBH] at hnext
        rw [show 11 + H.natDegree - 1 = H.natDegree + 10 by omega] at hnext
        rw [← hnext, embedded_ZetaNine__CoefficientMapShiftDegree__actual_nextCoeff_mul, embedded_ZetaNine__CoefficientMapShiftDegree__shiftB_nextCoeff, (embedded_ZetaNine__CoefficientMapShiftDegree__shiftB_monic n).leadingCoeff,
          one_mul, hHslead, embedded_ZetaNine__CoefficientMapShiftDegree__actual_shift_nextCoeff]
      rw [ZetaNine.CoefficientMapShiftDegree.shiftDifference, coeff_sub, hfirst, hsecond]
      ring
    have embedded_ZetaNine__CoefficientMapShiftDegree__actual_shift_difference_coefficient_ne_zero (n : ℕ) (hn : 1 ≤ n)
        (H : ℚ[X]) (hH : H ≠ 0) (hdeg : H.natDegree ≤ 7 * n - 3) :
        (ZetaNine.CoefficientMapShiftDegree.shiftDifference n H).coeff (H.natDegree + 10) ≠ 0 := by
      rw [embedded_ZetaNine__CoefficientMapShiftDegree__actual_shift_difference_coefficient n H hH]
      have hb : H.natDegree + 3 ≤ 7 * n := by omega
      have hbq : (H.natDegree : ℚ) + 3 ≤ 7 * (n : ℚ) := by exact_mod_cast hb
      apply mul_ne_zero
      · have hpos : 0 < 7 * (n : ℚ) - 2 - (H.natDegree : ℚ) := by linarith
        exact ne_of_gt hpos
      · exact leadingCoeff_ne_zero.mpr hH
    have embedded_ZetaNine__CoefficientMapShiftDegree__actual_shift_difference_degree_lower_bound (n : ℕ) (hn : 1 ≤ n)
        (H : ℚ[X]) (hH : H ≠ 0) (hdeg : H.natDegree ≤ 7 * n - 3) :
        H.natDegree + 10 ≤ (ZetaNine.CoefficientMapShiftDegree.shiftDifference n H).natDegree :=
      le_natDegree_of_ne_zero (embedded_ZetaNine__CoefficientMapShiftDegree__actual_shift_difference_coefficient_ne_zero n hn H hH hdeg)
    have embedded_ZetaNine__CoefficientMapShiftDegree__actual_shift_difference_small_degree_implies_zero (n : ℕ) (hn : 1 ≤ n)
        (H : ℚ[X]) (hdeg : H.natDegree ≤ 7 * n - 3)
        (hsmall : (ZetaNine.CoefficientMapShiftDegree.shiftDifference n H).natDegree ≤ 8) : H = 0 := by
      by_contra hH
      have h := embedded_ZetaNine__CoefficientMapShiftDegree__actual_shift_difference_degree_lower_bound n hn H hH hdeg
      omega
    have embedded_ZetaNine__CoefficientMapKernelBridge__finite_product_shift_identity (n : ℕ) (f : ℕ → ℚ) :
        (∏ k ∈ range n, f (k + 1)) * f 0 = (∏ k ∈ range n, f k) * f n := by
      have h := Finset.prod_range_succ' f n
      rw [Finset.prod_range_succ] at h
      simpa only [mul_comm] using h.symm
    have embedded_ZetaNine__CoefficientMapKernelBridge__positiveProduct_shift (n : ℕ) (t : ℚ) :
        ZetaNine.CoefficientMapKernelBridge.positiveProduct n (t + 1) * (t - (n : ℚ)) = t * ZetaNine.CoefficientMapKernelBridge.positiveProduct n t := by
      have h := embedded_ZetaNine__CoefficientMapKernelBridge__finite_product_shift_identity n (fun k => t - (k : ℚ))
      have he : ZetaNine.CoefficientMapKernelBridge.positiveProduct n (t + 1) = ∏ k ∈ range n, (t - (k : ℚ)) := by
        unfold ZetaNine.CoefficientMapKernelBridge.positiveProduct
        apply Finset.prod_congr rfl
        intro k hk
        ring
      rw [he]
      simpa only [ZetaNine.CoefficientMapKernelBridge.positiveProduct, Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero, mul_comm] using h.symm
    have embedded_ZetaNine__CoefficientMapKernelBridge__negativeProduct_shift (n : ℕ) (t : ℚ) :
        ZetaNine.CoefficientMapKernelBridge.negativeProduct n (t + 1) * (t + (n : ℚ) + 1) =
          ZetaNine.CoefficientMapKernelBridge.negativeProduct n t * (t + 2 * (n : ℚ) + 1) := by
      have h := embedded_ZetaNine__CoefficientMapKernelBridge__finite_product_shift_identity n (fun k => t + (n : ℚ) + ((k : ℚ) + 1))
      have he : (∏ k ∈ range n, (t + (n : ℚ) + (((k + 1 : ℕ) : ℚ) + 1))) =
          ZetaNine.CoefficientMapKernelBridge.negativeProduct n (t + 1) := by
        unfold ZetaNine.CoefficientMapKernelBridge.negativeProduct
        apply Finset.prod_congr rfl
        intro k hk
        push_cast
        ring
      rw [he] at h
      have hend : t + (n : ℚ) + ((n : ℚ) + 1) = t + 2 * (n : ℚ) + 1 := by ring
      simpa only [ZetaNine.CoefficientMapKernelBridge.negativeProduct, Nat.cast_zero, zero_add, hend] using h
    have embedded_ZetaNine__CoefficientMapKernelBridge__numerator_shift_identity (n : ℕ) (t : ℚ) :
        ZetaNine.CoefficientMap.numerator n (t + 1) * (t - (n : ℚ)) * (t + (n : ℚ) + 1) =
          ZetaNine.CoefficientMap.numerator n t * t * (t + 2 * (n : ℚ) + 1) := by
      change (n.factorial : ℚ) ^ 7 * ZetaNine.CoefficientMapKernelBridge.positiveProduct n (t + 1) * ZetaNine.CoefficientMapKernelBridge.negativeProduct n (t + 1) *
          (t - (n : ℚ)) * (t + (n : ℚ) + 1) =
        (n.factorial : ℚ) ^ 7 * ZetaNine.CoefficientMapKernelBridge.positiveProduct n t * ZetaNine.CoefficientMapKernelBridge.negativeProduct n t * t * (t + 2 * (n : ℚ) + 1)
      calc
        _ = (n.factorial : ℚ) ^ 7 * (ZetaNine.CoefficientMapKernelBridge.positiveProduct n (t + 1) * (t - (n : ℚ))) *
            (ZetaNine.CoefficientMapKernelBridge.negativeProduct n (t + 1) * (t + (n : ℚ) + 1)) := by ring
        _ = _ := by rw [embedded_ZetaNine__CoefficientMapKernelBridge__positiveProduct_shift, embedded_ZetaNine__CoefficientMapKernelBridge__negativeProduct_shift]; ring
    have embedded_ZetaNine__CoefficientMapKernelBridge__poleProduct_shift_identity (n : ℕ) (t : ℚ) :
        ZetaNine.CoefficientMap.poleProduct n (t + 1) * t = ZetaNine.CoefficientMap.poleProduct n t * (t + (n : ℚ) + 1) := by
      have h := embedded_ZetaNine__CoefficientMapKernelBridge__finite_product_shift_identity (n + 1) (fun k => t + (k : ℚ))
      simpa only [ZetaNine.CoefficientMap.poleProduct, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero,
        add_assoc, add_comm, add_left_comm] using h
    have embedded_ZetaNine__CoefficientMapKernelBridge__actual_R_shift_A_equals_R_B (n : ℕ) (t : ℚ)
        (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0)
        (hregular1 : ∀ k ≤ n, (t + 1) + (k : ℚ) ≠ 0) :
        ZetaNine.CoefficientMap.actualR n (t + 1) * ZetaNine.CoefficientMapKernelBridge.aValue n (t + 1) = ZetaNine.CoefficientMap.actualR n t * ZetaNine.CoefficientMapKernelBridge.bValue n t := by
      have hden := embedded_ZetaNine__CoefficientMap__poleProduct_ne_zero n t hregular
      have hden1 := embedded_ZetaNine__CoefficientMap__poleProduct_ne_zero n (t + 1) hregular1
      have hnum := embedded_ZetaNine__CoefficientMapKernelBridge__numerator_shift_identity n t
      have hpole := congrArg (fun x : ℚ => x ^ 9) (embedded_ZetaNine__CoefficientMapKernelBridge__poleProduct_shift_identity n t)
      simp only [mul_pow] at hpole
      unfold ZetaNine.CoefficientMap.actualR ZetaNine.CoefficientMapKernelBridge.aValue ZetaNine.CoefficientMapKernelBridge.bValue
      field_simp [hden, hden1]
      calc
        _ = (ZetaNine.CoefficientMap.numerator n (t + 1) * (t - (n : ℚ)) * (t + (n : ℚ) + 1)) *
            ((t + (n : ℚ) + 1) ^ 9 * ZetaNine.CoefficientMap.poleProduct n t ^ 9) := by ring
        _ = (ZetaNine.CoefficientMap.numerator n t * t * (t + 2 * (n : ℚ) + 1)) *
            (ZetaNine.CoefficientMap.poleProduct n (t + 1) ^ 9 * t ^ 9) := by rw [hnum, hpole]; ring
        _ = _ := by ring
    have embedded_ZetaNine__CoefficientMapKernelBridge__rootPolynomial_numerator_factor (n : ℕ) (t : ℚ) :
        (n.factorial : ℚ) ^ 7 * (ZetaNine.CoefficientMapTelescoper.rootPolynomial n).eval t =
          ZetaNine.CoefficientMap.numerator n t * (t - (n : ℚ) - 1) * (t + (n : ℚ)) := by
      rw [embedded_ZetaNine__CoefficientMapTelescoper__rootPolynomial_eq_explicit_products]
      simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
        Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      rw [Finset.prod_range_succ (fun k : ℕ => t - ((k : ℚ) + 1)) n,
        Finset.prod_range_succ' (fun k : ℕ => t + (n : ℚ) + (k : ℚ)) n]
      simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
      change (n.factorial : ℚ) ^ 7 * ((ZetaNine.CoefficientMapKernelBridge.positiveProduct n t * (t - ((n : ℚ) + 1))) *
          (ZetaNine.CoefficientMapKernelBridge.negativeProduct n t * (t + (n : ℚ)))) = _
      change _ = (n.factorial : ℚ) ^ 7 * ZetaNine.CoefficientMapKernelBridge.positiveProduct n t * ZetaNine.CoefficientMapKernelBridge.negativeProduct n t *
        (t - (n : ℚ) - 1) * (t + (n : ℚ))
      ring
    have embedded_ZetaNine__CoefficientMapKernelBridge__poleProduct_last_factor (n : ℕ) (hn1 : 1 ≤ n) (t : ℚ) :
        ZetaNine.CoefficientMap.poleProduct n t = (ZetaNine.CoefficientMapInjectivity.polePolynomial (n - 1)).eval t * (t + (n : ℚ)) := by
      rw [embedded_ZetaNine__CoefficientMapPartialFractions__polePolynomial_eval]
      unfold ZetaNine.CoefficientMap.poleProduct
      rw [show n - 1 + 1 = n by omega]
      exact Finset.prod_range_succ _ _
    have embedded_ZetaNine__CoefficientMapKernelBridge__actual_R_A_equals_Pzero (n : ℕ) (hn1 : 1 ≤ n) (t : ℚ)
        (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
        ZetaNine.CoefficientMap.actualR n t * ZetaNine.CoefficientMapKernelBridge.aValue n t =
          (n.factorial : ℚ) ^ 7 * (ZetaNine.CoefficientMapTelescoper.rootPolynomial n).eval t / (ZetaNine.CoefficientMapInjectivity.polePolynomial (n - 1)).eval t ^ 9 := by
      have hden := embedded_ZetaNine__CoefficientMapPartialFractions__polePolynomial_eval_ne_zero (n - 1) t
        (by intro k hk; exact hregular k (by omega))
      have hlast := hregular n (by omega)
      rw [embedded_ZetaNine__CoefficientMapKernelBridge__rootPolynomial_numerator_factor]
      unfold ZetaNine.CoefficientMap.actualR ZetaNine.CoefficientMapKernelBridge.aValue
      rw [embedded_ZetaNine__CoefficientMapKernelBridge__poleProduct_last_factor n hn1, mul_pow]
      field_simp [hden, hlast]
    have embedded_ZetaNine__CoefficientMapKernelBridge__telescoper_quotient_as_R_A (n : ℕ) (hn1 : 1 ≤ n) (W H : ℚ[X])
        (hH : ZetaNine.CoefficientMapTelescoper.telescoperNumerator n W = ZetaNine.CoefficientMapTelescoper.rootPolynomial n * H) (t : ℚ)
        (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
        ZetaNine.CoefficientMapTelescoper.telescoper n W t = ZetaNine.CoefficientMap.actualR n t * ZetaNine.CoefficientMapKernelBridge.aValue n t * H.eval t / (n.factorial : ℚ) ^ 7 := by
      have hfactor : (n.factorial : ℚ) ^ 7 ≠ 0 := pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero)
      rw [embedded_ZetaNine__CoefficientMapTelescoper__telescoper_actual_rational_representation n hn1 W t
        (by intro k hk; exact hregular k (by omega)), hH, Polynomial.eval_mul,
        embedded_ZetaNine__CoefficientMapKernelBridge__actual_R_A_equals_Pzero n hn1 t hregular]
      field_simp [hfactor]
    have embedded_ZetaNine__CoefficientMapKernelBridge__actual_R_ne_zero_above_n (n : ℕ) (t : ℚ) (ht : (n : ℚ) < t) : ZetaNine.CoefficientMap.actualR n t ≠ 0 := by
      have ht0 : (0 : ℚ) < t := lt_of_le_of_lt (Nat.cast_nonneg n) ht
      apply div_ne_zero
      · unfold ZetaNine.CoefficientMap.numerator
        apply mul_ne_zero
        · apply mul_ne_zero
          · exact pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero)
          · apply Finset.prod_ne_zero_iff.mpr
            intro k hk
            have hk1 : (k : ℚ) + 1 ≤ (n : ℚ) := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
            exact ne_of_gt (by linarith)
        · apply Finset.prod_ne_zero_iff.mpr
          intro k hk
          exact ne_of_gt (by positivity)
      · exact pow_ne_zero _ (embedded_ZetaNine__CoefficientMap__poleProduct_ne_zero n t
          (by intro k hk; exact ne_of_gt (add_pos_of_pos_of_nonneg ht0 (Nat.cast_nonneg k))))
    have embedded_ZetaNine__CoefficientMapKernelBridge__kernel_actual_polynomial_relation (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W H : ℚ[X])
        (hstrong : ZetaNine.CoefficientMapReflection.StrongProperMultiplier n W) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0)
        (hH : ZetaNine.CoefficientMapTelescoper.telescoperNumerator n W = ZetaNine.CoefficientMapTelescoper.rootPolynomial n * H) :
        C ((n.factorial : ℚ) ^ 7) * W.comp (ZetaNine.CoefficientMapInjectivity.baseU n) =
          ((X - C ((n : ℚ) + 1)) * (X + C (n : ℚ)) ^ 10) * H -
            (X ^ 10 * (X + C (2 * (n : ℚ) + 1))) * H.comp (X + C 1) := by
      apply Polynomial.eq_of_infinite_eval_eq
      apply (Set.Ioi_infinite ((n : ℚ) + 1)).mono
      intro t ht
      have ht1 : (n : ℚ) + 1 < t := ht
      have ht0 : (0 : ℚ) < t := by have hnonneg : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n; linarith
      have hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0 := by
        intro k hk
        exact ne_of_gt (add_pos_of_pos_of_nonneg ht0 (Nat.cast_nonneg k))
      have hregular1 : ∀ k ≤ n, (t + 1) + (k : ℚ) ≠ 0 := by
        intro k hk
        exact ne_of_gt (by positivity)
      have hR : ZetaNine.CoefficientMap.actualR n t ≠ 0 := embedded_ZetaNine__CoefficientMapKernelBridge__actual_R_ne_zero_above_n n t (by linarith)
      have hfac : (n.factorial : ℚ) ^ 7 ≠ 0 := pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero)
      have hdiff := embedded_ZetaNine__CoefficientMapTelescoper__actual_weightedR_is_difference n hn W hstrong hzero t hregular
      rw [embedded_ZetaNine__CoefficientMapKernelBridge__telescoper_quotient_as_R_A n hn1 W H hH t hregular,
        embedded_ZetaNine__CoefficientMapKernelBridge__telescoper_quotient_as_R_A n hn1 W H hH (t + 1) hregular1] at hdiff
      rw [embedded_ZetaNine__CoefficientMapKernelBridge__actual_R_shift_A_equals_R_B n t hregular hregular1] at hdiff
      unfold ZetaNine.CoefficientMap.weightedR at hdiff
      have he : (n.factorial : ℚ) ^ 7 * W.eval (t * (t + (n : ℚ))) =
          ZetaNine.CoefficientMapKernelBridge.aValue n t * H.eval t - ZetaNine.CoefficientMapKernelBridge.bValue n t * H.eval (t + 1) := by
        field_simp [hfac] at hdiff
        nlinarith [hdiff]
      simpa only [Set.mem_ofPred_eq, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
        ZetaNine.CoefficientMapInjectivity.baseU, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
        ZetaNine.CoefficientMapKernelBridge.aValue, ZetaNine.CoefficientMapKernelBridge.bValue, sub_sub, add_assoc] using he
    have embedded_ZetaNine__CoefficientMapKernelBridge__original_quartic_aggregate_kernel_zero (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
        (W : ℚ[X]) (hW : W.natDegree ≤ 4) (hzero : ZetaNine.CoefficientMapAggregate.aggregate n W = 0) : W = 0 := by
      have hstrong := embedded_ZetaNine__CoefficientMapReflection__quartic_is_strong_proper n (by omega) W hW
      obtain ⟨H, hH, hdegree⟩ := embedded_ZetaNine__CoefficientMapTelescoper__actual_polynomial_quotient_degree_bound n (by omega) hn W hstrong hzero
      have hrelation := embedded_ZetaNine__CoefficientMapKernelBridge__kernel_actual_polynomial_relation n (by omega) hn W H hstrong hzero hH
      have hdiff : ZetaNine.CoefficientMapShiftDegree.shiftDifference n H =
          C ((n.factorial : ℚ) ^ 7) * W.comp (ZetaNine.CoefficientMapInjectivity.baseU n) := hrelation.symm
      have hsmall : (ZetaNine.CoefficientMapShiftDegree.shiftDifference n H).natDegree ≤ 8 := by
        rw [hdiff]
        have hmul : (C ((n.factorial : ℚ) ^ 7) * W.comp (ZetaNine.CoefficientMapInjectivity.baseU n)).natDegree ≤
            (C ((n.factorial : ℚ) ^ 7)).natDegree + (W.comp (ZetaNine.CoefficientMapInjectivity.baseU n)).natDegree := Polynomial.natDegree_mul_le
        have hcomp := Polynomial.natDegree_comp_le (p := W) (q := ZetaNine.CoefficientMapInjectivity.baseU n)
        rw [Polynomial.natDegree_C, zero_add] at hmul
        rw [embedded_ZetaNine__CoefficientMapInjectivity__baseU_natDegree] at hcomp
        omega
      have hH0 := embedded_ZetaNine__CoefficientMapShiftDegree__actual_shift_difference_small_degree_implies_zero n (by omega) H hdegree hsmall
      rw [hH0] at hdiff
      simp only [ZetaNine.CoefficientMapShiftDegree.shiftDifference, Polynomial.zero_comp, mul_zero, sub_zero] at hdiff
      have hcomp : W.comp (ZetaNine.CoefficientMapInjectivity.baseU n) = 0 := by
        have hfac : C ((n.factorial : ℚ) ^ 7) ≠ (0 : ℚ[X]) :=
          Polynomial.C_ne_zero.mpr (pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero))
        exact (mul_eq_zero.mp hdiff.symm).resolve_left hfac
      apply embedded_ZetaNine__CoefficientMapInjectivity__weightedNumerator_zero_implies_multiplier_zero n W
      simp only [ZetaNine.CoefficientMapInjectivity.weightedNumerator, hcomp, mul_zero]
    have embedded_ZetaNine__CoefficientMapKernelBridge__original_quartic_aggregate_injective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
        (W V : ℚ[X]) (hW : W.natDegree ≤ 4) (hV : V.natDegree ≤ 4)
        (heq : ZetaNine.CoefficientMapAggregate.aggregate n W = ZetaNine.CoefficientMapAggregate.aggregate n V) : W = V := by
      have hdegree : (W - V).natDegree ≤ 4 :=
        le_trans (Polynomial.natDegree_sub_le W V) (max_le hW hV)
      have hzero : ZetaNine.CoefficientMapAggregate.aggregate n (W - V) = 0 := by
        change ZetaNine.CoefficientMapAggregate.aggregateLinearMap n (W - V) = 0
        rw [map_sub]
        exact sub_eq_zero.mpr heq
      exact sub_eq_zero.mp (embedded_ZetaNine__CoefficientMapKernelBridge__original_quartic_aggregate_kernel_zero n hn2 hn (W - V) hdegree hzero)
    have embedded_ZetaNine__CoefficientMapKernelBridge__original_five_dimensional_map_injective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
        Function.Injective (ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap n) := by
      intro a b heq
      apply embedded_ZetaNine__CoefficientMapAggregate__coordinatePolynomial_injective
      exact embedded_ZetaNine__CoefficientMapKernelBridge__original_quartic_aggregate_injective n hn2 hn (ZetaNine.CoefficientMapAggregate.coordinatePolynomial a) (ZetaNine.CoefficientMapAggregate.coordinatePolynomial b)
        (embedded_ZetaNine__CoefficientMapAggregate__coordinatePolynomial_natDegree_le a) (embedded_ZetaNine__CoefficientMapAggregate__coordinatePolynomial_natDegree_le b) heq
    have embedded_ZetaNine__CoefficientMapKernelBridge__original_five_dimensional_map_bijective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
        Function.Bijective (ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap n) := by
      have hi := embedded_ZetaNine__CoefficientMapKernelBridge__original_five_dimensional_map_injective n hn2 hn
      exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
    exact embedded_ZetaNine__CoefficientMapKernelBridge__original_five_dimensional_map_bijective
  ) : ∀ (n : ℕ), 2 ≤ n → Even n → Function.Bijective ⇑(ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap n)) n hn2 hn)

def inverseMultiplier (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) : ℚ[X] :=
  coordinatePolynomial ((actualAggregateEquiv n hn2 hn).symm b)

def prescribedL (b : Fin 5 → ℚ) : ℝ :=
  (b 0 : ℝ) +
    ((b 1 : ℝ) * CoefficientMapSummation.zetaReal 3 +
     (b 2 : ℝ) * CoefficientMapSummation.zetaReal 5 +
     (b 3 : ℝ) * CoefficientMapSummation.zetaReal 7 +
     (b 4 : ℝ) * CoefficientMapSummation.zetaReal 9)

end ZetaNine.CoefficientMapKernelBridge


