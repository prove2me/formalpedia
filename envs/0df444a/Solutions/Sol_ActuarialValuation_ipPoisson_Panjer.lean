-- Prove2me | solution 1 for ActuarialValuation.ipPoisson_Panjer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:52:45.424455+00:00
-- url     : https://prove2.me/submissions/c5aed71e-d7f3-46b8-a059-6222e1556f29

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_actuarial_ipPoisson
import Definitions.Def_actuarial_ipCompound
import Definitions.Def_actuarial_ipPoiRHS
import Theorems.Thm_ActuarialValuation_ipPoisson_ratio
import Theorems.Thm_ActuarialValuation_ipPoi_normalized
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ActuarialValuation
theorem solution (l : ℝ) (f : ℕ → ℝ) (k : ℕ) (hl : 0 ≤ l) (hf : ∀ n, 0 ≤ f n) (hs : (∑' n : ℕ, f n) = 1) (hk : 0 < k) : ipCompound (ipPoisson l) f k = ipPoiRHS l f (ipCompound (ipPoisson l) f) k := by
  have hsf : Summable f := by
    by_contra hn
    have hz := tsum_eq_zero_of_not_summable hn
    rw [hs] at hz
    norm_num at hz
  have hfold : ∀ n t, 0 ≤ ipFold f n t ∧ ipFold f n t ≤ 1 := by
    intro n
    induction n with
    | zero =>
      intro t
      change 0 ≤ ipPoint t ∧ ipPoint t ≤ 1
      unfold ipPoint
      split_ifs <;> constructor <;> norm_num
    | succ n ih =>
      intro t
      change 0 ≤ ipConvolve f (ipFold f n) t ∧ ipConvolve f (ipFold f n) t ≤ 1
      constructor
      · unfold ipConvolve
        exact Finset.sum_nonneg (fun j _ => mul_nonneg (hf j) (ih _).1)
      · calc
          ipConvolve f (ipFold f n) t ≤ ∑ j ∈ Finset.range (t+1), f j := by
            unfold ipConvolve
            apply Finset.sum_le_sum
            intro j hj
            nlinarith [mul_le_mul_of_nonneg_left (ih (t-j)).2 (hf j)]
          _ ≤ ∑' j : ℕ, f j := hsf.sum_le_tsum (Finset.range (t+1)) (by intro j hj; exact hf j)
          _ = 1 := hs
  have hp : Summable (ipPoisson l) := by
    by_contra hn
    have hz := tsum_eq_zero_of_not_summable hn
    rw [ipPoi_normalized l] at hz
    norm_num at hz
  have hpn (n : ℕ) : 0 ≤ ipPoisson l n := by
    dsimp [ipPoisson]
    exact div_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hl _)) (Nat.cast_nonneg _)
  have hslice (t : ℕ) : Summable (fun n : ℕ => ipPoisson l n * ipFold f n t) := by
    apply Summable.of_norm_bounded hp
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpn n) (hfold n t).1)]
    nlinarith [mul_le_mul_of_nonneg_left (hfold n t).2 (hpn n)]
  have hseries (n t : ℕ) : ipFold f n t = PowerSeries.coeff t ((PowerSeries.mk f)^n) := by
    induction n generalizing t with
    | zero =>
      change ipPoint t = PowerSeries.coeff t (1 : PowerSeries ℝ)
      simp [ipPoint]
    | succ n ih =>
      change ipConvolve f (ipFold f n) t = PowerSeries.coeff t ((PowerSeries.mk f)^(n+1))
      rw [pow_succ', PowerSeries.coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      unfold ipConvolve
      apply Finset.sum_congr rfl
      intro j hj
      simp only [PowerSeries.coeff_mk]
      rw [← ih]
  have hweight (n t : ℕ) (ht : 0 < t) : (t:ℝ)*ipFold f (n+1) t = ((n+1:ℕ):ℝ) * ∑ j ∈ Finset.range t, ((j+1:ℕ):ℝ)*f (j+1)*ipFold f n (t-(j+1)) := by
    let F : PowerSeries ℝ := PowerSeries.mk f
    have hd : PowerSeries.derivative ℝ (F^(n+1)) = (n+1 : PowerSeries ℝ) * ((PowerSeries.derivative ℝ F)*F^n) := by
      rw [PowerSeries.derivative_pow]
      simp only [Nat.add_sub_cancel_right, Nat.cast_add, Nat.cast_one]
      ring
    have hc := congrArg (PowerSeries.coeff (t-1)) hd
    rw [PowerSeries.coeff_derivative] at hc
    have ht0 : t-1+1=t := Nat.sub_add_cancel ht
    rw [ht0] at hc
    have hfin : PowerSeries.coeff (t-1) ((n+1 : PowerSeries ℝ) * ((PowerSeries.derivative ℝ F)*F^n)) = ((n+1:ℕ):ℝ) * PowerSeries.coeff (t-1) ((PowerSeries.derivative ℝ F)*F^n) := by
      have hc : (n+1 : PowerSeries ℝ) = PowerSeries.C (((n+1:ℕ):ℝ)) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (map_natCast (PowerSeries.C : ℝ →+* PowerSeries ℝ) (n+1)).symm
      rw [hc, PowerSeries.coeff_C_mul]
    rw [hfin] at hc
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
    simp only [Nat.succ_eq_add_one, ht0] at hc
    rw [← hseries (n+1) t] at hc
    have hconvert : (∑ j ∈ Finset.range t, PowerSeries.coeff j (PowerSeries.derivative ℝ F) * PowerSeries.coeff (t-1-j) (F^n)) = ∑ j ∈ Finset.range t, ((j+1:ℕ):ℝ)*f (j+1)*ipFold f n (t-(j+1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [PowerSeries.coeff_derivative, F, PowerSeries.coeff_mk]
      rw [← hseries n (t-1-j)]
      have heq : t-1-j=t-(j+1) := by simp [Nat.sub_sub, Nat.add_comm]
      rw [heq]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    rw [hconvert] at hc
    have hcast : ((t-1:ℕ):ℝ)+1=(t:ℝ) := by exact_mod_cast ht0
    rw [hcast] at hc
    nlinarith [hc]
  have hsuc : Summable (fun n : ℕ => ipPoisson l (n+1) * ipFold f (n+1) k) := (hslice k).comp_injective Nat.succ_injective
  have hpoint : ipFold f 0 k = 0 := by
    change ipPoint k = 0
    simp [ipPoint, Nat.ne_of_gt hk]
  have hstart : (k:ℝ)*ipCompound (ipPoisson l) f k = ∑' n : ℕ, (k:ℝ)*(ipPoisson l (n+1)*ipFold f (n+1) k) := by
    have hs0 := (hslice k).tsum_eq_zero_add
    change ipCompound (ipPoisson l) f k = ipPoisson l 0 * ipFold f 0 k + ∑' n : ℕ, ipPoisson l (n+1)*ipFold f (n+1) k at hs0
    rw [hpoint, mul_zero, zero_add] at hs0
    rw [hs0, ← tsum_mul_left]
  have hmain : (k:ℝ)*ipCompound (ipPoisson l) f k = l * (∑ j ∈ Finset.range k, ((j+1:ℕ):ℝ)*f (j+1)* ipCompound (ipPoisson l) f (k-(j+1))) := by
    calc
      _ = ∑' n : ℕ, ∑ j ∈ Finset.range k, (l*((j+1:ℕ):ℝ)*f (j+1)) * (ipPoisson l n*ipFold f n (k-(j+1))) := by
        rw [hstart]
        apply tsum_congr
        intro n
        calc
          _ = ipPoisson l (n+1) * ((k:ℝ)*ipFold f (n+1) k) := by ring
          _ = ipPoisson l (n+1) * (((n+1:ℕ):ℝ) * ∑ j ∈ Finset.range k, ((j+1:ℕ):ℝ)*f (j+1)*ipFold f n (k-(j+1))) := by
            rw [hweight n k hk]
          _ = ∑ j ∈ Finset.range k, (l*((j+1:ℕ):ℝ)*f (j+1)) * (ipPoisson l n*ipFold f n (k-(j+1))) := by
            rw [← mul_assoc, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            calc
              _ = (((n+1:ℕ):ℝ)*ipPoisson l (n+1)) * (((j+1:ℕ):ℝ)*f (j+1)*ipFold f n (k-(j+1))) := by ring
              _ = (l*ipPoisson l n) * (((j+1:ℕ):ℝ)*f (j+1)*ipFold f n (k-(j+1))) := by
                rw [ipPoisson_ratio l n]
              _ = _ := by ring
      _ = ∑ j ∈ Finset.range k, ∑' n : ℕ, (l*((j+1:ℕ):ℝ)*f (j+1)) * (ipPoisson l n*ipFold f n (k-(j+1))) := by
        exact Summable.tsum_finsetSum (fun j hj => (hslice (k-(j+1))).mul_left (l*((j+1:ℕ):ℝ)*f (j+1)))
      _ = l * (∑ j ∈ Finset.range k, ((j+1:ℕ):ℝ)*f (j+1)* ipCompound (ipPoisson l) f (k-(j+1))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [tsum_mul_left]
        unfold ipCompound
        ring
  have hkn : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  unfold ipPoiRHS
  field_simp
  nlinarith [hmain]
