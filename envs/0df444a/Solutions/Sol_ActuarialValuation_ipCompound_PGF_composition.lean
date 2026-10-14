-- Prove2me | solution 1 for ActuarialValuation.ipCompound_PGF_composition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:20:08.68386+00:00
-- url     : https://prove2.me/submissions/c6ad15ef-df0d-4dcc-a162-62b86c5ae336

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_actuarial_ipCountPGF
import Definitions.Def_actuarial_ipSeverityPGF
import Definitions.Def_actuarial_ipCompoundPGF
import Theorems.Thm_ActuarialValuation_ipFold_nonneg
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ActuarialValuation

theorem solution (p f : ℕ → ℝ) (z : ℝ)
    (hp : ∀ n, 0 ≤ p n) (hf : ∀ n, 0 ≤ f n)
    (hn : (∑' n : ℕ, p n) = 1) (hs : (∑' n : ℕ, f n) = 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ipCompoundPGF p f z = ipCountPGF p (ipSeverityPGF f z) := by
  have hsf : Summable f := by
    by_contra h; have hzero := tsum_eq_zero_of_not_summable h
    rw [hs] at hzero
    norm_num at hzero
  have hsp : Summable p := by
    by_contra h; have hzero := tsum_eq_zero_of_not_summable h
    rw [hn] at hzero
    norm_num at hzero
  have hzpow (k : ℕ) : 0 ≤ z^k ∧ z^k ≤ 1 :=
    ⟨pow_nonneg hz0 _, pow_le_one₀ hz0 hz1⟩
  have hw (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (hgs : Summable g) :
      Summable (fun k => g k * z^k) := by
    apply Summable.of_norm_bounded hgs
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg k) (hzpow k).1)]
    nlinarith [mul_le_mul_of_nonneg_left (hzpow k).2 (hg k)]
  have hfold : ∀ n, Summable (ipFold f n) := by
    intro n
    induction n with
    | zero =>
      apply summable_of_hasFiniteSupport
      change Set.Finite {k : ℕ | ipFold f 0 k ≠ 0}
      refine (Set.finite_singleton 0).subset ?_
      intro k hk
      have h : k = 0 := by
        by_contra he
        have hh : ipFold f 0 k = 0 := by simp [ipFold, ipPoint, he]
        exact hk hh
      simpa using h
    | succ n ih =>
      have hprod : Summable (fun x : ℕ × ℕ => f x.1 * ipFold f n x.2) :=
        hsf.mul_of_nonneg ih (fun k => hf k) (fun k => ipFold_nonneg f n k hf)
      change Summable (fun k : ℕ => ∑ j ∈ Finset.range (k+1), f j * ipFold f n (k-j))
      exact summable_sum_mul_range_of_summable_mul hprod
  have hFpos : 0 ≤ ipSeverityPGF f z := by
    unfold ipSeverityPGF
    exact tsum_nonneg (fun k => mul_nonneg (hf k) (hzpow k).1)
  have hFle : ipSeverityPGF f z ≤ 1 := by
    unfold ipSeverityPGF
    calc
      (∑' k, f k*z^k) ≤ ∑' k, f k := by
        apply (hw f hf hsf).tsum_le_tsum ?_ hsf
        intro k
        nlinarith [mul_le_mul_of_nonneg_left (hzpow k).2 (hf k)]
      _ = 1 := hs
  have hFpow (n : ℕ) : 0 ≤ (ipSeverityPGF f z)^n ∧ (ipSeverityPGF f z)^n ≤ 1 :=
    ⟨pow_nonneg hFpos _, pow_le_one₀ hFpos hFle⟩
  have hpower : ∀ n, (∑' k : ℕ, ipFold f n k * z^k) =
      (ipSeverityPGF f z)^n := by
    intro n
    induction n with
    | zero =>
      change (∑' k : ℕ, (if k = 0 then (1:ℝ) else 0)*z^k) = 1
      simp
    | succ n ih =>
      let a : ℕ → ℝ := fun k => f k * z^k
      let b : ℕ → ℝ := fun k => ipFold f n k * z^k
      have ha : Summable a := hw f hf hsf
      have hb : Summable b := hw (ipFold f n) (fun k => ipFold_nonneg f n k hf) (hfold n)
      have hab : Summable (fun x : ℕ × ℕ => a x.1*b x.2) :=
        ha.mul_of_nonneg hb
          (fun k => mul_nonneg (hf k) (hzpow k).1)
          (fun k => mul_nonneg (ipFold_nonneg f n k hf) (hzpow k).1)
      have hterm (k : ℕ) : ipFold f (n+1) k * z^k =
          ∑ j ∈ Finset.range (k+1), a j*b (k-j) := by
        change (∑ j ∈ Finset.range (k+1), f j*ipFold f n (k-j))*z^k = _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        have hjadd : j+(k-j)=k := Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
        dsimp [a,b]
        have hzp : z^k = z^j * z^(k-j) := by
          rw [← pow_add, hjadd]
        rw [hzp]
        ring
      calc
        (∑' k, ipFold f (n+1) k * z^k) =
            ∑' k, ∑ j ∈ Finset.range (k+1), a j*b (k-j) := by
          exact tsum_congr (fun k => hterm k)
        _ = (∑'k, a k)*(∑'k,b k) :=
          (ha.tsum_mul_tsum_eq_tsum_sum_range hb hab).symm
        _ = (ipSeverityPGF f z)^(n+1) := by
          change (ipSeverityPGF f z)*(∑' k, ipFold f n k*z^k) = _
          rw [ih, pow_succ']
  have hwp : Summable (fun n => p n*(ipSeverityPGF f z)^n) := by
    apply Summable.of_norm_bounded hsp
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp n) (hFpow n).1)]
    nlinarith [mul_le_mul_of_nonneg_left (hFpow n).2 (hp n)]
  have hrow (n : ℕ) : Summable (fun k => p n * ipFold f n k*z^k) := by
    simpa only [mul_assoc] using
      ((hw (ipFold f n) (fun k => ipFold_nonneg f n k hf) (hfold n)).mul_left (p n))
  have hpos (u : ℕ × ℕ) : 0 ≤ p u.1 * ipFold f u.1 u.2 * z^u.2 := mul_nonneg (mul_nonneg (hp u.1) (ipFold_nonneg f u.1 u.2 hf)) (hzpow u.2).1
  have hprod : Summable (fun u : ℕ × ℕ => p u.1 * ipFold f u.1 u.2 * z^u.2) := by
    apply (summable_prod_of_nonneg hpos).2
    constructor
    · exact hrow
    · convert hwp using 1
      funext n
      change (∑'k, p n * ipFold f n k*z^k) = _
      simp_rw [mul_assoc]
      rw [tsum_mul_left, hpower n]
  have hcol (k : ℕ) : Summable (fun n => p n * ipFold f n k*z^k) := by
    have hprod' : Summable (fun u : ℕ × ℕ => p u.2*ipFold f u.2 u.1*z^u.1) := hprod.prod_symm
    exact ((summable_prod_of_nonneg (fun u => hpos (u.2,u.1))).mp hprod').1 k
  have hcomm : (∑'k, ∑'n, p n * ipFold f n k *z^k) = ∑'n, ∑'k, p n * ipFold f n k *z^k := hprod.tsum_comm' hrow hcol
  calc
    ipCompoundPGF p f z = ∑' k, ∑' n, p n * ipFold f n k * z^k := by
      unfold ipCompoundPGF
      apply tsum_congr
      intro k
      change (∑'n, p n * ipFold f n k)*z^k = _
      rw [← tsum_mul_right]
    _ = ∑' n, ∑' k, p n*ipFold f n k*z^k := hcomm
    _ = ipCountPGF p (ipSeverityPGF f z) := by
      unfold ipCountPGF
      apply tsum_congr
      intro n
      simp_rw [mul_assoc]
      rw [tsum_mul_left, hpower n]
