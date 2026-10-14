-- Prove2me | solution 1 for ActuarialValuation.ipGeometric_Panjer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:13:12.530977+00:00
-- url     : https://prove2.me/submissions/b0b04ac7-6ebb-4475-81cf-baf130821652

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ipGeo
import Definitions.Def_actuarial_ipCompound
import Definitions.Def_actuarial_ipGeoRHS

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

/-- Renewal representation of the compound geometric mass at a positive severity. -/
theorem solution (q : ℝ) (f : ℕ → ℝ) (k : ℕ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hf : ∀ n, 0 ≤ f n)
    (hs : (∑' n : ℕ, f n) = 1) (hk : 0 < k) :
    (1-q*f 0)*ipCompound (ipGeo q) f k =
      ipGeoRHS q f (ipCompound (ipGeo q) f) k := by
  have hsf : Summable f := by
    by_contra hn
    have hz : (∑' n : ℕ, f n) = 0 := tsum_eq_zero_of_not_summable hn
    linarith
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
      change 0 ≤ ipConvolve f (ipFold f n) t ∧
        ipConvolve f (ipFold f n) t ≤ 1
      constructor
      · unfold ipConvolve
        exact Finset.sum_nonneg (fun j _ => mul_nonneg (hf j) (ih _).1)
      · calc
          ipConvolve f (ipFold f n) t ≤
              ∑ j ∈ Finset.range (t+1), f j := by
            unfold ipConvolve
            apply Finset.sum_le_sum
            intro j hj
            nlinarith [mul_le_mul_of_nonneg_left (ih (t-j)).2 (hf j)]
          _ ≤ ∑' j : ℕ, f j :=
            hsf.sum_le_tsum (Finset.range (t+1)) (by intro j hj; exact hf j)
          _ = 1 := hs
  have hnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hgeo : Summable (ipGeo q) := by
    change Summable (fun n : ℕ => (1-q)*q^n)
    exact (summable_geometric_of_norm_lt_one hnorm).mul_left (1-q)
  have hgn : ∀ n, 0 ≤ ipGeo q n := by
    intro n
    dsimp [ipGeo]
    exact mul_nonneg (by linarith) (pow_nonneg hq0 _)
  have hslice : ∀ t, Summable
      (fun n : ℕ => ipGeo q n * ipFold f n t) := by
    intro t
    apply Summable.of_norm_bounded hgeo
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hgn n) (hfold n t).1)]
    nlinarith [mul_le_mul_of_nonneg_left (hfold n t).2 (hgn n)]
  have hratio (n : ℕ) : ipGeo q (n+1) = q * ipGeo q n := by
    simp only [ipGeo, pow_succ]
    ring
  have hshift (t : ℕ) :
      (∑' n : ℕ, ipGeo q (n+1) * ipFold f (n+1) t) =
      q * ipConvolve f (ipCompound (ipGeo q) f) t := by
    calc
      (∑' n : ℕ, ipGeo q (n+1) * ipFold f (n+1) t) =
          ∑' n : ℕ, ∑ j ∈ Finset.range (t+1),
            (q*f j)*(ipGeo q n*ipFold f n (t-j)) := by
        apply tsum_congr
        intro n
        rw [hratio n]
        change (q*ipGeo q n)*
            (∑ j ∈ Finset.range (t+1), f j*ipFold f n (t-j)) = _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ j ∈ Finset.range (t+1), ∑' n : ℕ,
          (q*f j)*(ipGeo q n*ipFold f n (t-j)) := by
        exact Summable.tsum_finsetSum (fun j hj =>
          (hslice (t-j)).mul_left (q*f j))
      _ = ∑ j ∈ Finset.range (t+1),
          (q*f j)*ipCompound (ipGeo q) f (t-j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [tsum_mul_left]
        rfl
      _ = q * ipConvolve f (ipCompound (ipGeo q) f) t := by
        unfold ipConvolve
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hrec (t : ℕ) :
      ipCompound (ipGeo q) f t =
        (1-q)*ipPoint t +
        q*ipConvolve f (ipCompound (ipGeo q) f) t := by
    calc
      ipCompound (ipGeo q) f t =
          (∑' n : ℕ, ipGeo q n*ipFold f n t) := rfl
      _ = ipGeo q 0 * ipFold f 0 t +
          (∑' n : ℕ, ipGeo q (n+1)*ipFold f (n+1) t) := by
        exact (hslice t).tsum_eq_zero_add
      _ = (1-q)*ipPoint t +
          q*ipConvolve f (ipCompound (ipGeo q) f) t := by
        rw [hshift t]
        congr 1
        simp [ipGeo, ipFold]
  have hpoint : ipPoint k = 0 := by
    simp [ipPoint, Nat.ne_of_gt hk]
  have hhead : ipConvolve f (ipCompound (ipGeo q) f) k =
      f 0 * ipCompound (ipGeo q) f k +
      (∑ j ∈ Finset.range k,
        f (j+1)*ipCompound (ipGeo q) f (k-(j+1))) := by
    unfold ipConvolve
    rw [Finset.sum_range_succ']
    simp
    ring
  have hh := hrec k
  rw [hpoint, mul_zero, zero_add, hhead] at hh
  unfold ipGeoRHS
  nlinarith [hh]
