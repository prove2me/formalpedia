-- Prove2me | solution 1 for AKSSorting.Core.aks_sorting_network_log_depth
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:38:23.440779+00:00
-- url     : https://prove2.me/submissions/1ea2a962-d514-426f-9f9d-ea59c2b9984c

import Definitions.Def_GirvingAKS_LayeredAdapter
import Definitions.Def_GirvingAKS_Seiferas

/-!
# AKS theorem in the platform's layered model

`network n` (upstream `girving/aks`, Seiferas's construction) sorts, has greedy depth
at most `141·10^62·⌈log₂ n⌉` and size at most `705·10^61·n·⌈log₂ n⌉`.  The greedy
schedule of `Adapter.Schedule` turns it into a layered network with the same depth,
size and input-output behaviour.  Finally `⌈log₂ n⌉ ≤ 2 log₂ n` for `n ≥ 2`.
-/

namespace AKSLayered

theorem clog_le_two_logb (n : ℕ) (hn : 2 ≤ n) :
    (Nat.clog 2 n : ℝ) ≤ 2 * Real.logb 2 n := by
  set k := Nat.clog 2 n with hk_def
  have hk : 1 ≤ k := Nat.clog_pos (by norm_num) (by omega)
  have hlt : 2 ^ (k - 1) < n := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := n) (by omega)
    simpa [Nat.pred_eq_sub_one] using this
  have hnpos : (0 : ℝ) < n := by positivity
  have h1 : ((k : ℝ) - 1) < Real.logb 2 n := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) hnpos]
    have hcast : ((k : ℝ) - 1) = ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk]; simp
    rw [hcast, Real.rpow_natCast]
    exact_mod_cast hlt
  have h2 : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hnpos, Real.rpow_one]
    exact_mod_cast hn
  linarith

/-- The AKS theorem for the platform's layered comparator networks. -/
theorem aks_layered :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∃ N : AKSSorting.Core.ComparatorNetwork n,
      (N.depth : ℝ) ≤ c * Real.logb 2 n ∧
      (N.size : ℝ) ≤ c * n * Real.logb 2 n ∧
      N.Sorts := by
  refine ⟨282 * 10 ^ 62, by norm_num, fun n hn => ⟨toLayered (network n), ?_, ?_, ?_⟩⟩
  · rw [toLayered_depth]
    have hd : ((network n).depth : ℝ) ≤ 141 * 10 ^ 62 * (Nat.clog 2 n : ℝ) := by
      exact_mod_cast network_depth_le n
    have hl := clog_le_two_logb n hn
    nlinarith
  · rw [toLayered_size]
    have hs : ((network n).size : ℝ) ≤ 705 * 10 ^ 61 * (n : ℝ) * (Nat.clog 2 n : ℝ) := by
      exact_mod_cast network_size_le n
    have hl := clog_le_two_logb n hn
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hlog : 0 ≤ Real.logb 2 n := by linarith [clog_le_two_logb n hn,
      (Nat.cast_nonneg (Nat.clog 2 n) : (0 : ℝ) ≤ _)]
    have h3 : (n : ℝ) * (Nat.clog 2 n : ℝ) ≤ (n : ℝ) * (2 * Real.logb 2 n) :=
      mul_le_mul_of_nonneg_left hl hn0
    nlinarith
  · exact toLayered_sorts _ (network_sorts n)

end AKSLayered

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∃ N : AKSSorting.Core.ComparatorNetwork n,
      (N.depth : ℝ) ≤ c * Real.logb 2 n ∧
      (N.size : ℝ) ≤ c * n * Real.logb 2 n ∧
      N.Sorts :=
  AKSLayered.aks_layered

