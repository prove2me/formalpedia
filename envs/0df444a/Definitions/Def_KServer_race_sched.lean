-- Prove2me | Definitions.Def_KServer_race_sched
-- name    : KServer_race_sched
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T15:21:23.504653+00:00
-- url     : https://prove2.me/theorems/5784837c-037e-4eb1-b7b6-9e1cadabbb6c
-- title:
--   Coin schedule bookkeeping for the BCR race
-- statement:
--   Pure bookkeeping for the coin phase of the BCR race, which advances one of two sides at each of $\kappa$ steps according to a coin string $c \in \{L,R\}^{\kappa}$: the consumption counts $\mathrm{cnt}_L(c,j)$ and $\mathrm{cnt}_R(c,j)$ of left and right advances among the first $j$ coins, with their recursions, monotonicity, the identity $\mathrm{cnt}_L + \mathrm{cnt}_R = j$, and prefix-congruence; and the clamped size-weighted coin probability $$p_L(n_L, n_R, \varepsilon) = \frac{\max(n_R, \varepsilon)}{\max(n_L, \varepsilon) + \max(n_R, \varepsilon)},$$ which is strictly between $0$ and $1$ and satisfies $p_L + p_R = 1$. The size-weighting makes the consumed-size imbalance a martingale up to an $O(\varepsilon)$ compensator, and the clamp keeps all outcome weights positive.
-- source:
--   BCR randomized k-server lower bound, race construction

import Mathlib

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

namespace Race

/-! ### Coin schedule bookkeeping

The coin phase of the BCR race advances one of two sides at each of `κ`
steps.  Everything here is pure bookkeeping over coin strings
`c : Fin κ → Bool` (`true` = left): consumption counts, their basic
arithmetic, and the path-dependent coin weights (size-weighted with a
positivity clamp), whose per-step sums are one. -/

variable {κ : ℕ}

/-- Left-consumption count after `j` coin steps. -/
def cntL (c : Fin κ → Bool) (j : ℕ) : ℕ :=
  ((Finset.range j).filter (fun i => ∀ hi : i < κ, c ⟨i, hi⟩ = true)).card

/-- Right-consumption count after `j` coin steps. -/
def cntR (c : Fin κ → Bool) (j : ℕ) : ℕ :=
  ((Finset.range j).filter (fun i => ∀ hi : i < κ, c ⟨i, hi⟩ = false)).card

theorem cntL_zero (c : Fin κ → Bool) : cntL c 0 = 0 := by
  unfold cntL
  simp

theorem cntR_zero (c : Fin κ → Bool) : cntR c 0 = 0 := by
  unfold cntR
  simp

theorem cntL_succ (c : Fin κ → Bool) {j : ℕ} (hj : j < κ) :
    cntL c (j + 1) = cntL c j + (if c ⟨j, hj⟩ = true then 1 else 0) := by
  unfold cntL
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases hc : c ⟨j, hj⟩ = true
  · rw [if_pos (by intro hi; exact hc), if_pos hc,
      Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg (fun hall => hc (hall hj)), if_neg hc, add_zero]

theorem cntR_succ (c : Fin κ → Bool) {j : ℕ} (hj : j < κ) :
    cntR c (j + 1) = cntR c j + (if c ⟨j, hj⟩ = false then 1 else 0) := by
  unfold cntR
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases hc : c ⟨j, hj⟩ = false
  · rw [if_pos (by intro hi; exact hc), if_pos hc,
      Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg (fun hall => hc (hall hj)), if_neg hc, add_zero]

theorem cntL_add_cntR (c : Fin κ → Bool) {j : ℕ} (hj : j ≤ κ) :
    cntL c j + cntR c j = j := by
  induction j with
  | zero => rw [cntL_zero, cntR_zero]
  | succ j ih =>
    have hjκ : j < κ := by omega
    rw [cntL_succ c hjκ, cntR_succ c hjκ]
    have hih := ih (by omega)
    by_cases hc : c ⟨j, hjκ⟩ = true
    · rw [if_pos hc, if_neg (by simp [hc])]
      omega
    · rw [if_neg hc, if_pos (by simpa using hc)]
      omega

theorem cntL_le (c : Fin κ → Bool) {j : ℕ} (hj : j ≤ κ) : cntL c j ≤ j := by
  have := cntL_add_cntR c hj
  omega

theorem cntR_le (c : Fin κ → Bool) {j : ℕ} (hj : j ≤ κ) : cntR c j ≤ j := by
  have := cntL_add_cntR c hj
  omega

theorem cntL_mono (c : Fin κ → Bool) {j j' : ℕ} (h : j ≤ j') :
    cntL c j ≤ cntL c j' := by
  unfold cntL
  exact Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))))

theorem cntR_mono (c : Fin κ → Bool) {j j' : ℕ} (h : j ≤ j') :
    cntR c j ≤ cntR c j' := by
  unfold cntR
  exact Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))))

/-- Counts agree on coin strings agreeing below `j`. -/
theorem cntL_congr {c c' : Fin κ → Bool} {j : ℕ}
    (h : ∀ i : Fin κ, (i : ℕ) < j → c i = c' i) :
    cntL c j = cntL c' j := by
  unfold cntL
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  rw [Finset.mem_range] at hi
  constructor
  · intro hall hiκ
    rw [← h ⟨i, hiκ⟩ hi]
    exact hall hiκ
  · intro hall hiκ
    rw [h ⟨i, hiκ⟩ hi]
    exact hall hiκ

theorem cntR_congr {c c' : Fin κ → Bool} {j : ℕ}
    (h : ∀ i : Fin κ, (i : ℕ) < j → c i = c' i) :
    cntR c j = cntR c' j := by
  unfold cntR
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  rw [Finset.mem_range] at hi
  constructor
  · intro hall hiκ
    rw [← h ⟨i, hiκ⟩ hi]
    exact hall hiκ
  · intro hall hiκ
    rw [h ⟨i, hiκ⟩ hi]
    exact hall hiκ

/-- The clamped left-coin probability from the two next sizes. -/
noncomputable def probL (nL nR ε : ℝ) : ℝ :=
  (max nR ε) / (max nL ε + max nR ε)

theorem probL_pos {nL nR ε : ℝ} (hε : 0 < ε) : 0 < probL nL nR ε := by
  unfold probL
  have h1 : 0 < max nR ε := lt_of_lt_of_le hε (le_max_right _ _)
  have h2 : 0 < max nL ε := lt_of_lt_of_le hε (le_max_right _ _)
  positivity

theorem probL_lt_one {nL nR ε : ℝ} (hε : 0 < ε) : probL nL nR ε < 1 := by
  unfold probL
  have h1 : 0 < max nR ε := lt_of_lt_of_le hε (le_max_right _ _)
  have h2 : 0 < max nL ε := lt_of_lt_of_le hε (le_max_right _ _)
  rw [div_lt_one (by linarith)]
  linarith

/-- The two coin weights at one step sum to one. -/
theorem probL_add_probR (nL nR ε : ℝ) (hε : 0 < ε) :
    probL nL nR ε + probL nR nL ε = 1 := by
  unfold probL
  have h1 : 0 < max nR ε := lt_of_lt_of_le hε (le_max_right _ _)
  have h2 : 0 < max nL ε := lt_of_lt_of_le hε (le_max_right _ _)
  rw [div_add_div _ _ (by linarith) (by linarith)]
  rw [div_eq_one_iff_eq (by nlinarith)]
  ring

end Race

end KServer


