-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ShadowChains
-- name    : ConsistentSubmodular_Randomized_AdaptivityGap_ShadowChains
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:53.174927+00:00
-- url     : https://prove2.me/theorems/8e22f4f4-857a-4a85-baf5-d20389344bc1
-- title:
--   Chain hypothesis and the consecutive-interval instance with equalizing probabilities (5)
-- statement:
--   - `ChainHypothesis` $\alpha$ (a proposition): the hypothesis of Lemma 3: every instance $I$ of nonincreasing consecutive intervals with the equalizing distribution has adaptivity gap at least $\alpha$, for every $N$.
--   - `chainLeft` $d\,j$: the left endpoint $\ell_j=d_0+\dots+d_{j-1}$ of the $j$-th consecutive interval, for a sequence $d:\mathbb N\to\mathbb R$ of lengths.
--   - `chainProb` $d$: the equalizing probabilities (5): $p_0=1/d_0$ and $p_{j+1}=1/d_{j+1}-1/d_j$, so that $p_0+\dots+p_j=1/d_j$.
--   - `chainInstance` $N\,d\,hd\,hN$: given lengths with $d_{j+1}\le d_j$ for $j<N$ and $d_N=1$, the interval-selection instance on $\{0,\dots,N\}$ with intervals $[\ell_j,\ell_j+d_j]$ where $\ell_j=$ `chainLeft` $d\,j$, and probabilities $p_j=$ `chainProb` $d\,j$. The required properties (nonnegative left endpoints, $\ell_j\le r_j$, nonnegative probabilities, total mass $p_0+\dots+p_N=1/d_N=1$) follow from the hypotheses.
--
--   The file also proves basic facts about chains: the partial sums of $p$ telescope to $1/d_j$, every $d_j$ with $j\le N$ is at least $1$ (hence positive), and $p_j\ge0$.
--
--   These definitions turn a descending sequence of lengths ending at $1$ into the consecutive-interval instance with equalizing distribution analyzed in Lemma 4, connecting the chain computations with the adaptivity gap.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ShadowChains.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_EqualizingDistribution

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Shadow

/-- The hypothesis of Lemma 3: every instance of nonincreasing consecutive intervals with the
equalizing distribution has adaptivity gap at least `α`. -/
def ChainHypothesis (α : ℝ) : Prop :=
  ∀ (N : ℕ) (I : IntervalInstance N), I.IsNonincreasingConsecutive → I.IsEqualizing →
    α ≤ I.adaptivityGap

/-- The left endpoint `ℓ_j = d_0 + ⋯ + d_{j-1}` of the `j`-th consecutive interval. -/
def chainLeft (d : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, d i

/-- The equalizing probabilities (5), with `p_0 + ⋯ + p_j = 1 / d_j`. -/
def chainProb (d : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1 / d 0
  | j + 1 => 1 / d (j + 1) - 1 / d j

theorem sum_chainProb (d : ℕ → ℝ) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), chainProb d i = 1 / d j := by
  induction j with
  | zero => simp [chainProb]
  | succ j ih => rw [Finset.sum_range_succ, ih, chainProb]; ring

section

variable {N : ℕ} {d : ℕ → ℝ}

/-- The lengths of a chain ending at `d_N = 1` are at least one. -/
theorem chain_one_le (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1) {j : ℕ} (hj : j ≤ N) :
    1 ≤ d j := by
  have key : ∀ e j, j + e = N → 1 ≤ d j := by
    intro e
    induction e with
    | zero =>
      intro j h
      simp only [add_zero] at h
      subst h
      exact hN.ge
    | succ e ih =>
      intro j h
      exact (ih (j + 1) (by omega)).trans (hd j (by omega))
  exact key (N - j) j (by omega)

theorem chain_pos (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1) {j : ℕ} (hj : j ≤ N) :
    0 < d j :=
  zero_lt_one.trans_le (chain_one_le hd hN hj)

theorem chainProb_nonneg (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1) {j : ℕ}
    (hj : j ≤ N) : 0 ≤ chainProb d j := by
  cases j with
  | zero => exact (one_div_pos.mpr (chain_pos hd hN hj)).le
  | succ j =>
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (chain_pos hd hN hj) (hd j (by omega)))

/-- The consecutive intervals `[ℓ_j, ℓ_j + d_j]` of lengths `d_0, …, d_N` with the equalizing
distribution. -/
def chainInstance (N : ℕ) (d : ℕ → ℝ) (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1) :
    IntervalInstance N where
  left j := chainLeft d j
  right j := chainLeft d j + d j
  prob j := chainProb d j
  left_nonneg j := Finset.sum_nonneg fun i hi =>
    (chain_pos hd hN (by have := Finset.mem_range.mp hi; have := j.isLt; omega)).le
  left_le_right j := le_add_of_nonneg_right (chain_pos hd hN (by have := j.isLt; omega)).le
  prob_nonneg j := chainProb_nonneg hd hN (by have := j.isLt; omega)
  prob_sum := by rw [Fin.sum_univ_eq_sum_range (chainProb d) (N + 1), sum_chainProb, hN, div_one]

end

end ConsistentSubmodular.Shadow

end


