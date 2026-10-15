-- Prove2me | Definitions.Def_SecretaryAdvice_Samples_Setting
-- name    : SecretaryAdvice_Samples_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:13.419982+00:00
-- url     : https://prove2.me/theorems/f6838aed-0abb-4082-a12a-b639cb954a18
-- title:
--   Example 4 and §5, pp. 7, 15 — secretaries with k samples: outcomes, signals, information, policies, winning probability, threshold policies
-- statement:
--   This file sets up the **secretary problem with samples** (Example 4 of Dütting, Lattanzi, Paes Leme and Vassilvitskii). An adversary writes down $n+k$ distinct numbers. A uniformly random subset of $k$ of them is revealed as **samples**; the remaining $n$ numbers, the **secretaries**, are then presented one at a time in uniformly random order. The goal is to stop at the best of the $n$ secretaries.
--
--   Only the relative order of the numbers matters, so an outcome is a permutation $\sigma$ of the $k+n$ positions, read as "position $\mapsto$ value rank" (larger is better). Positions $0,\dots,k-1$ hold the samples and position $k+i$ holds the secretary of round $i$. Under the uniform distribution on the $(k+n)!$ permutations, the sample set is a uniformly random $k$-subset and the remaining numbers arrive in uniformly random order.
--
--   1. **Signal** $s_i\in\mathcal S=\{0,1,\dots,k\}$: the number of samples worse than the secretary of round $i$.
--   2. **Best-so-far event** $T_i$: the secretary of round $i$ beats every earlier secretary.
--   3. **Top event** $r_i=n$: the secretary of round $i$ is the best of the $n$ secretaries. Ranks are relative to the secretaries only; the samples do not count.
--   4. **Information** at round $i$: the relative order of the $k$ samples and the first $i+1$ secretaries (all comparisons $a\prec b$ among those positions). It determines $T_i$, $s_i$ and the earlier signals, and nothing about later arrivals.
--   5. **Policy** $q$: for each round, a stopping probability $q_i(x)\in[0,1]$ that is a function of the information $x$ at that round only. Policies may be randomized and history-dependent.
--   6. **Winning probability**
--   $$\mathrm{win}(q)=\frac{1}{(k+n)!}\sum_{\sigma}\sum_{i}\mathbf 1[r_i=n]\;q_i(x_i(\sigma))\prod_{j<i}\bigl(1-q_j(x_j(\sigma))\bigr),$$
--   the probability that $q$ stops, for the first time, at the best secretary.
--   7. **Probability** of an event $E$: $\mathbb P(E)=\#\{\sigma: E(\sigma)\}/(k+n)!$.
--   8. **Threshold policy** for a threshold function $t:\mathcal S\to[n]$: stop at the first round $i$ (counted from 1) with $T_i$ and $i\ge t(s_i)$, i.e. $\tau=\min\{i: T_i\text{ and }i\ge t(s_i)\}$. A threshold function is valid if $1\le t(s)\le n$ for every $s\in\mathcal S$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Rounds are 0-based in Lean (`Fin n`): Lean round $i$ is the paper's round $i+1$, so the threshold test reads $t(s_i)\le i+1$. The adversary's numbers are taken distinct (Example 4 does not say so; with ties "the best" is ambiguous). The product $\prod_{j<i}(1-q_j)$ makes "stop at most once" exact. Probabilities are finite averages over permutations, not integrals. Threshold functions are typed $\mathbb N\to\mathbb N$ and constrained only on $\mathcal S=\{0,\dots,k\}$, the values a signal can take.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 6 (§2 model, eq. (1)), p. 7 (Example 4), p. 9 (generic policy), p. 12 (threshold policy), p. 15 (§5 LP Formulation)

import Mathlib

namespace SecretaryAdvice.Samples

/-!
Example 4 (p. 7) and §5 (p. 15) of Dütting, Lattanzi, Paes Leme, Vassilvitskii,
*Secretaries with Advice* (arXiv:2011.06726v1): the secretary problem with `k` samples.

An adversary writes down `n + k` distinct numbers; only their relative order matters. An outcome
is a permutation `σ` of the `k + n` positions, read as *position ↦ value rank* (larger is better).
Positions `0, …, k-1` are the samples; position `k + i` is the online secretary of round
`i : Fin n` (the paper's round `i + 1`). A uniformly random `σ` is a uniformly random `k`-subset
of samples followed by a uniformly random order of the remaining `n` numbers.
-/

open Finset

/-- An outcome: a permutation of the `k + n` positions, read as *position ↦ value rank*. -/
abbrev Outcome (n k : ℕ) : Type := Equiv.Perm (Fin (k + n))

/-- The position of sample `a`. -/
def samplePos (n : ℕ) {k : ℕ} (a : Fin k) : Fin (k + n) := Fin.castAdd n a

/-- The position of the online secretary of round `i` (0-based). -/
def onlinePos {n : ℕ} (k : ℕ) (i : Fin n) : Fin (k + n) := Fin.natAdd k i

/-- The signal `s_i`: the number of samples worse than the secretary of round `i`. -/
def sig {n k : ℕ} (σ : Outcome n k) (i : Fin n) : ℕ :=
  (univ.filter fun a : Fin k => σ (samplePos n a) < σ (onlinePos k i)).card

/-- The best-so-far event `T_i` (1): the secretary of round `i` beats every earlier online
secretary. -/
def T {n k : ℕ} (σ : Outcome n k) (i : Fin n) : Prop :=
  ∀ j : Fin n, j < i → σ (onlinePos k j) < σ (onlinePos k i)

instance {n k : ℕ} (σ : Outcome n k) (i : Fin n) : Decidable (T σ i) := by
  unfold T; infer_instance

/-- `r_i = n`: the secretary of round `i` is the best of the `n` online secretaries (ranks are
relative to the online secretaries only, not to the samples). -/
def top {n k : ℕ} (σ : Outcome n k) (i : Fin n) : Prop :=
  ∀ j : Fin n, σ (onlinePos k j) ≤ σ (onlinePos k i)

instance {n k : ℕ} (σ : Outcome n k) (i : Fin n) : Decidable (top σ i) := by
  unfold top; infer_instance

/-- The information available at (0-based) round `m`: the relative order of the first
`k + m + 1` positions (the `k` samples and the online secretaries of rounds `0, …, m`);
`x a b = true` iff position `a` is worse than position `b`. -/
abbrev Info (k m : ℕ) : Type := Fin (k + m + 1) → Fin (k + m + 1) → Bool

/-- The embedding of the first `k + i + 1` positions into all positions. -/
def prefixPos {n k : ℕ} (i : Fin n) (a : Fin (k + i.val + 1)) : Fin (k + n) :=
  ⟨a.val, by have := a.isLt; have := i.isLt; omega⟩

/-- The information revealed by outcome `σ` at round `i`. -/
def info {n k : ℕ} (σ : Outcome n k) (i : Fin n) : Info k i.val :=
  fun a b => decide (σ (prefixPos i a) < σ (prefixPos i b))

/-- A (randomized, history-dependent) policy: at round `i` it maps the information to a
stopping probability. -/
abbrev Policy (n k : ℕ) : Type := (i : Fin n) → Info k i.val → ℝ

/-- A policy is valid if every stopping probability lies in `[0, 1]`. -/
def ValidPolicy {n k : ℕ} (q : Policy n k) : Prop :=
  ∀ (i : Fin n) (x : Info k i.val), 0 ≤ q i x ∧ q i x ≤ 1

/-- The probability that policy `q` stops at round `i` on outcome `σ`: it has not stopped at an
earlier round and stops at round `i`. -/
def pickProb {n k : ℕ} (q : Policy n k) (σ : Outcome n k) (i : Fin n) : ℝ :=
  q i (info σ i) * ∏ j ∈ univ.filter (fun j : Fin n => j < i), (1 - q j (info σ j))

/-- The winning probability of `q`: the probability of stopping at the best online secretary
when `σ` is uniformly random. -/
noncomputable def win {n k : ℕ} (q : Policy n k) : ℝ :=
  (1 / ((k + n).factorial : ℝ)) *
    ∑ σ : Outcome n k, ∑ i : Fin n, if top σ i then pickProb q σ i else 0

/-- The probability of an event under the uniform distribution on outcomes. -/
noncomputable def prob {n k : ℕ} (E : Outcome n k → Prop) [DecidablePred E] : ℝ :=
  ((univ.filter E).card : ℝ) / ((k + n).factorial : ℝ)

/-- The current (last) position of the information at round `m`. -/
def infoCur (k m : ℕ) : Fin (k + m + 1) := Fin.last (k + m)

/-- `T_i` read from the information: the current secretary beats every earlier online
secretary (positions `k, …, k + m - 1`). -/
def infoBestSoFar {k m : ℕ} (x : Info k m) : Bool :=
  decide (∀ b : Fin (k + m + 1), k ≤ b.val → b.val < k + m → x b (infoCur k m) = true)

/-- The signal read from the information: the number of samples worse than the current
secretary. -/
def infoSignal {k m : ℕ} (x : Info k m) : ℕ :=
  (univ.filter fun a : Fin k =>
    x (Fin.castLE (by omega) a) (infoCur k m) = true).card

/-- A threshold function `t : S → [n]` on the signal space `S = {0, …, k}`. -/
def ValidThreshold (n k : ℕ) (t : ℕ → ℕ) : Prop :=
  ∀ s, s ≤ k → 1 ≤ t s ∧ t s ≤ n

/-- The threshold policy `τ = min {i : T_i and i ≥ t(s_i)}` (1-based rounds): stop at round
`i` (0-based) iff the current secretary is best so far and `i + 1 ≥ t(s_i)`. -/
def thresholdPolicy {n k : ℕ} (t : ℕ → ℕ) : Policy n k :=
  fun i x => if infoBestSoFar x = true ∧ t (infoSignal x) ≤ i.val + 1 then 1 else 0

end SecretaryAdvice.Samples


