-- Prove2me | Definitions.Def_PermutationStreams_Parity_Supplement_OnePass
-- name    : PermutationStreams_Parity_Supplement_OnePass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:53:24.070106+00:00
-- url     : https://prove2.me/theorems/e09c59e6-1b58-44c0-85fb-ac75f8653e0a
-- title:
--   Deterministic clock-free one-pass streaming algorithms and their space
-- statement:
--   Fix $n$. A **deterministic one-pass streaming algorithm** for inputs $\pi_1,\dots,\pi_n$ with values in $[n]$ consists of a finite set $S$ of states, an initial state $s_0\in S$, a transition map $\delta:S\times[n]\to S$ and an output map $\mathrm{out}:S\to A$ into an answer set $A$. On input $\pi$ it computes
--
--   $$
--   s_i=\delta(s_{i-1},\pi_i)\quad(1\le i\le n),\qquad \text{answer}=\mathrm{out}(s_n).
--   $$
--
--   The transition sees only the current state and the current value; the position $i$ is not supplied, so any counter the algorithm needs is part of its state. The algorithm may depend arbitrarily on $n$. It **uses $s$ bits** when $|S|\le 2^s$; its space is the least such $s$, namely $\lceil\log_2|S|\rceil$.
--
--   This is the model of the paper's pattern-detection results, whose space bounds are state counts (Lemma 6.3 counts states and takes the logarithm).
--
--   **Formalization Note** Values are `Fin n` (the value $v$ stands for $v+1$); the state type is a parameter `S`, and finiteness is imposed as `[Fintype S]` wherever space is measured.
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §1 p. 1, §1.2 p. 2, §5.2–5.3 pp. 10–12 (register algorithms), §6.1 pp. 13–14 (state counts)

import Mathlib

namespace PermutationStreams.Parity.Supplement

/-- Braverman–Zamir §1 p.1, §1.2 p.2 and §6.1 pp.13–14: a deterministic one-pass streaming
algorithm for inputs `π(0), …, π(n-1)` with values in `Fin n` (the value `v` stands for `v + 1`).
`S` is its state set, `init` the initial state, and `step s x` the next state when the current
state is `s` and the arriving value is `x`. The transition sees only the state and the current
value: no position or clock is supplied, so a counter, if needed, lives in the (charged) state.
`out` turns the final state into the answer. The algorithm may depend arbitrarily on `n`. -/
structure OnePassAlg (n : ℕ) (S α : Type) where
  init : S
  step : S → Fin n → S
  out : S → α

/-- The state after reading `π(0), …, π(n-1)` in order from `init`. -/
def OnePassAlg.finalState {n : ℕ} {S α : Type} (A : OnePassAlg n S α)
    (π : Equiv.Perm (Fin n)) : S :=
  (List.finRange n).foldl (fun s i => A.step s (π i)) A.init

/-- The answer of one pass on the input permutation `π`. -/
def OnePassAlg.run {n : ℕ} {S α : Type} (A : OnePassAlg n S α) (π : Equiv.Perm (Fin n)) : α :=
  A.out (A.finalState π)

/-- The algorithm uses `s` bits: it has at most `2^s` states. The space of an algorithm is the
least such `s`, i.e. `⌈log₂ |S|⌉`. -/
def OnePassAlg.UsesBits {n : ℕ} {S α : Type} [Fintype S] (_A : OnePassAlg n S α) (s : ℕ) :
    Prop :=
  Fintype.card S ≤ 2 ^ s

end PermutationStreams.Parity.Supplement


