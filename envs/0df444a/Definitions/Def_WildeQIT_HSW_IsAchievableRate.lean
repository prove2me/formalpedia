-- Prove2me | Definitions.Def_WildeQIT_HSW_IsAchievableRate
-- name    : WildeQIT_HSW_IsAchievableRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T19:13:38.20649+00:00
-- url     : https://prove2.me/theorems/5fd7fc64-3131-4721-96c6-a65f7fc2ab05
-- title:
--   Achievable rate of classical communication over a quantum channel
-- statement:
--   A rate $C$ of classical communication is achievable for a quantum channel $\mathcal N$ if for all $\delta>0$ and $\varepsilon\in(0,1)$ there is an $n_0$ such that for every $n\ge n_0$ the channel has an $(n, C-\delta, \varepsilon)$ code: a code with $n$ channel uses, maximal error probability at most $\varepsilon$, and $|\mathcal M|\ge 1$ messages with
--
--   $$
--   \frac1n\log_2|\mathcal M| \ \ge\ C-\delta .
--   $$
--
--   The classical capacity is the supremum of the achievable rates.
--
--   **Formalization Note** The book's "$(n, C-\delta, \varepsilon)$ code" is read as a code of rate at least $C-\delta$: the number of messages is an integer, so the rate $C-\delta$ itself is in general not available, and removing messages from a code does not increase its maximal error. "Sufficiently large $n$" is an eventually-quantifier along the natural numbers.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §20.2.1, p. 562

import Mathlib
import Definitions.Def_WildeQIT_HSW_HasCode

namespace WildeQIT.HSW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §20.2.1, p. 562:
"A rate C of classical communication is achievable for a channel N if there exists an
(n, C − δ, ε) code for all δ > 0, ε ∈ (0, 1), and sufficiently large n."

**Formalization Note.** An `(n, C − δ, ε)` code is read as a code (`WildeQIT.HSW.HasCode`) with
`n` channel uses, `M ≥ 1` messages, maximal error at most `ε`, and rate
`(1/n) log₂ M ≥ C − δ` (the number of messages is an integer, so a rate of exactly `C − δ` is
in general not available; discarding messages of a code keeps its maximal error, so "at least"
loses nothing). "Sufficiently large n" is `∀ᶠ n in atTop`. -/
def IsAchievableRate {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : WildeQIT.QChannel A B) (C : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ᶠ n : ℕ in Filter.atTop, ∃ M : ℕ, 0 < M ∧ C - δ ≤ Real.logb 2 M / n ∧ HasCode N n M ε

end WildeQIT.HSW


