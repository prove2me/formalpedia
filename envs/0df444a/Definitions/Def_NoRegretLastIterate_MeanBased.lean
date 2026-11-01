-- Prove2me | Definitions.Def_NoRegretLastIterate_MeanBased
-- name    : NoRegretLastIterate_MeanBased
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:03.168312+00:00
-- url     : https://prove2.me/theorems/b0431c0c-6cf5-4b2c-8889-404b963bf833
-- title:
--   Definitions 2.4 and 2.5 — monotonic mean-based strategies
-- statement:
--   Let $\widehat Q_{t}=\frac1t\sum_{s=1}^{t}J_s$ be the empirical frequency of action 1 in player 2's first $t$ actions. A strategy of player 1 is **mean-based** (Definition 2.4) if it is given by maps $f_t:[0,1]\to[0,1]$ with
--   $$
--   P_t=f_t\big(\widehat Q_{t-1}\big),
--   $$
--   i.e. the opponent's empirical average is a sufficient statistic. It is **monotonic** (Definition 2.5) if for every $t\ge1$ the map $f_t$ is non-increasing or non-decreasing; the direction may differ from round to round. Player 2's mean-based strategies $g_t$ act on player 1's average $\widehat P_{t-1}$. Online-mirror-descent algorithms such as multiplicative weights with step size $1/\sqrt t$ are monotonic mean-based strategies.
--
--   This file also turns a mean-based strategy into the self-agnostic strategy $J\mapsto f_t(\widehat Q_{t-1}(J))$ to which the regret notions apply.
--
--   **Formalization Note** Lean round $n$ is paper round $n+1$, so `meanBased f n h = f n (Q̂_n)` with $\widehat Q_n$ the average of the $n$ past actions $h$. The empty average used in round 1 is $\widehat Q_0:=0$ (Lean's $0/0$); the paper leaves it undefined, and it only fixes the value $f_1(0)$ played in round 1. Monotonicity and the range condition are required on $[0,1]$.
-- source:
--   Muthukumar, Phade, Sahai, On the Impossibility of Convergence of Mixed Strategies with Optimal No-Regret Learning, arXiv:2012.02125v3, Definition 2.4 p.7, Definition 2.5 p.7

import Mathlib
import Definitions.Def_NoRegretLastIterate_Strategy

namespace NoRegretLastIterate

/-- arXiv:2012.02125v3, §2, p.5: the empirical average `Q̂ = (1/n) Σ_s J_s` of a history of `n`
actions (the frequency of action 1).

**Formalization Note** The paper never defines the empty average used in round 1; Lean's
`0 / 0 = 0` gives `Q̂_0 := 0`. This only fixes which value of `f_1` is played in round 1. -/
noncomputable def empAvg (n : ℕ) (h : Fin n → Fin 2) : ℝ :=
  (∑ k, bit (h k)) / n

/-- arXiv:2012.02125v3, Definition 2.4, p.7: the self-agnostic strategy induced by a *mean-based*
strategy `f`: in round `t` the player plays `P_t = f_t(Q̂_{t−1})`, a function of the opponent's
empirical average only.

**Formalization Note** Lean round `n` is paper round `n + 1`: `meanBased f n h = f n (Q̂_n)`,
where `Q̂_n` is the average of the `n` past opponent actions `h`. -/
noncomputable def meanBased (f : ℕ → ℝ → ℝ) : (n : ℕ) → (Fin n → Fin 2) → ℝ :=
  fun n h => f n (empAvg n h)

/-- arXiv:2012.02125v3, Definitions 2.4 and 2.5, p.7: `f` is a *monotonic mean-based* strategy:
every `f_t` maps `[0, 1]` into `[0, 1]`, and for every `t` the map `f_t` is non-increasing or
non-decreasing on `[0, 1]`. The direction may change from round to round ("does not require the
direction of the monotonicity to be the same across rounds", p.7). -/
def IsMonotonicMeanBased (f : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, ∀ x ∈ Set.Icc (0 : ℝ) 1, f n x ∈ Set.Icc (0 : ℝ) 1) ∧
  ∀ n, MonotoneOn (f n) (Set.Icc (0 : ℝ) 1) ∨ AntitoneOn (f n) (Set.Icc (0 : ℝ) 1)

end NoRegretLastIterate


