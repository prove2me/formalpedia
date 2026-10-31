-- Prove2me | Definitions.Def_AccelNewtonDinkelbach_IsRun
-- name    : AccelNewtonDinkelbach_IsRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:42.541987+00:00
-- url     : https://prove2.me/theorems/d8072e55-f815-4e97-ad13-8e686b634b49
-- title:
--   A run $\delta^{(1)},\dots,\delta^{(N)}$ of a Newton–Dinkelbach-type method
-- statement:
--   Fix a one-iteration relation (Algorithm 1's step or the relaxed step). A **run** with $N\ge1$ iterates consists of points $\delta^{(1)},\dots,\delta^{(N)}$ and supergradients $g^{(1)},\dots,g^{(N)}$ such that
--
--   1. the input is valid: $\delta^{(1)}\in\operatorname{dom}(f)$, $f(\delta^{(1)})\le 0$, $g^{(1)}\in\partial f(\delta^{(1)})$ and $g^{(1)}<0$;
--   2. for every $1\le i<N$, the pair $(\delta^{(i+1)},g^{(i+1)})$ is produced from $(\delta^{(i)},g^{(i)})$ by one iteration.
--
--   The run need not be complete: it may stop before the algorithm returns, so a statement about all runs covers every iterate the algorithm ever produces, including its last one.
--
--   **Formalization Note** Iterates are indexed from $1$, as in the paper; the values at index $0$ and beyond $N$ are ignored.
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, §3, p.6 and Algorithm 1 (input and line 11), p.7

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_superdiff

namespace AccelNewtonDinkelbach

/-- **A (prefix of a) run of a Newton–Dinkelbach-type method, iterates `δ(1), …, δ(N)`.**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, §3, p.6 and Algorithm 1, p.7: "The algorithm takes
as input an initial point δ(1) ∈ dom(f) and a supergradient g(1) ∈ ∂f(δ(1)) such that f(δ(1)) ≤ 0
and g(1) < 0", and line 11 "δ(i+1) ← δ, g(i+1) ← g".

`IsRun step dom f δ g N` says that `1 ≤ N`; the input satisfies `δ 1 ∈ dom`, `f (δ 1) ≤ 0`,
`g 1 ∈ ∂f(δ 1)` and `g 1 < 0`; and for every `1 ≤ i < N`, the pair `(δ (i+1), g (i+1))` is produced
from `(δ i, g i)` by one iteration `step`. With `step = LookAheadStep dom f` these are the runs of
Algorithm 1; with `step = RelaxedStep dom f` they include the standard method and Algorithm 1.

**Formalization Note** Iterates are 1-indexed, as on the page; the values `δ 0`, `g 0` and those
beyond `N` are ignored. The run need not be maximal: it may stop before the algorithm returns, so
statements about runs cover every iterate the algorithm produces, including the last one. -/
def IsRun (step : ℝ → ℝ → ℝ → ℝ → Prop) (dom : Set ℝ) (f : ℝ → ℝ) (δ g : ℕ → ℝ) (N : ℕ) :
    Prop :=
  1 ≤ N ∧ δ 1 ∈ dom ∧ f (δ 1) ≤ 0 ∧ g 1 ∈ superdiff dom f (δ 1) ∧ g 1 < 0 ∧
    ∀ i : ℕ, 1 ≤ i → i < N → step (δ i) (g i) (δ (i + 1)) (g (i + 1))

end AccelNewtonDinkelbach


