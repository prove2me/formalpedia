-- Prove2me | Definitions.Def_NisanRonen_Rounding_makespan
-- name    : NisanRonen_Rounding_makespan
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:15:45.014106+00:00
-- url     : https://prove2.me/theorems/2c6c1ea3-96bb-462a-b41c-da3cd57c63da
-- title:
--   Make-span $g(x, \tilde t)$
-- statement:
--   For an allocation $x$ of $k$ tasks to $n \ge 1$ agents and a vector $\tau$ of times, the **make-span** is the largest load:
--
--   $$
--   g(x, \tau) = \max_{1 \le i \le n} \sum_{j \in x^i} \tau_j .
--   $$
--
--   It is the objective function of the task scheduling problem with verification, evaluated at the actual times $\tilde t$. For a type matrix $t = (t^i_j)$ the make-span of $x$ at the true times is $g(x, \mathrm{corr}^*(x, t))$, where $\mathrm{corr}^*(x,t)_j = t^i_j$ for $j \in x^i$.
--
--   **Formalization Note** The maximum is a `Finset.sup'` over the agents, which requires at least one agent (`[NeZero n]`). With no tasks every load and the make-span are $0$.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, Definition 20, p. 187 (PDF p. 22): "The objective function is g(x, t̃) = max_i Σ_{j∈x^i} t̃_j (the make-span)"

import Mathlib
import Definitions.Def_NisanRonen_Rounding_load

namespace NisanRonen.Rounding

/-- **Make-span** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), Definition 20, p. 187: "The objective function is
`g(x, t̃) = max_i Σ_{j ∈ x^i} t̃_j` (the make-span)"). `makespan x τ = max_i load x τ i`.
The matrix form `g(y, t)` of the paper (p. 192) is `makespan y (corrStar y t)`.

**Formalization Note** The maximum is `Finset.sup'` over the nonempty set of agents, which needs
`[NeZero n]` (at least one agent). With no tasks (`k = 0`) every load is `0` and so is the
make-span. -/
noncomputable def makespan {n k : ℕ} [NeZero n] (x : Fin k → Fin n) (τ : Fin k → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (load x τ)

end NisanRonen.Rounding


