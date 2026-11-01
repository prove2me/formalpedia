-- Prove2me | Definitions.Def_LocalDOvS_SUS_IsPGS
-- name    : LocalDOvS_SUS_IsPGS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:28:58.935031+00:00
-- url     : https://prove2.me/theorems/aae56839-9b5a-42f6-abaa-bb346c87cfc0
-- title:
--   $(\epsilon,\delta)$-probability of good selection
-- statement:
--   An algorithm $A$ satisfies the **$(\epsilon,\delta)$-PGS guarantee** on a model $M$ over $X=[N]$ if
--
--   $$
--   P_M\Big(\tau_A=\infty\ \text{ or }\ \hat x\notin[N]\ \text{ or }\ f(\hat x)>\min_{x\in[N]}f(x)+\epsilon\Big)\le\delta ,
--   $$
--
--   where $\hat x$ is the solution returned. In words: with probability at least $1-\delta$ the algorithm returns a decision whose objective value is at most $\epsilon$ larger than the optimal one.
--
--   **Formalization Note** "$f(\hat x)\le\min f+\epsilon$" is written $f(\hat x)\le f(y)+\epsilon$ for all $y\in[N]$. The bound is on the outer measure of the failure set, so no measurability of $A$ is presupposed.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, §2.1, p.8

import Mathlib
import Definitions.Def_LocalDOvS_SUS_retPt
import Definitions.Def_LocalDOvS_SUS_meanFn
import Definitions.Def_LocalDOvS_SUS_tapeMeasure

open MeasureTheory

namespace LocalDOvS.SUS

/-- The `(ε, δ)`-probability of good selection (PGS) guarantee of algorithm `A` on model `M`
over `X = [N]` (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, §2.1, p.8: "The solution `x` returned
by an algorithm has an objective value at most `ε` larger than the optimal objective value with
probability at least `1 − δ`"). The failure event — the run does not stop, or it returns `x`
outside `[N]`, or `f(x) > f(y) + ε` for some `y ∈ [N]` — has probability at most `δ`.

**Formalization Note.** "at most `ε` larger than the optimal value" is written
`∀ y ∈ [N], f x ≤ f y + ε`, which avoids a minimum. The bound is on the outer measure of the
failure set, so no measurability of `A` is presupposed; for a measurable algorithm it is the
probability, and "probability at least `1 − δ` of success" is the same statement. -/
def IsPGS (N : ℕ) (ε δ : ℝ) (A : SeqAlg) (M : Model) : Prop :=
  tapeMeasure M {ω | ¬ (stopTime A ω ≠ ⊤ ∧ retPt A ω ∈ Finset.Icc 1 N ∧
      ∀ y ∈ Finset.Icc 1 N, meanFn M (retPt A ω) ≤ meanFn M y + ε)} ≤ ENNReal.ofReal δ

end LocalDOvS.SUS


