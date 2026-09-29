-- Prove2me | Definitions.Def_CycleCanceling_MinMean_Algorithm
-- name    : CycleCanceling_MinMean_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:10:32.824481+00:00
-- url     : https://prove2.me/theorems/68dcbc5b-4c7b-4361-935c-662f03c520a3
-- title:
--   Cycle capacity, canceling a cycle, and runs of the minimum-mean cycle-canceling algorithm
-- statement:
--   This file encodes Klein's cycle-canceling algorithm with Goldberg and Tarjan's minimum-mean selection rule.
--
--   1. The **capacity** of a residual cycle $\Gamma$ of a circulation $f$ is $\delta=\min_{(v,w)\in\Gamma}u_f(v,w)$, which is positive.
--   2. **Canceling** $\Gamma$ increases the flow on each arc of $\Gamma$ by $\delta$ and, to keep antisymmetry, decreases the flow on the reverse of each arc of $\Gamma$ by $\delta$:
--   $$
--   f'(v,w)=f(v,w)+\delta\cdot\#\{\text{occurrences of }(v,w)\text{ on }\Gamma\}-\delta\cdot\#\{\text{occurrences of }(w,v)\text{ on }\Gamma\}.
--   $$
--   3. One **minimum-mean iteration** takes $f$ to $f'$ if there is a residual cycle $\Gamma$ of $f$ whose mean cost is minimum among *all* residual cycles of $f$, whose cost is negative, and $f'$ is obtained from $f$ by canceling $\Gamma$. Ties between minimum-mean cycles are broken arbitrarily.
--   4. A **run of $K$ iterations** is a sequence $f_0,f_1,\dots,f_K$ in which $f_0$ is a circulation and each $f_{i+1}$ arises from $f_i$ by one minimum-mean iteration.
--
--   The algorithm stops exactly when no negative residual cycle is left, so "the algorithm terminates after at most $B$ iterations" means that every run has $K\le B$.
--
--   **Formalization Note** A run is a sequence `F : ℕ → V → V → ℝ` together with its length `K`; values `F i` for `i > K` are unconstrained. For a simple cycle with at least three arcs, canceling changes the flow by $+\delta$ on each arc of $\Gamma$ and by $-\delta$ on each reverse arc, exactly as in the paper; on one- and two-vertex cycles the update is the identity, but such cycles have cost $0$ and are never canceled.
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, p. 876, Section 2 (cycle-canceling algorithm, minimum-mean selection) and p. 879

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network

namespace CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The capacity of a residual cycle (p. 876): the minimum of the residual capacities
`u_f(v, w)` of its arcs. (The value `0` on the empty list is never used: residual cycles are
nonempty.) -/
def cycleCap (N : CircNetwork V) (f : V → V → ℝ) (Γ : List V) : ℝ :=
  match cycleArcs Γ with
  | [] => 0
  | a :: l => l.foldr (fun b acc => min (resCap N f b.1 b.2) acc) (resCap N f a.1 a.2)

/-- Canceling a cycle `Γ` (p. 876): increase the flow on each arc of `Γ` by the capacity `δ` of
`Γ`, and (to keep antisymmetry) decrease the flow on the reverse of each arc of `Γ` by `δ`:
`f'(v, w) = f(v, w) + δ·#{(v, w) on Γ} - δ·#{(w, v) on Γ}`. -/
def cancel (N : CircNetwork V) (f : V → V → ℝ) (Γ : List V) : V → V → ℝ :=
  fun v w => f v w + cycleCap N f Γ * ((cycleArcs Γ).count (v, w) : ℝ)
    - cycleCap N f Γ * ((cycleArcs Γ).count (w, v) : ℝ)

/-- One iteration of the minimum-mean cycle-canceling algorithm (pp. 876, 879): some residual
cycle `Γ` of `f` of minimum mean cost among all residual cycles of `f` has negative cost, and
`f' ` is obtained from `f` by canceling `Γ`. Ties are broken arbitrarily. -/
def IsMinMeanStep (N : CircNetwork V) (f f' : V → V → ℝ) : Prop :=
  ∃ Γ, IsMinMeanResidualCycle N f Γ ∧ cycleCost N Γ < 0 ∧ f' = cancel N f Γ

/-- A run of `K` iterations of the minimum-mean cycle-canceling algorithm: `F 0` is a
circulation and `F (i+1)` arises from `F i` by one minimum-mean cancellation, for every `i < K`. -/
def IsMinMeanRun (N : CircNetwork V) (F : ℕ → V → V → ℝ) (K : ℕ) : Prop :=
  IsCirculation N (F 0) ∧ ∀ i < K, IsMinMeanStep N (F i) (F (i + 1))

end CycleCanceling.MinMean


