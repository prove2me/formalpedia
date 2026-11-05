-- Prove2me | Definitions.Def_CondBasedProd_Selection
-- name    : CondBasedProd_Selection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:50.674347+00:00
-- url     : https://prove2.me/theorems/dc2dabd7-35ec-4c05-90d2-52b487421bc2
-- title:
--   Measurable rate selections and their feedback policies
-- statement:
--   A **measurable rate selection** is a function $\sigma(y,t)$ with values in $\mathcal S$ for levels $y\le\xi$ and times to maintenance $t\ge0$, measurable in $t$. Its **feedback policy** from the state $(x,t)$ produces, at elapsed time $v$ after $j$ increments, at the rate $\sigma(x+j,\,t-v)$: the level is then $x+j$ and the time to maintenance is $t-v$.
--
--   **Formalization Note** Measurability is asked of $t\mapsto\sigma(y,\max(t,0))$, since $\sigma$ is constrained on $t\ge0$ only; the rate reads $\sigma$ at $\max(t-v,0)$, and is $0$ on the branch $x+j>\xi$, which is never in force.
-- source:
--   Drent, Drent & Arts, Condition-Based Production for Stochastically Deteriorating Systems, arXiv:2308.07507v2, p.10 (the rate $s^*_\lambda(x,t)$ for state $(x,t)$ and the induced policy)

import Mathlib
import Definitions.Def_CondBasedProd_Policy

open Set

namespace CondBasedProd

/-- A **measurable rate selection** `σ(x,t)` on `x ≤ ξ`, `t ≥ 0`, with values in `𝒮`. Here `t` is the
time to maintenance, as in the paper.

**Formalization Note.** Measurability is asked of `t ↦ σ(y, max(t, 0))`, since `σ` is constrained on
`t ≥ 0` only. -/
structure Selection (M : Model) where
  /-- The rate at level `y` with time to maintenance `t`. -/
  rate : ℕ → ℝ → ℝ
  mem : ∀ y ≤ M.ξ, ∀ t, 0 ≤ t → rate y t ∈ Icc 0 M.sbar
  measurable : ∀ y ≤ M.ξ, Measurable fun t => rate y (max t 0)

/-- The **feedback policy** of `σ` from the start state `(x,t)`: at elapsed time `v` after `j`
increments the level is `x + j` and the time to maintenance is `t − v`, so the rate is
`σ(x + j, max(t − v, 0))`. The branch `x + j > ξ` is never in force and exists only to keep the rate
in `𝒮`. -/
noncomputable def Selection.feedback {M : Model} (σ : Selection M) (x : ℕ) (t : ℝ) : Policy M where
  φ := fun j v _ => if x + j ≤ M.ξ then σ.rate (x + j) (max (t - v) 0) else 0
  measurable := fun j => by
    by_cases h : x + j ≤ M.ξ
    · simp only [h, if_true]
      exact (σ.measurable _ h).comp (measurable_const.sub measurable_fst)
    · simp only [h, if_false]
      exact measurable_const
  mem := fun j v _ => by
    by_cases h : x + j ≤ M.ξ
    · simp only [h, if_true]
      exact σ.mem _ h _ (le_max_right _ _)
    · simp only [h, if_false]
      exact ⟨le_rfl, M.sbar_pos.le⟩

end CondBasedProd


