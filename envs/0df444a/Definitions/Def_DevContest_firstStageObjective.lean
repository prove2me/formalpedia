-- Prove2me | Definitions.Def_DevContest_firstStageObjective
-- name    : DevContest_firstStageObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:40.346192+00:00
-- url     : https://prove2.me/theorems/cdd5df2c-2b36-4588-9564-7ac4f964307a
-- title:
--   The objective of the first-stage problem (EC.39)
-- statement:
--   An **effort path** is a measurable function on $[0,\infty)$ with values in $[0,1]$. For a continuation payoff $V_1$, a belief $p$, rival efforts $x_1,x_0$ and a disclosure probability $\phi$, the payoff from date $t$ of an agent with no success who exerts $x$ is
--   $$
--   \int_t^\infty x_\tau(\lambda V_{1,\tau}-c)\,\exp\Bigl(-\int_t^\tau\bigl[x_s\lambda+p_sx_{1,s}\lambda+(1-p_s)x_{0,s}\lambda\phi_s\bigr]ds\Bigr)d\tau ,
--   $$
--   which is the objective in (EC.39). The bracket is the agent's own success rate plus the rate at which the rival's completion or a disclosure ends her first-stage problem.
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, display (EC.39), p.ec17

import Mathlib

open MeasureTheory

namespace DevContest

/-- An effort path on `[0,∞)`: measurable, with values in `[0,1]` at every `t ≥ 0`. -/
def IsEffort (x : ℝ → ℝ) : Prop := Measurable x ∧ ∀ t, 0 ≤ t → x t ∈ Set.Icc (0 : ℝ) 1

/-- The objective in display (EC.39), Khorasani, Körpeoğlu, Krishnan, *Dynamic Development Contests*,
author manuscript, p.ec17: the continuation payoff from `t` of an agent with no success who exerts
`x`, with continuation payoff `V1 τ` upon a first success at `τ`, belief `p`, rival efforts `x1`
(second stage) and `x0` (first stage), and disclosure probability `φ`:
`∫_t^∞ x_τ (λ V1_τ - c) exp(-∫_t^τ [x_s λ + p_s x1_s λ + (1-p_s) x0_s λ φ_s] ds) dτ`. -/
noncomputable def firstStageObjective (lam c : ℝ) (V1 p x1 x0 φ x : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in Set.Ioi t, x τ * (lam * V1 τ - c) *
    Real.exp (-∫ s in t..τ, (x s * lam + p s * x1 s * lam + (1 - p s) * x0 s * lam * φ s))

end DevContest


