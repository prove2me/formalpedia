-- Prove2me | Definitions.Def_LocalDOvS_SUS_stopTime
-- name    : LocalDOvS_SUS_stopTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:45.091986+00:00
-- url     : https://prove2.me/theorems/3b66a0f7-8f50-4ae1-96c5-fe53f362486f
-- title:
--   Simulation cost $\tau_A$ of a run
-- statement:
--   The **simulation cost** $\tau_A(\omega)\in\mathbb N\cup\{\infty\}$ of a run of $A$ on tape $\omega$ is the first time $t$ at which $A$ stops; each step before it is one simulation, so $\tau_A$ is the number of evaluations of $F(\cdot,\cdot)$. A run that never stops has $\tau_A=\infty$.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Definition 2, p.10

import Mathlib
import Definitions.Def_LocalDOvS_SUS_histAt

namespace LocalDOvS.SUS

/-- The simulation cost `τ_A` of a run (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, Definition 2,
p.10: "the number of simulation evaluations of `F(·,·)` for each implementation of algorithm
`A`"): the first time `t` at which `A` stops. Every step before it is one evaluation, so `τ` is
the number of evaluations.

**Formalization Note.** Valued in `ℕ∞`; a run that never stops has `τ = ⊤` (the infimum of the
empty set), never a junk finite value. -/
noncomputable def stopTime (A : SeqAlg) (ω : ℕ × ℕ → ℝ) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : ∃ x, A (histAt A ω t) = Step.stop x), (t : ℕ∞)

end LocalDOvS.SUS


