-- Prove2me | Definitions.Def_LocalDOvS_SUS_Model
-- name    : LocalDOvS_SUS_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:10.277357+00:00
-- url     : https://prove2.me/theorems/adf570e6-7af4-466a-88c4-4689ee93152c
-- title:
--   Simulation model (laws of the outputs)
-- statement:
--   A **simulation model** specifies, for every decision $x$, a probability law $\nu_x$ on $\mathbb R$: the law of one simulation output $F(x,\xi_x)$.
--
--   The paper describes a model as a triad of the decision space $X$, a probability space $(\mathcal Y,\mathcal B_{\mathcal Y})$ for the randomness $\xi_x$ and a measurable function $F$. A simulation-optimization algorithm only observes outputs, so it sees a model only through these laws, and independent replications are modelled by an independent product of them (see the tape).
--
--   **Formalization Note** Decisions are natural numbers; only $x\in[N]$ is ever simulated by the algorithms of the mission, so the laws at other $x$ are an unused parameter.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, §2, pp.8–9

import Mathlib

open MeasureTheory

namespace LocalDOvS.SUS

/-- A simulation model (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, §2, pp.8–9: the triad of the
decision space, the space of randomness `(Y, B_Y)` and the function `F`), given by what an
algorithm can observe: for each decision `x`, the law `law x` on `ℝ` of one simulation output
`F(x, ξ_x)`.

**Formalization Note.** Decisions are natural numbers; only `x ∈ [N] = {1, …, N}` are ever
simulated by the algorithms of this mission (`IsValidAlg`), so the laws at other `x` are an
unused parameter. Every law is a probability measure. Replacing `(Y, B_Y, F)` by the laws of the
outputs changes nothing an algorithm can see: independent replications are modelled by the
product tape `tapeMeasure`. -/
structure Model where
  /-- The law of one simulation output `F(x, ξ_x)` at decision `x`. -/
  law : ℕ → Measure ℝ
  /-- Each output law is a probability measure. -/
  isProb : ∀ x, IsProbabilityMeasure (law x)

end LocalDOvS.SUS


