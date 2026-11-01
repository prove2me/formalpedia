-- Prove2me | Definitions.Def_LocalDOvS_SUS_IsMeasurableAlg
-- name    : LocalDOvS_SUS_IsMeasurableAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:25:55.938592+00:00
-- url     : https://prove2.me/theorems/d9b91341-980e-4a3c-957c-bfe871951133
-- title:
--   Measurable sequential algorithm
-- statement:
--   A sequential algorithm is **measurable** if, for every number $k$ of evaluations, every sequence $x_1,\dots,x_k$ of simulated decisions and every step $a$, the set of output vectors $(v_1,\dots,v_k)\in\mathbb R^k$ after which the algorithm takes step $a$ is a Borel set.
--
--   Then the history, the simulation cost and the returned solution of a run are measurable functions of the tape, so that $\tau_A$ is a random variable as Definition 2 requires.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Definition 2, p.10

import Mathlib
import Definitions.Def_LocalDOvS_SUS_SeqAlg

namespace LocalDOvS.SUS

/-- Measurability of a sequential algorithm (Zhang–Zheng–Lavaei, arXiv:2012.02427v2,
Definition 2, p.10, where `τ_A` is "a random variable"): for every number `k` of evaluations,
every sequence of simulated decisions `ps`, and every step `a`, the set of observed output
vectors `v ∈ ℝ^k` on which `A` answers `a` is Borel.

**Formalization Note.** This makes the history, the stopping time and the returned solution of
every run measurable functions of the tape. -/
def IsMeasurableAlg (A : SeqAlg) : Prop :=
  ∀ (k : ℕ) (ps : Fin k → ℕ) (a : Step),
    MeasurableSet {v : Fin k → ℝ | A (List.ofFn fun i => (ps i, v i)) = a}

end LocalDOvS.SUS


