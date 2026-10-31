-- Prove2me | Definitions.Def_DynTargetMV_reachableStates
-- name    : DynTargetMV_reachableStates
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:14.566411+00:00
-- url     : https://prove2.me/theorems/4176fb75-2b2a-4d1f-840d-23ef36f5503f
-- title:
--   The set $\mathbb X_t$ of reachable states
-- statement:
--   For a real random variable $X_t$ with law $\mu$, the set of reachable states is the union of the interior of the support of $\mu$ and the set of atoms of $\mu$. Applied to the wealth $X^{\hat\pi}(t)$ this is the set $\mathbb X_t$ of p.8, the wealth levels at which Definition 1 tests the agent's time-$t$ self.
--
--   **Formalization Note** The support is Mathlib's `Measure.support`. The source conditions on the information at time 0. The solution from the deterministic $x_0$ carries no dependence on it, so the law under $P$ is used.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, p.8

import Mathlib

open MeasureTheory

namespace DynTargetMV

/-- The set of **reachable states** of a random wealth `Xt`: the union of the interior of the support
and the atoms of its distribution. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, p.8 (the set 𝕏_t).

**Formalization Note** Applied to `X^π̂(t)`, which is `F t`-measurable, so `Measure.map` is the law. The
source conditions on the information at time 0, which carries no information about the strong solution
from a deterministic start, so the unconditional law is used. -/
def reachableStates {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Xt : Ω → ℝ) : Set ℝ :=
  interior (P.map Xt).support ∪ {x | P.map Xt {x} ≠ 0}

end DynTargetMV


