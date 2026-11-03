-- Prove2me | Definitions.Def_StaticCalendar_period
-- name    : StaticCalendar_period
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:03.833057+00:00
-- url     : https://prove2.me/theorems/d81bcd66-478d-4bf8-8324-4dd6e7504d7e
-- title:
--   One period of Algorithm 1
-- statement:
--   The joint law of the pair (assortment, demand) in one period of Algorithm 1 run on $x$: the assortment equals $S$ with probability $x(S)$, and given $S$ the demand has law $D_S$. For feasible $x$ this is a probability measure.
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Algorithm 1, p.14

import Mathlib
import Definitions.Def_StaticCalendar_DemandModel

open MeasureTheory

namespace StaticCalendar

/-- The law of one period of Algorithm 1, arXiv:1811.01077v5, p.14: the assortment is `S` with
probability `x(S)`, and given `S` the demand has law `D S`.

**Formalization Note.** A finite mixture of the laws of `(S, Q)`, `Q ∼ D S`. It is a probability
measure when `x` is feasible. `Prod.mk S` is measurable. -/
noncomputable def period {n m : ℕ} (I : DemandModel n m) (x : Assortment n m → ℝ) :
    Measure (Assortment n m × Demand n m) :=
  ∑ S ∈ I.family, ENNReal.ofReal (x S) • (I.D S).map (Prod.mk S)

end StaticCalendar


