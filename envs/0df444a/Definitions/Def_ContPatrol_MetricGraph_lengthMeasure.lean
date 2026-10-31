-- Prove2me | Definitions.Def_ContPatrol_MetricGraph_lengthMeasure
-- name    : ContPatrol_MetricGraph_lengthMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:11:46.765629+00:00
-- url     : https://prove2.me/theorems/e3819abe-7fd8-4c43-bd68-697e7993cdac
-- title:
--   Length measure $\lambda$ and total length $\mu$
-- statement:
--   The **length** $\lambda$ is the measure on $Q$ that is Lebesgue measure on each open edge $(0,\lambda(e))$ and gives vertices measure zero. The **total length** of $Q$ is
--   $$\mu=\sum_{e}\lambda(e)=\lambda(Q).$$
--
--   The uniform attack strategy picks the attacked point according to $\lambda/\mu$, and $\mu$ appears in every value formula of the paper.
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, §3, pp.4–5

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_Point

namespace ContPatrol

namespace MetricGraph

open MeasureTheory

variable {V E : Type}

/-- **The length measure λ on Q and the total length µ.**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, §3, pp.4–5:
"We can then identify an edge e with an open interval of length λ(e), endowed with Lebesgue
measure ... and consider λ as a measure on Q, called length. The total length of Q is denoted by
µ = λ(Q)."

`G.lengthMeasure` is the sum over the edges `e` of Lebesgue measure on the open interval
`(0, λ(e))`, carried onto the edge; vertices have measure zero. -/
noncomputable def lengthMeasure (G : MetricGraph V E) : Measure G.Point :=
  Measure.sum fun e : E =>
    ((volume : Measure ℝ).comap (Subtype.val : Set.Ioo (0 : ℝ) (G.len e) → ℝ)).map
      (fun s => (Sum.inr ⟨e, s⟩ : G.Point))

/-- The total length `µ = Σ_e λ(e)` of the network (equal to `λ(Q)`). -/
def totalLength [Fintype E] (G : MetricGraph V E) : ℝ := ∑ e, G.len e

end MetricGraph

end ContPatrol


