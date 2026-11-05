-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_stepKernel
-- name    : BauerleRiederMDP_FiniteHorizon_stepKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:11.78761+00:00
-- url     : https://prove2.me/theorems/42c5c28b-338b-4c52-bf12-529567373156
-- title:
--   One transition of the controlled process
-- statement:
--   Let $h$ be a path of $j$ transitions with last state $x$, let $f$ be a measurable function of the path with values in $A$, and let $m$ be a calendar time. The one-step kernel sends $h$ to the law of $(h,f(h),X')$, where $X'\sim Q_m(\cdot\mid x,f(h))$.
--
--   This is property (ii) of the measure $\mathbb P^\pi_x$ of the book, written for paths that record states and actions.
--
--   **Formalization Note.** A path of $j$ transitions is an element of the history space $H_j$. The numbers $m$ and $j$ differ for a path started from a state at a time $n>0$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.17 (ii) and p.18

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel Hist histState measurable_histState)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- One transition of the controlled process (Bäuerle & Rieder (2011), p.17, PDF 32, property
(ii) of `ℙ^π_x`; p.18, PDF 33, for histories). A path `h` of `j` transitions is extended by the
action `f h` and a next state drawn from `Q_m(· | x, f h)`, where `x` is the last state of `h` and
`m` is the calendar time of the transition: the result is the law of `(h, f h, X')`.

**Formalization Note.** A path of `j` transitions is an element of the history space
`H_j = Hist E A j`, so states and actions are both recorded. `m` and `j` are separate because a
path started at time `n` from a state has `j = m - n`, while a path continued from a full history
has `j = m`. -/
noncomputable def stepKernel {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (m j : ℕ) (f : Hist E A j → A) (hf : Measurable f) :
    Kernel (Hist E A j) (Hist E A (j + 1)) :=
  (Kernel.id ×ₖ (M.Q m).comap (fun h => (histState j h, f h))
    ((measurable_histState j).prodMk hf)).map
      (fun p : Hist E A j × E => ((p.1, f p.1, p.2) : Hist E A j × A × E))

end BauerleRiederMDP.FiniteHorizon


