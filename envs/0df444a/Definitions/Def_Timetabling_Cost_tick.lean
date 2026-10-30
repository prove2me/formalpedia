-- Prove2me | Definitions.Def_Timetabling_Cost_tick
-- name    : Timetabling_Cost_tick
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:26:50.858035+00:00
-- url     : https://prove2.me/theorems/a9839934-a62b-4dda-b617-54645e00f65a
-- title:
--   One tick of running time (unit-cost model)
-- statement:
--   The algorithms of this mission are programs in a state monad whose state is a **tick counter** $s \in \mathbb{N}$, started at $0$. The primitive $\mathsf{tick}$ increases the counter by one:
--
--   $$
--   \mathsf{tick} : s \mapsto s + 1 .
--   $$
--
--   The **running time** of a run is the final value of the counter. Every algorithm of the mission follows one convention: input data are read only through ticked accessors (one tick per read), every iteration of every loop and every recursive call ticks once, and the unticked code between two ticks does only $O(1)$ work on the algorithm's own state. Under this convention the counter measures time in the unit-cost RAM model, which is how the $O(n^2)$ bound of Proposition 2.4 is made precise.
--
--   **Formalization Note** The monad is `StateM ℕ` and `tick` is `modify (· + 1)`.
-- source:
--   de Werra (1985), Proposition 2.4, p. 154, and Remark, p. 155 ("there is an O(n^2) algorithm"). D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib

namespace Timetabling.Cost

/-- **One unit of running time.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), Proposition 2.4, p. 154, and the
Remark, p. 155: "there is an O(n^2) algorithm".

Algorithms of this mission are programs in the state monad `StateM ℕ`, whose state is a tick
counter started at `0`. `tick` adds one to the counter. The time of a run is the final value of
the counter.

**Formalization Note.** This is the unit-cost RAM model. The convention, binding on every
algorithm of the mission: input data are read only through ticked accessors (one tick per read),
every iteration of every loop and every recursive call ticks once, and the pure (unticked) code
between two ticks does only `O(1)` work on the algorithm's own state. -/
def tick : StateM ℕ Unit := modify (· + 1)

end Timetabling.Cost


