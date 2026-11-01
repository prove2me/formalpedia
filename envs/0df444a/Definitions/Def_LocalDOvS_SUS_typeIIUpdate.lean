-- Prove2me | Definitions.Def_LocalDOvS_SUS_typeIIUpdate
-- name    : LocalDOvS_SUS_typeIIUpdate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:52.390712+00:00
-- url     : https://prove2.me/theorems/9aace812-b448-4107-8351-c8fbb02c289d
-- title:
--   Type-II Operation
-- statement:
--   The **Type-II Operation**: double the step size, $s\leftarrow 2s$, and keep every other active point,
--
--   $$
--   S\leftarrow\{x_{\min},x_{\min}+s,\dots,x_{\min}+ks\},\qquad x_{\min}=\min S,\ k=\lceil |S|/2\rceil-1,
--   $$
--
--   with the new $s$; the new active set has $\lceil M/2\rceil$ points. The bounds $x_L,x_U$ are unchanged.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Algorithm 2, lines 17–19, p.15

import Mathlib
import Definitions.Def_LocalDOvS_SUS_SUSState

namespace LocalDOvS.SUS

/-- The Type-II Operation (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, Algorithm 2, lines 17–19,
p.15): `s ← 2s` and `S ← {x_min, x_min + s, …, x_min + k s}` with the new `s`,
`x_min = min S` and `k = ⌈|S|/2⌉ − 1`; i.e. the new active set has `⌈M/2⌉` points.

**Formalization Note.** `⌈M/2⌉` is `(M + 1) / 2` in natural-number division. The bounds
`x_L`, `x_U` are unchanged (p.ec14). -/
def typeIIUpdate (st : SUSState) : SUSState :=
  { st with k := st.k + 1, s := 2 * st.s, M := (st.M + 1) / 2 }

end LocalDOvS.SUS


