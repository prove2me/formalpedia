-- Prove2me | Definitions.Def_LocalDOvS_SUS_actSet
-- name    : LocalDOvS_SUS_actSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:47.77698+00:00
-- url     : https://prove2.me/theorems/9af0e1a9-6de6-495d-9584-363095e140cd
-- title:
--   Active set $S_k$
-- statement:
--   The active set of a state, $S_k=\{x_0+j\,s : 0\le j<M\}$: the decisions that may still be returned.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Algorithm 2, p.15

import Mathlib
import Definitions.Def_LocalDOvS_SUS_SUSState

namespace LocalDOvS.SUS

/-- The active set `S_k = {x0 + j · s : j < M}` of a state of the shrinking uniform sampling
algorithm (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, Algorithm 2, p.15). -/
def actSet (st : SUSState) : Finset ℕ :=
  (Finset.range st.M).image (fun j => st.x0 + j * st.s)

end LocalDOvS.SUS


