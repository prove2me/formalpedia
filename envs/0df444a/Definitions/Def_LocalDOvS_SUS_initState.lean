-- Prove2me | Definitions.Def_LocalDOvS_SUS_initState
-- name    : LocalDOvS_SUS_initState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:52.274171+00:00
-- url     : https://prove2.me/theorems/69b436f7-5156-432b-9fe2-fbad475e2746
-- title:
--   Initial state of the algorithm
-- statement:
--   The initial state of the shrinking uniform sampling algorithm: $k=1$, $S_1=X=[N]$ (so $x_0=1$, $M=N$), step size $s=1$, bounds $x_{L,1}=1$, $x_{U,1}=N$, and no simulation made.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Algorithm 2, lines 1–2, p.15; p.ec14

import Mathlib
import Definitions.Def_LocalDOvS_SUS_SUSState

namespace LocalDOvS.SUS

/-- The initial state of the shrinking uniform sampling algorithm (Zhang–Zheng–Lavaei,
arXiv:2012.02427v2, Algorithm 2, lines 1–2, p.15, and p.ec14): `k = 1`, `S_1 = X = [N]`, step
size `s = 1`, `x_{L,1} = 1`, `x_{U,1} = N`, and no simulation made. -/
def initState (N : ℕ) : SUSState where
  k := 1
  x0 := 1
  s := 1
  M := N
  xL := 1
  xU := N
  cnt := fun _ => 0

end LocalDOvS.SUS


