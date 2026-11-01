-- Prove2me | Definitions.Def_LocalDOvS_SUS_Step
-- name    : LocalDOvS_SUS_Step
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:08.104252+00:00
-- url     : https://prove2.me/theorems/e1e1e351-7ffb-49ff-97fa-9e33345f0686
-- title:
--   A step of a sequential algorithm
-- statement:
--   At each point of its run, a simulation-optimization algorithm takes one **step**: either it simulates a decision $x$ once more, or it stops and returns a decision $x$ as its solution.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, §2.1–2.2, pp.9–10

import Mathlib

namespace LocalDOvS.SUS

/-- One decision of a sequential simulation-optimization algorithm (Zhang–Zheng–Lavaei,
arXiv:2012.02427v2, §2.1–2.2, pp.9–10): either simulate decision `x` once more, or stop and
return decision `x` as the solution. -/
inductive Step where
  /-- Simulate one more independent copy of `F(x, ξ_x)`. -/
  | sample (x : ℕ)
  /-- Stop and return `x`. -/
  | stop (x : ℕ)

end LocalDOvS.SUS


