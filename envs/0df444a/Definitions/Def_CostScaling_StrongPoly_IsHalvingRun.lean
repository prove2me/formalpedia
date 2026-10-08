-- Prove2me | Definitions.Def_CostScaling_StrongPoly_IsHalvingRun
-- name    : CostScaling_StrongPoly_IsHalvingRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:02:30.556158+00:00
-- url     : https://prove2.me/theorems/797c8418-6d52-49a0-92eb-3bde6d693dab
-- title:
--   Figure 3 — the circulation-level contract of the strongly polynomial loop
-- statement:
--   Let $f_0,f_1,\ldots$ be a sequence of flows in one circulation network, and let $ε(f_k)$ be the least error parameter at which $f_k$ is ε-optimal. It is a **halving run** when $f_0$ is a circulation and every positive-error step returns a circulation optimal at half the current tight error:
--
--   $$
--   ε(f_k)>0\quad\Longrightarrow\quad f_{k+1}\text{ is }\frac{ε(f_k)}2\text{-optimal}\qquad(k\ge0).
--   $$
--
--   This captures the part of each call to `refine` that Theorem 4.5 uses. At $ε(f_k)=0$ the loop returns, so later terms of the sequence carry no constraint.
--
--   **Formalization Note** The error parameter is computed from $f_k$ and is never a free sequence. Figure 3 also computes a price function; its existence is absorbed into ε-optimality. The reused reduced-cost convention is equivalent after $p\mapsto-p$.
-- source:
--   Goldberg & Tarjan, MIT/LCS/TM-333 (July 1987), Section 4.1, p. 13, refine contract; Section 4.2, Fig. 3, p. 15

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

namespace CostScaling.StrongPoly

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The circulation-level contract of successive calls to `refine` in Figure 3,
p. 15. The initial state is a circulation. At a positive tight error parameter
`epsOpt N (f k)`, the next state is optimal at half that parameter. After a zero
parameter the loop has returned and imposes no condition on later states. -/
def IsHalvingRun (N : CircNetwork V) (f : ℕ → V → V → ℝ) : Prop :=
  IsCirculation N (f 0) ∧
  ∀ k : ℕ, 0 < epsOpt N (f k) →
    IsEpsOptimal N (f (k + 1)) (epsOpt N (f k) / 2)

end CostScaling.StrongPoly


