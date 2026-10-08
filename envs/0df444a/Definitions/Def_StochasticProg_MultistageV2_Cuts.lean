-- Prove2me | Definitions.Def_StochasticProg_MultistageV2_Cuts
-- name    : StochasticProg_MultistageV2_Cuts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:41:35.909087+00:00
-- url     : https://prove2.me/theorems/ade89d44-b3e7-4c61-bff9-26dd8bd5d134
-- title:
--   Cut sets of the nested L-shaped method
-- statement:
--   A state of the nested L-shaped method assigns to every node $k$ a finite set of *feasibility cuts* $(D,d)$, representing constraints (1.3) $Dx_k\ge d$, and a finite set of *optimality cuts* $(E,e)$, representing constraints (1.4) $Ex_k+\theta_k\ge e$. While node $k$ has no optimality cut its subproblem carries the Step 0 constraint $\theta_k=0$.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed. (2011), Ch. 6, §6.1, constraints (1.3)–(1.4), Steps 0 and 2, pp. 267–268 (PDF pp. 288–289)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree

namespace StochasticProg.MultistageV2

/-- The state of the nested L-shaped method (p. 267): the cuts currently present in every
subproblem NLDS(t,k). A feasibility cut `(D, d) ∈ feas k` is constraint (1.3)
`D x^t_k ≥ d`; an optimality cut `(E, e) ∈ opt k` is constraint (1.4) `E x^t_k + θ^t_k ≥ e`.
While `opt k = ∅` the subproblem carries Step 0's constraint `θ^t_k = 0` (p. 267); Step 2
removes it together with adding the first optimality cut (p. 268). -/
structure Cuts {H : ℕ} (T : Multistage.Tree H) (n : ℕ) where
  /-- feasibility cuts (1.3) of each node -/
  feas : T.Node → Finset ((Fin n → ℝ) × ℝ)
  /-- optimality cuts (1.4) of each node -/
  opt : T.Node → Finset ((Fin n → ℝ) × ℝ)

end StochasticProg.MultistageV2


