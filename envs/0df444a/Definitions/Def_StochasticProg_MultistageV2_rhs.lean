-- Prove2me | Definitions.Def_StochasticProg_MultistageV2_rhs
-- name    : StochasticProg_MultistageV2_rhs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:42:34.515514+00:00
-- url     : https://prove2.me/theorems/a73bc383-7cb4-470c-8167-6cb5525a4bb2
-- title:
--   Right-hand side of the nested subproblem
-- statement:
--   For a node $k$ at stage $t$ and an ancestor decision $x_p$, the right-hand side of constraint (1.2) of $\mathrm{NLDS}(t,k)$ is $h^t_k - T^{t-1}_k x_p$ if $t>1$, and the initial condition $h^1$ if $k$ is the root (then $x_p$ is ignored).
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed. (2011), Ch. 6, §6.1, constraint (1.2) and the convention $b = h^1 - T^0x^0$, p. 267 (PDF p. 288)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_MultistageV2_Instance

namespace StochasticProg.MultistageV2

variable {H n m : ℕ} {T : Multistage.Tree H}

/-- The right-hand side of constraint (1.2) of NLDS(t,k), p. 267, given the ancestor's
current decision `xp = x^{t-1}_{a(k)}`: `h^t_k - T^{t-1}_k xp` for a non-root node, and the
initial condition `b = h^1 - T^0 x^0`, read as `h^1`, for the root (`xp` is then ignored). -/
def rhs (inst : Instance H n m T) (k : T.Node) (xp : Fin n → ℝ) : Fin m → ℝ :=
  if (T.stage k).val = 0 then inst.h k else inst.h k - (inst.Tmat k).mulVec xp

end StochasticProg.MultistageV2


