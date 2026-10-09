-- Prove2me | Definitions.Def_SLQSolv_Finite_Example52
-- name    : SLQSolv_Finite_Example52
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:36.082572+00:00
-- url     : https://prove2.me/theorems/ba5afd02-0944-4bf4-832a-d8f27e7aadc2
-- title:
--   Example 5.2, (5.2)–(5.3), pp. 2293–2294 — the data of a convex but non-finite problem
-- statement:
--   The data of Example 5.2: $n=m=1$, horizon $T=1$, the controlled SDE (5.2)
--
--   $$
--   dX(s)=u(s)\,ds+X(s)\,dW(s),\quad s\in[t,1],\qquad X(t)=x,
--   $$
--
--   and the cost (5.3)
--
--   $$
--   J^0(t,x;u)=\mathbb E\Big[-X(1)^2+\int_t^1e^{1-s}u(s)^2\,ds\Big].
--   $$
--
--   In the notation of Problem (SLQ): $A=0$, $B=1$, $C=1$, $D=0$, $Q=0$, $S=0$, $R(s)=e^{1-s}$, $G=-1$, and $b,\sigma,g,q,\rho=0$. These data satisfy (H1)–(H2).
--
--   The example shows that convexity of $u\mapsto J^0(0,x;u)$ does not imply finiteness of Problem (SLQ)$^0$.
--
--   **Formalization Note** The scalars are $1\times1$ matrices; $R(s)$ is defined for every $s\ge0$ by the same formula, and only $s\in[0,1]$ enters.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Example 5.2, (5.2)–(5.3), pp. 2293–2294

import Mathlib
import Definitions.Def_SLQSolv_Finite_Setting

open scoped NNReal Matrix

namespace SLQSolv.Finite

/-- The data of Example 5.2 (pp. 2293–2294), `n = m = 1`, `T = 1`: the state equation (5.2)
`dX = u ds + X dW` (`A = 0`, `B = 1`, `C = 1`, `D = 0`) and the cost (5.3)
`J⁰(t, x; u) = E[−X(1)² + ∫ₜ¹ e^{1−s} u(s)² ds]` (`G = −1`, `Q = 0`, `S = 0`, `R(s) = e^{1−s}`),
with all inhomogeneous terms `b, σ, q, ρ, g` equal to `0`. -/
noncomputable def ex52 (Ω : Type*) : Data Ω 1 1 where
  T := 1
  A := fun _ => 0
  B := fun _ => 1
  C := fun _ => 1
  D := fun _ => 0
  b := 0
  σ := 0
  Q := fun _ => 0
  S := fun _ => 0
  R := fun s => !![Real.exp (1 - (s : ℝ))]
  q := 0
  ρ := 0
  G := !![-1]
  g := 0

end SLQSolv.Finite


