-- Prove2me | Definitions.Def_RelSmoothFull_PrimalGrad_completedRate
-- name    : RelSmoothFull_PrimalGrad_completedRate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:41:30.958311+00:00
-- url     : https://prove2.me/theorems/1153d648-d781-4657-863f-7481bd589a8b
-- title:
--   Completed middle expression of (26) (corrected: undefined parameter cases completed)
-- statement:
--   Let $L,\mu,d$ be real numbers and let $k$ be a nonnegative integer. On the intended domain $L>0$, $\mu\ge0$, $k\ge1$, define the **completed primal-gradient bound** by
--
--   $$B(L,\mu,k,d)=\begin{cases}Ld/k,&\mu=0,\\ \mu d/((1+\mu/(L-\mu))^k-1),&0<\mu<L,\\ 0,&\mu\ge L.\end{cases}$$
--
--   In the convergence theorem, $d$ is the Bregman distance $D_h(u,x^0)$ from the initial point $x^0$ to the comparison point $u$, with derivative at $x^0$. The first branch is the right-hand limit specified after (26). The last branch completes the source-undefined parameter cases without restricting the theorem's parameters. This definition is purely numerical: it asserts no descent, rate, exact minimization, or vanishing divergence.
--
--   **Formalization Note** The function is total on all real parameters and natural indices. At $k=0$ it returns zero in every branch. At negative nonzero $\mu$ it returns zero. For $\mu=0$ and any $L$ it uses $Ld/k$ with total real division. These outside-domain conventions do not enter the theorem.
--
--   Differences from the source:
--   - correction: (26) specifies only the $\mu=0$ limit and leaves admissible divisions undefined at $\mu=L$ and some $\mu>L$ parameters → an explicit zero branch for $\mu\ge L$; reason: the source-admissible quadratic example $Q=[-1,1]$, $f=h=t^2/2$, $L=\mu=1$, $x^0=1$, $x^i=0$ for $i\ge1$ gives $1/(L-\mu)$, while $f=h=0$, $L=1$, $\mu=2$, $x^i=0$, $k=2$ gives $0/0$.
--   - encoding: the $\mu=0$ expression is specified as a right-hand limit → the branch $Ld/k$; reason: this is its actual limit for $L>0$ and $k\ge1$.
--   - encoding: the formula is used for $L>0$, $\mu\ge0$ and $k\ge1$ → a total real-valued arithmetic function with the stated outside-domain values; reason: the convergence theorem only uses the intended domain.
-- source:
--   Lu, Freund and Nesterov (2018), doi:10.1137/16M1099546, Theorem 3.1 / (26), printed p. 344, PDF p. 12; μ=0 evaluation confirmed on printed p. 345, PDF p. 13. Undefined-case completion documented in BRIEF.md.

import Mathlib

namespace RelSmoothFull.PrimalGrad

/-- The completed middle expression of Lu--Freund--Nesterov (2018), Theorem 3.1,
equation (26), printed p. 344 / PDF p. 12. Its mathematical use is for `L > 0`,
`μ ≥ 0`, `k ≥ 1`, and `d = D_h(u, x⁰)`.
The `μ = 0` branch is the stated right-hand limit. The zero branch at `μ ≥ L`
completes source-undefined parameter cases; the convergence theorem must establish
the resulting bounds, without assuming exactness or vanishing Bregman distance.
Outside the intended parameter domain this remains a total arithmetic function:
negative nonzero `μ` returns zero, and `k = 0` returns zero in every branch. -/
noncomputable def completedRate (L μ : ℝ) (k : ℕ) (d : ℝ) : ℝ :=
  if μ = 0 then L * d / (k : ℝ)
  else if 0 < μ ∧ μ < L then μ * d / ((1 + μ / (L - μ)) ^ k - 1)
  else 0

end RelSmoothFull.PrimalGrad


