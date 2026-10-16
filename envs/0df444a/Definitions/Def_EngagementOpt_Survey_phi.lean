-- Prove2me | Definitions.Def_EngagementOpt_Survey_phi
-- name    : EngagementOpt_Survey_phi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:52.993097+00:00
-- url     : https://prove2.me/theorems/31bf2dfa-0268-43d6-b016-7a9bbc81b982
-- title:
--   The function $\varphi(x)=\frac{x+1}{x}\bigl(1-\frac{\ln(x+1)}{x}\bigr)$ of (11) and Lemma D.1
-- statement:
--   For real $x$ define
--
--   $$
--   \varphi(x)=\frac{x+1}{x}\left(1-\frac{\ln(x+1)}{x}\right).
--   $$
--
--   With $x=\beta^t-1$ and $\beta=q/p$, $\varphi(x)$ is the derivative in $t$ of the closed form of $\mathbb E[T_q\mid T=t]$ (see (11)), and Lemma D.1 compares it with $1/2$.
--
--   **Formalization Note** The function is meaningful for $x>-1$, $x\ne0$. At $x=0$ Lean's division by zero returns $0$, and for $x\le-1$ the real logarithm returns a junk value; every statement about $\varphi$ in this mission restricts $x$ to $x>0$, $-1<x<0$, a punctured neighbourhood of $0$, the right neighbourhood of $-1$, or $x\to\infty$.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 21, eq. (11); p. 40, Lemma D.1

import Mathlib

namespace EngagementOpt.Survey

/-- The function `φ(x) = (x + 1)/x · (1 - ln(x + 1)/x)` of (11) and Lemma D.1 of
arXiv:2202.11776v3 (pp. 21, 40). It is meaningful for `x > -1`, `x ≠ 0`; every statement about it
restricts `x` to that domain. -/
noncomputable def phi (x : ℝ) : ℝ :=
  (x + 1) / x * (1 - Real.log (x + 1) / x)

end EngagementOpt.Survey


