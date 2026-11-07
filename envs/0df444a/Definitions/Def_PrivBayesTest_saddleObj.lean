-- Prove2me | Definitions.Def_PrivBayesTest_saddleObj
-- name    : PrivBayesTest_saddleObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:54.031577+00:00
-- url     : https://prove2.me/theorems/859f353d-a931-49d2-9a65-c26a6ec2fcd0
-- title:
--   Saddle objective $\Phi(\alpha,z)=\alpha A(z)+(1-\alpha)B(z)+\omega(\alpha)\varepsilon W(z)$ (eq. (7))
-- statement:
--   For functions $A,B,W$ of a variable $z$, a weight function $\omega$ and $\varepsilon>0$, Appendix C defines
--
--   $$
--   \Phi(\alpha,z) \;=\; \alpha A(z) + (1-\alpha)B(z) + \omega(\alpha)\,\varepsilon\,W(z),
--   $$
--
--   where $\omega(\alpha)$ is either $\tilde\alpha=\min\{\alpha,1-\alpha\}$ or $\alpha$. With $z=(R,S)$, $A=\mathrm{KL}(R\|P)$, $B=\mathrm{KL}(S\|Q)$, $W=\mathrm{TV}(R,S)$ and $\omega=\tilde\alpha$ this is the KL–TV objective $F_\alpha$.
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Appendix C, eq. (7), p.28

import Mathlib

namespace PrivBayesTest

/-- The objective of Appendix C, eq. (7), of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.28:
`Φ(α, z) = α A(z) + (1 − α) B(z) + ω(α) ε W(z)`, for functions `A, B, W` of a variable `z` and a
weight function `ω` (the paper takes `ω(α) = α̃ = min{α, 1 − α}` or `ω(α) = α`). -/
def saddleObj {E : Type*} (ω : ℝ → ℝ) (ε : ℝ) (A B W : E → ℝ) (α : ℝ) (z : E) : ℝ :=
  α * A z + (1 - α) * B z + ω α * ε * W z

end PrivBayesTest


