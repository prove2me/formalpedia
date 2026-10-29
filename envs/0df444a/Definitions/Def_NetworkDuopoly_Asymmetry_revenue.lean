-- Prove2me | Definitions.Def_NetworkDuopoly_Asymmetry_revenue
-- name    : NetworkDuopoly_Asymmetry_revenue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:03.524863+00:00
-- url     : https://prove2.me/theorems/9c9ae677-d9cb-4bfa-87fd-50e766077829
-- title:
--   Normalized Cournot revenue with the full-market boundary convention
-- statement:
--   Let $\alpha\in\mathbb R$ be a firm's quality, $\gamma\ge0$ the homogeneous network strength, $x\in[0,1]$ its own share and $y\in[0,1]$ its rival's share. Define its normalized revenue by
--   $$
--   R_{\alpha,\gamma}(x,y)=\begin{cases}
--   0,&x=0,\\
--   x\bigl(\alpha+\gamma x/2-\log x+\log(1-x-y)\bigr),&x>0,\ x+y<1,\\
--   -\infty,&\text{otherwise}.
--   \end{cases}
--   $$
--   The rival earns $R_{\alpha,\gamma}(y,x)$ in the identical-quality game. This payoff represents equation (7), including the zero-share and full-market conventions of the proof of Proposition 1. It permits negative finite payoffs and imposes no nonnegative-price restriction.
--
--   **Formalization Note** The codomain is the extended real line. The own-zero branch takes precedence, even at $(x,y)=(0,1)$. The formula is extended to all real arguments by the same cases, with negative own share assigned $-\infty$; game strategies remain in $[0,1]$. The definition accepts real $\gamma$, while theorem hypotheses impose its economic domain. Actual revenue is $n/\beta$ times this payoff for $n\ge1$ and common $\beta>0$ under Assumptions 1–2, so normalization preserves every comparison of unilateral revenues. The factor $\gamma/2$ includes the diagonal network effects.
-- source:
--   Chen and Chen (2021), Duopoly Competition with Network Effects in Discrete Choice Models, https://doi.org/10.1287/opre.2020.2079; supplied artifact pp. 13–16 (PDF 13–16), equations (3), (4), (7), Assumptions 1–2; p. ec1 (PDF 45), proof of Proposition 1 and footnote 10.

import Mathlib

namespace NetworkDuopoly.Asymmetry

noncomputable def revenue (α γ x y : ℝ) : EReal :=
  if x = 0 then 0
  else if 0 < x ∧ x + y < 1 then
    ((x * (α + γ * x / 2 - Real.log x + Real.log (1 - x - y)) : ℝ) : EReal)
  else ⊥

end NetworkDuopoly.Asymmetry


