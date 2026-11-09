-- Prove2me | Definitions.Def_GevreyGibbsSep_psiS
-- name    : GevreyGibbsSep_psiS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:49.709218+00:00
-- url     : https://prove2.me/theorems/d81d9dc7-02b8-45cb-aca6-3365095e928b
-- title:
--   Mollifier $\psi_s$
-- statement:
--   For $s>1$ the **mollifier** is
--   $$\psi_s(x)=\begin{cases}e^{-(1-x^2)^{-1/(s-1)}},&|x|<1,\\ 0,&|x|\ge1 .\end{cases}$$
--   It is $C^\infty$, supported on $[-1,1]$, and $s$-Gevrey (Proposition B.1).
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition B.5, Eq. (B16), p.37; Eq. (B18), p.38

import Mathlib

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The mollifier `ψ_s(x) = exp(−(1 − x²)^{−1/(s−1)})` for `|x| < 1` and `0` otherwise
(arXiv:2608.24527 (sha256 d4fd40eb…), Definition B.5, Eq. (B16), p.37; (B18), p.38). -/
noncomputable def psiS (s x : ℝ) : ℝ :=
  if |x| < 1 then Real.exp (- (1 - x ^ 2) ^ (-(1 / (s - 1)))) else 0

end GevreyGibbsSep


