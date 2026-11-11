-- Prove2me | Definitions.Def_GaussDiffSVP_coolB
-- name    : GaussDiffSVP_coolB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:59.737128+00:00
-- url     : https://prove2.me/theorems/4fdce9fb-ebfc-4b79-8485-d28a6972cdd7
-- title:
--   Degree factor $B_j = e^{A_rR_-^2}(\gamma/\sqrt2)^n$
-- statement:
--   $$B_j = e^{A_r R_-^2}\Big(\frac{\gamma}{\sqrt2}\Big)^n,$$
--   with $A_r$, $R_-^2$, $\gamma$ as for the cooling pair weight. The product $A_rR_-^2 = n(1-a_0)(1-w_n)/2$ does not depend on $r$. $B_j$ sets the weighted degree budget $D^+_j = \Upsilon_j B_j 2^{b_{\deg}}$.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (44), p.28

import Mathlib

namespace GaussDiffSVP

/-- The degree factor `B_j = e^{A_r R_−²} (γ/√2)ⁿ` of (44) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.28), with
`A_r = π(γ^{−2} − 1/2)/r²`, `R_−² = n r² a₁(1 − w_n)/(2π)`, `γ² = 2(1 − u)`, `a₁ = 4/(1 + u) − 2`
(see `coolWeight`).

**Formalization Note.** Written literally with the input width `r`; the product `A_r R_−²` does not
depend on `r` (p.29: "`A_r R_−² = n(1 − a₀)(1 − w_n)/2`"). -/
noncomputable def coolB (n : ℕ) (w u r : ℝ) : ℝ :=
  Real.exp (Real.pi * (1 / (2 * (1 - u)) - 1 / 2) / r ^ 2 *
      (n * r ^ 2 * (4 / (1 + u) - 2) * (1 - w) / (2 * Real.pi))) *
    (Real.sqrt (2 * (1 - u)) / Real.sqrt 2) ^ n

end GaussDiffSVP


