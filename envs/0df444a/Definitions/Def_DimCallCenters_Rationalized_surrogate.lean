-- Prove2me | Definitions.Def_DimCallCenters_Rationalized_surrogate
-- name    : DimCallCenters_Rationalized_surrogate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:04:11.135534+00:00
-- url     : https://prove2.me/theorems/ae03641f-f470-4c99-bd3b-8d2bdb964d14
-- title:
--   Approximating cost $C[z;\hat F,\hat\pi,\hat G]$
-- statement:
--   For three functions $\hat F, \hat\pi, \hat G : \mathbb R \to \mathbb R$ approximating $F_\lambda$, $\pi_\lambda$, $G_\lambda$, the approximating cost at $z$ is
--
--   $$C[z;\hat F,\hat\pi,\hat G] = \hat F(z) + \hat\pi(z)\,\hat G(z).$$
--
--   Its minimizer $z^*_\lambda$ over $z>0$, (9), is the candidate staffing function; with $\hat\pi = P$ (11) it gives the square-root staffing rules of the paper.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 12, Section 3, display C[z; F-hat, pi-hat, G-hat]

import Mathlib

namespace DimCallCenters.Rationalized

/-- The approximating cost `C[z; F̂, π̂, Ĝ] = F̂(z) + π̂(z) Ĝ(z)` of p. 12. -/
def surrogate (Fh pih Gh : ℝ → ℝ) (z : ℝ) : ℝ :=
  Fh z + pih z * Gh z

end DimCallCenters.Rationalized


