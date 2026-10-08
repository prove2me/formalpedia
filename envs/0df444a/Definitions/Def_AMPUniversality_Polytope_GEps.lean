-- Prove2me | Definitions.Def_AMPUniversality_Polytope_GEps
-- name    : AMPUniversality_Polytope_GEps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:52.931649+00:00
-- url     : https://prove2.me/theorems/21406b0b-ed2c-4da7-93f9-a22552d9d4ec
-- title:
--   Equation (C.3), p. 60 — scalar state-evolution function
-- statement:
--   Let $Z$ have the standard normal law and let $u_+=\max(u,0)$. For a sparsity probability $\varepsilon$ and threshold parameter $\alpha$, define
--
--   $$G_\varepsilon(\alpha)=\varepsilon(1+\alpha^2)+2(1-\varepsilon)\mathbb E[(Z-\alpha)_+^2].$$
--
--   The minimum of this function gives the critical sampling ratio in Lemma 9. The Gaussian expectation is represented by an integral; Lemma 8 explicitly states its integrability.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 60, equation (C.3)

import Mathlib

set_option autoImplicit false
open MeasureTheory

namespace AMPUniversality.Polytope

/-- The scalar state-evolution function in (C.3). -/
noncomputable def GEps (ε α : ℝ) : ℝ :=
  ε * (1 + α ^ 2) +
    2 * (1 - ε) *
      ∫ z : ℝ, (max (z - α) 0) ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1)

end AMPUniversality.Polytope


