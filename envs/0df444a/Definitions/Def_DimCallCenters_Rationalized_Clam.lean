-- Prove2me | Definitions.Def_DimCallCenters_Rationalized_Clam
-- name    : DimCallCenters_Rationalized_Clam
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:18:03.243333+00:00
-- url     : https://prove2.me/theorems/f643d3f6-dd1a-4e94-8aea-24e7cefcb6c6
-- title:
--   Normalized total cost $C_\lambda(x)$
-- statement:
--   For the model $(\mu, D_\lambda)$, staffing cost $F$, arrival rate $\lambda$ and $x > 0$,
--
--   $$C_\lambda(x) = F_\lambda(x) + \pi_\lambda(x)\,G_\lambda(x).$$
--
--   This is the total cost per unit time in excess of $F(\lambda/\mu)$, extended to non-integer staffing levels; the continuous optimum $x^*_\lambda$ of (8) minimizes it over $x > 0$.
--
--   **Formalization Note** The paper defines $C_\lambda(x) := C(N_\lambda(x),\lambda) - F(\lambda/\mu)$ and then rewrites it in the form above, using $\pi_\lambda(x) = \pi(N_\lambda(x),\lambda/\mu)$ at integer $N_\lambda(x)$. The rewritten form is the one meaningful at every $x > 0$, and it is the one used here.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 12, Section 3, C_lambda(x) = F_lambda(x) + pi_lambda(x) G_lambda(x)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Flam
import Definitions.Def_DimCallCenters_Rationalized_Glam
import Definitions.Def_DimCallCenters_Rationalized_piLam

namespace DimCallCenters.Rationalized

/-- The normalized total cost `C_λ(x) = F_λ(x) + π_λ(x) G_λ(x)` of p. 12 (the "can thus be
rewritten" form, which equals `C(N_λ(x), λ) - F(λ/μ)` when `N_λ(x)` is an integer). -/
noncomputable def Clam (M : WaitModel) (F : ℝ → ℝ) (lam x : ℝ) : ℝ :=
  Flam F M.μ lam x + piLam M.μ lam x * Glam M lam x

end DimCallCenters.Rationalized


