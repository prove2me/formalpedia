-- Prove2me | Definitions.Def_DimCallCenters_Constraint_Klam
-- name    : DimCallCenters_Constraint_Klam
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:57:33.681362+00:00
-- url     : https://prove2.me/theorems/07f341c3-6a08-4048-8c29-bf20704d79c4
-- title:
--   Continuous waiting cost K_λ(x) = π_λ(x) G_λ(x)
-- statement:
--   For a wait model, an arrival rate $\lambda > 0$ and $x > 0$, the **continuous waiting cost** is
--
--   $$K_\lambda(x) = \pi_\lambda(x)\,G_\lambda(x),$$
--
--   the product of the continuous probability of waiting and the scaled waiting cost. At an $x$ for which $N_\lambda(x)$ is an integer $N$, $K_\lambda(x) = K(N,\lambda)$, so $K_\lambda$ interpolates the waiting cost between integer staffing levels.
--
--   **Formalization Note** Defined for all real $x$; used only for $x > 0$.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 24, Section 8, definition of K_λ(x)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_WaitModel
import Definitions.Def_DimCallCenters_Rationalized_piLam
import Definitions.Def_DimCallCenters_Rationalized_Glam

namespace DimCallCenters.Constraint

/-- The continuous waiting cost `K_λ(x) = π_λ(x) G_λ(x)` of Section 8 (p. 24). -/
noncomputable def Klam (M : DimCallCenters.Rationalized.WaitModel) (lam x : ℝ) : ℝ :=
  DimCallCenters.Rationalized.piLam M.μ lam x * DimCallCenters.Rationalized.Glam M lam x

end DimCallCenters.Constraint


