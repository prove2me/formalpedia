-- Prove2me | Definitions.Def_OTDRO_Statics_Assumptions
-- name    : OTDRO_Statics_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:10:59.106321+00:00
-- url     : https://prove2.me/theorems/2d860181-89e2-4608-a787-45601f941b14
-- title:
--   Assumptions 3–5 and the decision-set radius
-- statement:
--   Assumption 3 requires a twice differentiable loss with $\ell''\le M$ for some $M>0$, and $\ell'(\beta^\top X)$ nonzero with positive probability for every $\beta\in B$. Assumption 4 says that $B$ is convex and compact, with radius $R_\beta=\sup_{\beta\in B}\|\beta\|$. Assumption 5 requires local strong convexity and, for each $\beta\in B$, constants $c_1,c_2>0$ and $p\in(0,1)$ such that
--
--   $$P_0\bigl(|\ell'(\beta^\top X)|>c_1,\ |\beta^\top X|>c_2\|\beta\|\bigr)\ge p.$$
--
--   These are the paper's conditions for dual smoothness and local strong convexity.
--
--   **Formalization Note** Local strong convexity means that $\ell''$ has a positive lower bound on each bounded interval. Assumption 5 forces $0\notin B$. The radius is used only when $B$ is nonempty and compact.
-- source:
--   arXiv:1810.02403v3, Assumptions 3–5, pp. 10–11

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting
import Definitions.Def_OTDRO_StrongCvx_Assumptions

namespace OTDRO.Statics

open MeasureTheory

/-- The radius R_β = sup_{β∈B} ‖β‖ from Assumption 4. It is used with B nonempty. -/
noncomputable def Rβ {d : ℕ} (B : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  sSup ((fun β => ‖β‖) '' B)

end OTDRO.Statics


