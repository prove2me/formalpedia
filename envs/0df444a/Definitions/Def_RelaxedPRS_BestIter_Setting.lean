-- Prove2me | Definitions.Def_RelaxedPRS_BestIter_Setting
-- name    : RelaxedPRS_BestIter_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:35.623725+00:00
-- url     : https://prove2.me/theorems/0e1cbeb0-f321-40c3-ab66-668a6cf9fcb6
-- title:
--   Lemma 1.1, p. 7, and §3, p. 10 — the auxiliary point x_g and the objective error f(x)+g(x)−f(x*)−g(x*)
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $f,g:\mathcal H\to(-\infty,\infty]$. This file adds two objects to the shared relaxed-PRS setting `RelaxedPRS.StrongCvx.Setting`, which it imports.
--
--   1. The **auxiliary point** of Lemma 1.1, $x_g=\mathbf{prox}_{\gamma g}(z)$, where the proximal map $\mathbf{prox}_{\gamma g}$ is given as a map $P_g:\mathcal H\to\mathcal H$.
--   2. The **objective error** at a point $x$ relative to a reference point $x^*$ (in the paper $x^*=\mathbf{prox}_{\gamma g}(z^*)$ for a fixed point $z^*$ of $T_{\mathrm{PRS}}$, a minimizer of $f+g$):
--   $$f(x)+g(x)-f(x^*)-g(x^*),$$
--   as a real number.
--
--   The objective error is the quantity whose best-iterate, nonergodic and ergodic rates are the subject of Sections 3–5.
--
--   **Formalization Note** The objective error is computed with `EReal.toReal`, which equals the true value only where $f(x),g(x),f(x^*),g(x^*)$ are finite. Every statement of the series evaluates it only at such points: at outputs of the proximal map of a proper function (always finite) and at points of a function with a Lipschitz gradient (real-valued). The auxiliary point here is the same function as `RelaxedPRS.StrongCvx.xg`; both names are kept because the theorem statements of different missions of the series use them.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 7, Lemma 1.1; p. 10, §3 (objective error f(x)+g(x)−f(x*)−g(x*))

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_RelaxedPRS_StrongCvx_Setting

namespace RelaxedPRS.BestIter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Lemma 1.1's auxiliary point x_g = prox_{γg}(z). -/
def xg (Pg : H → H) (z : H) : H := Pg z

/-- The objective error f(x) + g(x) − f(x*) − g(x*) as a real number. It is faithful only where
`f x`, `g x`, `f xs`, `g xs` are finite; every item of this mission uses it only at such points
(a prox output of a proper function, or any point of a function with a Lipschitz gradient, which
is real-valued). -/
noncomputable def objErr (f g : H → EReal) (xs x : H) : ℝ :=
  (f x).toReal + (g x).toReal - (f xs).toReal - (g xs).toReal

end RelaxedPRS.BestIter


