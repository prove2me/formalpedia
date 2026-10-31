-- Prove2me | Definitions.Def_PerspEpi_prox
-- name    : PerspEpi_prox
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:42.262566+00:00
-- url     : https://prove2.me/theorems/67f360f7-e233-43e8-a04b-d668b945365a
-- title:
--   Proximal map $P_\lambda f$
-- statement:
--   For $f \in \Gamma_0(E)$, $\lambda > 0$ and $x \in E$ the **proximal map** is
--
--   $$
--   P_\lambda f(x) = \operatorname*{argmin}_{u \in E}\Big\{ f(u) + \frac{1}{2\lambda}\|x-u\|^2 \Big\},
--   $$
--
--   the unique minimizer (it exists and is unique because the objective is lower semicontinuous and strongly convex on a finite-dimensional space).
--
--   **Formalization Note** `prox f λ x` is the element of the published argmin set `GenNewtonSubgrad.ProxReg.prox f λ x` when that set is a singleton, and `x` otherwise. The second branch never applies for $f \in \Gamma_0(E)$ and $\lambda > 0$, the only arguments used by the mission's statements.
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, p.1 and §4.1, p.14

import Mathlib
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope

namespace PerspEpi

/-- **Proximal map** `P_λ f`. Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, p.1 and §4.1, p.14:
"P_λ f(x) = argmin_{u ∈ E} {f(u) + (1/2λ)‖x − u‖²} (λ > 0)".

`prox f λ x` is the unique minimizer of `u ↦ f(u) + ‖x − u‖²/(2λ)` whenever it exists, i.e. the
unique element of the published argmin set `GenNewtonSubgrad.ProxReg.prox f λ x`
(`{p | ∀ y, f p + ‖p − x‖²/(2λ) ≤ f y + ‖y − x‖²/(2λ)}`).

**Formalization Note.** For `f ∈ Γ0(E)` (proper, closed, convex) and `λ > 0` the minimizer exists
and is unique (strong convexity and lower semicontinuity on a finite-dimensional space), so
`prox f λ x` is the paper's `P_λ f(x)`. The fallback value `x` is taken only when the argmin is not
a singleton, which does not occur for the arguments used in this mission. -/
noncomputable def prox {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal)
    (lam : ℝ) (x : E) : E := by
  classical exact if h : ∃! u, u ∈ GenNewtonSubgrad.ProxReg.prox f lam x then h.exists.choose else x

end PerspEpi


