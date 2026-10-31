-- Prove2me | Definitions.Def_PerspEpi_epiMul
-- name    : PerspEpi_epiMul
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:32.068854+00:00
-- url     : https://prove2.me/theorems/4cd6c4e4-b02f-4e1f-9734-e8625a6306b4
-- title:
--   Epi-multiplication $\lambda\star\omega$
-- statement:
--   For $\lambda > 0$ and $\omega : E \to \overline{\mathbb R}$ the **epi-multiplication** is
--
--   $$
--   (\lambda\star\omega)(x) = \lambda\,\omega(x/\lambda).
--   $$
--
--   It is the perspective map $\omega^\pi(\cdot,\lambda)$ for positive $\lambda$, and Lemma 1 describes its limit as $\lambda\downarrow 0$.
--
--   **Formalization Note** Values in `EReal`, with $\lambda\cdot(+\infty) = +\infty$ for $\lambda > 0$; only $\lambda>0$ is used.
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, §2, p.4

import Mathlib

namespace PerspEpi

/-- **Epi-multiplication.** Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, §2, p.4: "(λ ⋆ ω)(x) := λω(x/λ)" for λ > 0.

**Formalization Note.** Values in `EReal`; `λ · (+∞) = +∞` for `λ > 0`. Only `λ > 0` is used. -/
noncomputable def epiMul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (lam : ℝ)
    (φ : E → EReal) (x : E) : EReal :=
  (lam : EReal) * φ (lam⁻¹ • x)

end PerspEpi


