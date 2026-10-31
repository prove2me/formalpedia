-- Prove2me | Definitions.Def_PerspEpi_postComp
-- name    : PerspEpi_postComp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:36.136926+00:00
-- url     : https://prove2.me/theorems/297a5d44-0b2d-4fa7-a6f6-4e4cc93d2538
-- title:
--   Post-composition $g\circ\psi$
-- statement:
--   For $\psi \in \Gamma_0(E)$ and $g \in \Gamma_0(\mathbb R)$ the **post-composition** is
--
--   $$
--   (g\circ\psi)(x) = \begin{cases} g(\psi(x)) & x \in \operatorname{dom}\psi,\\ +\infty & \text{otherwise}. \end{cases}
--   $$
--
--   With $g = \delta_{\mathbb R_-}$ and $\psi(x,\alpha) = f(x)-\alpha$ it gives $\delta_{\operatorname{epi} f}$, which is how Corollary 14 follows from Proposition 8.
--
--   **Formalization Note** On $\operatorname{dom}\psi$ the value $\psi(x)$ is real and is passed to $g$ through `EReal.toReal`.
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, §6, p.22

import Mathlib

namespace PerspEpi

/-- **Post-composition** `g ∘ ψ`. Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, §6, p.22: "Given functions ψ ∈ Γ0(E) and
g ∈ Γ0(ℝ), we consider the composition (g ∘ ψ)(x) := g(ψ(x)) if x ∈ dom ψ; +∞ otherwise."

**Formalization Note.** On `dom ψ` the value `ψ x` is a real number (ψ is never `⊥`), recovered by
`EReal.toReal`. -/
noncomputable def postComp {E : Type*} (g : ℝ → EReal) (ψ : E → EReal) (x : E) : EReal :=
  if ψ x ≠ ⊤ then g (ψ x).toReal else ⊤

end PerspEpi


