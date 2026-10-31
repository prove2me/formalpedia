-- Prove2me | Definitions.Def_PerspEpi_scaleFn
-- name    : PerspEpi_scaleFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:37.855998+00:00
-- url     : https://prove2.me/theorems/8ee1954f-bb74-4902-b67b-f0aa548fa4cf
-- title:
--   Scalar multiple $\lambda\cdot\psi$ (with $0\cdot\psi=\delta_{\operatorname{dom}\psi}$)
-- statement:
--   For $\lambda \ge 0$ and $\psi : E \to \overline{\mathbb R}$,
--
--   $$
--   (\lambda\cdot\psi)(x) = \begin{cases} \lambda\,\psi(x) & \lambda > 0,\\ \delta_{\operatorname{dom}\psi}(x) & \lambda = 0. \end{cases}
--   $$
--
--   Proposition 8(b) expresses the proximal point of $g\circ\psi$ as that of $\bar\lambda\cdot\psi$.
--
--   **Formalization Note** The paper does not define $0\cdot\psi$; the convention $0\cdot\psi = \delta_{\operatorname{dom}\psi}$ is that of its reference [10] (Burke–Hoheisel–Nguyen). Values in `EReal`.
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, Proposition 8(b), p.22

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PerspEpi_ind

namespace PerspEpi

/-- **Scalar multiple** `λ · ψ`. Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, Proposition 8(b), p.22, uses `P_1(λ̄ · ψ)` for
`λ̄ ∈ argmin_{λ≥0}{g*(λ) + φ̄^ψ_x̄(λ)}`.

`scaleFn λ ψ = λψ` for `λ ≠ 0`, and `0 · ψ := δ_{dom ψ}`.

**Formalization Note.** The paper does not define `0 · ψ`; the convention `0 · ψ := δ_dom ψ` is the
one of its reference [10] (Burke–Hoheisel–Nguyen) for the subdifferential formula (30). Only
`λ ≥ 0` is used; for `λ > 0`, `λ · (+∞) = +∞`. -/
noncomputable def scaleFn {E : Type*} (lam : ℝ) (ψ : E → EReal) : E → EReal :=
  if lam = 0 then ind (AubinLipschitz.effDom ψ) else fun x => (lam : EReal) * ψ x

end PerspEpi


