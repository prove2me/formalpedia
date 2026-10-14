-- Prove2me | Definitions.Def_HeathcoteUnbounded_Psi
-- name    : HeathcoteUnbounded_Psi
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-13T14:32:56.518179+00:00
-- url     : https://prove2.me/theorems/9217caba-941b-45f9-8876-c213604650bd
-- title:
--   Heathcote's wave function $\psi(x)=x^{-1}\mathbf 1_{[1,\infty)}(x)$, eq. (4)
-- statement:
--   The complex-valued function $\psi:\mathbb R\to\mathbb C$ of equation (4) in the source,
--
--   $$\psi(x)=\begin{cases} x^{-1} & \text{if } x\ge 1,\\ 0 & \text{if } x<1.\end{cases}$$
--
--   It is the explicit wave function used to exhibit a normalized state of $L^2(\mathbb R)$ that lies outside the domains of the position and momentum operators.
--
--   **Formalization Note** `psi` is an ordinary function `ℝ → ℂ`; its class in $L^2(\mathbb R)$ is produced in the goal theorem.
-- source:
--   A. Heathcote, "Unbounded Operators and the Incompleteness of Quantum Mechanics", Philosophy of Science 57 (1990), 523–534, p. 5, eq. (4)

import Mathlib

namespace HeathcoteUnbounded

/-- Heathcote's wave function, eq. (4): `ψ(x) = x⁻¹` for `x ≥ 1` and `ψ(x) = 0` for `x < 1`. -/
noncomputable def psi : ℝ → ℂ := fun x => if 1 ≤ x then ((x : ℂ))⁻¹ else 0

end HeathcoteUnbounded


