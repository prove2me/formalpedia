-- Prove2me | Definitions.Def_MetodosNumericos_interpolacaoDefs
-- name    : MetodosNumericos_interpolacaoDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T16:34:03.402232+00:00
-- url     : https://prove2.me/theorems/246dfa80-fea8-410b-9603-c70eb690f41e
-- title:
--   Lagrange cardinal functions and the interpolating polynomial
-- statement:
--   The Lagrange cardinal function $L_i(t) = \\prod_{j \\neq i}(t-x_j)/(x_i-x_j)$ attached to a family of nodes, and the interpolating polynomial in Lagrange form $P_n(t) = \\sum_i f_i L_i(t)$.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 7, §7.3 Fórmula de Lagrange, pp. 138–140.

import Mathlib

namespace MetodosNumericos

/-- The `i`-th Lagrange cardinal function for the nodes `x₀, …, xₙ`:
`Lᵢ(t) = ∏_{j ≠ i} (t - xⱼ) / (xᵢ - xⱼ)`. -/
noncomputable def lagrangeBasis {n : ℕ} (xs : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (t : ℝ) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (t - xs j) / (xs i - xs j)

/-- The interpolating polynomial in Lagrange form (Fórmula de Lagrange):
`Pₙ(t) = ∑ᵢ fᵢ Lᵢ(t)`. -/
noncomputable def lagrangeInterp {n : ℕ} (xs fs : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin (n + 1), fs i * lagrangeBasis xs i t

end MetodosNumericos


