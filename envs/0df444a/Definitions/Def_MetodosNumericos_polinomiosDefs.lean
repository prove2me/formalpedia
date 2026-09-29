-- Prove2me | Definitions.Def_MetodosNumericos_polinomiosDefs
-- name    : MetodosNumericos_polinomiosDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T16:35:19.563467+00:00
-- url     : https://prove2.me/theorems/70cb9839-18a4-4c8c-ad2b-5583c21b52ad
-- title:
--   Polynomial in the book's index convention and Horner's coefficients
-- statement:
--   For a coefficient family $a$ and a degree $n$, $P(z) = \\sum_{i=0}^{n} a_i z^{n-i}$, evaluated either at a real or at a complex point, and the Horner coefficients at a point $c$, defined by $b_0 = a_0$ and $b_i = a_i + c\\,b_{i-1}$.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 4, §4.2 p. 74 and §4.5 p. 77 (algoritmo de Horner, caso real).

import Mathlib

namespace MetodosNumericos

/-- The polynomial `P(z) = a₀zⁿ + a₁z^{n-1} + ⋯ + aₙ` written with the book's
indexing convention: `a i` is the coefficient of `z^{n-i}`. -/
noncomputable def polyVal (a : ℕ → ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), a i * z ^ (n - i)

/-- The same polynomial evaluated at a complex point. -/
noncomputable def polyValC (a : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (n + 1), (a i : ℂ) * z ^ (n - i)

/-- The coefficients produced by Horner's algorithm at the point `z`:
`b₀ = a₀` and `bᵢ = aᵢ + z b_{i-1}`. -/
noncomputable def hornerSeq (a : ℕ → ℝ) (z : ℝ) : ℕ → ℝ
  | 0 => a 0
  | i + 1 => a (i + 1) + z * hornerSeq a z i

end MetodosNumericos


