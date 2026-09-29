-- Prove2me | Definitions.Def_MetodosNumericos_integracaoDefs
-- name    : MetodosNumericos_integracaoDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T16:33:40.711229+00:00
-- url     : https://prove2.me/theorems/6be95676-c9da-4416-95e2-6b1c1040c148
-- title:
--   Composite trapezoidal and Simpson rules
-- statement:
--   The composite trapezoidal rule with $n$ subintervals and the composite Simpson rule with $2k$ subintervals on $[a,b]$.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 8, §8.1 p. 164 (trapézios) and §8.2 pp. 169–172 (Simpson).

import Mathlib

namespace MetodosNumericos

/-- The composite trapezoidal rule (Método dos Trapézios) with `n` subintervals of
length `h = (b - a) / n` on `[a, b]`:
`h (f(x₀)/2 + f(x₁) + ⋯ + f(x_{n-1}) + f(xₙ)/2)`. -/
noncomputable def trapezoidRule (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  let h := (b - a) / n
  h * ((f a + f b) / 2 + ∑ i ∈ Finset.Ico 1 n, f (a + i * h))

/-- The composite Simpson rule (Método de Simpson) on `[a, b]` with an even number
`n = 2k` of subintervals of length `h = (b - a) / (2k)`:
`(h/3)(f(x₀) + 4f(x₁) + 2f(x₂) + ⋯ + 4f(x_{2k-1}) + f(x_{2k}))`. -/
noncomputable def simpsonRule (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) : ℝ :=
  let h := (b - a) / (2 * k)
  h / 3 * (f a + f b
    + 4 * ∑ i ∈ Finset.range k, f (a + (2 * i + 1) * h)
    + 2 * ∑ i ∈ Finset.Ico 1 k, f (a + (2 * i) * h))

end MetodosNumericos


