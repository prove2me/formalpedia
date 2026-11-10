-- Prove2me | Definitions.Def_EvasivePatterns_IsReciprocal
-- name    : EvasivePatterns_IsReciprocal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:13.504465+00:00
-- url     : https://prove2.me/theorems/17bd6704-cfb8-4356-82d6-cac684fda991
-- title:
--   Reciprocal rational polynomial
-- statement:
--   A nonzero polynomial $F \in \mathbb Q[z]$ is **reciprocal** when its reversal $F^*(z) = z^{\deg F} F(z^{-1})$ equals $F$ up to a nonzero rational factor, that is, its list of coefficients reads the same backwards, up to a factor. Over $\mathbb Q$ this is the autodagger property. For example $1 + z + z^2$ is reciprocal and $z^3 - z + 1$ is not.
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), §4, p.5 (PDF p.6), lines 154–156

import Mathlib

namespace EvasivePatterns

/-- **Reciprocal rational polynomial.** A nonzero `F ∈ ℚ[z]` is reciprocal when its reverse
`F^*(z) = z^{deg F} F(z^{−1})` is associated to `F` (equal up to a nonzero rational factor): the list of
coefficients reads the same backwards, up to a factor. Over `ℚ` this is the autodagger property
`F^† ∼ F`.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), §4, printed p. 5 (PDF p. 6), lines 155–156: "A nonzero polynomial
is autodagger if A^† is associated to A (equal up to a nonzero scalar). Over ℚ this is the familiar
reciprocal property: the list of coefficients reads the same backwards, up to a factor."

**Formalization Note** `F^*` is `Polynomial.reverse`; `Associated` in `ℚ[X]` is equality up to a unit,
i.e. a nonzero rational constant. -/
def IsReciprocal (F : Polynomial ℚ) : Prop :=
  F ≠ 0 ∧ Associated F.reverse F

end EvasivePatterns


