-- Prove2me | Definitions.Def_EvasivePatterns_dagger
-- name    : EvasivePatterns_dagger
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:33.664424+00:00
-- url     : https://prove2.me/theorems/e7bc26dd-497f-4483-8bd4-f1b7d1cbc2b1
-- title:
--   Conjugate reciprocal $A^\dagger(z)=z^{\deg A}\bar A(z^{-1})$
-- statement:
--   For a polynomial $A$ with coefficients in a subfield of $\mathbb C$, the **conjugate reciprocal** is
--   $$
--   A^\dagger(z) = z^{\deg A}\, \overline{A(1/\bar z)} = z^{\deg A}\, \bar A(z^{-1}),
--   $$
--   where $\bar A$ has the complex-conjugate coefficients. A nonzero $A$ is autodagger when $A^\dagger$ equals $A$ up to a nonzero scalar. For rational polynomials $A^\dagger = A^*$, the reversal.
--
--   **Formalization Note** Polynomials over a subfield $K \subseteq \mathbb C$ are complex polynomials with coefficients in $K$; $A^\dagger$ is the reversal of the coefficientwise conjugate.
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), §4, p.5 (PDF p.6), lines 153–154

import Mathlib

namespace EvasivePatterns

/-- **The conjugate reciprocal `A^†(z) = z^{deg A} \overline{A(1/\bar z)} = z^{deg A} \bar A(z^{−1})`**
of a polynomial with complex coefficients, `\bar A` the polynomial with conjugated coefficients.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), §4, printed p. 5 (PDF p. 6), lines 153–154: "For a polynomial
A ∈ K[z] over a field embedded in ℂ, define its conjugate reciprocal by
A^†(z) = z^{deg A} \overline{A(1/\bar z)} = z^{deg A} \bar A(z^{−1})."

**Formalization Note** Polynomials over a subfield `K ⊆ ℂ` are encoded as complex polynomials with
coefficients in `K`; `A^†` is the reverse (reflection at `natDegree`) of the coefficientwise complex
conjugate, which has the same degree as `A`. For an integer or rational polynomial `A^† = A^*`. -/
noncomputable def dagger (A : Polynomial ℂ) : Polynomial ℂ :=
  (A.map (starRingEnd ℂ)).reverse

end EvasivePatterns


