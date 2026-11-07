-- Prove2me | Definitions.Def_LCAntiConc_sphereConstraint
-- name    : LCAntiConc_sphereConstraint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:48.1299+00:00
-- url     : https://prove2.me/theorems/ab964508-1ee1-45f6-94ef-32765d094a79
-- title:
--   The sphere constraint $\|v\|_2^2-1$
-- statement:
--   For the formal variable $v=(v_1,\dots,v_d)$, the **sphere constraint** is the polynomial
--
--   $$\|v\|_2^2-1=\sum_{i=1}^d v_i^2-1\in\mathbb R[v].$$
--
--   Its zero set is the unit sphere $S^{d-1}$. Sum-of-squares proofs on the sphere are identities modulo multiples of this polynomial.
--
--   **Formalization Note** The formal variable is the family of variables of `MvPolynomial (Fin d) ℝ`.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), §1.1, p.2 (PDF p.4); (3.1), p.15 (PDF p.17)

import Mathlib

namespace LCAntiConc

/-- The sphere constraint polynomial `‖v‖₂² - 1 = ∑ᵢ vᵢ² - 1` in the formal variable
`v = (v₁, …, v_d)`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), §1.1, p.2 (PDF p.4), and (3.1), p.15
(PDF p.17).

**Formalization Note** The formal variable `v` is the family of variables of
`MvPolynomial (Fin d) ℝ`. -/
noncomputable def sphereConstraint (d : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ i, MvPolynomial.X i ^ 2 - 1

end LCAntiConc


