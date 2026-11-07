-- Prove2me | Definitions.Def_LCAntiConc_linForm
-- name    : LCAntiConc_linForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:51.644485+00:00
-- url     : https://prove2.me/theorems/123ad9e2-5522-49b0-b41d-81bab6fa638c
-- title:
--   The linear form $\langle x,v\rangle$ as a polynomial in $v$
-- statement:
--   For a fixed point $x\in\mathbb R^d$, the linear form
--
--   $$\langle x,v\rangle=\sum_{i=1}^d x_iv_i$$
--
--   is regarded as a polynomial in the formal variable $v$.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), (1.3), p.2 (PDF p.4)

import Mathlib

namespace LCAntiConc

/-- The linear form `⟨x, v⟩ = ∑ᵢ xᵢ vᵢ` as a polynomial in the formal variable `v`, for a fixed
point `x ∈ ℝ^d`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), (1.3), p.2 (PDF p.4).

**Formalization Note** `ℝ^d` is `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def linForm {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : MvPolynomial (Fin d) ℝ :=
  ∑ i, MvPolynomial.C (x i) * MvPolynomial.X i

end LCAntiConc


