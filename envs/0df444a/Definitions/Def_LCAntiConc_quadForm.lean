-- Prove2me | Definitions.Def_LCAntiConc_quadForm
-- name    : LCAntiConc_quadForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:06.040564+00:00
-- url     : https://prove2.me/theorems/eb633dd2-5598-4f73-8142-d8c641ddf3cd
-- title:
--   Quadratic form $v^\top Hv$ as a polynomial
-- statement:
--   For a fixed matrix $H\in\mathbb R^{n\times n}$, the quadratic form
--
--   $$v^\top Hv=\sum_{i,j=1}^n H_{ij}\,v_iv_j$$
--
--   is regarded as a polynomial in the formal variable $v$.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Lemmas 4.3–4.8, pp.18–24 (PDF pp.20–26)

import Mathlib

namespace LCAntiConc

/-- The quadratic form `vᵀ H v = ∑ᵢⱼ Hᵢⱼ vᵢ vⱼ` of a fixed matrix `H`, as a polynomial in the
formal variable `v`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Lemmas 4.3–4.8, pp.18–24 (PDF pp.20–26). -/
noncomputable def quadForm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, ∑ j, MvPolynomial.C (H i j) * MvPolynomial.X i * MvPolynomial.X j

end LCAntiConc


