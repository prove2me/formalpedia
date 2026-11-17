-- Prove2me | Definitions.Def_AnchoredEP_Supplement_oracleResponse
-- name    : AnchoredEP_Supplement_oracleResponse
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:11:31.796191+00:00
-- url     : https://prove2.me/theorems/f67d6432-f0d0-4b7e-9e6a-4b95ba19030f
-- title:
--   Response of the $p$th-order oracle
-- statement:
--   For an operator $F:\mathbb R^n\to\mathbb R^n$ and a point $z$, the **$p$th-order oracle response** is the family $\{D^jF(z):0\le j\le p-1\}$, with $D^0F=F$. For fixed-point problems the oracle returns the derivatives $D^jT(z)$ of the fixed-point operator $T$ instead.
--
--   **Formalization Note** $D^jF(z)$ is Mathlib's `iteratedFDeriv ℝ j F z`, which is the $j$-th derivative whenever $F$ is $j$ times differentiable, as in the lower-bound theorems.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Section 6, p.12

import Mathlib
import Definitions.Def_AnchoredEP_Supplement_OracleOutput

namespace AnchoredEP.Supplement

/-- **The `p`th-order oracle response of an operator at a point.** Jiang–Yoon, arXiv:2609.30212,
Section 6, p.12: the oracle outputs `{D^jF(z) : 0 ≤ j ≤ p − 1}`, `D⁰F = F` (for fixed-point
problems, `D^jT`).

`oracleResponse p F z j = iteratedFDeriv ℝ j F z`, the `j`-th derivative of `F` at `z`.

**Formalization Note.** For `F` that is `(p−1)`-times continuously differentiable, as in
Theorems 6.1 and 6.4, `iteratedFDeriv ℝ j F z` is the `j`-th derivative `D^jF(z)`;
`iteratedFDeriv ℝ 0 F z` is the constant `0`-linear map with value `F(z)`. -/
noncomputable def oracleResponse (p : ℕ) {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin n)) : OracleOutput p n :=
  fun j => iteratedFDeriv ℝ (j : ℕ) F z

end AnchoredEP.Supplement


