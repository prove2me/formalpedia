-- Prove2me | Definitions.Def_SampleRemoval_moment
-- name    : SampleRemoval_moment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:02:47.770537+00:00
-- url     : https://prove2.me/theorems/024910d1-4c8e-4eb2-81b5-873a6a070d56
-- title:
--   Weighted moment vector $g(w)=\sum_i w_i x_i y_i$
-- statement:
--   Let $(x_i,y_i)\in\mathbb R^d\times\mathbb R$, $i\in[n]$, be the observations. For a weight vector $w$ the **weighted moment vector** is
--
--   $$
--   g(w)=\sum_{i=1}^n w_i\,x_i\,y_i\in\mathbb R^d .
--   $$
--
--   Together with the Gram matrix $G(w)$ it determines the weighted least-squares estimate $\beta(w)=G(w)^{-1}g(w)$.
--
--   **Formalization Note** `x : Fin n → Fin d → ℝ`, `y : Fin n → ℝ`; the paper's index $i$ is the Lean index $i-1$.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), §2, Weighted least squares, p.3 (PDF p.5)

import Mathlib

set_option autoImplicit false

namespace SampleRemoval

/-- The weighted moment vector `g(w) = Σᵢ wᵢ xᵢ yᵢ` of observations `(xᵢ, yᵢ) ∈ ℝᵈ × ℝ`
(Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), §2, "Weighted least squares", p.3).

**Formalization Note** `x : Fin n → Fin d → ℝ`, `y : Fin n → ℝ`; the paper's index
`i ∈ [n]` is the Lean index `i − 1`. -/
def moment {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (w : Fin n → ℝ) : Fin d → ℝ :=
  ∑ i, (w i * y i) • x i

end SampleRemoval


