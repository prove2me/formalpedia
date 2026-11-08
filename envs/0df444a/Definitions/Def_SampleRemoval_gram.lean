-- Prove2me | Definitions.Def_SampleRemoval_gram
-- name    : SampleRemoval_gram
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:02:54.109834+00:00
-- url     : https://prove2.me/theorems/a24e1fd6-8246-4c38-bd1f-d883ceb65d1b
-- title:
--   Weighted Gram matrix $G(w)=\sum_i w_i x_i x_i^{\top}$
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$ be the design vectors of $n$ observations. For a weight vector $w\in\mathbb R^n$ the **weighted Gram matrix** is the $d\times d$ matrix
--
--   $$
--   G(w)=\sum_{i=1}^n w_i\,x_i x_i^{\top}.
--   $$
--
--   The paper uses it for weights $w\in[0,1]^n$, where $w_i$ is the fraction of observation $i$ that is retained; $w=\mathbf 1_S$ keeps exactly the observations in $S$. It is the matrix whose inverse defines the weighted least-squares estimate.
--
--   **Formalization Note** The design is a function `Fin n → Fin d → ℝ`; the paper's observation $i\in[n]$ is the Lean index $i-1$. The definition is total in $w$.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), §2, Weighted least squares, p.3 (PDF p.5)

import Mathlib

set_option autoImplicit false

open Matrix

namespace SampleRemoval

/-- The weighted Gram matrix `G(w) = Σᵢ wᵢ xᵢ xᵢ⊤` of a design `x₁, …, xₙ ∈ ℝᵈ` under a weight
vector `w` (Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), §2, "Weighted least squares", p.3).

**Formalization Note** The design is `x : Fin n → Fin d → ℝ`; the paper's observation
`i ∈ [n]` is the Lean index `i − 1`. The definition is total in `w`; the paper uses it for
`w ∈ [0, 1]ⁿ`, and every statement of the mission carries that constraint where it matters. -/
def gram {n d : ℕ} (x : Fin n → Fin d → ℝ) (w : Fin n → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ i, w i • Matrix.vecMulVec (x i) (x i)

end SampleRemoval


