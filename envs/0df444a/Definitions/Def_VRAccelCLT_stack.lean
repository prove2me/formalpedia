-- Prove2me | Definitions.Def_VRAccelCLT_stack
-- name    : VRAccelCLT_stack
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:12.287301+00:00
-- url     : https://prove2.me/theorems/2693bb61-297a-4e77-bdc1-6845ddc94815
-- title:
--   Stacked vector $(u;v)\in\mathbb R^{2m}$
-- statement:
--   For $u,v\in\mathbb R^m$, the **stacked vector** $\begin{pmatrix}u\\v\end{pmatrix}\in\mathbb R^{2m}$ has $u$ as its first block and $v$ as its second. Theorem 2 states its CLT for $\begin{pmatrix}y_k-x^*\\y_{k-1}-x^*\end{pmatrix}$.
--
--   **Formalization Note** The block order matches the block matrices $H_2$, $P_2$ (first summand of the index set = first block).
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, Theorem 2, p.19

import Mathlib

namespace VRAccelCLT

/-- **Stacked vector** `(u ; v) ∈ ℝ^{2m}` of two vectors of `ℝᵐ`. Lei, Shanbhag,
arXiv:2006.07769v3, Theorem 2, p.19, the vector `(yk − x∗ ; yk−1 − x∗)`.

**Formalization Note.** `ℝ^{2m}` is `EuclideanSpace ℝ (Fin m ⊕ Fin m)`: the coordinates indexed by
`Sum.inl i` are those of `u` (first block), those indexed by `Sum.inr i` are those of `v`, matching
the block order of `Matrix.fromBlocks`. -/
def stack {m : ℕ} (u v : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m ⊕ Fin m) :=
  WithLp.toLp 2 (Sum.elim (fun i => u i) (fun i => v i))

end VRAccelCLT


