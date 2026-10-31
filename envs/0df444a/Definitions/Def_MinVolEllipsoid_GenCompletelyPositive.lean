-- Prove2me | Definitions.Def_MinVolEllipsoid_GenCompletelyPositive
-- name    : MinVolEllipsoid_GenCompletelyPositive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:43:40.373053+00:00
-- url     : https://prove2.me/theorems/2f608f40-db97-4843-acd7-e0956652f41e
-- title:
--   Generalized completely positive matrices $\mathcal C^*(\mathcal K)$
-- statement:
--   Let $\mathcal K\subseteq\mathbb R^K$ be a cone. The set of **generalized completely positive matrices** with respect to $\mathcal K$ is
--
--   $$
--   \mathcal C^*(\mathcal K)=\Bigl\{M\in\mathbb S^K:\ M=\textstyle\sum_{i\in[I]}x_ix_i^\top,\ x_i\in\mathcal K\Bigr\}.
--   $$
--
--   It is the dual cone of $\mathcal C(\mathcal K)$. The conic inequality $M\succeq_{\mathcal C^*(\mathcal K)}0$ means $M\in\mathcal C^*(\mathcal K)$.
--
--   **Formalization Note** The number of summands may be $0$, whereas the paper takes $I$ to be a positive integer; for a cone containing $0$ (such as the cone of display (2)) the two sets coincide, since the summand $00^\top=0$ can always be added. A sum of matrices $x_ix_i^\top$ is automatically symmetric, so no symmetry clause is needed.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, §1.1 Generalized Copositive Matrices, p.5

import Mathlib

open Matrix

namespace MinVolEllipsoid

/-- **Generalized completely positive matrices `𝒞*(𝒦)`** (Mittal & Hanasusanto,
arXiv:1807.07507v4, §1.1, "Generalized Copositive Matrices", p.5:
`𝒞*(𝒦) = {M ∈ 𝕊ᴷ : M = ∑_{i∈[I]} xᵢxᵢ⊤, xᵢ ∈ 𝒦}` where `I` is a positive integer).

`GenCompletelyPositive C M` says that `M = ∑ᵢ xᵢ xᵢ⊤` for finitely many vectors `xᵢ ∈ C`.
Such an `M` is automatically symmetric. The conic inequality `M ⪰_{𝒞*(𝒦)} 0` is
`GenCompletelyPositive C M`.

**Formalization Note** The number of summands `m` may be `0` (the paper requires `I ≥ 1`). For a
cone containing `0` the two sets coincide, since a summand `0 0⊤ = 0` may always be added. -/
def GenCompletelyPositive {ι : Type*} [Fintype ι] (C : Set (ι → ℝ)) (M : Matrix ι ι ℝ) : Prop :=
  ∃ (m : ℕ) (x : Fin m → ι → ℝ), (∀ i, x i ∈ C) ∧ M = ∑ i, vecMulVec (x i) (x i)

end MinVolEllipsoid


