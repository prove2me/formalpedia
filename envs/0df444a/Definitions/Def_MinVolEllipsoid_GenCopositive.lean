-- Prove2me | Definitions.Def_MinVolEllipsoid_GenCopositive
-- name    : MinVolEllipsoid_GenCopositive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:43:44.12362+00:00
-- url     : https://prove2.me/theorems/65c91cea-d154-464c-9295-c7de8516c4ef
-- title:
--   Generalized copositive matrices $\mathcal C(\mathcal K)$
-- statement:
--   Let $\mathcal K\subseteq\mathbb R^K$ be a cone. The set of **generalized copositive matrices** with respect to $\mathcal K$ is
--
--   $$
--   \mathcal C(\mathcal K)=\{M\in\mathbb S^K:\ x^\top Mx\ge0\ \ \forall x\in\mathcal K\}.
--   $$
--
--   For $\mathcal K=\mathbb R^K_+$ these are the copositive matrices, for $\mathcal K=\mathbb R^K$ the positive semidefinite ones. The conic inequality $P\succeq_{\mathcal C(\mathcal K)}Q$ means $P-Q\in\mathcal C(\mathcal K)$, and $P\preceq_{\mathcal C(\mathcal K)}0$ means $-P\in\mathcal C(\mathcal K)$.
--
--   **Formalization Note** Vectors are `ι → ℝ` over a finite index type, $x^\top Mx$ is `x ⬝ᵥ (M *ᵥ x)`, and membership in $\mathbb S^K$ is the clause `M.IsSymm`. No condition on $\mathcal K$ is bundled.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, §1.1 Generalized Copositive Matrices, p.5

import Mathlib

open Matrix

namespace MinVolEllipsoid

/-- **Generalized copositive matrices `𝒞(𝒦)`** (Mittal & Hanasusanto, arXiv:1807.07507v4, §1.1,
"Generalized Copositive Matrices", p.5: `𝒞(𝒦) = {M ∈ 𝕊ᴷ : x⊤Mx ≥ 0 ∀x ∈ 𝒦}`).

`GenCopositive C M` says that `M` is symmetric and `v⊤ M v ≥ 0` for every `v ∈ C`. The conic
inequality `P ⪰_{𝒞(𝒦)} Q` of p.5 is `GenCopositive C (P - Q)`, and `P ⪯_{𝒞(𝒦)} 0` is
`GenCopositive C (-P)`.

**Formalization Note** Vectors are `ι → ℝ` over a finite index type, and `v⊤ M v` is
`v ⬝ᵥ (M *ᵥ v)`. Membership in `𝕊ᴷ` is the clause `M.IsSymm`. No condition on `C` is bundled:
the paper's `𝒦` is any cone, and the statements that use this predicate say which one. -/
def GenCopositive {ι : Type*} [Fintype ι] (C : Set (ι → ℝ)) (M : Matrix ι ι ℝ) : Prop :=
  M.IsSymm ∧ ∀ v ∈ C, 0 ≤ v ⬝ᵥ (M *ᵥ v)

end MinVolEllipsoid


