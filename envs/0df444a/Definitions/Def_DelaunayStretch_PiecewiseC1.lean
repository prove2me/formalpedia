-- Prove2me | Definitions.Def_DelaunayStretch_PiecewiseC1
-- name    : DelaunayStretch_PiecewiseC1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:54:39.686244+00:00
-- url     : https://prove2.me/theorems/5f14a488-c9a9-4ebd-b7aa-6103b3460fb4
-- title:
--   Piecewise $C^1$ structures and incident gradients
-- statement:
--   Let $H$ be a real function on $\Omega\times\mathbb R$. A **piecewise $C^1$ structure** for $H$ consists of finitely many closed subsets $Z_1,\dots,Z_m$ of $\Omega\times\mathbb R$ that cover $\Omega\times\mathbb R$, and functions $H_1,\dots,H_m$, where $H_i$ is continuously differentiable on an open neighborhood of $Z_i$, such that $H=H_i$ on $Z_i$ for every $i$. For $z\in\Omega\times\mathbb R$, the **incident gradients** of $H$ at $z$ are the vectors $\nabla H_i(z)$ for the indices $i$ with $z\in Z_i$.
--
--   Incident gradients replace the gradient in conditions (H2) and (H4), which allows the clipped functions of Section 5.
--
--   **Formalization Note** "Closed subsets of $\Omega\times\mathbb R$" is closed in the subspace topology: $Z_i=K\cap(\Omega\times\mathbb R)$ with $K$ closed in $\mathbb R^4$. The neighborhoods are open in $\mathbb R^4$, and continuous differentiability is $C^1$ on that open set.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Definition 4.5, p.26

import Mathlib
import Definitions.Def_DelaunayStretch_potential

namespace DelaunayStretch

/-- **Piecewise `C¹` structure** for `H` (Definition 4.5, p.26): finitely many closed subsets
`Z₁, …, Zₘ` of `Ω × ℝ` that cover `Ω × ℝ`, and functions `H₁, …, Hₘ`, where `Hᵢ` is
continuously differentiable on an open neighborhood of `Zᵢ`, such that `H = Hᵢ` on `Zᵢ`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026),
Definition 4.5, p.26.

**Formalization Note** "Closed subsets of `Ω × ℝ`" means closed in the subspace topology:
`Zᵢ = K ∩ (Ω × ℝ)` with `K` closed in `ℝ⁴`. The neighborhood is open in `ℝ⁴`. -/
structure PiecewiseC1 (H : R4 → ℝ) where
  /-- the number of pieces `m` -/
  m : ℕ
  /-- the pieces `Z₁, …, Zₘ` -/
  Z : Fin m → Set R4
  /-- the functions `H₁, …, Hₘ` -/
  F : Fin m → R4 → ℝ
  closed : ∀ i, ∃ K : Set R4, IsClosed K ∧ Z i = K ∩ OmegaTimesR
  cover : ∀ z ∈ OmegaTimesR, ∃ i, z ∈ Z i
  smooth : ∀ i, ∃ V : Set R4, IsOpen V ∧ Z i ⊆ V ∧ ContDiffOn ℝ 1 (F i) V
  agree : ∀ i, ∀ z ∈ Z i, H z = F i z

/-- The **incident gradients** of `H` at `z` with respect to the structure `P`
(Definition 4.5, p.26): the vectors `∇Hᵢ(z)` for the indices `i` with `z ∈ Zᵢ`. -/
def PiecewiseC1.IncidentGradient {H : R4 → ℝ} (P : PiecewiseC1 H) (z g : R4) : Prop :=
  ∃ i, z ∈ P.Z i ∧ g = gradient4 (P.F i) z

end DelaunayStretch


