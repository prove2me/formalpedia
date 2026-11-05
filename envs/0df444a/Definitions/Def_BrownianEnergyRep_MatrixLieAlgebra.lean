-- Prove2me | Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
-- name    : BrownianEnergyRep_MatrixLieAlgebra
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:00:34.535603+00:00
-- url     : https://prove2.me/theorems/ae018671-6026-4c6d-9587-cfcbc98a3b7d
-- title:
--   Lie algebra $\mathfrak g$ of a matrix group with an $\mathrm{Ad}_G$-invariant inner product
-- statement:
--   Let $G$ be a subgroup of $\mathrm{GL}_n(\mathbb R)$. This structure records the Lie algebra $\mathfrak g$ of $G$ together with an $\mathrm{Ad}_G$-invariant inner product. The space $\mathfrak g$ is a real inner product space $E$ with an injective linear map $\iota:E\to M_n(\mathbb R)$ whose image is the set of matrices $A$ with
--   $$
--   e^{tA}\in G\quad\text{for all } t\in\mathbb R .
--   $$
--   For $x\in G$, the adjoint action $\mathrm{Ad}_x$ is the map of $E$ with $\iota(\mathrm{Ad}_x a)=x\,\iota(a)\,x^{-1}$, and each $\mathrm{Ad}_x$ is a linear isometry of $E$. The bracket satisfies $\iota([a,b])=\iota(a)\iota(b)-\iota(b)\iota(a)$.
--
--   This is the common setting of the paper: every construction on $G$ and on $W(\mathfrak g)$ uses this data.
--
--   **Formalization Note** The inner product is the one of $E$, so any invariant inner product is allowed, not only the negative Killing form. The maps $\mathrm{Ad}$ and $[\cdot,\cdot]$ are determined by $\iota$, because $\iota$ is injective; they are stored as fields so that $\mathfrak g$-valued formulas need no inverse of $\iota$.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, §2, p.2

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- The Lie algebra `𝔤` of a matrix group `G ⊂ GLₙ(ℝ)` with an `Ad_G`-invariant inner product
(arXiv:1511.07378v1, §2, p.2). `E` is `𝔤` as an inner product space and `incl : E → Mat n` is its identification
with the matrices `A` such that `exp(tA) ∈ G` for all real `t`.

**Formalization Note** The inner product is the inner product of `E`, so it is data and any
`Ad_G`-invariant one is allowed. `Ad x` is `A ↦ xAx⁻¹` read through `incl`; that it is a linear
isometry of `E` is the `Ad_G`-invariance. `Ad`, `bracket` and their continuity are determined by
`incl`, which is injective; they are fields so that `𝔤`-valued formulas need no inverse of `incl`. -/
structure MatrixLieAlgebra {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  incl : E →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ
  incl_injective : Function.Injective incl
  mem_range_iff : ∀ A : Matrix (Fin n) (Fin n) ℝ, A ∈ LinearMap.range incl ↔
    ∀ t : ℝ, ∃ x ∈ G, (x : Matrix (Fin n) (Fin n) ℝ) = NormedSpace.exp (t • A)
  Ad : ↥G →* (E ≃ₗᵢ[ℝ] E)
  incl_Ad : ∀ (x : ↥G) (a : E), incl (Ad x a) =
    ((x : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) * incl a *
      (((x⁻¹ : ↥G) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
  Ad_continuous : ∀ a : E, Continuous fun x : ↥G => Ad x a
  bracket : E →L[ℝ] E →L[ℝ] E
  incl_bracket : ∀ a b : E, incl (bracket a b) = incl a * incl b - incl b * incl a

end BrownianEnergyRep


