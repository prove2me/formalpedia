-- Prove2me | Definitions.Def_WalledBrauer_Blocks_Partitions
-- name    : WalledBrauer_Blocks_Partitions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:42:27.89779+00:00
-- url     : https://prove2.me/theorems/0948e1ad-0be1-43d1-8def-c47f6a32fd55
-- title:
--   Contents of boxes and $\delta$-balanced bipartitions (p. 17, Definition 7.2, p. 32)
-- statement:
--   Let $\lambda$ be a partition with Young diagram $[\lambda]$. The box $d$ in row $i$ and column $j$ has **content** $c(d)=j-i$ (p. 17). Write $\sum_{d\in[\lambda]}c(d)$ for the total content, and $c_i(\lambda)$ for the number of boxes of $\lambda$ of content $i$ (p. 32).
--
--   **Definition 7.2.** Let $\delta$ be an element of a ring $R$ (in the paper, $R=k$). Two bipartitions $(\lambda^L,\lambda^R)$ and $(\mu^L,\mu^R)$ are **$\delta$-balanced** if there is a pairing of the boxes of $[\lambda^L/(\lambda^L\cap\mu^L)]$ with those of $[\lambda^R/(\lambda^R\cap\mu^R)]$, and a pairing of the boxes of $[\mu^L/(\lambda^L\cap\mu^L)]$ with those of $[\mu^R/(\lambda^R\cap\mu^R)]$, such that in every pair
--   $$
--   c(d)+c(d') = -\delta \quad\text{in } R .
--   $$
--
--   Balance is the combinatorial shadow of the block relation. Section 7 of the paper shows that in characteristic zero it characterises the blocks of $B_{r,s}(\delta)$, and Section 8 turns it into a Weyl-group orbit condition.
--
--   **Formalization Note** Young diagrams are Mathlib's `YoungDiagram` with 0-based cells $(i,j)$, and the content $j-i$ is unchanged by the shift. The skew diagram $[\lambda/(\lambda\cap\mu)]$ is the cell-set difference `λ.cells \ μ.cells`. A pairing is a bijection between the two finite cell sets. Contents are integers cast into $R$, and `IsBalanced` is stated for an arbitrary `AddGroupWithOne R`: $R=k$ for the block results and $R=\mathbb Z$ for Section 8.
-- source:
--   Cox, De Visscher, Doty & Martin, On the blocks of the walled Brauer algebra, arXiv:0709.0851v1, p. 17 (content), p. 28, Definition 7.2, p. 32 (c_i)

import Mathlib

namespace WalledBrauer.Blocks

/-- The content `c(d) = j - i` of the box `d` in row `i`, column `j` of a Young diagram (p. 17).
Mathlib's cells are 0-based, which does not change `j - i`. -/
def content (d : ℕ × ℕ) : ℤ := (d.2 : ℤ) - d.1

/-- The total content `∑_{d ∈ [λ]} c(d)` of a Young diagram. -/
def totalContent (μ : YoungDiagram) : ℤ := ∑ d ∈ μ.cells, content d

/-- `c_i(λ)`: the number of boxes of `λ` of content `i` (p. 32). -/
def contentCount (μ : YoungDiagram) (i : ℤ) : ℕ := (μ.cells.filter fun d => content d = i).card

/-- There is a bijection between the box sets `X` and `Y` under which the contents of each pair
sum to `-δ` in `R`. -/
def PairsToNegDelta {R : Type*} [AddGroupWithOne R] (δ : R) (X Y : Finset (ℕ × ℕ)) : Prop :=
  ∃ f : X ≃ Y, ∀ d : X, ((content d.1 : ℤ) : R) + ((content (f d).1 : ℤ) : R) = -δ

/-- Definition 7.2 (p. 28): `(λL, λR)` and `(μL, μR)` are `δ`-balanced when the boxes of
`[λL / (λL ∩ μL)]` can be paired with those of `[λR / (λR ∩ μR)]`, and the boxes of
`[μL / (λL ∩ μL)]` with those of `[μR / (λR ∩ μR)]`, so that the contents of each pair sum to
`-δ` in `R`. -/
def IsBalanced {R : Type*} [AddGroupWithOne R] (δ : R) (lamL lamR muL muR : YoungDiagram) : Prop :=
  PairsToNegDelta δ (lamL.cells \ muL.cells) (lamR.cells \ muR.cells) ∧
    PairsToNegDelta δ (muL.cells \ lamL.cells) (muR.cells \ lamR.cells)

end WalledBrauer.Blocks


