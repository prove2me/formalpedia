-- Prove2me | Definitions.Def_BlockSSM_Supplement_VbSeries
-- name    : BlockSSM_Supplement_VbSeries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:03:49.656839+00:00
-- url     : https://prove2.me/theorems/9e6402ef-ff41-4354-aa91-51b72ad353ae
-- title:
--   Series with factors in $V_b$ and $\ell_b(G)$
-- statement:
--   A **series with factors in $V_b$** of length $k$ is a subnormal series
--   $$
--   1=N_0\trianglelefteq N_1\trianglelefteq\dots\trianglelefteq N_k=G,\qquad N_i/N_{i-1}\in V_b ,
--   $$
--   where $V_b=\{X: w^{\twoheadrightarrow}(X)\le b\}$ and $N_{i-1}$ need only be normal in $N_i$. Then $\ell_b(G)$ is the least such $k$, or $\infty$ if none exists; the **normal-series variant** is the least $k$ among series all of whose terms are normal in $G$.
--
--   These are the group-theoretic sides of the cascade depth theorem.
--
--   **Formalization Note** The factor is the quotient group $N_i/(N_{i-1}\cap N_i)$ of $N_i$, with $N_{i-1}\le N_i$ required; infima in $\mathbb N\cup\{\infty\}$.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), §8, p.8 (PDF p.9), and Proposition 3, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_BlockSSM_Supplement_coveringWidth

universe u

namespace BlockSSM.Supplement

/-- **A subnormal series with factors in `V_b`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), §8, p.8 (PDF p.9): "a subnormal series
1 = N₀ ⊴ N₁ ⊴ ⋯ ⊴ N_k = G, N_i/N_{i−1} ∈ V_b", where (Proposition 3, p.2) `V_b = {G : w↠(G) ≤ b}`.

**Formalization Note.** `N_{i−1}` is only required to be normal in `N_i` (as the subgroup
`N_{i−1} ∩ N_i` of `N_i`, with `N_{i−1} ≤ N_i`); the factor is the quotient group
`N_i ⧸ N_{i−1}`, and `w↠` is `coveringWidth`. -/
structure VbSeries (G : Type u) [Group G] (b : ℕ∞) (k : ℕ) where
  /-- The terms `N₀, …, N_k`. -/
  N : Fin (k + 1) → Subgroup G
  /-- `N₀ = 1`. -/
  bot : N 0 = ⊥
  /-- `N_k = G`. -/
  top : N (Fin.last k) = ⊤
  /-- `N_{i−1} ≤ N_i`. -/
  le : ∀ i : Fin k, N i.castSucc ≤ N i.succ
  /-- `N_{i−1} ⊴ N_i`. -/
  normal : ∀ i : Fin k, ((N i.castSucc).subgroupOf (N i.succ)).Normal
  /-- Every factor lies in `V_b`. -/
  factor_mem : ∀ i : Fin k,
    coveringWidth (↥(N i.succ) ⧸ (N i.castSucc).subgroupOf (N i.succ)) ≤ b

/-- **`ℓ_b(G)`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), §8, p.8 (PDF p.9): "Let ℓ_b(G) be the least k such that there is a
subnormal series 1 = N₀ ⊴ N₁ ⊴ ⋯ ⊴ N_k = G, N_i/N_{i−1} ∈ V_b, or ∞ if none exists."

**Formalization Note.** Infimum in `ℕ∞`. -/
noncomputable def seriesLength (G : Type u) [Group G] (b : ℕ∞) : ℕ∞ :=
  sInf {D : ℕ∞ | ∃ k : ℕ, D = (k : ℕ∞) ∧ Nonempty (VbSeries G b k)}

/-- The normal-series variant of `ℓ_b(G)`. Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 16, p.8 (PDF p.9): the least length of
such a series in which "every N_i is required to be normal in G".

**Formalization Note.** Infimum in `ℕ∞`. -/
noncomputable def normalSeriesLength (G : Type u) [Group G] (b : ℕ∞) : ℕ∞ :=
  sInf {D : ℕ∞ | ∃ (k : ℕ) (S : VbSeries G b k), D = (k : ℕ∞) ∧ ∀ i, (S.N i).Normal}

end BlockSSM.Supplement


