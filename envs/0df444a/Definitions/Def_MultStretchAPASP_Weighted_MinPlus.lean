-- Prove2me | Definitions.Def_MultStretchAPASP_Weighted_MinPlus
-- name    : MultStretchAPASP_Weighted_MinPlus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:08:41.668193+00:00
-- url     : https://prove2.me/theorems/e363efee-cf87-427f-80e4-58fe326ecd09
-- title:
--   The (min, +)-product A ⋆ B, entrywise (1 + ε)-approximations, and the outputs of Algorithm 9
-- statement:
--   For matrices with entries in $[0,\infty]$, the **(min, +)-product** over a finite inner index set $K$ is
--   $$(A\star B)[x,y]=\min_{k\in K}\bigl(A[x,k]+B[k,y]\bigr)$$
--   (Definition 2.13, which allows $+\infty$ entries). A matrix $M$ is an **entrywise $(1+\varepsilon)$-approximation** of $A\star B$ on the entries $R\times C$ if
--   $$(A\star B)[x,y]\le M[x,y]\le(1+\varepsilon)\,(A\star B)[x,y]\qquad(x\in R,\ y\in C),$$
--   so an infinite entry is reproduced exactly. Algorithm 9, $\textsc{Offset\_Shifted\_AMPMM}(M_1,M_2,\mathrm{off}_1,\mathrm{off}_2,\varepsilon)$, subtracts $\mathrm{off}_i$ from every finite entry of $M_i$, takes any entrywise $(1+\varepsilon)$-approximation $\bar M$ of $\bar M_1\star\bar M_2$, and adds $\mathrm{off}_1+\mathrm{off}_2$ back to every finite entry; a possible output of Algorithm 9 is any matrix obtained this way.
--
--   **Formalization Note.** Matrices are functions of a row and a column index; the relevant rows, inner indices and columns are finite sets `R`, `K`, `C`. Subtraction is the truncated subtraction of `ℝ≥0∞`: it leaves `⊤` unchanged and is exact when an entry is at least its offset, which is Algorithm 9's input guarantee. Offsets are non-negative reals. The black box of Algorithm 9 is quantified: every admissible $\bar M$ gives a possible output.
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 7, Definition 2.13 and Theorem 2.15; p. 20, Algorithm 9

import Mathlib

set_option autoImplicit false

open scoped ENNReal NNReal

namespace MultStretchAPASP.Weighted

/-!
# The (min, +)-product, its entrywise (1 + ε)-approximations, and Algorithm 9

Saggi, Sapir, *Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime*,
arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), Definition 2.13 (p. 7),
Theorem 2.15 (p. 7) and Algorithm 9 (p. 20).

* Matrices have entries in `ℝ≥0∞` (non-negative reals and `+∞`, as Definition 2.13 allows for the
  (min, +)-product). A matrix is a function `A : α → ι → ℝ≥0∞` of a row and a column index; the
  rows, inner indices and columns that matter are given as finite sets `R`, `K`, `C` (an
  `l₁ × l₂` matrix of the paper is the restriction to `R × K`).
* `minPlus K A B x y = (A ⋆ B)[x, y] = min_{k ∈ K} (A[x, k] + B[k, y])` (`⊤` for empty `K`).
* `IsApproxMinPlus ε R K C A B M`: `M` is an entrywise `(1 + ε)`-approximation of `A ⋆ B` on
  `R × C`: `(A ⋆ B)[x, y] ≤ M[x, y] ≤ (1 + ε)·(A ⋆ B)[x, y]` (so an infinite entry is exact).
* `IsOffsetShiftedOut ε R K C M₁ M₂ off₁ off₂ M`: `M` is a possible output of Algorithm 9,
  `Offset_Shifted_AMPMM(M₁, M₂, off₁, off₂, ε)`: `M̄ᵢ` subtracts `offᵢ` from every finite entry of
  `Mᵢ` (truncated subtraction in `ℝ≥0∞`, which leaves `⊤` unchanged and is exact when the
  entry is at least the offset, as Algorithm 9's input guarantees), `M̄` is any entrywise
  `(1 + ε)`-approximation of `M̄₁ ⋆ M̄₂`, and `M` adds `off₁ + off₂` back to every entry (`⊤`
  stays `⊤`). The black box of line 2 is quantified: every admissible `M̄` is a possible run.
  Offsets are non-negative reals.
-/

/-- `(A ⋆ B)[x, y] = min_{k ∈ K} (A[x, k] + B[k, y])`. -/
noncomputable def minPlus {α ι β : Type*} (K : Finset ι) (A : α → ι → ℝ≥0∞)
    (B : ι → β → ℝ≥0∞) (x : α) (y : β) : ℝ≥0∞ :=
  ⨅ k ∈ K, A x k + B k y

/-- `M` is an entrywise `(1 + ε)`-approximation of `A ⋆ B` on the entries `R × C`. -/
def IsApproxMinPlus {α ι β : Type*} (ε : ℝ) (R : Finset α) (K : Finset ι) (C : Finset β)
    (A : α → ι → ℝ≥0∞) (B : ι → β → ℝ≥0∞) (M : α → β → ℝ≥0∞) : Prop :=
  ∀ x ∈ R, ∀ y ∈ C,
    minPlus K A B x y ≤ M x y ∧ M x y ≤ ENNReal.ofReal (1 + ε) * minPlus K A B x y

/-- Algorithm 9: `M` is a possible output of `Offset_Shifted_AMPMM(M₁, M₂, off₁, off₂, ε)` on the
entries `R × C`. -/
def IsOffsetShiftedOut {α ι β : Type*} (ε : ℝ) (R : Finset α) (K : Finset ι) (C : Finset β)
    (M₁ : α → ι → ℝ≥0∞) (M₂ : ι → β → ℝ≥0∞) (off₁ off₂ : ℝ≥0) (M : α → β → ℝ≥0∞) : Prop :=
  ∃ Mbar : α → β → ℝ≥0∞,
    IsApproxMinPlus ε R K C (fun x k => M₁ x k - (off₁ : ℝ≥0∞)) (fun k y => M₂ k y - (off₂ : ℝ≥0∞))
      Mbar ∧
    ∀ x ∈ R, ∀ y ∈ C, M x y = Mbar x y + ((off₁ : ℝ≥0∞) + (off₂ : ℝ≥0∞))

end MultStretchAPASP.Weighted


