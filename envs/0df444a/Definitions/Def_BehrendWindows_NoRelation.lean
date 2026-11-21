-- Prove2me | Definitions.Def_BehrendWindows_NoRelation
-- name    : BehrendWindows_NoRelation
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-21T01:46:25.668274+00:00
-- url     : https://prove2.me/theorems/e599aff4-31a2-4410-9991-eaf297d9fde4
-- title:
--   No $L$-relation among three distinct points
-- statement:
--   Let $T\subset\mathbb{Z}$ be finite and $L\in\mathbb{N}$. The set $T$ has **no $L$-relation** if there are no three pairwise distinct elements $s_1,s_2,s_3\in T$ and integers $i,j$ with
--
--   1. $i\neq 0$, $j\neq 0$, $i\neq j$,
--   2. $|i|\le L$ and $|j|\le L$,
--
--   such that
--
--   $$j\,(s_2-s_1)=i\,(s_3-s_1).$$
--
--   This is the form in which the property is stated in the Lean development accompanying L. Alpöge's November 2026 announcement. It sits between two sparseness conditions: $(2L+1)$-sparse sets have no $L$-relation, and sets with no $L$-relation are $(L+1)$-sparse.
-- source:
--   No published source states the version uniform in m; statement from the mission proposal, relation form; L. Alpöge, Remark (20 Nov 2026), https://alpo.ge/remark.pdf

import Mathlib

namespace BehrendWindows

/-- No `L`-relation: no three distinct elements `s₁, s₂, s₃` of `T` satisfy
`j * (s₂ - s₁) = i * (s₃ - s₁)` for distinct non-zero integers `i, j` with
`|i|, |j| ≤ L`. -/
def NoRelation (T : Finset ℤ) (L : ℕ) : Prop :=
  ∀ s₁ ∈ T, ∀ s₂ ∈ T, ∀ s₃ ∈ T, s₁ ≠ s₂ → s₁ ≠ s₃ → s₂ ≠ s₃ →
    ∀ i j : ℤ, i ≠ 0 → j ≠ 0 → i ≠ j → |i| ≤ L → |j| ≤ L →
      j * (s₂ - s₁) ≠ i * (s₃ - s₁)

end BehrendWindows


