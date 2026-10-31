-- Prove2me | Definitions.Def_LeastMajorized_SchurConvex
-- name    : LeastMajorized_SchurConvex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:51.233336+00:00
-- url     : https://prove2.me/theorems/82775669-77cd-453e-bbd3-aaf7c4808917
-- title:
--   Schur-convex function $\Phi:\mathbb R^n\to\mathbb R$
-- statement:
--   For $x\in\mathbb R^n$ let $x^{\downarrow}$ be its non-increasing rearrangement. A vector $x$ is **majorized** by $y$, written $x\prec y$, if $\sum_{i=1}^k x^{\downarrow}_i\le\sum_{i=1}^k y^{\downarrow}_i$ for all $k\in N$ and $x(N)=y(N)$. A function $\Phi:\mathbb R^n\to\mathbb R$ is **Schur-convex** if it preserves the order of majorization:
--
--   $$
--   x\prec y\ \Longrightarrow\ \Phi(x)\le\Phi(y).
--   $$
--
--   Schur-convex functions are the symmetric objectives that a least majorized element minimizes simultaneously; they appear in Lemma 6 and in statement 3 of Theorem 5.
--
--   **Formalization Note** $x\prec y$ is the published definition `RetailVariety.Fashion.Majorized` (decreasing rearrangements via sorting permutations, equal totals, top-$k$ partial sums for $1\le k<n$), which is the paper's equivalent form "$x\prec^{\downarrow}y$ and $x(N)=y(N)$". Continuity is not part of the definition; it is a separate hypothesis wherever the paper says "continuous Schur-convex".
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, §3.1, p.7

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Majorization

namespace LeastMajorized

/-- **Schur-convex function**, Schoot Uiterkamp, arXiv:2201.06596v2, §3.1, p.7: "A function
`Φ: ℝⁿ → ℝ` is said to be Schur-convex if it preserves the order of majorization, i.e., if
`Φ(x) ≤ Φ(y)` whenever `x ≺ y`."

**Formalization Note** `x ≺ y` is the published `RetailVariety.Fashion.Majorized x y`: the
decreasing rearrangements `x↓ = x ∘ σx`, `y↓ = y ∘ σy` (antitone) have equal totals and
`Σ_{i=1}^k x↓ᵢ ≤ Σ_{i=1}^k y↓ᵢ` for `1 ≤ k < n`. This is the paper's equivalent form
"`x ≺↓ y` and `x(N) = y(N)`" (p.7; the case `k = n` of `≺↓` is the equality of totals).
Continuity is not part of the definition; it is a separate hypothesis wherever the paper
says "continuous Schur-convex". -/
def SchurConvex {n : ℕ} (Φ : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, RetailVariety.Fashion.Majorized x y → Φ x ≤ Φ y

end LeastMajorized


