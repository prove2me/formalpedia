-- Prove2me | Definitions.Def_BinaryQueryLB_Supplement_strongAnswer
-- name    : BinaryQueryLB_Supplement_strongAnswer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:49:49.822004+00:00
-- url     : https://prove2.me/theorems/1ea8c8e0-81e6-4d09-b402-bc1a971983f9
-- title:
--   Answer $\big(f(y),\langle v,G(f,y)\rangle\big)$ of the strong oracle $O^*$
-- statement:
--   Under a first-order chart $G$, the strong oracle $O^*$ answers the query $(y,v)$ on the function $f$ by
--   $$
--   \big(f(y),\ \langle v,G(f,y)\rangle\big)\in\mathbb R\times\mathbb R,
--   $$
--   the exact value of $f$ at $y$ together with one exact linear measurement of the reported subgradient, with the Euclidean inner product of $\mathbb R^d$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.2, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_Chart

namespace BinaryQueryLB.Supplement

/-- **Answer of the strong oracle O\*.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.2, p.12: "The oracle `O∗` answers a query `(y, v)` with `y ∈ X` and `v ∈ R^d` by the exact pair
`(f(y), ⟨v, g_f(y)⟩)`", where `g_f(y) = G(f, y)` under the chart `G` (Definition 2.2, p.11).

`strongAnswer G f (y, v) = (f y, ⟨v, G f y⟩)`, with the Euclidean inner product of ℝ^d.

**Formalization Note.** ℝ^d is `EuclideanSpace ℝ (Fin d)`, whose inner product is the Euclidean
one `∑ᵢ vᵢ gᵢ`. -/
noncomputable def strongAnswer {d : ℕ} (G : BinaryQueryLB.Chart d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : ℝ × ℝ :=
  (f q.1, inner ℝ q.2 (G f q.1))

end BinaryQueryLB.Supplement


