-- Prove2me | Definitions.Def_TractableComposite_prodSimplex
-- name    : TractableComposite_prodSimplex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:45.492051+00:00
-- url     : https://prove2.me/theorems/67c8b885-6806-4b7a-bdc7-49f46786adb2
-- title:
--   A product of simplices given by vertex lists
-- statement:
--   Given, for each $i\in\{1,\dots,d\}$, points $\upsilon_{i0},\dots,\upsilon_{in}\in\mathbb R^{n+1}$, this is the product
--
--   $$\prod_{i=1}^d\operatorname{conv}\{\upsilon_{i0},\dots,\upsilon_{in}\}\subseteq\mathbb R^{d\times(n+1)}.$$
--
--   It describes the polytope $Q$ (vertices (3)), the polytope $R$ of Lemma 2 and the product $S$ of §2.2.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), §2.2, p.7; Lemma 2, p.10; (3), p.4

import Mathlib

namespace TractableComposite

/-- **A Cartesian product of simplices given by their vertices.** For
`υ : Fin d → Fin (n+1) → (Fin (n+1) → ℝ)`, `prodSimplex υ = ∏ᵢ conv{υᵢ₀, …, υᵢₙ}`.
He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), §2.2, p.7 (`S = ∏ Sᵢ`), Lemma 2, p.10 (`R = ∏ Rᵢ`), (3)–(4), p.4 (`Q = ∏ Qᵢ`).

**Formalization Note.** A point of the product is `r : Fin d → Fin (n+1) → ℝ` with `r i ∈ conv(range (υ i))`. -/
def prodSimplex {d n : ℕ} (υ : Fin d → Fin (n + 1) → (Fin (n + 1) → ℝ)) : Set (Fin d → Fin (n + 1) → ℝ) :=
  {r | ∀ i, r i ∈ convexHull ℝ (Set.range (υ i))}

end TractableComposite


