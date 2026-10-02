-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_hull
-- name    : LeblSCV_Pseudoconvex_hull
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T04:03:09.870364+00:00
-- url     : https://prove2.me/theorems/c1deda9f-486d-4db5-b9c5-80c2d0fc0b10
-- title:
--   Definition 2.5.1 — hull of $K$ with respect to a class $\mathcal{F}$
-- statement:
--   Let $\mathcal{F}$ be a class of extended-real-valued functions ($\mathbb{R} \cup \{-\infty, \infty\}$) defined on an open set $U$. For $K \subset U$, the **hull** of $K$ with respect to $\mathcal{F}$ is
--   $$\widehat{K} = \left\{ x \in U : f(x) \le \sup_{y \in K} f(y) \text{ for all } f \in \mathcal{F} \right\}.$$
--
--   The hull depends on $U$, because $\mathcal{F}$ consists of functions defined on $U$.
--
--   **Formalization Note.** The functions take values in `EReal`, a complete lattice, so the supremum is the genuine one ($-\infty$ for empty $K$). Only the values of each $f$ at points of $U$ enter. The definition is stated for an arbitrary type $X$ in place of $\mathbb{R}^n$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 90, Definition 2.5.1

import Mathlib

namespace LeblSCV.Pseudoconvex

/-- Definition 2.5.1 (Lebl, p. 90), hull: for a class `𝓕` of extended-real-valued functions
defined on the open set `U` and `K ⊂ U`, the hull of `K` with respect to `𝓕` is
`K̂ = {x ∈ U : f(x) ≤ sup_{y ∈ K} f(y) for all f ∈ 𝓕}`.
Extended reals are `EReal = ℝ ∪ {−∞, ∞}` (footnote on p. 90), a complete lattice, so the
supremum is the genuine one (`−∞` for empty `K`). Only the values of each `f` on `U` enter. -/
def hull {X : Type*} (U : Set X) (𝓕 : Set (X → EReal)) (K : Set X) : Set X :=
  {x | x ∈ U ∧ ∀ f ∈ 𝓕, f x ≤ ⨆ y ∈ K, f y}

end LeblSCV.Pseudoconvex


