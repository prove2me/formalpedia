-- Prove2me | Definitions.Def_DDNNFNeg_coverNumberMulti
-- name    : DDNNFNeg_coverNumberMulti
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:48.108066+00:00
-- url     : https://prove2.me/theorems/cb4d0f20-6277-4fd3-9360-a60ec95a8a14
-- title:
--   Multi-partition rectangle $b$-cover number $\mathrm{Cov}^m_b(f)$
-- statement:
--   For a Boolean function $f : \{0,1\}^X \to \{0,1\}$ with $|X| \ge 2$ and a bit $b \in \{0,1\}$, the **multi-partition rectangle $b$-cover number** $\mathrm{Cov}^m_b(f)$ is the least $k$ such that there exist rectangles $R_1, \dots, R_k$, each with respect to a (possibly different) balanced partition, with
--   $$
--   f^{-1}(b) = \bigcup_{i=1}^{k} R_i .
--   $$
--
--   This is the quantity that lower-bounds DNNF size (Theorem 3.1).
--
--   **Formalization Note** The least $k$ is an infimum over $\mathbb N$. For $|X| \ge 2$ a balanced partition exists and singletons are rectangles, so the infimum is attained; for $|X| \le 1$ Lean's convention gives $0$, and every statement using this number assumes $|X| \ge 2$, as the paper does.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §3.2, p.8

import Mathlib
import Definitions.Def_DDNNFNeg_IsBalanced
import Definitions.Def_DDNNFNeg_IsRectangle

namespace DDNNFNeg

/-- The multi-partition rectangle `b`-cover number `Cov^m_b(f)` of `f : {0,1}^X → {0,1}`
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §3.2, p.8): the least `k` such that there are rectangles `R₁, …, R_k`, each with
respect to a (possibly different) balanced partition, with `f⁻¹(b) = R₁ ∪ ⋯ ∪ R_k`.

**Formalization Note** The paper defines `Cov^m_b(f)` only for `|X| ≥ 2`, where a balanced
partition exists and singletons are rectangles, so the set below is nonempty. Lean's
`sInf ∅ = 0` is the value for `|X| ≤ 1`; every statement using this number assumes
`2 ≤ |X|`. -/
noncomputable def coverNumberMulti {X : Type*} [Fintype X] [DecidableEq X] (b : Bool)
    (f : (X → Bool) → Bool) : ℕ :=
  sInf {k : ℕ | ∃ R : Fin k → Set (X → Bool),
    (∀ i, ∃ A : Finset X, IsBalanced A ∧ IsRectangle A (R i)) ∧
    (⋃ i, R i) = {x | f x = b}}

end DDNNFNeg


