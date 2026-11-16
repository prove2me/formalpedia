-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_coverNumberFixed
-- name    : DDNNFNeg_Supplement_coverNumberFixed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:43:39.456729+00:00
-- url     : https://prove2.me/theorems/327e73c5-0bd5-4c77-8a95-f26cba1164ba
-- title:
--   Fixed-partition rectangle $b$-cover number $\mathrm{Cov}^{(A,B)}_b(f)$
-- statement:
--   Let $X$ be a finite set, $f : \{0,1\}^X \to \{0,1\}$ a Boolean function, $(A,B)$ a partition of $X$ and $b \in \{0,1\}$. A **rectangle** with respect to $(A,B)$ is a set $S \times T$ with $S \subseteq \{0,1\}^A$ and $T \subseteq \{0,1\}^B$. The **fixed-partition rectangle $b$-cover number** $\mathrm{Cov}^{(A,B)}_b(f)$ is the least $k$ such that there are rectangles $R_1, \dots, R_k$ with respect to $(A,B)$ with
--
--   $$f^{-1}(b) = \bigcup_{i=1}^k R_i.$$
--
--   It is the fixed-partition counterpart of the multi-partition cover number $\mathrm{Cov}^m_b$ and the right-hand side of the lifting Theorem 6.1.
--
--   **Formalization Note** The partition is encoded by $A$ (with $B = A^{\mathrm c}$) and may be any partition. The minimum always exists (singletons are rectangles); it is $0$ exactly when $f^{-1}(b) = \emptyset$.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §3.2, p.8

import Mathlib
import Definitions.Def_DDNNFNeg_IsRectangle

namespace DDNNFNeg.Supplement

/-- The fixed-partition rectangle `b`-cover number `Cov^{(A,B)}_b(f)` of `f : {0,1}^X → {0,1}`
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §3.2, p.8): the least `k` such that there are rectangles `R₁, …, R_k`, all with respect to
the one partition `(A, B)` of `X`, with `f⁻¹(b) = R₁ ∪ ⋯ ∪ R_k`.

**Formalization Note** The partition `(A, B)` is encoded by `A : Finset X`, with `B = Aᶜ`, as in
`DDNNFNeg.IsRectangle`. The partition is arbitrary (not required to be balanced). The set below
is never empty (the singletons of `f⁻¹(b)` are rectangles), so `sInf` is a genuine minimum; it is
`0` exactly when `f⁻¹(b) = ∅`. -/
noncomputable def coverNumberFixed {X : Type*} [Fintype X] [DecidableEq X] (A : Finset X)
    (b : Bool) (f : (X → Bool) → Bool) : ℕ :=
  sInf {k : ℕ | ∃ R : Fin k → Set (X → Bool), (∀ i, IsRectangle A (R i)) ∧
    (⋃ i, R i) = {x | f x = b}}

end DDNNFNeg.Supplement


