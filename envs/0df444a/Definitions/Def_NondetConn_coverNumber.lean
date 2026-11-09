-- Prove2me | Definitions.Def_NondetConn_coverNumber
-- name    : NondetConn_coverNumber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:21:38.835189+00:00
-- url     : https://prove2.me/theorems/22fbe0bf-5884-4855-921a-aa9acbf64d95
-- title:
--   1-rectangle cover number $C^1(f)$
-- statement:
--   Let $f : \alpha \times \beta \to \{0,1\}$ be a two-party function. A **1-monochromatic rectangle** is a product $R \times S$ with $R \subseteq \alpha$, $S \subseteq \beta$ on which $f$ is identically $1$. The **1-cover number** $C^1(f)$ is the least $k$ such that $k$ such rectangles (possibly overlapping) cover $f^{-1}(1)$:
--   $$
--   C^1(f) = \min\Bigl\{k : \exists\, R_1\times S_1, \dots, R_k \times S_k \text{ 1-monochromatic with } f^{-1}(1) \subseteq \textstyle\bigcup_l R_l \times S_l\Bigr\}.
--   $$
--
--   Its logarithm is the nondeterministic communication complexity of $f$, and the proof of Theorem 4.1 lower-bounds it by counting.
--
--   **Formalization Note** The cover predicate is the published `ExtensionComplexity.TSP.IsOneRectangleCover`. On finite input sets the minimum is over a nonempty set (singleton rectangles), so the infimum is never the junk value of an empty set.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §3 "Communication complexity", p.8 (PDF p.10), and proof of Theorem 4.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_SlackMatrix

namespace NondetConn

/-- **1-cover number** of a two-party function `f : α → β → Prop` (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac),
§3 "Communication complexity", p.8, and proof of Theorem 4.1, p.10): the least number `k` of
1-monochromatic rectangles `R₁ × S₁, …, R_k × S_k` (each containing only inputs with `f a b`)
that together cover `f⁻¹(1)`. Rectangles may overlap.

**Formalization Note** The cover predicate is the published
`ExtensionComplexity.TSP.IsOneRectangleCover`. On finite `α`, `β` the set of admissible `k` is
nonempty (one singleton rectangle per 1-input), so the `sInf` is the genuine minimum and never the
junk value `sInf ∅ = 0`. -/
noncomputable def coverNumber {α β : Type*} (f : α → β → Prop) : ℕ :=
  sInf {k : ℕ | ∃ R : Fin k → Set α × Set β, ExtensionComplexity.TSP.IsOneRectangleCover f R}

end NondetConn


