-- Prove2me | Definitions.Def_XOSMax_Supplement_orderClassCount
-- name    : XOSMax_Supplement_orderClassCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:33:17.061849+00:00
-- url     : https://prove2.me/theorems/f7179369-e06c-5723-86eb-5a05f01277d9
-- title:
--   Number of order-equivalence classes of $k$-XOS functions
-- statement:
--   Two set functions are order-equivalent when they induce the same comparison relation on every pair of subsets. The quantity $N_{k,n}$ is the number of comparison relations realized by $k$-XOS functions on $[n]$.
--
--   Counting realized relations makes this the true finite number of equivalence classes, rather than the cardinality of the uncountable function space.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, footnote 3, p.2; Section 4, p.13

import Mathlib
import Definitions.Def_XOSMax_IsKXOS

namespace XOSMax.Supplement

open XOSMax

/-- The number of order-equivalence classes of `k`-XOS functions on `[n]`: a class is represented
by its binary comparison relation `f(X) ≤ f(Y)` (Filmus, Kawase, Kobayashi & Yamaguchi,
arXiv:1811.09045v3, footnote 3, p.2, and §4, p.13).

**Formalization Note** This counts realized relations rather than real-valued functions. The carrier
of relations is finite, so `Set.ncard` is the actual finite cardinality rather than its default value
on an infinite set. Additive functions are the case `k=1`, exactly as in the paper. -/
noncomputable def orderClassCount (k n : ℕ) : ℕ :=
  Set.ncard {R : Finset (Fin n) → Finset (Fin n) → Prop |
    ∃ f : Finset (Fin n) → ℝ,
      IsKXOS k f ∧ ∀ X Y, R X Y ↔ f X ≤ f Y}

end XOSMax.Supplement


