-- Prove2me | Definitions.Def_MatroidEquitability_IsBasePartition
-- name    : MatroidEquitability_IsBasePartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:49.916787+00:00
-- url     : https://prove2.me/theorems/3fe9239f-af71-4307-8c4e-1c6eca70330f
-- title:
--   Partition $E=B_1\sqcup\dots\sqcup B_k$ of the ground set into $k$ bases
-- statement:
--   A family $B_1,\dots,B_k$ of subsets is a **partition of the ground set of $M$ into bases** if
--
--   1. each $B_i$ is a base of $M$;
--   2. the $B_i$ are pairwise disjoint;
--   3. $\bigcup_i B_i=E$.
--
--   This is the object of the main theorem, and both 2 and 3 are essential: $k$ copies of one base would otherwise have equal weights.
--
--   **Formalization Note** The index set is `Fin k`. When $E=\emptyset$ the empty base is repeated, which the disjointness condition allows.
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Theorem 1, p.1 (PDF p.3)

import Mathlib

namespace MatroidEquitability

/-- `B₁, …, B_k` is a partition of the ground set of `M` into bases, `E = B₁ ⊔ ⋯ ⊔ B_k` (Theorem 1,
printed p.1 = PDF p.3 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)).

**Formalization Note.** The bases are indexed by `Fin k`, repetition of the empty base being allowed
when `E = ∅`. Both pairwise disjointness and the covering of `M.E` are required: without them `k`
copies of one base would qualify. -/
def IsBasePartition {α : Type*} {k : ℕ} (M : Matroid α) (B : Fin k → Set α) : Prop :=
  (∀ i, M.IsBase (B i)) ∧ Pairwise (Function.onFun Disjoint B) ∧ ⋃ i, B i = M.E

end MatroidEquitability


