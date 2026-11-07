-- Prove2me | Definitions.Def_MatroidEquitability_IsBlock
-- name    : MatroidEquitability_IsBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:47.238672+00:00
-- url     : https://prove2.me/theorems/9d57a2bf-fb71-4142-aad0-419d49234a11
-- title:
--   Block of a matroid: $B$ and $E\setminus B$ are both bases
-- statement:
--   A set $B\subseteq E$ is a **block** of the matroid $M=(E,\mathcal I)$ if both $B$ and $E\setminus B$ are bases of $M$. A matroid is a **block matroid** if its ground set can be partitioned into two bases, that is, if it has a block.
--
--   The proof of the main theorem reduces to the block matroid obtained by restricting $M$ to the union of two bases.
--
--   **Formalization Note** No separate predicate is introduced for block matroids: the existence of a block expresses it.
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), §1.3, p.7 (PDF p.9)

import Mathlib

namespace MatroidEquitability

/-- A set `B` is a block of `M = (E, I)` if both `B` and `E \ B` are bases of `M` (§1.3, printed p.7 =
PDF p.9 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)).

**Formalization Note.** `M` is a block matroid exactly when some block exists, so there is no
separate predicate for block matroids. -/
def IsBlock {α : Type*} (M : Matroid α) (B : Set α) : Prop :=
  M.IsBase B ∧ M.IsBase (M.E \ B)

end MatroidEquitability


