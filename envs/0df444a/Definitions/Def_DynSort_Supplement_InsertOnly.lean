-- Prove2me | Definitions.Def_DynSort_Supplement_InsertOnly
-- name    : DynSort_Supplement_InsertOnly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:38:05.416203+00:00
-- url     : https://prove2.me/theorems/d4b66b07-2118-427f-a0c2-be59d84c8919
-- title:
--   Insertion-only update sequences and their inserted values
-- statement:
--   This module adds the insertion-only (online sorting) setting to the published fully dynamic sorting model `DynSort.OnlineAlg`.
--
--   1. An update sequence $\sigma$ is **insertion-only** if every update of $\sigma$ is an insertion $\mathrm{insert}(x)$ of a real $x$. On an array of $n$ cells, an insertion-only sequence that is valid has at most $n$ updates, and its elements remain in the array permanently.
--   2. The **inserted values** of $\sigma$ form the list $(x_1,\dots,x_k)$ of the reals inserted by $\sigma$, in arrival order (deletions are skipped).
--
--   For an insertion-only $\sigma$, $\mathrm{OPT}(x_1,\dots,x_k)=\max_j x_j-\min_j x_j$ is the optimal cost of the complete insertion sequence, the quantity that the Remark after Theorem 39 assumes known to the algorithm. These notions state the insertion-only results, Theorems 3 and 39, and the hypothesis of the reduction of Theorem 4.
--
--   **Formalization Note** For an insertion-only $\sigma$ and any legal arrangement after $\sigma$, the stored sequence is a permutation of the inserted values, so both have the same $\mathrm{OPT}$.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), §2, p.6 (PDF p.8), 'Insertion-Only and Fully Dynamic Updates'; Remark after Theorem 39, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_DynSort_OnlineAlg

namespace DynSort.Supplement

open DynSort

/-! # The insertion-only (online sorting) setting

Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §2, p.6 (PDF p.8), "Insertion-Only and Fully
Dynamic Updates"; Remark after Theorem 39, p.34 (PDF p.36).

In the insertion-only setting elements arrive one at a time and remain in the array permanently.
The Remark on p.34 speaks of "the optimal cost of the complete insertion sequence"; for an
insertion-only update sequence this is `opt` of the list of inserted values.

**Formalization Note.** These are predicates and functions on the published update sequences
`DynSort.Update` (`Definitions.Def_DynSort_OnlineAlg`). An insertion-only sequence on `n` cells is
`InsertOnly σ ∧ Valid n σ`, i.e. at most `n` insertions. For an insertion-only `σ` and any legal
arrangement `a` after `σ`, `seq σ a` is a permutation of `insertedValues σ`, so both have the
same `opt`.
-/

/-- **Insertion-only update sequence** (§2, p.6): every update of `σ` is an insertion. -/
def InsertOnly (σ : List Update) : Prop :=
  ∀ u ∈ σ, ∃ x : ℝ, u = Update.insert x

/-- **The inserted values** of `σ`, in arrival order (the payloads of its insertions). For an
insertion-only `σ`, `opt (insertedValues σ)` is "the optimal cost of the complete insertion
sequence" of the Remark on p.34. -/
def insertedValues (σ : List Update) : List ℝ :=
  σ.filterMap (fun u => match u with
    | .insert x => some x
    | .delete _ => none)

end DynSort.Supplement


