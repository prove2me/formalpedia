-- Prove2me | Definitions.Def_SchedComplexity_Partition_PartitionProblem
-- name    : SchedComplexity_Partition_PartitionProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:46:57.984189+00:00
-- url     : https://prove2.me/theorems/e9868710-1543-40bc-8ab9-7dcabe903bfc
-- title:
--   PARTITION over positive integers (Theorem 2(a)) and its binary language
-- statement:
--   **PARTITION** (Brucker, Lenstra & Rinnooy Kan, Theorem 2(a)): *given positive integers $a_1,\dots,a_t$, does there exist a subset $S \subset T = \{1,\dots,t\}$ such that*
--
--   $$\sum_{j\in S} a_j \;=\; \sum_{j\in T-S} a_j\ ?$$
--
--   Here $S \subset T$ means an arbitrary subset; since all $a_j$ are positive, $S=\emptyset$ and $S=T$ are solutions only when $t=0$.
--
--   1. The predicate *PartitionSolvable* says that the list $a=(a_1,\dots,a_t)$ admits such a subset $S$.
--   2. The language $L_{\mathrm{PARTITION}}$ consists of the binary codes of the lists $(a_1,\dots,a_t)$ whose entries are all **positive** and which admit a partition. The code writes each $a_j$ in binary, least significant bit first, followed by a separator symbol (the published encoding `ProjSchedTW.Complexity.Encoding.encNats`).
--
--   This is the source language of both reductions of Theorem 3.
--
--   **Formalization Note** Indices are 0-based (`Fin t`). Positivity is part of the language, not of the predicate: a code of a list with a zero entry is not in the language. The published `ProjSchedTW.Complexity.partitionLang` (Neumann, Schwindt & Zimmermann) allows zero sizes and is therefore a different language; only its alphabet `BSym` and the code `encNats` are reused.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 14, Theorem 2(a)

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace SchedComplexity.Partition

open ProjSchedTW.Complexity (BSym encNats)

/-- PARTITION (Brucker, Lenstra & Rinnooy Kan 1975, Theorem 2(a), p. 14): the integers
`a_1, …, a_t` (the list `a`, `t = a.length`, indices `j < t`) admit a subset `S` of the
index set `T` with `Σ_{j ∈ S} a_j = Σ_{j ∈ T - S} a_j`. The paper's `S ⊂ T` means "subset";
`S` ranges over all subsets of `T`, including `∅` and `T`. Positivity of the `a_j` is part of
the language `partitionLang`, not of this predicate. -/
def PartitionSolvable (a : List ℕ) : Prop :=
  ∃ S : Finset (Fin a.length), ∑ j ∈ S, a.get j = ∑ j ∈ Sᶜ, a.get j

/-- The PARTITION language (Theorem 2(a), p. 14): the binary codes `encNats [a_1, …, a_t]` of
the lists of **positive** integers that admit a partition. A code of a list with a zero entry is
not in the language. -/
def partitionLang : CookPvsNP.Lang BSym :=
  { c | ∃ a : List ℕ, (∀ x ∈ a, 0 < x) ∧ PartitionSolvable a ∧ c = encNats a }

end SchedComplexity.Partition


