-- Prove2me | Definitions.Def_ReentrantScheduling_FBFS_Supplement_Policies
-- name    : ReentrantScheduling_FBFS_Supplement_Policies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T13:14:36.721793+00:00
-- url     : https://prove2.me/theorems/9e839e89-41fb-423f-a0d3-13a4da2e5127
-- title:
--   §VII — global IFBFS, ULBFS and CFLBFS buffer rankings
-- statement:
--   Let $B$ be all dependent pairs $(p,i)$ of part type and route stage. A global buffer ranking is a bijection from $B$ to the consecutive ranks $0,\ldots,|B|-1$. At a common center, lower rank has higher priority.
--
--   IFBFS preserves each type's forward order globally:
--
--   $$i<j\implies\beta(p,i)<\beta(p,j).$$
--
--   ULBFS concatenates the types' entire reverse routes in any total order of the types. CFLBFS partitions the types into a reverse set $P_L$ and its forward complement $P_F$. Each reverse type occupies one contiguous reverse-route block; each forward type preserves its forward route order and can interleave with other forward types and whole reverse blocks. Either set may be empty. The reverse-block identity is
--
--   $$\beta(p,i)=\beta(p,l_p-1)+(l_p-1-i),\qquad p\in P_L,$$
--
--   with 0-based stages $0\le i<l_p$. These predicates specify exactly the global policy families needed by Theorem 5; they impose no stability conclusion.
--
--   **Formalization Note** Ranks are finite bijections. ULBFS explicitly quantifies over every permutation of types. The CFLBFS block identity uses natural subtraction only on stages below the positive route length; it is exact there, including a one-stage route.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1414, §VII, IFBFS, ULBFS, CFLBFS and dispatch by total buffer ordering

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Supplement_MultipleLines

namespace ReentrantScheduling.FBFS.Supplement

namespace MultipleLines

variable (N : MultipleLines)

/-- A bijective global rank of all buffers: every position is occupied once. -/
abbrev Ranking := N.Buffer ≃ Fin (Fintype.card N.Buffer)

/-- IFBFS preserves each type's forward route globally, even across different centers. -/
def IFBFS (β : N.Ranking) : Prop :=
  ∀ p (i j : Fin (N.l p)), i < j → β ⟨p, i⟩ < β ⟨p, j⟩

/-- ULBFS concatenates intact reversed routes in any total order of types. -/
def ULBFS (β : N.Ranking) : Prop :=
  ∃ typeOrder : Fin N.P ≃ Fin N.P,
    ∀ (a b : N.Buffer), β a < β b ↔
      (typeOrder a.1 < typeOrder b.1 ∨ (a.1 = b.1 ∧ b.2.val < a.2.val))

/-- CFLBFS: P_L is the set of reversed types; its complement P_F is forward.
For each reversed type the rank of stage i is its last stage's rank plus l_p-1-i.
Thus its entire reverse route is contiguous. Empty P_L and empty P_F are allowed. -/
def CFLBFS (β : N.Ranking) (P_L : Set (Fin N.P)) : Prop :=
  (∀ p, p ∈ P_L → ∀ i : Fin (N.l p),
    (β ⟨p, i⟩).val =
      (β ⟨p, ⟨N.l p - 1, by have := N.l_pos p; omega⟩⟩).val + (N.l p - 1 - i.val)) ∧
  (∀ p, p ∉ P_L → ∀ (i j : Fin (N.l p)), i < j → β ⟨p, i⟩ < β ⟨p, j⟩)

end MultipleLines

end ReentrantScheduling.FBFS.Supplement


