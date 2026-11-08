-- Prove2me | Definitions.Def_TightClock_IsGoodTree
-- name    : TightClock_IsGoodTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:25:00.424284+00:00
-- url     : https://prove2.me/theorems/8c21f704-ad76-47a9-af38-a4c5c7e43a68
-- title:
--   Good tree, Definition 6.8
-- statement:
--   A realized tree is **good** if at every state $J$ fewer than $n$ nodes are exceptional, and at the initial state $J^0$ no node is exceptional.
--
--   **Formalization Note** The first clause ranges over all of $\{0,\dots,L,\bot\}^n$, including unreachable states. Nodes are counted by index, not by bidder set.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Definition 6.8, §6.5, p.43 (PDF p.46)

import Mathlib
import Definitions.Def_TightClock_IsExceptional
import Definitions.Def_TightClock_initialState

set_option autoImplicit false

namespace TightClock

open Classical in
/-- Definition 6.8: a tree is good if at every state fewer than `n` nodes are exceptional, and at the initial
state `J⁰` no node is exceptional. Afshinmehr et al., manuscript (STOC 2027 submission), §6.5, p.43 (PDF 46).

**Formalization Note** "Every state" is all of `{0, …, L, ⊥}ⁿ`, including unreachable states. Nodes are
counted by index, not by bidder set. -/
def IsGoodTree {q L : ℕ} (T : Tree q L) : Prop :=
  (∀ J : State q L, (Finset.univ.filter (IsExceptional T J)).card < bidderCount q L) ∧
    ∀ D : NonrootNode q L, ¬ IsExceptional T (initialState q L) D

end TightClock


