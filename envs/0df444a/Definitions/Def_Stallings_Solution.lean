-- Prove2me | Definitions.Def_Stallings_Solution
-- name    : Stallings_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:14:21.313415+00:00
-- url     : https://prove2.me/theorems/de5281d2-f225-40d6-847b-603408b941fd
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Arthur Freitas Ramos (Arthur742Ramos/stallings-folding; see pinned Apache-2.0 LICENSE and PROVENANCE.md)'s pinned Verified Stallings folding for finitely generated subgroups of F2 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Solution.lean

import Definitions.Def_Stallings
set_option autoImplicit true
namespace Stallings
def completeStatement (S : List (List (Fin 2 × Bool))) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (base : V)
    (next : V → (Fin 2 × Bool) → Option V),
    (∀ v x w, next v x = some w → next w (x.1, !x.2) = some v) ∧
    ∀ g : FreeGroup (Fin 2),
      (let run : List (Fin 2 × Bool) → Option V := fun word =>
        word.foldl (fun state letter =>
          state.bind fun vertex => next vertex letter) (some base)
       run (FreeGroup.toWord g) = some base) ↔
        g ∈ Subgroup.closure
          (Set.range fun i : Fin S.length => FreeGroup.mk (S.get i))
end Stallings


