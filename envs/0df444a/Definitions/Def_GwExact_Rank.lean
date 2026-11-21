-- Prove2me | Definitions.Def_GwExact_Rank
-- name    : GwExact_Rank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T20:20:41.242987+00:00
-- url     : https://prove2.me/theorems/59fcb459-fb30-4086-9686-2e73b6667d71
-- title:
--   Rank
-- statement:
--   Definitions and structural lemmas for Rank, from arhancanli and contributors's pinned Exact Gallai–van der Waerden numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GwExact
section Rename
variable {α : Type*} [DecidableEq α] (f : ℕ → α)
noncomputable def firstPos (i : ℕ) : ℕ := Nat.find (⟨i, rfl⟩ : ∃ j, f j = f i)
noncomputable def numCols (m : ℕ) : ℕ := ((Finset.range m).image f).card
noncomputable def rank (i : ℕ) : ℕ := numCols f (firstPos f i)
end Rename
end GwExact


