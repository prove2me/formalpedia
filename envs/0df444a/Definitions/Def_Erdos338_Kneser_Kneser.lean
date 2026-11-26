-- Prove2me | Definitions.Def_Erdos338_Kneser_Kneser
-- name    : Erdos338_Kneser_Kneser
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:56:47.662607+00:00
-- url     : https://prove2.me/theorems/809a3829-b67f-45a7-af27-44f611a31ad9
-- title:
--   Kneser
-- statement:
--   Definitions and structural lemmas for Kneser, from Veljko Janoski (veljjanoski/erdos338-palomar; includes Kneser's theorem adapted under Apache-2.0 from Mantas Baksys and Yael Dillies in YaelDillies/misc-yd and definitions under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 338: restricted order of robust sets of positive lower density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/Kneser.lean

module
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Definitions.Def_Erdos338_Kneser_MulStab
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Function MulAction
open scoped Pointwise
variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}
namespace Finset
variable (s t)
end Finset


