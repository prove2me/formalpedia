-- Prove2me | Definitions.Def_LeanPool_UlmsTheorem_Ulm_Theorem
-- name    : LeanPool_UlmsTheorem_Ulm_Theorem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:57:53.003596+00:00
-- url     : https://prove2.me/theorems/2bfbc9c7-c19f-4ac6-a110-f01b247a246e
-- title:
--   Theorem
-- statement:
--   Definitions and structural lemmas for Theorem, from Elan Roth; LeanPool contributors's pinned Ulm’s theorem for abelian p-groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Theorem.lean

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Classification
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Invariance
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace UlmsTheorem
open Cardinal Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
end UlmsTheorem


