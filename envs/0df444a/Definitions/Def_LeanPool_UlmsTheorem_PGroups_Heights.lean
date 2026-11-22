-- Prove2me | Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
-- name    : LeanPool_UlmsTheorem_PGroups_Heights
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:53:34.236592+00:00
-- url     : https://prove2.me/theorems/124b599d-e37e-40fa-9402-9cd4a0bd92c6
-- title:
--   Heights
-- statement:
--   Definitions and structural lemmas for Heights, from Elan Roth; LeanPool contributors's pinned Ulm’s theorem for abelian p-groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Heights.lean

module
public import Mathlib.Data.ENat.Lattice
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Mathlib.Algebra.Module.NatInt
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace UlmsTheorem
variable (p : ℕ)
def IsPrimaryPGroup (G : Type*) [AddCommGroup G] : Prop :=
  ∀ x : G, ∃ n : ℕ, p ^ n • x = 0
def IsPReduced (G : Type*) [AddCommGroup G] : Prop :=
  ∃ α : Ordinal.{0}, ulmSubgroup p α (G := G) = ⊥
structure IsReducedPGroup (G : Type*) [AddCommGroup G] : Prop where
  primary : IsPrimaryPGroup p G
  reduced : IsPReduced p G
def IsPSeparable (G : Type*) [AddCommGroup G] : Prop :=
  ∀ x : G, (∀ n : ℕ, ∃ y : G, p ^ n • y = x) → x = 0
section ReducedLemmas
variable {G : Type*} [AddCommGroup G]
end ReducedLemmas
noncomputable def pHeight {G : Type*} [AddCommGroup G] (x : G) : ℕ∞ :=
  letI : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then ⊤ else sSup (WithTop.some '' {n : ℕ | ∃ y : G, p ^ n • y = x})
section HeightLemmas
variable {G : Type*} [AddCommGroup G]
end HeightLemmas
end UlmsTheorem


