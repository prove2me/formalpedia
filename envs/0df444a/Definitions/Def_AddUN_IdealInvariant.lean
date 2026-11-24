-- Prove2me | Definitions.Def_AddUN_IdealInvariant
-- name    : AddUN_IdealInvariant
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:19:29.020739+00:00
-- url     : https://prove2.me/theorems/469ac3ef-08ca-45e0-a1ae-b29343ea8d97
-- title:
--   Ideal Invariant
-- statement:
--   Definitions and structural lemmas for Ideal Invariant, from VictorLiwentao (VictorLiwentao/open-logic-24-add-un; see pinned Apache-2.0 LICENSE and source headers)'s pinned Additivity of universally null sets and Goto Question 6.3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/IdealInvariant.lean

module
public import Mathlib.SetTheory.Cardinal.Basic
set_option autoImplicit false
@[expose] public section
@[expose] public section
universe u
open Cardinal Set
namespace IdealInvariant
variable {X : Type u} {I : Set (Set X)} {𝒜 : Set (Set X)} {A : Set X}
noncomputable def add (I : Set (Set X)) : Cardinal.{u} :=
  ⨅ 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ⋃₀ 𝒜 ∉ I}, #𝒜.1
noncomputable def cov (I : Set (Set X)) : Cardinal.{u} :=
  ⨅ 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ⋃₀ 𝒜 = univ}, #𝒜.1
noncomputable def non (I : Set (Set X)) : Cardinal.{u} :=
  ⨅ A : {A : Set X // A ∉ I}, #A.1
noncomputable def cof (I : Set (Set X)) : Cardinal.{u} :=
  ⨅ 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ∀ A ∈ I, ∃ B ∈ 𝒜, A ⊆ B}, #𝒜.1
end IdealInvariant


