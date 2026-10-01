-- Prove2me | Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
-- name    : LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T14:05:45.181783+00:00
-- url     : https://prove2.me/theorems/e10d48de-49fc-4e1d-b4d9-6e4a7cf3cd1d
-- title:
--   A cyclic-factor series for the wreath product
-- statement:
--   The diagonal central subgroup, base subgroup, and intermediate invariant subgroups used to build the supersolvable series for the wreath product of order $162$.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization interface.

import Mathlib
import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy.HeisenbergExample

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def diagonal : C3 →* G where
  toFun z := ⟨fun _ => z, 1⟩
  map_one' := rfl
  map_mul' := by intros; apply SemidirectProduct.ext <;> rfl

def Z : Subgroup G := diagonal.range
instance : DecidablePred (· ∈ Z) := fun x =>
  inferInstanceAs (Decidable (∃ z : C3, diagonal z = x))

instance : Z.Normal where
  conj_mem := by
    rintro _ ⟨z, rfl⟩ g
    have hc : ∀ z : C3, ∀ g : G, g * diagonal z * g⁻¹ = diagonal z := by decide
    rw [hc]
    exact ⟨z, rfl⟩

def baseSubgroup : Subgroup G := (SemidirectProduct.rightHom : G →* S).ker
instance : baseSubgroup.Normal := inferInstanceAs (SemidirectProduct.rightHom : G →* S).ker.Normal
instance : DecidablePred (· ∈ baseSubgroup) := fun x =>
  inferInstanceAs (Decidable (x.right = 1))

def V : Subgroup G := N ⊓ baseSubgroup
instance : V.Normal := inferInstanceAs (N ⊓ baseSubgroup).Normal
instance : DecidablePred (· ∈ V) := fun x => inferInstanceAs
  (Decidable (x ∈ N ∧ x ∈ baseSubgroup))

def M : Subgroup G := (sign.comp (SemidirectProduct.rightHom : G →* S)).ker
instance : M.Normal := inferInstanceAs (sign.comp (SemidirectProduct.rightHom : G →* S)).ker.Normal
instance : DecidablePred (· ∈ M) := fun x => inferInstanceAs (Decidable (sign x.right = 1))

def v : G := ⟨fun i => Multiplicative.ofAdd (![1, 2, 0] i), 1⟩















end LocalConjugacy.HeisenbergExample

end LocalConjugacy.Proof

end


