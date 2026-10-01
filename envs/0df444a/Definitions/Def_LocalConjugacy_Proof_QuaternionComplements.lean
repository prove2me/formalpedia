-- Prove2me | Definitions.Def_LocalConjugacy_Proof_QuaternionComplements
-- name    : LocalConjugacy_Proof_QuaternionComplements
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:36:50.390607+00:00
-- url     : https://prove2.me/theorems/6ee855a4-b97e-4759-98ee-a61d9070f6d9
-- title:
--   The two complements in the quaternion example
-- statement:
--   The semidirect product $Q_8\rtimes S_3$, its sign section, and the graph subgroup of that section, which is the second complement compared with the standard symmetric factor.
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
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Quaternion
import Definitions.Def_LocalConjugacy_Proof_QuaternionCohomology
import Definitions.Def_LocalConjugacy_Proof_QuaternionMatrices
import Definitions.Def_LocalConjugacy_Proof_QuaternionAction

/-! Supporting definitions and the structural proofs required by their types and values. -/

section


/-! The two complements underlying the quaternion obstruction. Local conjugators
come from the Sylow coboundaries, while a finite certificate rules out a global
conjugator in the entire 48-element ambient group. -/
namespace LocalConjugacy.Proof.QuaternionComplements

set_option maxRecDepth 20000
set_option maxHeartbeats 0

abbrev G := Q8 ⋊[quaternionAction] S3

/-- Normal forms enumerate the 48 ambient elements for the finite certificates. -/
instance : Fintype G := Fintype.ofEquiv (Q8 × S3) SemidirectProduct.equivProd.symm

/-- Coordinate equality avoids proof-transport reduction in the generic
semidirect-product decision procedure. -/
instance (priority := high) : DecidableEq G := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right)
    ⟨fun h => SemidirectProduct.ext h.1 h.2,
     fun h => ⟨congrArg SemidirectProduct.left h, congrArg SemidirectProduct.right h⟩⟩

/-- The nontrivial central sign cocycle in the symmetric-group presentation. -/
def signValue (s : S3) : Q8 := LocalConjugacy.QuaternionExample.signCocycle (dihedralEquiv.symm s)

/-- The graph of the sign cocycle is a homomorphic section of the projection. -/
def signSection : S3 →* G where
  toFun s := ⟨signValue s, s⟩
  map_one' := by decide
  map_mul' := by decide

/-- The second complement, explicitly as the sign graph. -/
def secondComplement : Subgroup G := signSection.range

/-- Decidable membership uses the six possible section values. -/
instance : DecidablePred (· ∈ secondComplement) := fun x =>
  inferInstanceAs (Decidable (∃ s : S3, signSection s = x))

/-- Decidable membership in the normal quaternion factor. -/
instance : DecidablePred (· ∈ quaternionKernel quaternionAction) := fun x =>
  inferInstanceAs (Decidable (∃ q : Q8, (SemidirectProduct.inl : Q8 →* G) q = x))











end LocalConjugacy.Proof.QuaternionComplements

end


