-- Prove2me | Definitions.Def_LocalConjugacy_Proof_CocycleZorn
-- name    : LocalConjugacy_Proof_CocycleZorn
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:20:42.792986+00:00
-- url     : https://prove2.me/theorems/e134c14a-106d-4c76-9a36-c589805a2503
-- title:
--   Partial cocycle extension
-- statement:
--   The predicate that a cocycle on a subgroup extends to a larger subgroup, including agreement on the original domain. It organizes the maximal-extension argument.
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

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Compactness
variable {J : Type*} [Group J] [TopologicalSpace J] [CompactSpace J]





end Compactness

section Extension
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

/-- A cocycle's cohomology class extends to a specified intermediate subgroup. -/
def Cocycle.ExtendsTo {P : Subgroup J} (f : Cocycle (N := N) P) (H : Subgroup J) : Prop :=
  ∃ (hPH : P ≤ H) (F : Cocycle (N := N) H), RestrictsTo hPH F f





end Extension

section Obstructions
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]















end Obstructions

section Invariance
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J] [TopologicalSpace N]
  [MulDistribMulAction J N] [ContinuousSMul J N]



end Invariance
end LocalConjugacy

end LocalConjugacy.Proof

end


