-- Prove2me | Definitions.Def_LocalConjugacy_Proof_CocycleRebase
-- name    : LocalConjugacy_Proof_CocycleRebase
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:21:42.568472+00:00
-- url     : https://prove2.me/theorems/611e5dd2-7e34-47c7-8c74-725d37137889
-- title:
--   Changing the ambient subgroup of a cocycle
-- statement:
--   Conversions between a cocycle on a subgroup and its presentation as a cocycle on the top subgroup of that subgroup, retaining the induced coefficient action.
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

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

namespace Cocycle

/-- Regard a cocycle on an ambient subgroup as a cocycle on the whole subgroup
viewed as a group in its own right. -/
def subgroupTop {L : Subgroup J} (f : Cocycle (N := N) L) :
    Cocycle (J := L) (N := N) ⊤ where
  toFun x := f.toFun x
  continuous_toFun := f.continuous_toFun.comp continuous_subtype_val
  map_mul x y := f.map_mul x y

def ofSubgroupTop {L : Subgroup J} (f : Cocycle (J := L) (N := N) ⊤) :
    Cocycle (N := N) L where
  toFun x := f.toFun ⟨x, trivial⟩
  continuous_toFun := f.continuous_toFun.comp (continuous_id.subtype_mk _)
  map_mul x y := f.map_mul ⟨x, trivial⟩ ⟨y, trivial⟩

/-- Restrict the ambient group used for the cocycle action, without changing
the domain subgroup or the values. -/
def onSubgroup {L K : Subgroup J} (f : Cocycle (N := N) K) :
    Cocycle (J := L) (N := N) (K.subgroupOf L) where
  toFun x := f.toFun ⟨x, x.property⟩
  continuous_toFun := f.continuous_toFun.comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
  map_mul x y := f.map_mul ⟨x, x.property⟩ ⟨y, y.property⟩



end Cocycle



end LocalConjugacy

end LocalConjugacy.Proof

end


