-- Prove2me | Definitions.Def_LocalConjugacy_Proof_FiniteCoefficientSubgroup
-- name    : LocalConjugacy_Proof_FiniteCoefficientSubgroup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:23:53.47007+00:00
-- url     : https://prove2.me/theorems/dac9d995-3f73-4550-9fa3-e4fd15220bc6
-- title:
--   Restricting the coefficient group
-- statement:
--   The induced action on an invariant coefficient subgroup and the cocycle obtained by corestricting to that subgroup when all values lie in it.
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
import Definitions.Def_LocalConjugacy_Proof_CocycleProducts

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy



section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [CompactSpace J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]



end

section Subgroup
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N]
  [MulDistribMulAction J N]
  (M : Subgroup N) (hM : ∀ (j : J) (n : N), n ∈ M → j • n ∈ M)

@[instance_reducible] def coefficientSubgroupAction : MulDistribMulAction J M where
  smul j n := ⟨j • n.val, hM j n.val n.property⟩
  one_smul n := Subtype.ext (one_smul J n.val)
  mul_smul j k n := Subtype.ext (mul_smul j k n.val)
  smul_one j := Subtype.ext (smul_one j)
  smul_mul j n m := Subtype.ext (smul_mul' j n.val m.val)



namespace Cocycle

def corestrictCoefficient {K : Subgroup J} (f : Cocycle (N := N) K)
    (hf : ∀ x, f.toFun x ∈ M) :
    letI := coefficientSubgroupAction M hM
    Cocycle (N := M) K := by
  letI := coefficientSubgroupAction M hM
  exact { toFun := fun x => ⟨f.toFun x, hf x⟩
          continuous_toFun := f.continuous_toFun.subtype_mk hf
          map_mul := fun x y => Subtype.ext (f.map_mul x y) }

end Cocycle
end Subgroup

end LocalConjugacy

end LocalConjugacy.Proof

end


