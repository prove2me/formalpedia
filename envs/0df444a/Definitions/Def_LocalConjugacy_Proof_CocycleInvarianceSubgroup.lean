-- Prove2me | Definitions.Def_LocalConjugacy_Proof_CocycleInvarianceSubgroup
-- name    : LocalConjugacy_Proof_CocycleInvarianceSubgroup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:21:04.894288+00:00
-- url     : https://prove2.me/theorems/7036d3bd-4ae4-47ed-a206-6d642c58536b
-- title:
--   The subgroup preserving a cocycle class
-- statement:
--   The subgroup of ambient elements under which a cocycle class is stable. Its subgroup structure records closure of the stability condition under multiplication and inversion.
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
  [TopologicalSpace J] [IsTopologicalGroup J]
  [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction J N] [ContinuousSMul J N]
  {K : Subgroup J} [K.Normal]

/-- The stabilizer of the cohomology class under twisting. -/
def cocycleInvarianceSubgroup (f : Cocycle (N := N) K) : Subgroup J where
  carrier := {j | Cohomologous f (twistCocycle f j)}
  one_mem' := by
    change Cohomologous f (twistCocycle f 1)
    rw [twist_one]
    exact cohomologous_refl f
  mul_mem' := by
    intro a b ha hb
    change Cohomologous f (twistCocycle f (a * b))
    rw [twist_mul]
    exact cohomologous_trans ha (twist_cohomologous hb a)
  inv_mem' := by
    intro a ha
    have h := twist_cohomologous ha a⁻¹
    rw [← twist_mul, inv_mul_cancel, twist_one] at h
    exact cohomologous_symm h





end LocalConjugacy

end LocalConjugacy.Proof

end


