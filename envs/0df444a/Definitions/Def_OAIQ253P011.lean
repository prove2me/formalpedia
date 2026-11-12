-- Prove2me | Definitions.Def_OAIQ253P011
-- name    : OAIQ253P011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T06:10:26.989758+00:00
-- url     : https://prove2.me/theorems/3cf97730-5cc8-42f8-94c9-7337bdd8b33f
-- title:
--   Definitions bundle OAIQ253P011 of the split of OpenAI, The Partition Principle does not imply Choice
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 11 definitions and 13 theorems. The definitions and types are `OAI.PartitionPilot.Forcing.SetFormula.orbitCodeFamilyPairFormula`, `OAI.PartitionPilot.Forcing.TransitiveGround.preparationEntryFormula`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAction`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixAction`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingStageFormula`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingStepFormula`, `OAI.PartitionPilot.Forcing.TransitiveGround.supportedCertificateFamilyEnv`, `OAI.PartitionPilot.Forcing.TransitiveGround.supportedEqualitySequenceEnv`, `OAI.PartitionPilot.Forcing.TransitiveGround.varyingBody`, `OAI.PartitionPilot.Forcing.TransitiveGround.varyingPreparationFormula`, `OAI.PartitionPilot.Forcing.TransitiveGround.visibilityProfileEnv`.
--
--   **Sources.** They come from these modules of lean/OAI/SetTheory, in whole or in part: `PartitionPrinciple_Definability_GroundRefinementPairClassGraphs`, `PartitionPrinciple_Definability_GroundSemanticAlignedLargerCutTests`, `PartitionPrinciple_Definability_GroundSemanticFairPreparationLimits`, `PartitionPrinciple_Definability_GroundSemanticRepresentedDomainAbsentLift`, `PartitionPrinciple_Definability_GroundSemanticStructuralCutActions`, `PartitionPrinciple_Definability_GroundSemanticStructuralDataSupport`, `PartitionPrinciple_Definability_GroundSemanticStructuralPrefixPreparationInputs`, `PartitionPrinciple_Definability_GroundVaryingPreparationRelations`, `PartitionPrinciple_Forcing_GroundMainFinalSupportedCertificateFamilies`, `PartitionPrinciple_Forcing_GroundPreparationForcing`, `PartitionPrinciple_Forcing_GroundStructuralForcingHistoryConstruction`, `PartitionPrinciple_Forcing_GroundSupportedCertificateFamilyDecisions`, `PartitionPrinciple_Geometry_GroundStructuralCompleteProjections`, `PartitionPrinciple_Geometry_GroundStructuralFinitePowerTerms`.
--
--   **Imports.** It imports the published bundle `Def_PartitionPrinciple`; the bundle `OAIQ253P009` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.augmented_profile_family`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_forcedSupportedCertificateFamily`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_groundFairPreparationOrbit`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_groundStoredPreparedStrengthening`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_prefixPreparationBatch`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_rowSemanticQuotientInjectionModel`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_dense_mixture_equalities`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_lifted_rows_not_wellorderable_not_choice`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_ordinal_choice`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_refinement_quotient_injection`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_represented_domain_dense`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.successor_prepared_insertion_profiles`, `OAI.PartitionPilot.Forcing.TransitiveGround.countableRow_semanticStructuralTrace_jointZF_sequenceReflection`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticBinaryRow_ordinal_partial_cover`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_ground_supported_hs`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_injection_package`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_pair_eq_iff`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_subset_quotients`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_supported_hs`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignment_occurrence_act`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignment_occurrence_fixed_index`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralCrossStagePower_hs`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixMembershipName_eval`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixRefinementEnvironment`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixRefinementNormalization`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixSharedCondition_spec`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_aligned_copy_crossCollisions`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_aligned_copy_crossCollisions_at_larger_cut`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_aligned_cut_tests_at_larger_cut`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_assignmentClassRequest_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_assignment_tests`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_augmentedClassRequests`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_insertion_crossCollisions`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_typed_assignment_certificates`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_decide_represented_visibleLift`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_dense_visibleLift`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_insert_absentLift`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_insert_visibleLift`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_absentLift`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_absentLift_actor`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_or_fresh`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_commonRefinementNames`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_refinementIndices`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_refinementOutputs` and `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_storedRefinementIndices`; the proofs of `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment.structural_bounds_with`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.augmented_profile_family`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_forcedSupportedCertificateFamily`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_groundFairPreparationOrbit`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_groundStoredPreparedStrengthening`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_prefixPreparationBatch`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_rowSemanticQuotientInjectionModel`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_compatible_insertion_unions`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_dense_mixture_equalities`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_lifted_rows_not_wellorderable_not_choice`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_ordinal_choice`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_refinement_quotient_injection`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_represented_domain_dense`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_support_prepared_strengthening`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.successor_prepared_insertion_profiles`, `OAI.PartitionPilot.Forcing.TransitiveGround.binaryRowStructuralAssignmentImage_dataBound`, `OAI.PartitionPilot.Forcing.TransitiveGround.countableRow_semanticStructuralTrace_jointZF_sequenceReflection`, `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticBinaryRow_ordinal_partial_cover`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_ground_supported_hs`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_injection_package`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_pair_eq_iff`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_subset_quotients`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_supported_hs`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignment_occurrence_act`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignment_occurrence_fixed_index`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralCrossStagePower_hs`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixMembershipName_eval`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixRefinementEnvironment`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixRefinementNormalization`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixSharedCondition_spec`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_aligned_copy_crossCollisions`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_aligned_copy_crossCollisions_at_larger_cut`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_aligned_cut_tests_at_larger_cut`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_assignmentClassRequest_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_assignment_tests`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_augmentedClassRequests`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_insertion_crossCollisions`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_preparationEvent_certificate_domain`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_typed_assignment_certificates`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_decide_represented_visibleLift`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_dense_visibleLift`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_insert_absentLift`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_insert_visibleLift`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_absentLift`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_absentLift_actor`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_or_fresh`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_commonPowerAntichains`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_commonRefinementNames`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_refinementIndices`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_refinementOutputs`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_storedPreparation_request_bounds` and `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_storedRefinementIndices`.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); definitions carved from lean/OAI/SetTheory at commit 7ef5c0c

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P009

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRefinementPairClassGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing




section
open SetRealization SetFormula
universe u

namespace SetFormula

def orbitCodeFamilyPairFormula : SetFormula 5 :=
  ex (.conj (binaryApplication orbitCodeEqualityFormula
    (extend 3 (extend 4 (extend 5 Fin.elim0))) 1 0) (orderedPairFormula 2 1 0))
end SetFormula

end



open SetRealization SetFormula
universe u


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPreparationForcing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)
variable (K : I → Subgroup G)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

noncomputable def visibilityProfileEnv (F : ZFSet.{u}) (hF : F ∈ M.sets)
    (z : (M.nameDomain s).names) : Assignment (M.nameDomain s) 4 :=
  ![z, ⟨M.niceVisibilityEvaluationName a s b T K,
      M.niceVisibilityEvaluationName_mem a s b t K pairing unions powers separation collection
        carrier group nodes supports maps hT valid⟩,
    ⟨Name.check s ⊤ b.carrier, M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) b.carrier nodes⟩,
    ⟨Name.check s ⊤ F, M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) F hF⟩]

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalSupportedCertificateFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation I) (K : I → Subgroup G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

noncomputable def supportedEqualitySequenceEnv (B f : ZFSet.{u})
    (hB : B ∈ M.sets) (hf : f ∈ M.sets) (z : (M.nameDomain s).names) :
    Assignment (M.nameDomain s) 6 :=
  let check (x : ZFSet.{u}) (hx : x ∈ M.sets) : (M.nameDomain s).names :=
    ⟨Name.check s ⊤ x, M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) x hx⟩
  ![check B hB,
    check (M.niceSupportNameCodes a s T K)
      (M.niceSupportNameCodes_mem a s b T K t pairing unions powers separation collection
        carrier group nodes supports maps hT valid),
    check f hf,
    check (M.niceSupportRelation a s b T K)
      (M.niceSupportRelation_mem a s b T K t pairing unions powers separation collection
        carrier group nodes supports maps hT valid),
    ⟨M.niceSupportEvaluationName a s T K,
      M.niceSupportEvaluationName_mem a s T K t b pairing unions powers separation collection
        carrier group nodes supports maps hT valid⟩,
    z]

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundVaryingPreparationRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def preparationEntryFormula {n}
    (z upperOrder cutGraph meet omega C E : Fin n) (fields : Fin 15 → Fin n) : SetFormula n :=
  let old := suffixIndex n 2
  let v := prefixIndex n 2
  exBlock 2 (.conj (BoundedFormula.orderedPairFormula (old z) (v 0) (v 1)).toFormula
    (M.storedPreparationFormula pairing unions powers separation
      (v 0) (v 1) (old upperOrder) (old cutGraph) (old meet) (old omega) (old C) (old E)
      (fun j => old (fields j))))

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def varyingBody {n}
    (z packed Q upperOrder nodes T levels omega C E : Fin n) : SetFormula (n + 22) :=
  let old := suffixIndex n 22
  let v := prefixIndex n 22
  let f := fun j : Fin 15 => v j.succ.succ.succ.succ.succ.succ.succ
  .conj (varyingShape z packed nodes T).toFormula
    (.conj (BoundedFormula.meetOrderFormula (f 10) (f 11) (v 5)).toFormula
      (.conj (rowAssignmentCutGraphFormula (v 6) (old Q) (f 7) (old levels) (v 0))
        (M.storedPreparationFormula pairing unions powers separation
          (v 1) (v 2) (old upperOrder) (v 6) (v 5) (old omega) (old C) (old E) f)))

noncomputable def varyingPreparationFormula {n}
    (z packed Q upperOrder nodes T levels omega C E : Fin n) : SetFormula n :=
  exBlock 22 (varyingBody M pairing unions powers separation z packed Q upperOrder nodes T levels omega C E)

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundStructuralForcingHistoryConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

noncomputable def structuralForcingStageFormula {n : Nat}
    (output rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 stages history N : Fin n) : SetFormula n :=
  .ex (.conj
    (M.structuralForcingCarrierFormula pairing unions powers separation collection
      0 rows.succ G.succ nodes.succ nodeOrder.succ basis.succ T.succ T2.succ stages.succ history.succ N.succ)
    (reindex (extend output.succ ![0, rows.succ, rowOrder.succ, rowTop.succ, rowAction.succ,
      G.succ, nodes.succ, nodeOrder.succ, nodeAction.succ, basis.succ, T.succ, T2.succ, stages.succ, history.succ])
      (M.definable_structuralForcingStageFromCarrier pairing unions powers separation collection).formula))

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

noncomputable def structuralForcingStepFormula : SetFormula 15 :=
  M.structuralForcingStageFormula pairing unions powers separation collection
    2 3 4 5 6 7 8 9 10 11 12 13 0 1 14

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundStructuralCompleteProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G L : Type u} [Group G] [PartialOrder L]
variable (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 stages history : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
variable (witnesses : ∀ level P order top action,
  ZFSet.pair level (forcingStageCode P order top action) ∈ history →
    RawRefinementStageWitness M t b d base directed T T2 level P order top action)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
include pairing unions powers separation collection group nodes supports hHistory hT witnesses

theorem structuralHistory_rawTests_mono :
    ∀ level (data : Fin 15 → ZFSet.{u}), ZFSet.pair level (refinementFormulaDataCode data) ∈ packed →
      ∀ A lower stronger, stageOneRawTests M data A lower →
        ZFSet.pair stronger lower ∈ data 8 → stageOneRawTests M data A stronger := by
  intro level data entry A lower stronger tests below
  obtain ⟨_, P, order, top, action, stored, rfl⟩ :=
    M.structuralRefinementHistory_fields t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history data entry
  have ground := M.forcingStageCode_fields
    (M.transitive (M.union_mem unions (M.union_mem unions hHistory))
      (pair_second_mem_doubleUnion stored))
  exact (witnesses level P order top action stored).rawTests_order_mono
    pairing unions powers separation collection ground.1 group nodes ground.2.1 supports hT
    A lower stronger tests below

theorem structuralTrace_completeProjection
    (rows rowOrder rowTop rowAction alpha : ZFSet.{u})
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (nodeOrder : b.conditionOrder ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (hStages : stages ∈ M.sets) (hAlpha : alpha ∈ M.sets) (hRows : rows ∈ M.sets)
    (ordinal : ordinalSetProperty stages) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
    (trace : OrdinalRecursionTrace (fun level prior stage =>
      stage = M.structuralForcingStage rows rowOrder rowTop rowAction t.carrier b.carrier b.conditionOrder
        (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (rowOrderLaw : PartialOrderCode rows rowOrder) (topMem : rowTop ∈ rows)
    (topRows : ∀ row ∈ rows, ZFSet.pair row rowTop ∈ rowOrder) :
    let run := M.structuralForcingTrace_recursiveOrder rows rowOrder rowTop rowAction t.carrier b.carrier
      b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
    let mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
      pairing unions powers separation collection group nodes supports hHistory hT witnesses
    let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
      ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
      (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
        (Fin.cases hT (Fin.cases hT2 (Fin.cases hStages (Fin.cases hHistory (fun j => Fin.elim0 j)))))))))
    letI := M.refinementHistoryPartialOrder rowOrderLaw T stages packed
    letI := M.refinementHistoryPartialOrder rowOrderLaw T alpha (graphRestriction alpha packed)
    CompleteProjection (run.restriction ordinal cutOrdinal subset rowOrderLaw)
      (run.inclusion ordinal cutOrdinal subset pairing unions powers separation infinite choice
        hStages hPacked hT hAlpha hRows rowTop topMem topRows mono rowOrderLaw) := by
  dsimp only
  exact (M.structuralForcingTrace_recursiveOrder rows rowOrder rowTop rowAction t.carrier b.carrier
    b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace).completeProjection
    ordinal cutOrdinal subset pairing unions powers separation infinite choice hStages _ hT hAlpha hRows
    rowTop topMem topRows
    (M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
      pairing unions powers separation collection group nodes supports hHistory hT witnesses) rowOrderLaw

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticFairPreparationLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

theorem semanticStructuralTrace_completeProjection
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (alpha : ZFSet.{u}) (hAlpha : alpha ∈ M.sets)
    (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
      t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
      T T2 ordinal trace
    let witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace
    let mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
      pairing unions powers separation collection group nodes supports hh hT witnesses
    let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
      ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
      (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
        (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    CompleteProjection (run.restriction ordinal cutOrdinal subset c.conditionOrder_code)
      (run.inclusion ordinal cutOrdinal subset pairing unions powers separation infinite choice
        hs hPacked hT hAlpha carrier rowTop topMem topRows mono c.conditionOrder_code) := by
  dsimp only
  exact M.structuralTrace_completeProjection t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT
    (M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace)
    c.carrier c.conditionOrder rowTop (a.actionGraph c t) alpha infinite choice nodeOrder hT2 hs hAlpha carrier
    ordinal cutOrdinal subset trace c.conditionOrder_code topMem topRows

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralDataSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
open scoped ZFSet
local notation "rawGraph" => rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
  (M.structuralAssignments t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history)
  (a.actionGraph c t)
  (M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history)
include hs hh ordinal trace

theorem semanticStructuralAction_code :
    PosetActionCode t.carrier Q ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
      (M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed) rawGraph := by
  exact (M.semanticStructuralCurrent_witness c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace _ _ _ _
    (M.structuralForcingStage_eq c.carrier c.conditionOrder rowTop (a.actionGraph c t)
      t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history).symm).action_code

noncomputable def semanticStructuralAction :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    PosetAction G (SetMembers Q) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  have code := M.semanticStructuralAction_code c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
  rw [← M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T stages packed] at code
  exact code.toPresentedPosetAction t (SetMembers.presentation Q)

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralCutActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history alpha : ZFSet.{u}} (hh : history ∈ M.sets)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
local notation "rawGraph" => rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
  (M.structuralAssignments t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 alpha history)
  (a.actionGraph c t)
  (M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 alpha history)
include hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefixAction_code :
    PosetActionCode t.carrier Q ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
      (M.refinementHistoryOrder c.carrier c.conditionOrder T alpha lowerPacked) rawGraph := by
  have code := M.semanticStructuralAction_code c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hAlpha
    (M.graphRestriction_mem unions separation hAlpha hh) cutOrdinal (trace.restrict cutOrdinal subset)
  have packedEq := (M.structuralRefinementHistory_history_restrict t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 alpha history).trans
      (M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 subset)
  rw [packedEq, M.structuralAssignments_history_restrict, M.structuralAssignmentActionGraph_history_restrict] at code
  exact code

noncomputable def semanticStructuralPrefixAction :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    PosetAction G (SetMembers Q) := by
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  have code := M.semanticStructuralPrefixAction_code c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
  rw [← M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T alpha lowerPacked] at code
  exact code.toPresentedPosetAction t (SetMembers.presentation Q)

local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefixAction_graph :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    (act).actionGraph (SetMembers.presentation Q) t = rawGraph := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  unfold semanticStructuralPrefixAction
  exact PosetActionCode.toPresentedPosetAction_graph _ _ _

theorem semanticStructuralPrefixAction_coordinates :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    ∀ (g : G) (p : SetMembers Q) (r : R) (A : ZFSet.{u}),
      SetMembers.raw p = ZFSet.pair (c.encode r) A →
      SetMembers.raw ((act).iso g p) = ZFSet.pair (c.encode (a.iso g r))
        (M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  intro g p r A code
  have edge := ((act).triple_mem_actionGraph (SetMembers.presentation Q) t g p ((act).iso g p)).2 rfl
  rw [M.semanticStructuralPrefixAction_graph] at edge
  change ZFSet.pair (ZFSet.pair (t.encode g) (SetMembers.raw p)) (SetMembers.raw ((act).iso g p)) ∈ _ at edge
  obtain ⟨q, D, _, target⟩ := exists_presentedRowAssignmentCoordinates c
    (M.refinementHistoryForcing_shape c.carrier T alpha lowerPacked) (SetMembers.raw_mem ((act).iso g p))
  rw [code, target] at edge
  obtain ⟨_, _, row, data⟩ := (presentedRowAssignmentGraph_entry a c t Q _ _ g r q A D).1 edge
  rw [target, row, data]
  rfl

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAlignedLargerCutTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history alpha : ZFSet.{u}} (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
open scoped ZFSet
include hh ordinal trace hAlpha cutOrdinal subset

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefix_stageCode :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
      t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha (graphRestriction alpha history) =
      forcingStageCode lower.carrier lower.conditionOrder (lower.encode ⊤) ((act).actionGraph lower t) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  dsimp only
  rw [M.structuralForcingStage_eq]
  unfold structuralForcingCarrier
  rw [M.structuralRefinementHistory_history_restrict,
    M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 subset,
    M.structuralAssignments_history_restrict, M.structuralAssignmentActionGraph_history_restrict,
    M.refinementHistoryDecodedOrder_eq, M.refinementHistoryDecodedTop_eq,
    M.semanticStructuralPrefixAction_graph]
  rfl

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
open scoped ZFSet
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefix_refinementData_entry :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ZFSet.pair alpha (M.refinementLevelFormulaDataCode act lower b d alpha T T2 valid) ∈ packed := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  have validSecond := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T2 valid2
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have hGraph : (act).actionGraph lower t ∈ M.sets := by
    rw [M.semanticStructuralPrefixAction_graph]
    have ground := M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier rowAction group nodes nodeOrder nodeAction supports hT hT2 hAlpha hh omega
    unfold structuralForcingCarrier at ground
    rw [M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 subset] at ground
    exact ground
  have maps := M.conditionMapFamily_mem_of_actionGraph act lower t pairing unions powers separation
    collection hQ group hGraph
  obtain ⟨stage, stored⟩ := trace.1.total member
  have same := (trace.2 alpha member stage stored).trans
    (M.semanticStructuralPrefix_stageCode c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hh ordinal trace hAlpha cutOrdinal subset)
  have exactStored : ZFSet.pair alpha
      (forcingStageCode lower.carrier lower.conditionOrder (lower.encode ⊤) ((act).actionGraph lower t))
      ∈ history := same ▸ stored
  have entry := (M.structuralRefinementHistory_entry t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history alpha
    lower.carrier lower.conditionOrder (lower.encode ⊤) ((act).actionGraph lower t)
    _ trace.1 exactStored).2 rfl
  rw [M.rawRefinementFormulaDataCode_eq act lower t b d pairing unions powers separation collection
    hQ group nodes supports maps alpha T T2 valid validSecond] at entry
  exact entry

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticRepresentedDomainAbsentLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefix_refinementSystem :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    RefinementStageSystem M act lower t b d base directed alpha T T2 := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have entry := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have fields : ∀ j, M.refinementLevelFormulaData act lower b d alpha T T2 valid j ∈ M.sets :=
    M.refinementFormulaDataCode_fields_mem _ (M.transitive
      (M.union_mem unions (M.union_mem unions hPacked)) (pair_second_mem_doubleUnion entry))
  have hQ : lower.carrier ∈ M.sets := fields 7
  have hOrder : lower.conditionOrder ∈ M.sets := fields 8
  have hGraph : (act).actionGraph lower t ∈ M.sets := by
    rw [M.semanticStructuralPrefixAction_graph]
    have ground := M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier rowAction group nodes nodeOrder nodeAction supports hT hT2 hAlpha hh omega
    unfold structuralForcingCarrier at ground
    rw [M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 subset] at ground
    exact ground
  have maps := M.conditionMapFamily_mem_of_actionGraph act lower t pairing unions powers separation
    collection hQ group hGraph
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  obtain ⟨firstValid, firstClosed, firstChildren⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a act image coordinates emptyImage
    (d.principalSupportFamily base directed) T valid1 closed1 symmetric1
  obtain ⟨secondValid, secondClosed, secondChildren⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a act image coordinates emptyImage
    (d.principalSupportFamily base directed) T2 valid2 closed2 symmetric2
  exact M.refinementStageSystem act lower t b d base directed pairing unions powers separation collection
    hQ hOrder group nodes nodeOrder maps nodeMaps supports hAlpha hT hT2
    firstValid secondValid firstClosed secondClosed firstChildren secondChildren

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralPrefixPreparationInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

theorem semanticStructuralTrace_internally_closed
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (rowClosed : InternallyCountablyClosed M c) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    InternallyCountablyClosed M (SetMembers.presentation
      (M.refinementHistoryForcing c.carrier T stages packed)) := by
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
    T T2 ordinal trace
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  have unionTests := M.structuralHistory_rawTests_union t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  exact M.refinementHistory_internally_closed c T stages packed run ordinal unionTests
    pairing unions powers separation infinite choice carrier hT hs hPacked rowClosed

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefix_preparation_inputs
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (rowClosed : InternallyCountablyClosed M c) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    let lower := SetMembers.presentation Q
    lower.carrier ∈ M.sets ∧ lower.conditionOrder ∈ M.sets ∧
    (act).conditionMapFamily lower t ∈ M.sets ∧ InternallyCountablyClosed M lower ∧
    (∀ g (tau : Name lower), tau.val ∈ T → ((act).act lower g tau).val ∈ T) ∧
    (∀ tau : Name lower, tau.val ∈ T →
      HereditarilySymmetric act lower (d.principalSupportFamily base directed) tau) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let lower := SetMembers.presentation Q
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hLowerPacked := M.graphRestriction_mem unions separation hAlpha hPacked
  have hQ : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers
    separation carrier hT hAlpha hLowerPacked omega
  have hOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround
      hT hAlpha hLowerPacked omega
  have hAssignments := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, alpha, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hAlpha (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hAssignmentAction := M.structuralAssignmentActionGraph_mem pairing unions powers separation
    collection group nodes nodeOrder nodeAction supports hT hT2 hAlpha hh
  have hGraph : (act).actionGraph lower t ∈ M.sets := by
    rw [M.semanticStructuralPrefixAction_graph]
    exact M.rawRowAssignmentActionGraph_mem pairing unions powers separation collection group hQ
      carrier (M.union_mem unions (M.union_mem unions hQ)) hAssignments rowAction hAssignmentAction
  have maps := M.conditionMapFamily_mem_of_actionGraph act lower t pairing unions powers separation
    collection hQ group hGraph
  have packedEq := (M.structuralRefinementHistory_history_restrict t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 alpha history).trans
      (M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 subset)
  have closed := M.semanticStructuralTrace_internally_closed c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hAlpha (M.graphRestriction_mem unions separation hAlpha hh) cutOrdinal
      (trace.restrict cutOrdinal subset) infinite choice rowClosed
  dsimp only at closed
  rw [packedEq] at closed
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  obtain ⟨_, terms, children⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a act image coordinates emptyImage
    (d.principalSupportFamily base directed) T valid1 closed1 symmetric1
  exact ⟨hQ, hOrder, maps, closed, terms, children⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSupportedCertificateFamilyDecisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation L)
variable (T : ZFSet.{u}) (K : L → Subgroup G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (omega : ZFSet.omega ∈ M.sets)

noncomputable def supportedCertificateFamilyEnv (nodeOrder J k : ZFSet.{u})
    (hOrder : nodeOrder ∈ M.sets) (hJ : J ∈ M.sets) (hk : k ∈ M.sets)
    (validJ : ∀ z ∈ J, IsName s z) : Assignment (M.nameDomain s) 12 :=
  let check (x : ZFSet.{u}) (hx : x ∈ M.sets) : (M.nameDomain s).names :=
    ⟨Name.check s ⊤ x, M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) x hx⟩
  let N := M.niceSupportNameCodes a s T K
  let hN := M.niceSupportNameCodes_mem a s b T K t pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  ![check k hk, check J hJ, check (M.groundPower b.carrier) (M.groundPower_mem powers nodes),
    check (M.groundSmallSubsets b.carrier ZFSet.omega)
      (M.groundSmallSubsets_mem powers separation nodes omega),
    check (M.groundRelations b.carrier N)
      (M.groundRelations_mem pairing unions powers separation nodes hN),
    check b.carrier nodes, check N hN, check nodeOrder hOrder,
    check (M.niceSupportRelation a s b T K)
      (M.niceSupportRelation_mem a s b T K t pairing unions powers separation collection
        carrier group nodes supports maps hT valid),
    ⟨Name.inputEvaluationName s J validJ,
      M.inputEvaluationName_mem s pairing unions powers separation collection carrier hJ validJ⟩,
    ⟨M.niceSupportEvaluationName a s T K,
      M.niceSupportEvaluationName_mem a s T K t b pairing unions powers separation collection
        carrier group nodes supports maps hT valid⟩,
    ⟨M.niceVisibilityEvaluationName a s b T K,
      M.niceVisibilityEvaluationName_mem a s b t K pairing unions powers separation collection
        carrier group nodes supports maps hT valid⟩]

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundStructuralFinitePowerTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {R : Type u} (c : Presentation R)

theorem structuralTrace_finitePowerTerms
    (rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : c.carrier ∈ M.sets) (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName c.pairEmpty z) (topMem : rowTop ∈ c.carrier)
    {stages history : ZFSet.{u}} (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier rowOrder rowTop rowAction G nodes nodeOrder nodeAction
        basis T T2 level prior) stages history) (n : Nat) :
    let packed := M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history
    let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
    J ∈ M.sets ∧ ∀ alpha : ZFSet.{u}, ordinalSetProperty alpha → alpha ⊆ stages →
      ∀ z ∈ J, IsName (SetMembers.presentation
        (M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed))) z := by
  have oneGround := M.orderedPair_mem pairing (M.transitive carrier topMem)
    (M.empty_mem ⟨c.carrier, carrier⟩)
  have ground := M.iteratedPairNameFamily_mem pairing unions powers separation oneGround hT n
  have original : ∀ z ∈ iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n, IsName c.pairEmpty z := by
    obtain ⟨p, rfl⟩ := (c.mem_carrier rowTop).1 topMem
    exact iteratedPairNameFamily_valid p valid n
  let run := M.structuralForcingTrace_recursiveOrder c.carrier rowOrder rowTop rowAction G nodes
    nodeOrder nodeAction basis T T2 ordinal trace
  refine ⟨ground, ?_⟩
  intro alpha alphaOrdinal subset
  exact M.refinementHistoryRowNameFamily_valid c (run.carriers.restrict alphaOrdinal subset)
    alphaOrdinal carrier (iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n) original

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end


