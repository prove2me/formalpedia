-- Prove2me | Definitions.Def_OAIQ253P007
-- name    : OAIQ253P007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:58:19.026264+00:00
-- url     : https://prove2.me/theorems/321b52f3-4f9d-45ee-817c-8aefdec25c3a
-- title:
--   Definitions bundle OAIQ253P007 of the split of OpenAI, The Partition Principle does not imply Choice
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 314 declarations of OpenAI's Lean: 124 definitions, 4 inductive types or structures and 186 theorems. The definitions and types are `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.FairPreparationLowerBoundResult`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.GraphValueCandidateDensity`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.GroundSupportPreparedStrengtheningResult`, `OAI.PartitionPilot.Forcing.GroundMainStage.initialBirth`, `OAI.PartitionPilot.Forcing.GroundMainStage.initialChronological`, `OAI.PartitionPilot.Forcing.GroundMainStage.initialChronologyBound`, `OAI.PartitionPilot.Forcing.GroundMainStage.initialChronologyField`, `OAI.PartitionPilot.Forcing.GroundMainStage.initialChronologyGraph`, `OAI.PartitionPilot.Forcing.GroundMainStage.initialGroundChronologyFields`, `OAI.PartitionPilot.Forcing.GroundMainStage.initialHistory`, `OAI.PartitionPilot.Forcing.GroundMainStage.initialSerializedChronology`, `OAI.PartitionPilot.Forcing.GroundSerializedChronology.decodedLayer`, `OAI.PartitionPilot.Forcing.GroundSerializedChronology.fixedTopFields`, `OAI.PartitionPilot.Forcing.GroundSerializedChronology.fixedTopValues`, `OAI.PartitionPilot.Forcing.GroundSerializedChronology.layerWitness`, `OAI.PartitionPilot.Forcing.GroundSerializedChronology.normalizeBounds`, `OAI.PartitionPilot.Forcing.GroundSerializedChronology.toHistory`, `OAI.PartitionPilot.Forcing.GroundSetTerm.app`, `OAI.PartitionPilot.Forcing.PreparedCertificateCode`, `OAI.PartitionPilot.Forcing.PreparedCertificateFamilyCode`, `OAI.PartitionPilot.Forcing.RawRefinementStageWitness`, `OAI.PartitionPilot.Forcing.RecursiveRefinementDataHistory`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory.inclusion`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory.inclusionFunction`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory.restriction`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory.restrictionFunction`, `OAI.PartitionPilot.Forcing.RefinementStageSystem`, `OAI.PartitionPilot.Forcing.SerializedChronologyCode.toGround`, `OAI.PartitionPilot.Forcing.SetFormula.binaryRowCodeFormula`, `OAI.PartitionPilot.Forcing.SetFormula.binaryRowEntryFormula`, `OAI.PartitionPilot.Forcing.SetFormula.binaryRowSetEntryFormula`, `OAI.PartitionPilot.Forcing.SetFormula.checkEntryFormula`, `OAI.PartitionPilot.Forcing.SetFormula.checkNameCodeFormula`, `OAI.PartitionPilot.Forcing.SetFormula.codedNameActionFormula`, `OAI.PartitionPilot.Forcing.SetFormula.definableRelationEntryFormula`, `OAI.PartitionPilot.Forcing.SetFormula.hereditaryCertificateFormula`, `OAI.PartitionPilot.Forcing.SetFormula.hereditaryStepFormula`, `OAI.PartitionPilot.Forcing.SetFormula.indexedGraphNameCodeFormula`, `OAI.PartitionPilot.Forcing.SetFormula.indexedGraphNameEntryFormula` and 88 more.
--
--   **Sources.** They come from these modules of lean/OAI/SetTheory, in whole or in part: `PartitionPrinciple_Definability_BatchGraphSetFormulas`, `PartitionPrinciple_Definability_BoundedAtomicEquality`, `PartitionPrinciple_Definability_EqualityStepSyntax`, `PartitionPrinciple_Definability_GroundAssignmentClassGraphs`, `PartitionPrinciple_Definability_GroundDefinableRelationProducts`, `PartitionPrinciple_Definability_GroundMainFinalGraphValueCandidateAvailability`, `PartitionPrinciple_Definability_GroundPartialFunctionSpaces`, `PartitionPrinciple_Definability_GroundRefinementLevelSingleCodes`, `PartitionPrinciple_Definability_GroundRefinementPairClassGraphs`, `PartitionPrinciple_Definability_GroundVaryingPreparationRelations`, `PartitionPrinciple_Definability_NameSupportFormulas`, `PartitionPrinciple_Definability_OrbitImageFormulas`, `PartitionPrinciple_Definability_PreparedCertificateCodes`, `PartitionPrinciple_Definability_RefinementIndexActionFormulas`, `PartitionPrinciple_Definability_RenamedEntryFormulas`, `PartitionPrinciple_Forcing_ActiveNameImageSymmetry`, `PartitionPrinciple_Forcing_GroundBinaryRowNameCodes`, `PartitionPrinciple_Forcing_GroundDefinableRefinementNameGraphs`, `PartitionPrinciple_Forcing_GroundFlatSuccessorFullActionGraph`, `PartitionPrinciple_Forcing_GroundForcingHistoryOrders`, `PartitionPrinciple_Forcing_GroundGraphValueDescendantWitnesses`, `PartitionPrinciple_Forcing_GroundIndexedGraphNameFamilies`, `PartitionPrinciple_Forcing_GroundMainFinalStructuralCommonSupportInduction`, `PartitionPrinciple_Forcing_GroundMainFinalStructuralSupportPreparation`, `PartitionPrinciple_Forcing_GroundMainFinalSupportedCertificateFamilies`, `PartitionPrinciple_Forcing_GroundMixtureNames`, `PartitionPrinciple_Forcing_GroundNameSequenceForcingWitness`, `PartitionPrinciple_Forcing_GroundNiceNameGraphs`, `PartitionPrinciple_Forcing_GroundNicePreparationWitnessBounds`, `PartitionPrinciple_Forcing_GroundNiceRefinementIndexActionLaws`, `PartitionPrinciple_Forcing_GroundOrdinaryEqualityDecisionFusion`, `PartitionPrinciple_Forcing_GroundOrdinaryMembershipAntichainFamilies`, `PartitionPrinciple_Forcing_GroundPreparedWitnessSelections`, `PartitionPrinciple_Forcing_GroundProductActions`, `PartitionPrinciple_Forcing_GroundRawNiceNameGraphs`, `PartitionPrinciple_Forcing_GroundRawRefinementStageWitnesses`, `PartitionPrinciple_Forcing_GroundRawRowAssignmentActions`, `PartitionPrinciple_Forcing_GroundRawStageRefinementTestActions`, `PartitionPrinciple_Forcing_GroundRecursiveRowNameActions`, `PartitionPrinciple_Forcing_GroundRefinementAssignmentActionFamilies`, `PartitionPrinciple_Forcing_GroundRefinementValidityForcing`, `PartitionPrinciple_Forcing_GroundRenamedNameFamilyBounds`, `PartitionPrinciple_Forcing_GroundRepresentedDomainConditions`, `PartitionPrinciple_Forcing_GroundStageOneRawNames`, `PartitionPrinciple_Forcing_GroundStructuralForcingHistoryConstruction`, `PartitionPrinciple_Forcing_IndexedTupleNames`, `PartitionPrinciple_Forcing_NameRenameSteps`, `PartitionPrinciple_Forcing_RecursiveRefinementUnionConditions`, `PartitionPrinciple_Forcing_RefinementAssignmentActionLaws`, `PartitionPrinciple_Forcing_RefinementAssignmentLabelNames`, `PartitionPrinciple_Forcing_RenamedPairNameFamilies`, `PartitionPrinciple_Forcing_StageTwoAssignmentTestActions`, `PartitionPrinciple_Forcing_SymmetricGroundForcing`, `PartitionPrinciple_Forcing_UniformGroundNames`, `PartitionPrinciple_Geometry_CheckCertificates`, `PartitionPrinciple_Geometry_GroundBatchEmbeddingRecognition`, `PartitionPrinciple_Geometry_GroundCertificateBasisUnions`, `PartitionPrinciple_Geometry_GroundCertificateProfileImageFamilies`, `PartitionPrinciple_Geometry_GroundDefinableRowAssignmentOrders`, `PartitionPrinciple_Geometry_GroundDefinableSelections`, `PartitionPrinciple_Geometry_GroundEqualityStep`, `PartitionPrinciple_Geometry_GroundHartogs`, `PartitionPrinciple_Geometry_GroundIndexedClassInclusions`, `PartitionPrinciple_Geometry_GroundMixtureDensityRecovery`, `PartitionPrinciple_Geometry_GroundNiceRefinementVisibility`, `PartitionPrinciple_Geometry_GroundPreparedAlignedReferenceCollisions`, `PartitionPrinciple_Geometry_GroundPreparedPositionCollisions`, `PartitionPrinciple_Geometry_GroundRawRefinementDataIdentification`, `PartitionPrinciple_Geometry_GroundRefinementAssignmentImages`, `PartitionPrinciple_Geometry_GroundRefinementRawTestMonotonicity`, `PartitionPrinciple_Geometry_GroundSerializedBoundNormalization`, `PartitionPrinciple_Geometry_GroundStoredPreparationFamilyPersistence`, `PartitionPrinciple_Geometry_RawEqualitySteps`, `PartitionPrinciple_Geometry_RepresentativeIndexSteps`, `PartitionPrinciple_Geometry_UniformAtomicEquality`, `PartitionPrinciple_Models_GroundOrdinalPartitionInjectionAssembly`, `PartitionPrinciple_Models_GroundRefinementQuotientNames`, `PartitionPrinciple_Transfinite_GroundBinaryRowStageOneRefinement`, `PartitionPrinciple_Transfinite_GroundFairPreparationLimitCertificates`, `PartitionPrinciple_Transfinite_GroundInitialCompressionHistory`, `PartitionPrinciple_Transfinite_GroundInitialMainSeedSuccessorSerialization`, `PartitionPrinciple_Transfinite_GroundInitialMainStage`, `PartitionPrinciple_Transfinite_GroundRecursiveRefinementBinaryUnions`, `PartitionPrinciple_Transfinite_GroundRecursiveRowCompleteProjection`, `PartitionPrinciple_Transfinite_GroundSerializedChronologyTimeEquality`, `PartitionPrinciple_Transfinite_GroundStageOneAssignmentUnions`, `PartitionPrinciple_Transfinite_GroundStageOneTestEquivalence`, `PartitionPrinciple_Transfinite_GroundStageThreeAssignmentFamilies`, `PartitionPrinciple_Transfinite_GroundStandardInaccessible`, `PartitionPrinciple_Transfinite_GroundStructuralHistoryTestUnions`, `PartitionPrinciple_Transfinite_RefinementBirthEnumerationFairness`, `PartitionPrinciple_Transfinite_RefinementHistoryPrefixLevels`, `PartitionPrinciple_Transfinite_SerializedChronologyCodes`.
--
--   **Imports.** It imports the published bundle `Def_PartitionPrinciple`; the bundles `OAIQ253P004` and `OAIQ253P005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ253P009` and `OAIQ253P010`; the proofs of `OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData.exists_rankedTargetSerialization` and `OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialExternalBoundedGeometry`.
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
import Definitions.Def_OAIQ253P004
import Definitions.Def_OAIQ253P005

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPartialFunctionSpaces
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def definable_groundRelations
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} => M.groundRelations (env 0) (env 1)) :=
  (M.definable_groundPower powers).comp
    (fun _ => M.definable_product pairing unions powers separation)

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_EqualityStepSyntax
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

universe u

theorem realize_atomicApplication (U : Set ZFSet.{u}) {k m : Nat} (E : SetFormula (k + 3))
    (params : Fin k → Fin m) (p x y : Fin m) (env : Fin m → ZFSet.{u}) :
    Realize U (atomicApplication E params p x y) env ↔
      Realize U E (extend (env p) (extend (env x) (extend (env y) (fun i => env (params i))))) := by
  rw [atomicApplication, realize_reindex, map_extend, map_extend, map_extend]

end PartitionPilot.Forcing.SetFormula



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_relationMembership (D : Name.NameDomain s)
    (R : P → Name s → Name s → Prop)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k) (params : Fin k → Fin m)
    (pi si ti : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (meaning : M.RelationMeaning s D R E (fun j => env (params j)))
    (p : P) (σ τ : D.names) (hp : env pi = s.encode p)
    (hσ : env si = σ.val.val) (hτ : env ti = τ.val.val) :
    Realize M.sets (membershipFormula E c o params pi si ti) env ↔
      Name.RelationMembership R p σ.val τ.val := by
  have hτM : env ti ∈ M.sets := hτ ▸ ground τ.val τ.property
  rw [membershipFormula, M.realize_allConditions s _ _ env carrier hc]
  change (∀ q : P, Realize M.sets _ (extend (s.encode q) env)) ↔
    ∀ q, q ≤ p → ∃ t, t ≤ q ∧ ∃ ν r,
      Name.Entry ν τ.val r ∧ t ≤ r ∧ R t σ.val ν
  apply forall_congr'
  intro q
  rw [realize_imp, M.realize_conditionLE s pairing carrier order 0 pi.succ (params o).succ
    (extend (s.encode q) env) q p rfl hp ho]
  apply forall_congr'
  intro _
  rw [M.realize_exConditions s (params c).succ _ (extend (s.encode q) env) carrier hc]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨v, hv, rest⟩ := (realize_ex M.sets _ _).1 ht
    obtain ⟨r, entry, tq, tr, eq⟩ := (M.realize_exConditions s (params c).succ.succ.succ _
      (extend v (extend (s.encode t) (extend (s.encode q) env))) carrier hc).1 rest
    let e := extend (s.encode r) (extend v (extend (s.encode t) (extend (s.encode q) env)))
    have raw := (M.realize_pairMembershipFormula pairing 1 0 ti.succ.succ.succ.succ e
      hv (M.transitive carrier (s.encode_mem r)) hτM).1 entry
    change ZFSet.pair v (s.encode r) ∈ env ti at raw
    rw [hτ] at raw
    let ν : Name s := ⟨v, Name.isName_of_pair_mem τ.val v r raw⟩
    have hν : ν ∈ D.names := D.children τ.property raw
    have forced := (realize_atomicApplication M.sets E
      (fun j => (params j).succ.succ.succ.succ) 2 si.succ.succ.succ.succ 1 e).1 eq
    change Realize M.sets E (extend (s.encode t) (extend (env si)
      (extend v (fun j => env (params j))))) at forced
    rw [hσ] at forced
    exact ⟨t, (M.realize_conditionLE s pairing carrier order 2 3
      (params o).succ.succ.succ.succ e t q rfl rfl ho).1 tq,
      ν, r, raw, (M.realize_conditionLE s pairing carrier order 2 0
        (params o).succ.succ.succ.succ e t r rfl rfl ho).1 tr,
      (meaning t σ ⟨ν, hν⟩).1 forced⟩
  · rintro ⟨t, tq, ν, r, entry, tr, forced⟩
    have hν : ν ∈ D.names := D.children τ.property entry
    refine ⟨t, ?_⟩
    rw [realize_ex]
    refine ⟨ν.val, ground ν hν, ?_⟩
    apply (M.realize_exConditions s (params c).succ.succ.succ _
      (extend ν.val (extend (s.encode t) (extend (s.encode q) env))) carrier hc).2
    let e := extend (s.encode r) (extend ν.val (extend (s.encode t) (extend (s.encode q) env)))
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · apply (M.realize_pairMembershipFormula pairing 1 0 ti.succ.succ.succ.succ e
        (ground ν hν) (M.transitive carrier (s.encode_mem r)) hτM).2
      change ZFSet.pair ν.val (s.encode r) ∈ env ti
      rw [hτ]
      exact entry
    · exact (M.realize_conditionLE s pairing carrier order 2 3
        (params o).succ.succ.succ.succ e t q rfl rfl ho).2 tq
    · exact (M.realize_conditionLE s pairing carrier order 2 0
        (params o).succ.succ.succ.succ e t r rfl rfl ho).2 tr
    · apply (realize_atomicApplication M.sets E
        (fun j => (params j).succ.succ.succ.succ) 2 si.succ.succ.succ.succ 1 e).2
      change Realize M.sets E (extend (s.encode t) (extend (env si)
        (extend ν.val (fun j => env (params j)))))
      rw [hσ]
      exact (meaning t σ ⟨ν, hν⟩).2 forced

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem relationMeaning_swap (D : Name.NameDomain s) (R : P → Name s → Name s → Prop)
    {k : Nat} (E : SetFormula (k + 3)) (constants : Fin k → ZFSet.{u})
    (meaning : M.RelationMeaning s D R E constants) :
    M.RelationMeaning s D (fun p σ τ => R p τ σ) (swapEquality E) constants := by
  intro p σ τ
  rw [swapEquality, realize_atomicApplication]
  exact meaning p τ σ

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundEqualityStep
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_matchingDirection (D : Name.NameDomain s)
    (R : P → Name s → Name s → Prop)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k) (params : Fin k → Fin m)
    (pi si ti : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (meaning : M.RelationMeaning s D R E (fun j => env (params j)))
    (p : P) (σ τ : D.names) (hp : env pi = s.encode p)
    (hσ : env si = σ.val.val) (hτ : env ti = τ.val.val) :
    Realize M.sets (matchingDirectionFormula E c o params pi si ti) env ↔
      ∀ ρ r, Name.Entry ρ σ.val r → ∀ q, q ≤ p → q ≤ r →
        Name.RelationMembership R q ρ τ.val := by
  have hσM : env si ∈ M.sets := hσ ▸ ground σ.val σ.property
  change (∀ v ∈ M.sets, Realize M.sets _ (extend v env)) ↔ _
  constructor
  · intro h ρ r entry q qp qr
    have hρ := D.children σ.property entry
    have first := (M.realize_allConditions s (params c).succ _
      (extend ρ.val env) carrier hc).1 (h ρ.val (ground ρ hρ)) r
    have raw : ZFSet.pair ρ.val (s.encode r) ∈ env si := hσ ▸ entry
    have guard := (M.realize_pairMembershipFormula pairing 1 0 si.succ.succ
      (extend (s.encode r) (extend ρ.val env))
      (ground ρ hρ) (M.transitive carrier (s.encode_mem r)) hσM).2 raw
    have second := (realize_imp M.sets _ _ _).1 first guard
    have third := (M.realize_allConditions s (params c).succ.succ _
      (extend (s.encode r) (extend ρ.val env)) carrier hc).1 second q
    let e := extend (s.encode q) (extend (s.encode r) (extend ρ.val env))
    have body := (realize_imp M.sets _ _ e).1 third
      ⟨(M.realize_conditionLE s pairing carrier order 0 pi.succ.succ.succ
        (params o).succ.succ.succ e q p rfl hp ho).2 qp,
       (M.realize_conditionLE s pairing carrier order 0 1
        (params o).succ.succ.succ e q r rfl rfl ho).2 qr⟩
    exact (M.realize_relationMembership s D R ground pairing carrier order E c o
      (fun j => (params j).succ.succ.succ) 0 2 ti.succ.succ.succ e hc ho meaning
      q ⟨ρ, hρ⟩ τ rfl rfl hτ).1 body
  · intro h v hv
    apply (M.realize_allConditions s (params c).succ _ (extend v env) carrier hc).2
    intro r
    apply (realize_imp M.sets _ _ _).2
    intro guard
    have raw := (M.realize_pairMembershipFormula pairing 1 0 si.succ.succ
      (extend (s.encode r) (extend v env)) hv (M.transitive carrier (s.encode_mem r)) hσM).1 guard
    change ZFSet.pair v (s.encode r) ∈ env si at raw
    rw [hσ] at raw
    let ρ : Name s := ⟨v, Name.isName_of_pair_mem σ.val v r raw⟩
    have hρ : ρ ∈ D.names := D.children σ.property raw
    apply (M.realize_allConditions s (params c).succ.succ _
      (extend (s.encode r) (extend v env)) carrier hc).2
    intro q
    let e := extend (s.encode q) (extend (s.encode r) (extend v env))
    apply (realize_imp M.sets _ _ e).2
    rintro ⟨qp, qr⟩
    apply (M.realize_relationMembership s D R ground pairing carrier order E c o
      (fun j => (params j).succ.succ.succ) 0 2 ti.succ.succ.succ e hc ho meaning
      q ⟨ρ, hρ⟩ τ rfl rfl hτ).2
    exact h ρ r raw q
      ((M.realize_conditionLE s pairing carrier order 0 pi.succ.succ.succ
        (params o).succ.succ.succ e q p rfl hp ho).1 qp)
      ((M.realize_conditionLE s pairing carrier order 0 1
        (params o).succ.succ.succ e q r rfl rfl ho).1 qr)

theorem realize_equalityStep (D : Name.NameDomain s)
    (R : P → Name s → Name s → Prop)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k) (params : Fin k → Fin m)
    (pi si ti : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (meaning : M.RelationMeaning s D R E (fun j => env (params j)))
    (p : P) (σ τ : D.names) (hp : env pi = s.encode p)
    (hσ : env si = σ.val.val) (hτ : env ti = τ.val.val) :
    Realize M.sets (equalityStepFormula E c o params pi si ti) env ↔
      Name.EqualityStep R p σ.val τ.val := by
  change (Realize M.sets _ env ∧ Realize M.sets _ env) ↔ _
  rw [M.realize_matchingDirection s D R ground pairing carrier order E c o params pi si ti
    env hc ho meaning p σ τ hp hσ hτ,
    M.realize_matchingDirection s D (fun t ρ ν => R t ν ρ) ground pairing carrier order
      (swapEquality E) c o params pi ti si env hc ho
      (M.relationMeaning_swap s D R E _ meaning) p τ σ hp hτ hσ]
  exact (Name.equalityStep_dense R p σ.val τ.val).symm

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RawEqualitySteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_rawMembership (R : P → ZFSet.{u} → ZFSet.{u} → Prop)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k) (params : Fin k → Fin m)
    (pi si ti : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (meaning : M.RawRelationMeaning s R E (fun j => env (params j)))
    (p : P) (hp : env pi = s.encode p) (hσ : env si ∈ M.sets) (hτ : env ti ∈ M.sets) :
    Realize M.sets (membershipFormula E c o params pi si ti) env ↔
      M.RawMembership s R p (env si) (env ti) := by
  rw [membershipFormula, M.realize_allConditions s _ _ env carrier hc]
  change (∀ q : P, Realize M.sets _ (extend (s.encode q) env)) ↔ _
  apply forall_congr'
  intro q
  rw [realize_imp, M.realize_conditionLE s pairing carrier order 0 pi.succ (params o).succ
    (extend (s.encode q) env) q p rfl hp ho]
  apply forall_congr'
  intro _
  rw [M.realize_exConditions s (params c).succ _ (extend (s.encode q) env) carrier hc]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨v, hv, rest⟩ := (realize_ex M.sets _ _).1 ht
    obtain ⟨r, entry, tq, tr, rel⟩ := (M.realize_exConditions s (params c).succ.succ.succ _
      (extend v (extend (s.encode t) (extend (s.encode q) env))) carrier hc).1 rest
    let e := extend (s.encode r) (extend v (extend (s.encode t) (extend (s.encode q) env)))
    have lookup := (realize_atomicApplication M.sets E
      (fun j => (params j).succ.succ.succ.succ) 2 si.succ.succ.succ.succ 1 e).1 rel
    exact ⟨t, (M.realize_conditionLE s pairing carrier order 2 3
      (params o).succ.succ.succ.succ e t q rfl rfl ho).1 tq,
      v, hv, r,
      (M.realize_pairMembershipFormula pairing 1 0 ti.succ.succ.succ.succ e
        hv (M.transitive carrier (s.encode_mem r)) hτ).1 entry,
      (M.realize_conditionLE s pairing carrier order 2 0
        (params o).succ.succ.succ.succ e t r rfl rfl ho).1 tr,
      (meaning t (env si) hσ v hv).1 lookup⟩
  · rintro ⟨t, tq, v, hv, r, entry, tr, rel⟩
    refine ⟨t, ?_⟩
    rw [realize_ex]
    refine ⟨v, hv, ?_⟩
    apply (M.realize_exConditions s (params c).succ.succ.succ _
      (extend v (extend (s.encode t) (extend (s.encode q) env))) carrier hc).2
    let e := extend (s.encode r) (extend v (extend (s.encode t) (extend (s.encode q) env)))
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · exact (M.realize_pairMembershipFormula pairing 1 0 ti.succ.succ.succ.succ e
        hv (M.transitive carrier (s.encode_mem r)) hτ).2 entry
    · exact (M.realize_conditionLE s pairing carrier order 2 3
        (params o).succ.succ.succ.succ e t q rfl rfl ho).2 tq
    · exact (M.realize_conditionLE s pairing carrier order 2 0
        (params o).succ.succ.succ.succ e t r rfl rfl ho).2 tr
    · exact (realize_atomicApplication M.sets E
        (fun j => (params j).succ.succ.succ.succ) 2 si.succ.succ.succ.succ 1 e).2
        ((meaning t (env si) hσ v hv).2 rel)

theorem realize_rawMatching (R : P → ZFSet.{u} → ZFSet.{u} → Prop)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k) (params : Fin k → Fin m)
    (pi si ti : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (meaning : M.RawRelationMeaning s R E (fun j => env (params j)))
    (p : P) (hp : env pi = s.encode p) (hσ : env si ∈ M.sets) (hτ : env ti ∈ M.sets) :
    Realize M.sets (matchingDirectionFormula E c o params pi si ti) env ↔
      M.RawMatching s R p (env si) (env ti) := by
  change (∀ v ∈ M.sets, Realize M.sets _ (extend v env)) ↔ _
  apply forall_congr'
  intro v
  apply forall_congr'
  intro hv
  rw [M.realize_allConditions s (params c).succ _ (extend v env) carrier hc]
  apply forall_congr'
  intro r
  rw [realize_imp, M.realize_pairMembershipFormula pairing 1 0 si.succ.succ
    (extend (s.encode r) (extend v env)) hv (M.transitive carrier (s.encode_mem r)) hσ]
  apply forall_congr'
  intro _
  rw [M.realize_allConditions s (params c).succ.succ _
    (extend (s.encode r) (extend v env)) carrier hc]
  apply forall_congr'
  intro q
  let e := extend (s.encode q) (extend (s.encode r) (extend v env))
  rw [realize_imp]
  change (Realize M.sets _ e ∧ Realize M.sets _ e → Realize M.sets _ e) ↔ _
  rw [M.realize_conditionLE s pairing carrier order 0 pi.succ.succ.succ
    (params o).succ.succ.succ e q p rfl hp ho,
    M.realize_conditionLE s pairing carrier order 0 1 (params o).succ.succ.succ e q r rfl rfl ho,
    M.realize_rawMembership s R pairing carrier order E c o
      (fun j => (params j).succ.succ.succ) 0 2 ti.succ.succ.succ e hc ho meaning q rfl hv hτ]
  exact and_imp

theorem realize_rawEqualityStep (R : P → ZFSet.{u} → ZFSet.{u} → Prop)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k) (params : Fin k → Fin m)
    (pi si ti : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (meaning : M.RawRelationMeaning s R E (fun j => env (params j)))
    (p : P) (hp : env pi = s.encode p) (hσ : env si ∈ M.sets) (hτ : env ti ∈ M.sets) :
    Realize M.sets (equalityStepFormula E c o params pi si ti) env ↔
      M.RawEqualityStep s R p (env si) (env ti) := by
  have swapped : M.RawRelationMeaning s (fun t x y => R t y x) (swapEquality E)
      (fun j => env (params j)) := by
    intro t x hx y hy
    rw [swapEquality, realize_atomicApplication]
    exact meaning t y hy x hx
  change (Realize M.sets _ env ∧ Realize M.sets _ env) ↔ _
  rw [M.realize_rawMatching s R pairing carrier order E c o params pi si ti
    env hc ho meaning p hp hσ hτ,
    M.realize_rawMatching s (fun t x y => R t y x) pairing carrier order
      (swapEquality E) c o params pi ti si env hc ho swapped p hp hτ hσ]
  rfl

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BoundedAtomicEquality
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

variable {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_equalityState
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (z S : ZFSet.{u}) (hz : z ∈ M.sets) (hS : S ∈ M.sets) :
    Realize M.sets equalityStateFormula (extend z (extend S (equalityParameters s))) ↔
      ∃ p x, x ∈ M.sets ∧ ∃ y, y ∈ M.sets ∧
        z = ZFSet.pair (s.encode p) (ZFSet.pair x y) ∧
        M.RawEqualityStep s (RawCodedRelation s S) p x y := by
  let env := extend z (extend S (equalityParameters s))
  rw [equalityStateFormula, M.realize_exConditions s 2 _ env carrier rfl]
  apply exists_congr
  intro p
  rw [realize_ex]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  rw [realize_ex]
  apply exists_congr
  intro y
  apply and_congr_right
  intro hy
  let e := extend y (extend x (extend (s.encode p) env))
  change (Realize M.sets _ e ∧ Realize M.sets _ e) ↔ _
  rw [M.realize_orderedTripleFormula pairing 3 2 1 0 e hz
    (M.transitive carrier (s.encode_mem p)) hx hy,
    M.realize_rawEqualityStep s (RawCodedRelation s S) pairing carrier order
      codedRelationFormula 1 2 (fun j => j.succ.succ.succ.succ) 2 1 0 e rfl rfl
      (M.rawRelationMeaning_coded s pairing carrier S hS) p rfl hx hy]
  rfl

theorem equalityState_mono
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {z S T : ZFSet.{u}} (hz : z ∈ M.sets) (hS : S ∈ M.sets) (hT : T ∈ M.sets)
    (sub : S ⊆ T) :
    Realize M.sets equalityStateFormula (extend z (extend S (equalityParameters s))) →
      Realize M.sets equalityStateFormula (extend z (extend T (equalityParameters s))) := by
  rw [M.realize_equalityState s pairing carrier order z S hz hS,
    M.realize_equalityState s pairing carrier order z T hz hT]
  rintro ⟨p, x, hx, y, hy, shape, step⟩
  exact ⟨p, x, hx, y, hy, shape, M.rawEqualityStep_mono s (fun _ _ _ h => sub h) step⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem rawEqualityStep_names (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (S : ZFSet.{u}) (hS : S ∈ M.sets) (p : P) (σ τ : D.names) :
    M.RawEqualityStep s (RawCodedRelation s S) p σ.val.val τ.val.val ↔
      Name.EqualityStep (Name.codedEqualityRelation s S) p σ.val τ.val := by
  let constants := extend S (equalityParameters s)
  let env := extend (s.encode p) (extend σ.val.val (extend τ.val.val constants))
  have raw := M.realize_rawEqualityStep s (RawCodedRelation s S) pairing carrier order
    codedRelationFormula 1 2 (fun j => j.succ.succ.succ) 0 1 2 env rfl rfl
    (M.rawRelationMeaning_coded s pairing carrier S hS) p rfl
    (ground σ.val σ.property) (ground τ.val τ.property)
  have named := M.realize_equalityStep s D (Name.codedEqualityRelation s S)
    ground pairing carrier order codedRelationFormula 1 2 (fun j => j.succ.succ.succ)
    0 1 2 env rfl rfl (M.relationMeaning_coded s D ground pairing carrier 0 constants hS)
    p σ τ rfl rfl rfl
  exact raw.symm.trans named

theorem realize_equalityState_names (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (S : ZFSet.{u}) (hS : S ∈ M.sets) (p : P) (σ τ : D.names) :
    Realize M.sets equalityStateFormula
      (extend (ZFSet.pair (s.encode p) (ZFSet.pair σ.val.val τ.val.val))
        (extend S (equalityParameters s))) ↔
      Name.EqualityStep (Name.codedEqualityRelation s S) p σ.val τ.val := by
  have hz := M.orderedPair_mem pairing (M.transitive carrier (s.encode_mem p))
    (M.orderedPair_mem pairing (ground σ.val σ.property) (ground τ.val τ.property))
  rw [M.realize_equalityState s pairing carrier order _ S hz hS]
  constructor
  · rintro ⟨q, x, _, y, _, shape, step⟩
    obtain ⟨pq, xy⟩ := ZFSet.pair_inj.1 shape
    have peq := s.injective pq
    obtain ⟨sx, ty⟩ := ZFSet.pair_inj.1 xy
    subst q
    subst x
    subst y
    exact (M.rawEqualityStep_names s D ground pairing carrier order S hS p σ τ).1 step
  · intro step
    exact ⟨p, σ.val.val, ground σ.val σ.property, τ.val.val, ground τ.val τ.property, rfl,
      (M.rawEqualityStep_names s D ground pairing carrier order S hS p σ τ).2 step⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_UniformAtomicEquality
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_membershipFormula (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k) (params : Fin k → Fin m)
    (pi si ti : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (atomic : M.EqualityMeaning s D E (fun j => env (params j)))
    (p : P) (σ τ : D.names) (hp : env pi = s.encode p)
    (hσ : env si = σ.val.val) (hτ : env ti = τ.val.val) :
    Realize M.sets (membershipFormula E c o params pi si ti) env ↔
      Name.ForcesMem p σ.val τ.val := by
  have hτM : env ti ∈ M.sets := hτ ▸ ground τ.val τ.property
  rw [membershipFormula, M.realize_allConditions s _ _ env carrier hc]
  change (∀ q : P, Realize M.sets _ (extend (s.encode q) env)) ↔
    ∀ q, q ≤ p → ∃ t, t ≤ q ∧ ∃ ν r,
      Name.Entry ν τ.val r ∧ t ≤ r ∧ Name.ForcesEq t σ.val ν
  apply forall_congr'
  intro q
  rw [realize_imp, M.realize_conditionLE s pairing carrier order 0 pi.succ (params o).succ
    (extend (s.encode q) env) q p rfl hp ho]
  apply forall_congr'
  intro _
  rw [M.realize_exConditions s (params c).succ _ (extend (s.encode q) env) carrier hc]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨v, hv, rest⟩ := (realize_ex M.sets _ _).1 ht
    obtain ⟨r, entry, tq, tr, eq⟩ := (M.realize_exConditions s (params c).succ.succ.succ _
      (extend v (extend (s.encode t) (extend (s.encode q) env))) carrier hc).1 rest
    let e := extend (s.encode r) (extend v (extend (s.encode t) (extend (s.encode q) env)))
    have raw := (M.realize_pairMembershipFormula pairing 1 0 ti.succ.succ.succ.succ e
      hv (M.transitive carrier (s.encode_mem r)) hτM).1 entry
    change ZFSet.pair v (s.encode r) ∈ env ti at raw
    rw [hτ] at raw
    let ν : Name s := ⟨v, Name.isName_of_pair_mem τ.val v r raw⟩
    have hν : ν ∈ D.names := D.children τ.property raw
    have forced := (realize_atomicApplication M.sets E
      (fun j => (params j).succ.succ.succ.succ) 2 si.succ.succ.succ.succ 1 e).1 eq
    change Realize M.sets E (extend (s.encode t) (extend (env si)
      (extend v (fun j => env (params j))))) at forced
    rw [hσ] at forced
    exact ⟨t, (M.realize_conditionLE s pairing carrier order 2 3
      (params o).succ.succ.succ.succ e t q rfl rfl ho).1 tq,
      ν, r, raw, (M.realize_conditionLE s pairing carrier order 2 0
        (params o).succ.succ.succ.succ e t r rfl rfl ho).1 tr,
      (atomic t σ ⟨ν, hν⟩).1 forced⟩
  · rintro ⟨t, tq, ν, r, entry, tr, forced⟩
    have hν : ν ∈ D.names := D.children τ.property entry
    refine ⟨t, ?_⟩
    rw [realize_ex]
    refine ⟨ν.val, ground ν hν, ?_⟩
    apply (M.realize_exConditions s (params c).succ.succ.succ _
      (extend ν.val (extend (s.encode t) (extend (s.encode q) env))) carrier hc).2
    let e := extend (s.encode r) (extend ν.val (extend (s.encode t) (extend (s.encode q) env)))
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · apply (M.realize_pairMembershipFormula pairing 1 0 ti.succ.succ.succ.succ e
        (ground ν hν) (M.transitive carrier (s.encode_mem r)) hτM).2
      change ZFSet.pair ν.val (s.encode r) ∈ env ti
      rw [hτ]
      exact entry
    · exact (M.realize_conditionLE s pairing carrier order 2 3
        (params o).succ.succ.succ.succ e t q rfl rfl ho).2 tq
    · exact (M.realize_conditionLE s pairing carrier order 2 0
        (params o).succ.succ.succ.succ e t r rfl rfl ho).2 tr
    · apply (realize_atomicApplication M.sets E
        (fun j => (params j).succ.succ.succ.succ) 2 si.succ.succ.succ.succ 1 e).2
      change Realize M.sets E (extend (s.encode t) (extend (env si)
        (extend ν.val (fun j => env (params j)))))
      rw [hσ]
      exact (atomic t σ ⟨ν, hν⟩).2 forced

end PartitionPilot.Forcing.TransitiveGround



section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem equalityCertificate_sound (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (S : ZFSet.{u}) (hS : S ∈ M.sets)
    (certificate : Realize M.sets equalityCertificateFormula (extend S (equalityParameters s)))
    (p : P) (σ τ : D.names) :
    Name.codedEqualityRelation s S p σ.val τ.val → Name.ForcesEq p σ.val τ.val := by
  have post : ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p,
      Name.codedEqualityRelation s S p σ τ → Name.EqualityStep (Name.codedEqualityRelation s S) p σ τ := by
    intro σ hσ τ hτ p rel
    have step := (realize_imp M.sets _ _ _).1
      (certificate _ (M.transitive hS rel)) rel
    exact (M.realize_equalityState_names s D ground pairing carrier order S hS
      p ⟨σ, hσ⟩ ⟨τ, hτ⟩).1 step
  exact Name.postfixed_equality_sound D (Name.codedEqualityRelation s S) post
    σ.val σ.property τ.val τ.property p

theorem exists_equalityState_fixedPoint
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (B : ZFSet.{u}) (hB : B ∈ M.sets) :
    ∃ S ∈ M.sets, S ⊆ B ∧
      definableOperator M.sets equalityStateFormula (equalityParameters s) B S = S := by
  have members : ∀ i, equalityParameters s i ∈ M.sets :=
    Fin.cases carrier (Fin.cases order (fun i => Fin.elim0 i))
  have mono : ∀ S ∈ M.sets, ∀ T ∈ M.sets, S ⊆ B → T ⊆ B → S ⊆ T →
      definableOperator M.sets equalityStateFormula (equalityParameters s) B S ⊆
        definableOperator M.sets equalityStateFormula (equalityParameters s) B T := by
    intro S hS T hT _ _ sub z hz
    obtain ⟨hzB, step⟩ := ZFSet.mem_sep.1 hz
    exact ZFSet.mem_sep.2 ⟨hzB,
      M.equalityState_mono s pairing carrier order (M.transitive hB hzB) hS hT sub step⟩
  obtain ⟨S, hS, bound, fixed, _⟩ := M.exists_greatest_definable_fixedPoint unions powers separation
    equalityStateFormula (equalityParameters s) members hB mono
  exact ⟨S, hS, bound, fixed⟩

theorem equality_fixedPoint_iff (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {B S : ZFSet.{u}} (hS : S ∈ M.sets)
    (bound : ∀ p (σ τ : D.names), ZFSet.pair (s.encode p) (ZFSet.pair σ.val.val τ.val.val) ∈ B)
    (fixed : definableOperator M.sets equalityStateFormula (equalityParameters s) B S = S)
    (p : P) (σ τ : D.names) :
    Name.codedEqualityRelation s S p σ.val τ.val ↔ Name.ForcesEq p σ.val τ.val := by
  have step : ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p,
      Name.codedEqualityRelation s S p σ τ ↔ Name.EqualityStep (Name.codedEqualityRelation s S) p σ τ := by
    intro σ hσ τ hτ p
    change ZFSet.pair (s.encode p) (ZFSet.pair σ.val τ.val) ∈ S ↔ _
    calc
      _ ↔ ZFSet.pair (s.encode p) (ZFSet.pair σ.val τ.val) ∈
          definableOperator M.sets equalityStateFormula (equalityParameters s) B S := by rw [fixed]
      _ ↔ _ := by
        rw [definableOperator, ZFSet.mem_sep,
          M.realize_equalityState_names s D ground pairing carrier order S hS p ⟨σ, hσ⟩ ⟨τ, hτ⟩]
        exact and_iff_right (bound p ⟨σ, hσ⟩ ⟨τ, hτ⟩)
  exact Name.fixed_equality_iff D (Name.codedEqualityRelation s S) step σ.property τ.property p

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem exists_atomicEquality_certificate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (p : P) (σ τ : Name s) (hσ : σ.val ∈ M.sets) (hτ : τ.val ∈ M.sets)
    (forced : Name.ForcesEq p σ τ) :
    ∃ S ∈ M.sets, Realize M.sets equalityCertificateFormula (extend S (equalityParameters s)) ∧
      Name.codedEqualityRelation s S p σ τ := by
  obtain ⟨T, hT, σT, τT, trans⟩ := M.exists_pair_transitiveCover pairing unions separation collection hσ hτ
  let D := namesInTransitiveSet s T (fun hx hy => trans _ hx _ hy)
  have ground : ∀ ν ∈ D.names, ν.val ∈ M.sets := fun _ hν => M.transitive hT hν
  obtain ⟨C, hC, pairBound⟩ := M.exists_pair_bound pairing unions powers hT hT
  obtain ⟨B, hB, tripleBound⟩ := M.exists_pair_bound pairing unions powers carrier hC
  have bound : ∀ q (ν ρ : D.names),
      ZFSet.pair (s.encode q) (ZFSet.pair ν.val.val ρ.val.val) ∈ B := by
    intro q ν ρ
    exact tripleBound (s.encode q) (s.encode_mem q) _
      (pairBound ν.val.val ν.property ρ.val.val ρ.property)
  obtain ⟨S, hS, hSB, fixed⟩ := M.exists_equalityState_fixedPoint s pairing unions powers separation
    carrier order B hB
  exact ⟨S, hS, M.fixedPoint_equalityCertificate s hS hSB fixed,
    (M.equality_fixedPoint_iff s D ground pairing carrier order hS bound fixed p ⟨σ, σT⟩ ⟨τ, τT⟩).2 forced⟩

theorem forcesEq_iff_exists_certificate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (p : P) (σ τ : Name s) (hσ : σ.val ∈ M.sets) (hτ : τ.val ∈ M.sets) :
    Name.ForcesEq p σ τ ↔
      ∃ S ∈ M.sets, Realize M.sets equalityCertificateFormula (extend S (equalityParameters s)) ∧
        Name.codedEqualityRelation s S p σ τ := by
  constructor
  · exact M.exists_atomicEquality_certificate s pairing unions powers separation collection carrier order
      p σ τ hσ hτ
  · rintro ⟨S, hS, certificate, rel⟩
    exact M.equalityCertificate_sound s (M.nameDomain s) (fun _ h => h)
      pairing carrier order S hS certificate p ⟨σ, hσ⟩ ⟨τ, hτ⟩ rel

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_uniformEqualityFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (p : P) (σ τ : Name s) (hσ : σ.val ∈ M.sets) (hτ : τ.val ∈ M.sets) :
    Realize M.sets uniformEqualityFormula
      (extend (s.encode p) (extend σ.val (extend τ.val (equalityParameters s)))) ↔
      Name.ForcesEq p σ τ := by
  rw [M.forcesEq_iff_exists_certificate s pairing unions powers separation collection carrier order p σ τ hσ hτ,
    uniformEqualityFormula, realize_ex]
  apply exists_congr
  intro S
  apply and_congr_right
  intro hS
  let env := extend S (extend (s.encode p) (extend σ.val (extend τ.val (equalityParameters s))))
  change (Realize M.sets _ env ∧ Realize M.sets _ env) ↔ _
  rw [realize_atomicApplication,
    M.realize_tripleMembershipFormula pairing 1 2 3 0 env
      (M.transitive carrier (s.encode_mem p)) hσ hτ hS, map_empty]
  rfl

theorem equalityMeaning_lifted (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k : Nat} (c o : Fin k) (constants : Fin k → ZFSet.{u})
    (hc : constants c = s.carrier) (ho : constants o = s.conditionOrder) :
    M.EqualityMeaning s D (liftedEqualityFormula c o) constants := by
  intro p σ τ
  rw [liftedEqualityFormula, realize_atomicApplication, map_extend, map_extend, map_empty]
  change Realize M.sets uniformEqualityFormula
    (extend (s.encode p) (extend σ.val.val (extend τ.val.val
      (extend (constants c) (extend (constants o) Fin.elim0))))) ↔ _
  rw [hc, ho]
  exact M.realize_uniformEqualityFormula s pairing unions powers separation collection carrier order
    p σ.val τ.val (ground σ.val σ.property) (ground τ.val τ.property)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_UniformGroundNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.SetFormula

universe u

theorem realize_domainApplication (U : Set ZFSet.{u}) {k m : Nat}
    (N : SetFormula (k + 1)) (params : Fin k → Fin m) (x : Fin m) (env : Fin m → ZFSet.{u}) :
    Realize U (domainApplication N params x) env ↔
      Realize U N (extend (env x) (fun i => env (params i))) := by
  rw [domainApplication, realize_reindex, map_extend]

end PartitionPilot.Forcing.SetFormula



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_forcingTranslation (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k n : Nat} (A : ForcingPrimitives k) (φ : SetFormula n) :
    ∀ {m} (params : Fin k → Fin m) (pi : Fin m) (names : Fin n → Fin m)
      (env : Fin m → ZFSet.{u}),
      env (params A.carrier) = s.carrier → env (params A.order) = s.conditionOrder →
      M.EqualityMeaning s D A.equality (fun j => env (params j)) →
      M.DomainMeaning s D A.domain (fun j => env (params j)) →
      ∀ (p : P) (nameEnv : Assignment D n), env pi = s.encode p →
      (∀ i, env (names i) = (nameEnv i).val.val) →
      (Realize M.sets (forcingTranslation A φ params pi names) env ↔ Forces D φ nameEnv p) := by
  induction φ with
  | equal i j =>
    intro m params pi names env hc ho atomic domain p nameEnv hp hnames
    change Realize M.sets (atomicApplication A.equality params pi (names i) (names j)) env ↔ _
    rw [realize_atomicApplication, hp, hnames i, hnames j]
    exact atomic p (nameEnv i) (nameEnv j)
  | mem i j =>
    intro m params pi names env hc ho atomic domain p nameEnv hp hnames
    exact M.realize_membershipFormula s D ground pairing carrier order A.equality
      A.carrier A.order params pi (names i) (names j) env hc ho atomic p
      (nameEnv i) (nameEnv j) hp (hnames i) (hnames j)
  | neg φ ih =>
    intro m params pi names env hc ho atomic domain p nameEnv hp hnames
    change Realize M.sets (allConditions _ _) env ↔
      ∀ q, q ≤ p → ¬ Forces D φ nameEnv q
    rw [M.realize_allConditions s (params A.carrier) _ env carrier hc]
    apply forall_congr'
    intro q
    rw [realize_imp, M.realize_conditionLE s pairing carrier order 0 pi.succ
      (params A.order).succ (extend (s.encode q) env) q p rfl hp ho]
    apply forall_congr'
    intro _
    exact not_congr (ih (fun j => (params j).succ) 0 (fun i => (names i).succ)
      (extend (s.encode q) env) hc ho atomic domain q nameEnv rfl hnames)
  | conj φ ψ ihφ ihψ =>
    intro m params pi names env hc ho atomic domain p nameEnv hp hnames
    exact and_congr (ihφ params pi names env hc ho atomic domain p nameEnv hp hnames)
      (ihψ params pi names env hc ho atomic domain p nameEnv hp hnames)
  | all φ ih =>
    intro m params pi names env hc ho atomic domain p nameEnv hp hnames
    change (∀ x ∈ M.sets, Realize M.sets (imp
      (domainApplication A.domain (fun j => (params j).succ) 0)
      (forcingTranslation A φ (fun j => (params j).succ) pi.succ
        (extend 0 (fun i => (names i).succ)))) (extend x env)) ↔
      ∀ τ : D.names, Forces D φ (extend τ nameEnv) p
    constructor
    · intro h τ
      have hx := ground τ.val τ.property
      have belongs : Realize M.sets (domainApplication A.domain (fun j => (params j).succ) 0)
          (extend τ.val.val env) :=
        (realize_domainApplication M.sets A.domain _ _ _).2 ((domain τ.val.val hx).2 ⟨τ, rfl⟩)
      have body := (realize_imp M.sets _ _ _).1 (h τ.val.val hx) belongs
      apply (ih (fun j => (params j).succ) pi.succ (extend 0 (fun i => (names i).succ))
        (extend τ.val.val env) hc ho atomic domain p (extend τ nameEnv) hp ?_).1 body
      intro i
      exact Fin.cases rfl (fun j => hnames j) i
    · intro h x hx
      rw [realize_imp, realize_domainApplication]
      intro belongs
      obtain ⟨τ, rfl⟩ := (domain x hx).1 belongs
      apply (ih (fun j => (params j).succ) pi.succ (extend 0 (fun i => (names i).succ))
        (extend τ.val.val env) hc ho atomic domain p (extend τ nameEnv) hp ?_).2 (h τ)
      intro i
      exact Fin.cases rfl (fun j => hnames j) i






end PartitionPilot.Forcing.TransitiveGround



section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_forcingWithGroundEquality (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k n m : Nat} (c o : Fin k) (N : SetFormula (k + 1)) (φ : SetFormula n)
    (params : Fin k → Fin m) (pi : Fin m) (names : Fin n → Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (domain : M.DomainMeaning s D N (fun j => env (params j)))
    (p : P) (nameEnv : Assignment D n) (hp : env pi = s.encode p)
    (hnames : ∀ i, env (names i) = (nameEnv i).val.val) :
    Realize M.sets (forcingTranslation (withGroundEquality c o N) φ params pi names) env ↔
      Forces D φ nameEnv p :=
  M.realize_forcingTranslation s D ground pairing carrier order (withGroundEquality c o N) φ
    params pi names env hc ho
    (M.equalityMeaning_lifted s D ground pairing unions powers separation collection carrier order c o _ hc ho)
    domain p nameEnv hp hnames

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem realize_uniformNameFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (x : ZFSet.{u}) (hx : x ∈ M.sets) :
    Realize M.sets uniformNameFormula (extend x (extend s.carrier Fin.elim0)) ↔ IsName s x := by
  rw [M.isName_iff_exists_certificate s pairing unions powers separation collection carrier x hx,
    uniformNameFormula, realize_ex]
  apply exists_congr
  intro S
  apply and_congr_right
  intro _
  change (Realize M.sets _ _ ∧ x ∈ S) ↔ _
  rw [realize_domainApplication, map_extend, map_empty]
  rfl

theorem domainMeaning_liftedNames
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets)
    {k : Nat} (c : Fin k) (constants : Fin k → ZFSet.{u}) (hc : constants c = s.carrier) :
    M.DomainMeaning s (M.nameDomain s) (liftedNameFormula c) constants := by
  intro x hx
  rw [liftedNameFormula, realize_domainApplication, map_extend, map_empty]
  change Realize M.sets uniformNameFormula (extend x (extend (constants c) Fin.elim0)) ↔ _
  rw [hc, M.realize_uniformNameFormula s pairing unions powers separation collection carrier x hx]
  constructor
  · intro name
    exact ⟨⟨⟨x, name⟩, hx⟩, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact τ.val.property

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameRenameSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_ordinaryGroundForcing
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k n m : Nat} (c o : Fin k) (φ : SetFormula n)
    (params : Fin k → Fin m) (pi : Fin m) (names : Fin n → Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (p : P) (nameEnv : Assignment (M.nameDomain s) n) (hp : env pi = s.encode p)
    (hnames : ∀ i, env (names i) = (nameEnv i).val.val) :
    Realize M.sets (forcingTranslation (ordinaryGroundPrimitives c o) φ params pi names) env ↔
      Forces (M.nameDomain s) φ nameEnv p :=
  M.realize_forcingWithGroundEquality s (M.nameDomain s) (fun _ h => h) pairing unions powers
    separation collection carrier order c o (liftedNameFormula c) φ params pi names env hc ho
    (M.domainMeaning_liftedNames s pairing unions powers separation collection carrier c _ hc)
    p nameEnv hp hnames

end PartitionPilot.Forcing.TransitiveGround




end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundProductActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem realize_uniformRenameFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (σ τ : Name s) (hσ : σ.val ∈ M.sets) (hτ : τ.val ∈ M.sets) :
    Realize M.sets uniformRenameFormula (extend σ.val (extend τ.val (renameParameters s f))) ↔
      Name.rename s f σ = τ := by
  rw [M.rename_eq_iff_exists_certificate s pairing unions powers separation collection carrier f graph σ τ hσ hτ,
    uniformRenameFormula, realize_ex]
  apply exists_congr
  intro R
  apply and_congr_right
  intro hr
  let env := extend R (extend σ.val (extend τ.val (renameParameters s f)))
  change (Realize M.sets _ env ∧ Realize M.sets _ env) ↔ _
  rw [realize_atomicApplication, map_empty,
    M.realize_pairMembershipFormula pairing 1 2 0 env hσ hτ hr]
  rfl

end PartitionPilot.Forcing.TransitiveGround



end


section

namespace PartitionPilot.Forcing.SetFormula

def nameActionFormula : SetFormula 5 :=
  ex (.conj (pairMembershipFormula 1 0 5)
    (binaryApplication uniformRenameFormula (extend 4 (extend 0 Fin.elim0)) 2 3))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem realize_nameActionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (g : G) (σ τ : Name s) (hσ : σ.val ∈ M.sets) (hτ : τ.val ∈ M.sets) :
    Realize M.sets nameActionFormula
      (extend (t.encode g) (extend σ.val (extend τ.val
        (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ↔
      a.act s g σ = τ := by
  rw [nameActionFormula, realize_ex]
  have hg := M.transitive group (t.encode_mem g)
  have graph := M.conditionMap_graph_mem a s t maps g
  let base := extend (t.encode g) (extend σ.val (extend τ.val
    (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))
  constructor
  · rintro ⟨F, hF, lookup, renamed⟩
    have raw := (M.realize_pairMembershipFormula pairing 1 0 5 (extend F base) hg hF maps).1 lookup
    have eq := (a.pair_mem_conditionMapFamily s t g F).1 raw
    subst F
    rw [realize_binaryApplication, map_extend, map_extend, map_empty] at renamed
    exact (M.realize_uniformRenameFormula s pairing unions powers separation collection carrier
      (a.iso g) graph σ τ hσ hτ).1 renamed
  · intro eq
    refine ⟨s.graph s (a.iso g), graph, ?_, ?_⟩
    · exact (M.realize_pairMembershipFormula pairing 1 0 5 (extend (s.graph s (a.iso g)) base)
        hg graph maps).2 ((a.pair_mem_conditionMapFamily s t g _).2 rfl)
    · rw [realize_binaryApplication, map_extend, map_extend, map_empty]
      exact (M.realize_uniformRenameFormula s pairing unions powers separation collection carrier
        (a.iso g) graph σ τ hσ hτ).2 eq

end PartitionPilot.Forcing.TransitiveGround



end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RenamedEntryFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def renamedChildFormula : SetFormula 4 :=
  ex (exConditions 3 (.conj (orderedPairFormula 2 1 0)
    (.conj (domainApplication uniformNameFormula (extend 4 Fin.elim0) 3)
      (binaryApplication uniformRenameFormula (extend 4 (extend 5 Fin.elim0)) 1 3))))

def renamedEntryFormula : SetFormula 4 :=
  ex (exConditions 3 (.conj (pairMembershipFormula 1 0 3)
    (ex (exConditions 5 (.conj (orderedPairFormula 4 1 0)
      (.conj (pairMembershipFormula 2 0 7)
        (.conj (domainApplication uniformNameFormula (extend 6 Fin.elim0) 1)
          (binaryApplication uniformRenameFormula (extend 6 (extend 7 Fin.elim0)) 3 1))))))))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem realize_renamedChildFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (σ : Name s) (hσ : σ.val ∈ M.sets) (p : P) (y : ZFSet.{u}) (hy : y ∈ M.sets) :
    Realize M.sets renamedChildFormula
      (extend (ZFSet.pair σ.val (s.encode p)) (extend y (renameParameters s f))) ↔
      y = (Name.rename s f σ).val := by
  let base := extend (ZFSet.pair σ.val (s.encode p)) (extend y (renameParameters s f))
  have hp := M.transitive carrier (s.encode_mem p)
  have hz := M.orderedPair_mem pairing hσ hp
  rw [renamedChildFormula, realize_ex]
  constructor
  · rintro ⟨x, hx, rest⟩
    obtain ⟨r, shape, name, renamed⟩ := (M.realize_exConditions s 3 _ (extend x base) carrier rfl).1 rest
    let e := extend (s.encode r) (extend x base)
    have raw := (M.realize_orderedPairFormula pairing 2 1 0 e hz hx
      (M.transitive carrier (s.encode_mem r))).1 shape
    change ZFSet.pair σ.val (s.encode p) = ZFSet.pair x (s.encode r) at raw
    obtain ⟨sx, pr⟩ := ZFSet.pair_inj.1 raw
    have cond := s.injective pr
    subst x
    subst r
    rw [realize_domainApplication, map_extend, map_empty] at name
    have nameY := (M.realize_uniformNameFormula s pairing unions powers separation collection carrier y hy).1 name
    rw [realize_binaryApplication, map_extend, map_extend, map_empty] at renamed
    have eq := (M.realize_uniformRenameFormula s pairing unions powers separation collection carrier f graph
      σ ⟨y, nameY⟩ hσ hy).1 renamed
    exact (congrArg Subtype.val eq).symm
  · intro eq
    subst y
    refine ⟨σ.val, hσ, ?_⟩
    apply (M.realize_exConditions s 3 _ (extend σ.val base) carrier rfl).2
    refine ⟨p, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 2 1 0 _ hz hσ hp).2 rfl
    · rw [realize_domainApplication, map_extend, map_empty]
      exact (M.realize_uniformNameFormula s pairing unions powers separation collection carrier _ hy).2
        (Name.rename s f σ).property
    · rw [realize_binaryApplication, map_extend, map_extend, map_empty]
      exact (M.realize_uniformRenameFormula s pairing unions powers separation collection carrier f graph
        σ (Name.rename s f σ) hσ hy).2 rfl

theorem realize_renamedEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (τ : Name s) (hτ : τ.val ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets renamedEntryFormula (extend z (extend τ.val (renameParameters s f))) ↔
      z ∈ (Name.rename s f τ).val := by
  let base := extend z (extend τ.val (renameParameters s f))
  rw [renamedEntryFormula, realize_ex]
  constructor
  · rintro ⟨x, hx, rest⟩
    obtain ⟨p, old, rest⟩ := (M.realize_exConditions s 3 _ (extend x base) carrier rfl).1 rest
    have entry := (M.realize_pairMembershipFormula pairing 1 0 3
      (extend (s.encode p) (extend x base)) hx (M.transitive carrier (s.encode_mem p)) hτ).1 old
    let σ : Name s := ⟨x, Name.isName_of_pair_mem τ x p entry⟩
    obtain ⟨y, hy, rest⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨q, shape, condition, name, renamed⟩ := (M.realize_exConditions s 5 _
      (extend y (extend (s.encode p) (extend x base))) carrier rfl).1 rest
    let e := extend (s.encode q) (extend y (extend (s.encode p) (extend x base)))
    have raw := (M.realize_orderedPairFormula pairing 4 1 0 e hz hy
      (M.transitive carrier (s.encode_mem q))).1 shape
    have cond := (M.realize_pairMembershipFormula pairing 2 0 7 e
      (M.transitive carrier (s.encode_mem p)) (M.transitive carrier (s.encode_mem q)) graph).1 condition
    have pq := (s.pair_mem_graph s f p q).1 cond
    rw [realize_domainApplication, map_extend, map_empty] at name
    have nameY := (M.realize_uniformNameFormula s pairing unions powers separation collection carrier y hy).1 name
    let ν : Name s := ⟨y, nameY⟩
    rw [realize_binaryApplication, map_extend, map_extend, map_empty] at renamed
    have eq := (M.realize_uniformRenameFormula s pairing unions powers separation collection carrier f graph σ ν hx hy).1 renamed
    have member := (Name.entry_rename s f τ ν q).2 ⟨σ, p, entry, eq, pq⟩
    change z = ZFSet.pair y (s.encode q) at raw
    rw [raw]
    exact member
  · intro member
    obtain ⟨ν, q, rfl⟩ := Name.entries_cover (Name.rename s f τ) member
    obtain ⟨σ, p, entry, image, cond⟩ := (Name.entry_rename s f τ ν q).1 member
    have hσ := (M.nameDomain s).children hτ entry
    have hν := M.pair_left hz
    refine ⟨σ.val, hσ, ?_⟩
    apply (M.realize_exConditions s 3 _ (extend σ.val base) carrier rfl).2
    refine ⟨p, ?_, ?_⟩
    · exact (M.realize_pairMembershipFormula pairing 1 0 3 _ hσ
        (M.transitive carrier (s.encode_mem p)) hτ).2 entry
    · rw [realize_ex]
      refine ⟨ν.val, hν, ?_⟩
      apply (M.realize_exConditions s 5 _ (extend ν.val (extend (s.encode p) (extend σ.val base))) carrier rfl).2
      let e := extend (s.encode q) (extend ν.val (extend (s.encode p) (extend σ.val base)))
      refine ⟨q, ?_, ?_, ?_, ?_⟩
      · exact (M.realize_orderedPairFormula pairing 4 1 0 e hz hν
          (M.transitive carrier (s.encode_mem q))).2 rfl
      · exact (M.realize_pairMembershipFormula pairing 2 0 7 e
          (M.transitive carrier (s.encode_mem p)) (M.transitive carrier (s.encode_mem q)) graph).2
          ((s.pair_mem_graph s f p q).2 cond)
      · rw [realize_domainApplication, map_extend, map_empty]
        exact (M.realize_uniformNameFormula s pairing unions powers separation collection carrier ν.val hν).2 ν.property
      · rw [realize_binaryApplication, map_extend, map_extend, map_empty]
        exact (M.realize_uniformRenameFormula s pairing unions powers separation collection carrier f graph σ ν hσ hν).2 image

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NameSupportFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.SetFormula

def nameSupportFormula : SetFormula 6 :=
  allConditions 3 (imp (pairMembershipFormula 2 0 5)
    (atomicApplication nameActionFormula (extend 3 (extend 6 Fin.elim0)) 0 1 1))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem realize_nameSupportFormula (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (i : I) (hi : b.encode i ∈ M.sets) (τ : Name s) (hτ : τ.val ∈ M.sets) :
    Realize M.sets nameSupportFormula
      (extend τ.val (extend (b.encode i) (extend s.carrier (extend t.carrier
        (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0)))))) ↔
      K i ≤ a.stabilizer s τ := by
  let env := extend τ.val (extend (b.encode i) (extend s.carrier (extend t.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0)))))
  rw [nameSupportFormula, M.realize_allConditions t 3 _ env group rfl]
  change (∀ g, Realize M.sets _ _) ↔ ∀ g, g ∈ K i → a.act s g τ = τ
  apply forall_congr'
  intro g
  let e := extend (t.encode g) env
  rw [realize_imp, M.realize_pairMembershipFormula pairing 2 0 5 e hi
    (M.transitive group (t.encode_mem g)) supports]
  change (ZFSet.pair (b.encode i) (t.encode g) ∈ supportBasisCode b t K → Realize M.sets _ e) ↔ _
  rw [pair_mem_supportBasisCode]
  apply forall_congr'
  intro _
  rw [realize_atomicApplication, map_extend, map_extend, map_empty]
  exact M.realize_nameActionFormula a s t pairing unions powers separation collection
    carrier group maps g τ τ hτ hτ

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_SymmetricGroundForcing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def nameSymmetryFormula : SetFormula 6 :=
  exConditions 3 (allConditions 3 (imp (pairMembershipFormula 1 0 6)
    (atomicApplication nameActionFormula (extend 3 (extend 7 Fin.elim0)) 0 2 2)))

end PartitionPilot.Forcing.SetFormula



namespace PartitionPilot.Forcing.SetFormula

def hereditaryStepFormula : SetFormula 7 :=
  .conj (domainApplication nameSymmetryFormula (fun j => j.succ.succ) 0)
    (binaryApplication nameCodeStepFormula (extend 2 Fin.elim0) 0 1)

def hereditaryCertificateFormula : SetFormula 6 := postfixedFormula hereditaryStepFormula

end PartitionPilot.Forcing.SetFormula

end


section

namespace PartitionPilot.Forcing.SetFormula

def uniformHereditaryFormula : SetFormula 6 :=
  ex (.conj (domainApplication hereditaryCertificateFormula (fun j => j.succ.succ) 0) (.mem 1 0))

def liftedHereditaryFormula {k : Nat} (c g i b a : Fin k) : SetFormula (k + 1) :=
  domainApplication uniformHereditaryFormula
    (extend c.succ (extend g.succ (extend i.succ (extend b.succ (extend a.succ Fin.elim0))))) 0

end PartitionPilot.Forcing.SetFormula

end


namespace PartitionPilot.Forcing.SetFormula

def symmetricGroundPrimitives : ForcingPrimitives 6 :=
  withGroundEquality 0 1 (liftedHereditaryFormula 0 2 3 4 5)

end PartitionPilot.Forcing.SetFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundGraphValueDescendantWitnesses
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem rename_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets) :
    ∀ τ : Name s, τ.val ∈ M.sets → (Name.rename s f τ).val ∈ M.sets := by
  intro τ
  induction τ using Name.inductionOn with
  | step τ ih =>
    intro hτ
    have members : ∀ i, renameParameters s f i ∈ M.sets :=
      Fin.cases carrier (Fin.cases graph (fun i => Fin.elim0 i))
    have witnesses : ∀ z ∈ τ.val, ∃ y ∈ M.sets,
        Realize M.sets renamedChildFormula (extend z (extend y (renameParameters s f))) := by
      intro z hz
      obtain ⟨σ, p, rfl⟩ := Name.entries_cover τ hz
      have hσ := (M.nameDomain s).children hτ hz
      have imageM := ih σ p hz hσ
      exact ⟨(Name.rename s f σ).val, imageM,
        (M.realize_renamedChildFormula s pairing unions powers separation collection carrier f graph
          σ hσ p _ imageM).2 rfl⟩
    obtain ⟨W, hW, images⟩ := M.collection_witness collection renamedChildFormula
      (renameParameters s f) members hτ witnesses
    have children : ∀ σ p, Name.Entry σ τ p → (Name.rename s f σ).val ∈ W := by
      intro σ p entry
      obtain ⟨y, hyW, rel⟩ := images _ entry
      have eq := (M.realize_renamedChildFormula s pairing unions powers separation collection carrier f graph
        σ ((M.nameDomain s).children hτ entry) p y (M.transitive hW hyW)).1 rel
      exact eq ▸ hyW
    obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers hW carrier
    have bound : (Name.rename s f τ).val ⊆ B := by
      intro z hz
      obtain ⟨ν, q, rfl⟩ := Name.entries_cover (Name.rename s f τ) hz
      obtain ⟨σ, p, entry, image, _⟩ := (Name.entry_rename s f τ ν q).1 hz
      exact pairBound ν.val (image ▸ children σ p entry) (s.encode q) (s.encode_mem q)
    have selected := M.separation_mem separation renamedEntryFormula (extend τ.val (renameParameters s f))
      (Fin.cases hτ members) hB
    have eq : ZFSet.sep (fun z => Realize M.sets renamedEntryFormula
        (extend z (extend τ.val (renameParameters s f)))) B = (Name.rename s f τ).val := by
      apply ZFSet.ext
      intro z
      rw [ZFSet.mem_sep]
      constructor
      · rintro ⟨hzB, rel⟩
        exact (M.realize_renamedEntryFormula s pairing unions powers separation collection carrier f graph
          τ hτ z (M.transitive hB hzB)).1 rel
      · intro hz
        exact ⟨bound hz, (M.realize_renamedEntryFormula s pairing unions powers separation collection carrier f graph
          τ hτ z (M.transitive hB (bound hz))).2 hz⟩
    exact eq ▸ selected

variable {G : Type u} [Group G] [PartialOrder P]

theorem act_mem (a : PosetAction G P) (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (g : G) (τ : Name s) (hτ : τ.val ∈ M.sets) : (a.act s g τ).val ∈ M.sets :=
  M.rename_mem s pairing unions powers separation collection carrier (a.iso g)
    (M.conditionMap_graph_mem a s t maps g) τ hτ

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}}
variable (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)

include pairing unions powers separation collection carrier maps closed

theorem niceNameCandidates_act_iff (K : Subgroup G) (g : G) (τ : Name s) :
    (a.act s g τ).val ∈ M.niceNameCandidates a s T (K.map (conjugateHom g)) ↔
      τ.val ∈ M.niceNameCandidates a s T K := by
  rw [M.mem_niceNameCandidates, M.mem_niceNameCandidates,
    niceNameCode_act_iff a s closed g τ]
  constructor
  · rintro ⟨ground, code⟩
    have back := M.act_mem s a t pairing unions powers separation collection
      carrier maps g⁻¹ (a.act s g τ) ground
    exact ⟨by simpa only [a.act_inv_left] using back, code⟩
  · rintro ⟨ground, code⟩
    exact ⟨M.act_mem s a t pairing unions powers separation collection
      carrier maps g τ ground, code⟩

theorem niceNameCandidates_principal_act_iff (d : PosetAction G L)
    (g : G) (v : L) (τ : Name s) :
    (a.act s g τ).val ∈ M.niceNameCandidates a s T (d.principalFix (d.iso g v)) ↔
      τ.val ∈ M.niceNameCandidates a s T (d.principalFix v) := by
  rw [← principalFix_map_conjugate d g v]
  exact M.niceNameCandidates_act_iff a s t pairing unions powers separation collection
    carrier maps closed (d.principalFix v) g τ

end PartitionPilot.Forcing.TransitiveGround


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_CheckCertificates
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.SetFormula

def uniformCheckFormula : SetFormula 3 :=
  ex (.conj (binaryApplication checkCertificateFormula Fin.elim0 0 3) (pairMembershipFormula 1 2 0))

end PartitionPilot.Forcing.SetFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_IndexedTupleNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_uniformCheckFormula {P : Type u} (s : Presentation P) (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hone : s.encode one ∈ M.sets) (x y : ZFSet.{u}) (hx : x ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets uniformCheckFormula (extend x (extend y (extend (s.encode one) Fin.elim0))) ↔
      y = (Name.check s one x).val := by
  rw [uniformCheckFormula, realize_ex]
  constructor
  · rintro ⟨R, hr, cert, rel⟩
    rw [realize_binaryApplication, map_empty] at cert
    exact M.checkCertificate_sound s one pairing hone hr cert x hx y hy
      ((M.realize_pairMembershipFormula pairing 1 2 0
        (extend R (extend x (extend y (extend (s.encode one) Fin.elim0)))) hx hy hr).1 rel)
  · intro eq
    obtain ⟨R, hr, cert, rel⟩ := M.exists_groundCheck_certificate s one pairing unions powers separation collection
      hone x hx (eq ▸ hy)
    refine ⟨R, hr, ?_, ?_⟩
    · rw [realize_binaryApplication, map_empty]
      exact cert
    · apply (M.realize_pairMembershipFormula pairing 1 2 0
        (extend R (extend x (extend y (extend (s.encode one) Fin.elim0)))) hx hy hr).2
      rwa [eq]

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.SetFormula

def checkEntryFormula : SetFormula 3 :=
  ex (ex (.conj (.mem 1 3)
    (.conj (binaryApplication uniformCheckFormula (extend 4 Fin.elim0) 1 0)
      (orderedPairFormula 2 0 4))))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem realize_checkEntryFormula (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hone : s.encode one ∈ M.sets) (x z : ZFSet.{u}) (hx : x ∈ M.sets) (hz : z ∈ M.sets)
    (children : ∀ v ∈ x, (Name.check s one v).val ∈ M.sets) :
    Realize M.sets checkEntryFormula (extend z (extend x (extend (s.encode one) Fin.elim0))) ↔
      z ∈ (Name.check s one x).val := by
  rw [checkEntryFormula, realize_ex, Name.mem_check_code]
  constructor
  · rintro ⟨v, hv, body⟩
    obtain ⟨w, hw, member, checked, shape⟩ := (realize_ex M.sets _ _).1 body
    rw [realize_binaryApplication, map_extend, map_empty] at checked
    have eq := (M.realize_uniformCheckFormula s one pairing unions powers separation collection hone v w hv hw).1 checked
    have pair := (M.realize_orderedPairFormula pairing 2 0 4
      (extend w (extend v (extend z (extend x (extend (s.encode one) Fin.elim0))))) hz hw hone).1 shape
    exact ⟨v, member, pair.trans (congrArg (fun q => ZFSet.pair q (s.encode one)) eq)⟩
  · rintro ⟨v, member, eq⟩
    refine ⟨v, M.transitive hx member, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.check s one v).val, children v member, member, ?_, ?_⟩
    · rw [realize_binaryApplication, map_extend, map_empty]
      exact (M.realize_uniformCheckFormula s one pairing unions powers separation collection hone v _
        (M.transitive hx member) (children v member)).2 rfl
    · exact (M.realize_orderedPairFormula pairing 2 0 4
        (extend (Name.check s one v).val (extend v (extend z (extend x (extend (s.encode one) Fin.elim0)))))
        hz (children v member) hone).2 eq

theorem check_mem (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hone : s.encode one ∈ M.sets) :
    ∀ x ∈ M.sets, (Name.check s one x).val ∈ M.sets := by
  intro x
  induction x using ZFSet.inductionOn with
  | h x ih =>
    intro hx
    have children : ∀ v ∈ x, (Name.check s one v).val ∈ M.sets :=
      fun v hv => ih v hv (M.transitive hx hv)
    have witnesses : ∀ v ∈ x, ∃ w ∈ M.sets,
        Realize M.sets uniformCheckFormula (extend v (extend w (extend (s.encode one) Fin.elim0))) := by
      intro v hv
      exact ⟨(Name.check s one v).val, children v hv,
        (M.realize_uniformCheckFormula s one pairing unions powers separation collection hone v _
          (M.transitive hx hv) (children v hv)).2 rfl⟩
    obtain ⟨W, hW, covers⟩ := M.collection_witness collection uniformCheckFormula (extend (s.encode one) Fin.elim0)
      (Fin.cases hone (fun i => Fin.elim0 i)) hx witnesses
    have inW : ∀ v ∈ x, (Name.check s one v).val ∈ W := by
      intro v hv
      obtain ⟨w, hw, rel⟩ := covers v hv
      have eq := (M.realize_uniformCheckFormula s one pairing unions powers separation collection hone v w
        (M.transitive hx hv) (M.transitive hW hw)).1 rel
      exact eq ▸ hw
    obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers hW
      (M.unorderedPair_mem pairing hone hone)
    have bound : (Name.check s one x).val ⊆ B := by
      intro z hz
      obtain ⟨v, hv, rfl⟩ := (Name.mem_check_code s one x z).1 hz
      exact pairBound _ (inW v hv) _ (ZFSet.mem_pair.2 (Or.inl rfl))
    have selected := M.separation_mem separation checkEntryFormula (extend x (extend (s.encode one) Fin.elim0))
      (Fin.cases hx (Fin.cases hone (fun i => Fin.elim0 i))) hB
    have eq : ZFSet.sep (fun z => Realize M.sets checkEntryFormula
        (extend z (extend x (extend (s.encode one) Fin.elim0)))) B = (Name.check s one x).val := by
      apply ZFSet.ext
      intro z
      rw [ZFSet.mem_sep]
      constructor
      · rintro ⟨hz, rel⟩
        exact (M.realize_checkEntryFormula s one pairing unions powers separation collection hone x z hx
          (M.transitive hB hz) children).1 rel
      · intro hz
        exact ⟨bound hz, (M.realize_checkEntryFormula s one pairing unions powers separation collection hone x z hx
          (M.transitive hB (bound hz)) children).2 hz⟩
    exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

def checkNameCodeFormula {n} (output x one : Fin n) : SetFormula n :=
  binaryApplication uniformCheckFormula (extend one Fin.elim0) x output

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem checkNameCode_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {one x : ZFSet.{u}} (hone : one ∈ M.sets) (hx : x ∈ M.sets) :
    checkNameCode one x ∈ M.sets :=
  M.check_mem (checkCodePresentation one) ⟨()⟩ pairing unions powers separation collection hone x hx

theorem realize_checkNameCodeFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {n} (output x one : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (checkNameCodeFormula output x one) env ↔
      env output = checkNameCode (env one) (env x) := by
  rw [checkNameCodeFormula, realize_binaryApplication, map_extend, map_empty]
  exact M.realize_uniformCheckFormula (checkCodePresentation (env one)) ⟨()⟩
    pairing unions powers separation collection (members one) (env x) (env output)
    (members x) (members output)

end TransitiveGround





namespace SetFormula

def indexedGraphValueFormula : SetFormula 4 :=
  ex (ex (.conj (pairMembershipFormula 2 1 4)
    (.conj (binaryApplication uniformCheckFormula (extend 5 Fin.elim0) 2 0)
      (orderedPairNameCodeFormula 3 0 1 5))))

def indexedGraphNameEntryFormula : SetFormula 4 :=
  ex (ex (.conj (.mem 1 3)
    (.conj (binaryApplication indexedGraphValueFormula (extend 4 (extend 5 Fin.elim0)) 1 0)
      (orderedPairFormula 2 0 5))))

end SetFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundDefinableSelections
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

def definable_separation (separation : SeparationSchema M.sets)
    {n : Nat} (φ : SetFormula (n + 1)) :
    GroundDefinableFunction M (fun env : Fin (n + 1) → ZFSet.{u} =>
      ZFSet.sep (fun z => Realize M.sets φ (extend z (fun j => env j.succ))) (env 0)) where
  formula := separationCodeFormula φ
  closed := by
    intro env members
    exact M.separation_mem separation φ (fun j => env j.succ) (fun j => members j.succ) (members 0)
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
    · intro w hw
      exact M.transitive (members 0) (ZFSet.mem_sep.1 hw).1
    · intro w _
      rw [ZFSet.mem_sep]
      change (w ∈ env 0 ∧ Realize M.sets (reindex _ φ) _) ↔ _
      rw [realize_reindex, map_extend]
      rfl

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_OrbitImageFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.SetFormula

def codedNameActionFormula : SetFormula 5 :=
  .conj (domainApplication uniformNameFormula (extend 3 Fin.elim0) 1)
    (.conj (domainApplication uniformNameFormula (extend 3 Fin.elim0) 2) nameActionFormula)

def orbitImageFormula : SetFormula 6 :=
  ex (exConditions 5 (.conj (.mem 1 4) (.conj (orderedPairFormula 2 0 1)
    (atomicApplication codedNameActionFormula (extend 5 (extend 7 Fin.elim0)) 0 1 3))))

end PartitionPilot.Forcing.SetFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundHartogs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

universe u

theorem realize_relationImage (U : Set ZFSet.{u}) {n : Nat} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (A y : ZFSet.{u}) :
    Realize U (relationImageFormula φ) (extend y (extend A params)) ↔
      ∃ x ∈ U, x ∈ A ∧ Realize U φ (extend x (extend y params)) := by
  simp only [relationImageFormula, realize_ex, Realize, realize_binaryApplication]
  rfl

theorem replacement_of_collection_separation (U : Set ZFSet.{u})
    (collection : CollectionSchema U) (separation : SeparationSchema U) : ReplacementSchema U := by
  intro n φ params members A hA total
  have existsWitness : ∀ x ∈ U, x ∈ A → ∃ y ∈ U, Realize U φ (extend x (extend y params)) := by
    intro x hx xA
    obtain ⟨y, hy, rel, _⟩ := total x hx xA
    exact ⟨y, hy, rel⟩
  obtain ⟨B, hB, bounds⟩ := collection φ params members A hA existsWitness
  obtain ⟨C, hC, selected⟩ := separation (relationImageFormula φ) (extend A params) (Fin.cases hA members) B hB
  refine ⟨C, hC, ?_⟩
  intro y hy
  rw [selected y hy, realize_relationImage]
  constructor
  · exact And.right
  · intro image
    obtain ⟨x, hx, xA, rel⟩ := image
    obtain ⟨z, hz, zB, relz⟩ := bounds x hx xA
    obtain ⟨w, _, _, unique⟩ := total x hx xA
    have eq : y = z := (unique y hy rel).trans (unique z hz relz).symm
    exact ⟨eq.symm ▸ zB, x, hx, xA, rel⟩

end PartitionPilot.Forcing.SetFormula

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMixtureNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.SetFormula

def subgroupOrbitFormula : SetFormula 6 :=
  exConditions 4 (.conj (.mem 0 3)
    (atomicApplication codedNameActionFormula (extend 4 (extend 6 Fin.elim0)) 0 2 1))

end PartitionPilot.Forcing.SetFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RefinementAssignmentLabelNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order in
theorem realize_refinementClassEntryFormula {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (R w : Name s) (hR : R.val ∈ M.sets) (hw : w.val ∈ M.sets)
    (x : ZFSet.{u}) (hx : x ∈ M.sets) :
    Realize M.sets refinementClassEntryFormula
      (extend x (extend T (extend R.val (extend w.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))))) ↔
      x ∈ (Name.refinementClass T valid R w).val := by
  let env := extend x (extend T (extend R.val (extend w.val
    (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))))
  have hone := M.transitive carrier (s.encode_mem ⊤)
  have members : ∀ j, env j ∈ M.sets :=
    Fin.cases hx (Fin.cases hT (Fin.cases hR (Fin.cases hw
      (Fin.cases carrier (Fin.cases order (Fin.cases hone (fun j => Fin.elim0 j)))))))
  change Realize M.sets refinementClassEntryFormula env ↔ _
  rw [refinementClassEntryFormula, realize_ex]
  constructor
  · rintro ⟨z, hz, body⟩
    obtain ⟨q, hq, body⟩ := (realize_ex M.sets _ _).1 body
    obtain ⟨v, hv, member, hqP, entry, pairName, forced⟩ := (realize_ex M.sets _ _).1 body
    change z ∈ T at member
    change q ∈ s.carrier at hqP
    obtain ⟨p, rfl⟩ := (s.mem_carrier q).1 hqP
    let σ : Name s := ⟨z, valid z member⟩
    have hpGround := M.transitive carrier (s.encode_mem p)
    have all : ∀ j, (extend v (extend (s.encode p) (extend z env))) j ∈ M.sets :=
      Fin.cases hv (Fin.cases hpGround (Fin.cases hz members))
    have entryEq := (M.realize_orderedPairFormula pairing 3 2 1 _ hx hz hpGround).1 entry
    change x = ZFSet.pair z (s.encode p) at entryEq
    have pairEq := (M.realize_orderedPairNameCodeFormula pairing 0 2 6 9 _ all).1 pairName
    have named : v = (Name.orderedPair ⊤ σ w).val :=
      pairEq.trans (Name.orderedPair_code ⊤ σ w).symm
    have hpair : (Name.orderedPair ⊤ σ w).val ∈ M.sets := named ▸ hv
    let names : Assignment (M.nameDomain s) 2 :=
      extend ⟨Name.orderedPair ⊤ σ w, hpair⟩ (extend ⟨R, hR⟩ Fin.elim0)
    have atom := (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
      carrier order 0 1 (.mem 0 1) ![7, 8] 1 ![0, 5] _ rfl rfl p names rfl
      (Fin.cases named (Fin.cases rfl (fun j => Fin.elim0 j)))).1 forced
    rw [entryEq]
    exact (Name.entry_refinementClass T valid R w σ p).2 ⟨member, atom⟩
  · intro member
    obtain ⟨σ, p, rfl⟩ := Name.entries_cover (Name.refinementClass T valid R w) member
    obtain ⟨hσT, forced⟩ := (Name.entry_refinementClass T valid R w σ p).1 member
    have hσ := M.transitive hT hσT
    have hp := M.transitive carrier (s.encode_mem p)
    have hpair : (Name.orderedPair ⊤ σ w).val ∈ M.sets := by
      rw [Name.orderedPair_code]
      exact M.orderedPairNameCode_mem pairing hone hσ hw
    refine ⟨σ.val, hσ, ?_⟩
    rw [realize_ex]
    refine ⟨s.encode p, hp, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.orderedPair ⊤ σ w).val, hpair, hσT, s.encode_mem p, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 3 2 1 _ hx hσ hp).2 rfl
    · exact (M.realize_orderedPairNameCodeFormula pairing 0 2 6 9 _
        (Fin.cases hpair (Fin.cases hp (Fin.cases hσ members)))).2
        (Name.orderedPair_code ⊤ σ w)
    · let names : Assignment (M.nameDomain s) 2 :=
        extend ⟨Name.orderedPair ⊤ σ w, hpair⟩ (extend ⟨R, hR⟩ Fin.elim0)
      exact (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
        carrier order 0 1 (.mem 0 1) ![7, 8] 1 ![0, 5] _ rfl rfl p names rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))).2 forced

include pairing unions powers separation collection carrier order in
theorem refinementClass_eq_selection {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (R w : Name s) (hR : R.val ∈ M.sets) (hw : w.val ∈ M.sets) :
    (Name.refinementClass T valid R w).val =
      ZFSet.sep (fun x => Realize M.sets refinementClassEntryFormula
        (extend x (extend T (extend R.val (extend w.val
          (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))))))
        (ZFSet.prod T s.carrier) := by
  have bound := M.prod_mem pairing unions powers separation hT carrier
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sep]
  constructor
  · intro member
    have hx := Name.refinementClass_subset T valid R w member
    exact ⟨hx, (M.realize_refinementClassEntryFormula s pairing unions powers separation collection
      carrier order hT valid R w hR hw x (M.transitive bound hx)).2 member⟩
  · rintro ⟨hx, formula⟩
    exact (M.realize_refinementClassEntryFormula s pairing unions powers separation collection
      carrier order hT valid R w hR hw x (M.transitive bound hx)).1 formula

include pairing unions powers separation collection carrier order in
theorem refinementClass_mem {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (R w : Name s) (hR : R.val ∈ M.sets) (hw : w.val ∈ M.sets) :
    (Name.refinementClass T valid R w).val ∈ M.sets := by
  rw [M.refinementClass_eq_selection s pairing unions powers separation collection carrier order
    hT valid R w hR hw]
  exact M.separation_mem separation refinementClassEntryFormula _
    (Fin.cases hT (Fin.cases hR (Fin.cases hw (Fin.cases carrier (Fin.cases order
      (Fin.cases (M.transitive carrier (s.encode_mem ⊤)) (fun j => Fin.elim0 j)))))))
    (M.prod_mem pairing unions powers separation hT carrier)

end TransitiveGround
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRefinementPairClassGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)

theorem refinementClassGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {T W : ZFSet.{u}} (hT : T ∈ M.sets) (hW : W ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (validW : ∀ z ∈ W, IsName s z)
    (R : Name s) (hR : R.val ∈ M.sets) :
    Name.refinementClassGraph T valid R W validW ∈ M.sets := by
  let B := ZFSet.prod T s.carrier
  have hB := M.prod_mem pairing unions powers separation hT carrier
  let slots : Fin 7 → Fin 7 := ![1, 2, 3, 0, 4, 5, 6]
  let defined := (M.definable_separation separation refinementClassEntryFormula).reindex slots
  let params := extend B (extend T (extend R.val
    (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))
  have whole := defined.graph_mem pairing separation collection params
    (Fin.cases hB (Fin.cases hT (Fin.cases hR (Fin.cases carrier
      (Fin.cases order (Fin.cases (M.transitive carrier (s.encode_mem ⊤))
        (fun j => Fin.elim0 j))))))) hW
  have value (w : Name s) (hw : w.val ∈ W) :
      ZFSet.sep (fun x => Realize M.sets refinementClassEntryFormula
        (extend x (fun j => (extend w.val params) (slots j.succ))))
        ((extend w.val params) (slots 0)) = (Name.refinementClass T valid R w).val := by
    have args : (fun j : Fin 6 => (extend w.val params) (slots j.succ)) =
        extend T (extend R.val (extend w.val
          (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))) := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) j
    rw [args]
    exact (M.refinementClass_eq_selection s pairing unions powers separation collection
      carrier order hT valid R w hR (M.transitive hW hw)).symm
  have equal : defined.graph params W = Name.refinementClassGraph T valid R W validW := by
    apply ZFSet.ext
    intro x
    rw [defined.mem_graph, Name.mem_refinementClassGraph]
    constructor
    · rintro ⟨z, hz, equal⟩
      let w : Name s := ⟨z, validW z hz⟩
      exact ⟨w, hz, equal.trans (congrArg (ZFSet.pair z) (value w hz))⟩
    · rintro ⟨w, hw, equal⟩
      exact ⟨w.val, hw, equal.trans (congrArg (ZFSet.pair w.val) (value w hw).symm)⟩
  exact equal ▸ whole

end TransitiveGround




namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem orderedPairNameGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {one W f g : ZFSet.{u}} (hone : one ∈ M.sets) (hW : W ∈ M.sets)
    (hf : f ∈ M.sets) (hg : g ∈ M.sets) : orderedPairNameGraph one W f g ∈ M.sets := by
  have bound := M.prod_mem pairing unions powers separation hW
    (M.orderedPairNameFamily_mem pairing unions powers separation hone
      (M.functionGraphRange_mem unions separation hW hf) (M.functionGraphRange_mem unions separation hW hg))
  let params := extend W (extend f (extend g (extend one Fin.elim0)))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hW (Fin.cases hf (Fin.cases hg (Fin.cases hone (fun j => Fin.elim0 j))))
  have selected := M.separation_mem separation orderedPairNameGraphEntryFormula params members bound
  have equal : ZFSet.sep (fun x => Realize M.sets orderedPairNameGraphEntryFormula (extend x params))
      (ZFSet.prod W (orderedPairNameFamily one (functionGraphRange W f) (functionGraphRange W g))) =
      orderedPairNameGraph one W f g := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hx, formula⟩
      exact (M.realize_orderedPairNameGraphEntryFormula pairing _
        (Fin.cases (M.transitive bound hx) members)).1 formula
    · intro member
      have hx := (ZFSet.mem_sep.1 member).1
      exact ⟨hx, (M.realize_orderedPairNameGraphEntryFormula pairing _
        (Fin.cases (M.transitive bound hx) members)).2 member⟩
  exact equal ▸ selected

end TransitiveGround

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]

theorem refinementPairClassGraph_mem (s : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {T W : ZFSet.{u}} (hT : T ∈ M.sets) (hW : W ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (validW : ∀ z ∈ W, IsName s z)
    (Rf Rc : Name s) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets) :
    Name.refinementPairClassGraph T valid Rf Rc W validW ∈ M.sets :=
  M.orderedPairNameGraph_mem pairing unions powers separation
    (M.transitive carrier (s.encode_mem ⊤)) hW
    (M.refinementClassGraph_mem s pairing unions powers separation collection carrier order hT hW valid validW Rf hRf)
    (M.refinementClassGraph_mem s pairing unions powers separation collection carrier order hT hW valid validW Rc hRc)

end TransitiveGround


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BatchGraphSetFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_exactReindexedBoundedSetFormula {n k} (output : Fin n) (entry : BoundedFormula k)
    (slots : Fin k → Fin (n + 1)) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    {target : ZFSet.{u}} (ground : target ∈ M.sets)
    (meaning : ∀ z, BoundedFormula.Truth entry (fun i => extend z env (slots i)) ↔ z ∈ target) :
    Realize M.sets (exactSetFormula output (reindex slots entry.toFormula)) env ↔ env output = target := by
  apply M.realize_exactSetFormula output _ env (members output) (fun _ hz => M.transitive ground hz)
  intro z hz
  rw [realize_reindex]
  have extended : ∀ i : Fin (n + 1), extend z env i ∈ M.sets := Fin.cases hz members
  exact (BoundedFormula.realize_toFormula M entry _
    (fun i => extended (slots i))).trans (meaning z)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_batchShadowSetFormula {n} (output i p qs ms anchors es qb mb ab eb : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets)
    (qBound : env qb = ZFSet.sUnion (ZFSet.sUnion (env qs)))
    (mBound : env mb = ZFSet.sUnion (ZFSet.sUnion (env ms)))
    (aBound : env ab = ZFSet.sUnion (ZFSet.sUnion (env anchors)))
    (eBound : env eb = ZFSet.sUnion (ZFSet.sUnion (env es))) :
    Realize M.sets (batchShadowSetFormula output i p qs ms anchors es qb mb ab eb) env ↔
      env output = batchAttachmentShadowGraph (env i) (env p) (env qs) (env ms) (env anchors) (env es) := by
  apply M.realize_exactReindexedBoundedSetFormula output _ _ env members
    (M.batchAttachmentShadowGraph_mem pairing unions powers separation
      (members i) (members p) (members qs) (members ms) (members anchors) (members es))
  intro z
  rw [BoundedFormula.truth_batchShadowGraphFormula]
  change (∃ j ∈ env i, ∃ Q ∈ env qb, ∃ μ ∈ env mb, ∃ a ∈ env ab, ∃ ell ∈ env eb,
    ∃ q ∈ Q, ∃ v ∈ env p, z = ZFSet.pair (ZFSet.pair j q) v ∧
      ZFSet.pair j Q ∈ env qs ∧ ZFSet.pair j μ ∈ env ms ∧
      ZFSet.pair j a ∈ env anchors ∧ ZFSet.pair j ell ∈ env es ∧
      ∃ c ∈ Q, ZFSet.pair (ZFSet.pair q a) c ∈ μ ∧ ZFSet.pair c v ∈ ell) ↔ _
  rw [qBound, mBound, aBound, eBound, batchAttachmentShadowGraph, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨j, hj, Q, _, _, _, _, _, _, _, q, hq, v, hv, equal, entry, _⟩ := witness
    rw [equal]
    exact ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain (env i) (env qs) j q).2 ⟨hj, Q, entry, hq⟩, hv⟩
  · exact And.right

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ActiveNameImageSymmetry
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order in
theorem realize_activeNameImageEntryFormula {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U : Name s) (hU : U.val ∈ M.sets)
    (image : Name s → Name s) (graph : ZFSet.{u}) (hgraph : graph ∈ M.sets)
    (entries : ∀ (w : Name s) z, ZFSet.pair w.val z ∈ graph ↔
      w.val ∈ T ∧ z = (image w).val)
    (x : ZFSet.{u}) (hx : x ∈ M.sets) :
    Realize M.sets activeNameImageEntryFormula
      (extend x (extend T (extend U.val (extend graph
        (extend s.carrier (extend s.conditionOrder Fin.elim0)))))) ↔
      x ∈ (Name.activeImage T valid U image).val := by
  let env := extend x (extend T (extend U.val (extend graph
    (extend s.carrier (extend s.conditionOrder Fin.elim0)))))
  change Realize M.sets activeNameImageEntryFormula env ↔ _
  rw [activeNameImageEntryFormula, realize_ex]
  constructor
  · rintro ⟨w, hw, body⟩
    obtain ⟨z, hz, body⟩ := (realize_ex M.sets _ _).1 body
    obtain ⟨q, hq, member, condition, code, imageEntry, forced⟩ :=
      (realize_ex M.sets _ _).1 body
    change w ∈ T at member
    change q ∈ s.carrier at condition
    obtain ⟨p, rfl⟩ := (s.mem_carrier q).1 condition
    let term : Name s := ⟨w, valid w member⟩
    have equal := (M.realize_orderedPairFormula pairing 3 1 0 _ hx hz hq).1 code
    have graphEntry := (M.realize_pairMembershipFormula pairing 2 1 6 _ hw hz hgraph).1 imageEntry
    have imageEqual := ((entries term z).1 graphEntry).2
    let names : Assignment (M.nameDomain s) 2 := extend ⟨term, hw⟩ (extend ⟨U, hU⟩ Fin.elim0)
    have atom := (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
      carrier order 0 1 (.mem 0 1) ![7, 8] 0 ![2, 5] _ rfl rfl p names rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))).1 forced
    change x = ZFSet.pair z (s.encode p) at equal
    rw [equal, imageEqual]
    exact (Name.entry_activeImage T valid U image (image term) p).2
      ⟨term, member, atom, rfl⟩
  · intro member
    obtain ⟨z, p, rfl⟩ := Name.entries_cover (Name.activeImage T valid U image) member
    obtain ⟨w, hwT, forced, rfl⟩ := (Name.entry_activeImage T valid U image z p).1 member
    have hw := M.transitive hT hwT
    have hp := M.transitive carrier (s.encode_mem p)
    have graphEntry := (entries w (image w).val).2 ⟨hwT, rfl⟩
    have hz := M.transitive (M.union_mem unions (M.union_mem unions hgraph))
      (pair_second_mem_doubleUnion graphEntry)
    refine ⟨w.val, hw, ?_⟩
    rw [realize_ex]
    refine ⟨(image w).val, hz, ?_⟩
    rw [realize_ex]
    refine ⟨s.encode p, hp, hwT, s.encode_mem p, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 3 1 0 _ hx hz hp).2 rfl
    · exact (M.realize_pairMembershipFormula pairing 2 1 6 _ hw hz hgraph).2 graphEntry
    · let names : Assignment (M.nameDomain s) 2 := extend ⟨w, hw⟩ (extend ⟨U, hU⟩ Fin.elim0)
      exact (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
        carrier order 0 1 (.mem 0 1) ![7, 8] 0 ![2, 5] _ rfl rfl p names rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))).2 forced

include pairing unions powers separation collection carrier order in
theorem activeImage_eq_selection {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U : Name s) (hU : U.val ∈ M.sets)
    (image : Name s → Name s) (graph : ZFSet.{u}) (hgraph : graph ∈ M.sets)
    (entries : ∀ (w : Name s) z, ZFSet.pair w.val z ∈ graph ↔
      w.val ∈ T ∧ z = (image w).val) :
    (Name.activeImage T valid U image).val =
      ZFSet.sep (fun x => Realize M.sets activeNameImageEntryFormula
        (extend x (extend T (extend U.val (extend graph
          (extend s.carrier (extend s.conditionOrder Fin.elim0)))))))
        (ZFSet.prod (functionGraphRange T graph) s.carrier) := by
  have rangeGround := M.functionGraphRange_mem unions separation hT hgraph
  have boundGround := M.prod_mem pairing unions powers separation rangeGround carrier
  have bound := Name.activeImage_subset T valid U image (functionGraphRange T graph)
    (fun w hw => (mem_functionGraphRange T graph _).2
      ⟨w.val, hw, (entries w (image w).val).2 ⟨hw, rfl⟩⟩)
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sep]
  constructor
  · intro member
    exact ⟨bound member,
      (M.realize_activeNameImageEntryFormula s pairing unions powers separation collection
        carrier order hT valid U hU image graph hgraph entries x
        (M.transitive boundGround (bound member))).2 member⟩
  · rintro ⟨hx, formula⟩
    exact (M.realize_activeNameImageEntryFormula s pairing unions powers separation collection
      carrier order hT valid U hU image graph hgraph entries x
      (M.transitive boundGround hx)).1 formula

include pairing unions powers separation collection carrier order in
theorem activeImage_mem {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U : Name s) (hU : U.val ∈ M.sets)
    (image : Name s → Name s) (graph : ZFSet.{u}) (hgraph : graph ∈ M.sets)
    (entries : ∀ (w : Name s) z, ZFSet.pair w.val z ∈ graph ↔
      w.val ∈ T ∧ z = (image w).val) :
    (Name.activeImage T valid U image).val ∈ M.sets := by
  rw [M.activeImage_eq_selection s pairing unions powers separation collection carrier order
    hT valid U hU image graph hgraph entries]
  exact M.separation_mem separation activeNameImageEntryFormula _
    (Fin.cases hT (Fin.cases hU (Fin.cases hgraph (Fin.cases carrier
      (Fin.cases order (fun j => Fin.elim0 j))))))
    (M.prod_mem pairing unions powers separation
      (M.functionGraphRange_mem unions separation hT hgraph) carrier)

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundIndexedClassInclusions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem indexedClassInclusion_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U L E i : ZFSet.{u}} (hU : U ∈ M.sets) (hL : L ∈ M.sets)
    (hE : E ∈ M.sets) (hi : i ∈ M.sets) : indexedClassInclusion U L E i ∈ M.sets :=
  M.indexedRelationSection_mem pairing unions powers separation hU
    (M.equivalenceClasses_mem powers separation hL hE)
    (M.equivalenceClassifier_mem pairing unions powers separation hL hE) hi

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {T U L E : ZFSet.{u}} (hT : T ∈ M.sets) (hU : U ∈ M.sets)
variable (hL : L ∈ M.sets) (hE : E ∈ M.sets)
include pairing unions powers separation hT hU hL hE

theorem indexedClassInclusions_function :
    ZFSet.IsFunc T (M.groundRelations U (equivalenceClasses L E))
      (M.indexedClassInclusions T U L E) :=
  M.indexedRelationSections_function pairing unions powers separation hT hU
    (M.equivalenceClasses_mem powers separation hL hE)
    (M.equivalenceClassifier_mem pairing unions powers separation hL hE)

theorem indexedClassInclusions_entries (i f : ZFSet.{u}) :
    ZFSet.pair i f ∈ M.indexedClassInclusions T U L E ↔
      i ∈ T ∧ f = indexedClassInclusion U L E i :=
  (M.indexedRelationSections_spec pairing unions powers separation hT hU
    (M.equivalenceClasses_mem powers separation hL hE)
    (M.equivalenceClassifier_mem pairing unions powers separation hL hE)).2.2 i f

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundRefinementQuotientNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order in
theorem refinementQuotient_mem {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U R : Name s)
    (hU : U.val ∈ M.sets) (hR : R.val ∈ M.sets) :
    (Name.refinementQuotient T valid U R).val ∈ M.sets :=
  M.activeImage_mem s pairing unions powers separation collection carrier order hT valid U hU
    (Name.refinementClass T valid R) (Name.refinementClassGraph T valid R T valid)
    (M.refinementClassGraph_mem s pairing unions powers separation collection carrier order
      hT hT valid valid R hR)
    (Name.pair_mem_refinementClassGraph T valid R T valid)

include pairing unions powers separation collection carrier order in
theorem refinementNaturalMap_mem {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s)
    (hU : U.val ∈ M.sets) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets) :
    (Name.refinementNaturalMap T valid U Rf Rc).val ∈ M.sets :=
  M.activeImage_mem s pairing unions powers separation collection carrier order hT valid U hU
    (fun w => Name.orderedPair ⊤ (Name.refinementClass T valid Rf w) (Name.refinementClass T valid Rc w))
    (Name.refinementPairClassGraph T valid Rf Rc T valid)
    (M.refinementPairClassGraph_mem s pairing unions powers separation collection carrier order
      hT hT valid valid Rf Rc hRf hRc)
    (Name.pair_mem_refinementPairClassGraph T valid Rf Rc T valid)

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundAssignmentClassGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

theorem realize_refinementClassCodeFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (R w : Name s) (hR : R.val ∈ M.sets) (hw : w.val ∈ M.sets)
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets refinementClassCodeFormula
      (extend z (extend T (extend R.val (extend w.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))))) ↔
      z = (Name.refinementClass T valid R w).val := by
  have ground := M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid R w hR hw
  apply M.realize_exactSetFormula 0 _ _ hz (fun _ h => M.transitive ground h)
  intro x hx
  rw [realize_reindex, map_extend]
  exact M.realize_refinementClassEntryFormula s pairing unions powers separation collection
    carrier order hT valid R w hR hw x hx

end TransitiveGround

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation collection carrier order

theorem realize_refinementMapEntryFormula {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s)
    (hU : U.val ∈ M.sets) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets)
    (x : ZFSet.{u}) (hx : x ∈ M.sets) :
    Realize M.sets refinementMapEntryFormula
      (extend x (extend T (extend U.val (extend Rf.val (extend Rc.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))))) ↔
      x ∈ (Name.refinementNaturalMap T valid U Rf Rc).val := by
  let env := extend x (extend T (extend U.val (extend Rf.val (extend Rc.val
    (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))))
  have members : ∀ j, env j ∈ M.sets :=
    Fin.cases hx (Fin.cases hT (Fin.cases hU (Fin.cases hRf (Fin.cases hRc
      (Fin.cases carrier (Fin.cases order (Fin.cases (M.transitive carrier (s.encode_mem ⊤))
        (fun j => Fin.elim0 j))))))))
  have fineArgs (w f c v q : ZFSet.{u}) :
      (fun j : Fin 7 => (extend q (extend v (extend c (extend f (extend w env)))))
        (![3, 6, 8, 4, 10, 11, 12] j)) =
        extend f (extend T (extend Rf.val (extend w
          (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
  have coarseArgs (w f c v q : ZFSet.{u}) :
      (fun j : Fin 7 => (extend q (extend v (extend c (extend f (extend w env)))))
        (![2, 6, 9, 4, 10, 11, 12] j)) =
        extend c (extend T (extend Rc.val (extend w
          (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
  change Realize M.sets refinementMapEntryFormula env ↔ _
  rw [refinementMapEntryFormula, realize_ex]
  constructor
  · rintro ⟨w, hw, body⟩
    obtain ⟨f, hf, body⟩ := (realize_ex M.sets _ _).1 body
    obtain ⟨c, hc, body⟩ := (realize_ex M.sets _ _).1 body
    obtain ⟨v, hv, body⟩ := (realize_ex M.sets _ _).1 body
    obtain ⟨q, hq, member, condition, pair, fine, coarse, named, forced⟩ := (realize_ex M.sets _ _).1 body
    change w ∈ T at member
    change q ∈ s.carrier at condition
    obtain ⟨p, rfl⟩ := (s.mem_carrier q).1 condition
    let term : Name s := ⟨w, valid w member⟩
    rw [realize_reindex, fineArgs] at fine
    rw [realize_reindex, coarseArgs] at coarse
    have feq := (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
      carrier order hT valid Rf term hRf hw f hf).1 fine
    have ceq := (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
      carrier order hT valid Rc term hRc hw c hc).1 coarse
    have all : ∀ j, (extend (s.encode p) (extend v (extend c (extend f (extend w env))))) j ∈ M.sets := Fin.cases hq (Fin.cases hv (Fin.cases hc (Fin.cases hf (Fin.cases hw members))))
    have veq := (M.realize_orderedPairNameCodeFormula pairing 1 3 2 12 _ all).1 named
    have equal := (M.realize_orderedPairFormula pairing 5 1 0 _ hx hv hq).1 pair
    let names : Assignment (M.nameDomain s) 2 := extend ⟨term, hw⟩ (extend ⟨U, hU⟩ Fin.elim0)
    have atom := (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
      carrier order 0 1 (.mem 0 1) ![10, 11] 0 ![4, 7] _ rfl rfl p names rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))).1 forced
    change x = ZFSet.pair v (s.encode p) at equal
    change v = orderedPairNameCode (s.encode ⊤) f c at veq
    rw [feq, ceq, ← Name.orderedPair_code] at veq
    rw [equal, veq]
    exact (Name.entry_refinementNaturalMap T valid U Rf Rc _ p).2 ⟨term, member, atom, rfl⟩
  · intro member
    obtain ⟨v, p, rfl⟩ := Name.entries_cover (Name.refinementNaturalMap T valid U Rf Rc) member
    obtain ⟨w, hwT, forced, rfl⟩ := (Name.entry_refinementNaturalMap T valid U Rf Rc v p).1 member
    have hw := M.transitive hT hwT
    have hp := M.transitive carrier (s.encode_mem p)
    have hf := M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid Rf w hRf hw
    have hc := M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid Rc w hRc hw
    have hv : (Name.orderedPair ⊤ (Name.refinementClass T valid Rf w) (Name.refinementClass T valid Rc w)).val ∈ M.sets := by
      rw [Name.orderedPair_code]
      exact M.orderedPairNameCode_mem pairing (M.transitive carrier (s.encode_mem ⊤)) hf hc
    refine ⟨w.val, hw, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.refinementClass T valid Rf w).val, hf, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.refinementClass T valid Rc w).val, hc, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.orderedPair ⊤ (Name.refinementClass T valid Rf w) (Name.refinementClass T valid Rc w)).val, hv, ?_⟩
    rw [realize_ex]
    refine ⟨s.encode p, hp, hwT, s.encode_mem p, ?_, ?_, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 5 1 0 _ hx hv hp).2 rfl
    · rw [realize_reindex, fineArgs]
      exact (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
        carrier order hT valid Rf w hRf hw _ hf).2 rfl
    · rw [realize_reindex, coarseArgs]
      exact (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
        carrier order hT valid Rc w hRc hw _ hc).2 rfl
    · exact (M.realize_orderedPairNameCodeFormula pairing 1 3 2 12 _
        (Fin.cases hp (Fin.cases hv (Fin.cases hc (Fin.cases hf (Fin.cases hw members)))))).2
        (Name.orderedPair_code ⊤ _ _)
    · let names : Assignment (M.nameDomain s) 2 := extend ⟨w, hw⟩ (extend ⟨U, hU⟩ Fin.elim0)
      exact (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
        carrier order 0 1 (.mem 0 1) ![10, 11] 0 ![4, 7] _ rfl rfl p names rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))).2 forced

theorem realize_refinementMapCodeFormula {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s)
    (hU : U.val ∈ M.sets) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets)
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets refinementMapCodeFormula
      (extend z (extend T (extend U.val (extend Rf.val (extend Rc.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))))) ↔
      z = (Name.refinementNaturalMap T valid U Rf Rc).val := by
  have ground := M.refinementNaturalMap_mem s pairing unions powers separation collection
    carrier order hT valid U Rf Rc hU hRf hRc
  apply M.realize_exactSetFormula 0 _ _ hz (fun _ h => M.transitive ground h)
  intro x hx
  rw [realize_reindex, map_extend]
  exact M.realize_refinementMapEntryFormula s pairing unions powers separation collection
    carrier order hT valid U Rf Rc hU hRf hRc x hx

end TransitiveGround

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation collection carrier order

theorem realize_refinementQuotientEntryFormula {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U R : Name s) (hU : U.val ∈ M.sets) (hR : R.val ∈ M.sets)
    (x : ZFSet.{u}) (hx : x ∈ M.sets) :
    Realize M.sets refinementQuotientEntryFormula
      (extend x (extend T (extend U.val (extend R.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))))) ↔
      x ∈ (Name.refinementQuotient T valid U R).val := by
  let env := extend x (extend T (extend U.val (extend R.val
    (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))))
  have classArgs (w c q : ZFSet.{u}) :
      (fun j : Fin 7 => (extend q (extend c (extend w env))) (![1, 4, 6, 2, 7, 8, 9] j)) =
        extend c (extend T (extend R.val (extend w
          (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
  change Realize M.sets refinementQuotientEntryFormula env ↔ _
  rw [refinementQuotientEntryFormula, realize_ex]
  constructor
  · rintro ⟨w, hw, body⟩
    obtain ⟨c, hc, body⟩ := (realize_ex M.sets _ _).1 body
    obtain ⟨q, hq, member, condition, pair, recognized, forced⟩ := (realize_ex M.sets _ _).1 body
    change w ∈ T at member
    change q ∈ s.carrier at condition
    obtain ⟨p, rfl⟩ := (s.mem_carrier q).1 condition
    let term : Name s := ⟨w, valid w member⟩
    rw [realize_reindex, classArgs] at recognized
    have code := (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
      carrier order hT valid R term hR hw c hc).1 recognized
    have equal := (M.realize_orderedPairFormula pairing 3 1 0 _ hx hc hq).1 pair
    let names : Assignment (M.nameDomain s) 2 := extend ⟨term, hw⟩ (extend ⟨U, hU⟩ Fin.elim0)
    have atom := (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
      carrier order 0 1 (.mem 0 1) ![7, 8] 0 ![2, 5] _ rfl rfl p names rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))).1 forced
    change x = ZFSet.pair c (s.encode p) at equal
    rw [equal, code]
    exact (Name.entry_refinementQuotient T valid U R _ p).2 ⟨term, member, atom, rfl⟩
  · intro member
    obtain ⟨c, p, rfl⟩ := Name.entries_cover (Name.refinementQuotient T valid U R) member
    obtain ⟨w, hwT, forced, rfl⟩ := (Name.entry_refinementQuotient T valid U R c p).1 member
    have hw := M.transitive hT hwT
    have hp := M.transitive carrier (s.encode_mem p)
    have hc := M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid R w hR hw
    refine ⟨w.val, hw, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.refinementClass T valid R w).val, hc, ?_⟩
    rw [realize_ex]
    refine ⟨s.encode p, hp, hwT, s.encode_mem p, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 3 1 0 _ hx hc hp).2 rfl
    · rw [realize_reindex, classArgs]
      exact (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
        carrier order hT valid R w hR hw _ hc).2 rfl
    · let names : Assignment (M.nameDomain s) 2 := extend ⟨w, hw⟩ (extend ⟨U, hU⟩ Fin.elim0)
      exact (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
        carrier order 0 1 (.mem 0 1) ![7, 8] 0 ![2, 5] _ rfl rfl p names rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))).2 forced

theorem realize_refinementQuotientCodeFormula {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U R : Name s) (hU : U.val ∈ M.sets) (hR : R.val ∈ M.sets)
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets refinementQuotientCodeFormula
      (extend z (extend T (extend U.val (extend R.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0))))))) ↔
      z = (Name.refinementQuotient T valid U R).val := by
  have ground := M.refinementQuotient_mem s pairing unions powers separation collection carrier order hT valid U R hU hR
  apply M.realize_exactSetFormula 0 _ _ hz (fun _ h => M.transitive ground h)
  intro x hx
  rw [realize_reindex, map_extend]
  exact M.realize_refinementQuotientEntryFormula s pairing unions powers separation collection
    carrier order hT valid U R hU hR x hx

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundBinaryRowNameCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def binaryRowEntryFormula {n} (z c q i one bit : Fin n) : SetFormula n :=
  ex (ex (ex (.conj (.mem 2 c.succ.succ.succ)
    (.conj (.mem 1 q.succ.succ.succ)
      (.conj (binaryApplication uniformCheckFormula (extend one.succ.succ.succ Fin.elim0) 2 0)
        (.conj (BoundedFormula.tripleMembershipFormula i.succ.succ.succ 2 bit.succ.succ.succ 1).toFormula
          (orderedPairFormula z.succ.succ.succ 0 1)))))))

def binaryRowCodeFormula : SetFormula 6 :=
  let entry := reindex (extend 0 (extend 3 (extend 4 (extend 1
    (extend 5 (extend 6 Fin.elim0)))))) (binaryRowEntryFormula 0 1 2 3 4 5)
  .all (.conj (imp (.mem 0 2) entry) (imp entry (.mem 0 2)))

def binaryRowSetEntryFormula : SetFormula 6 :=
  ex (ex (.conj (.mem 1 3)
    (.conj (binaryApplication binaryRowCodeFormula
      (extend 4 (extend 5 (extend 6 (extend 7 Fin.elim0)))) 1 0)
      (orderedPairFormula 2 0 6))))

end PartitionPilot.Forcing.SetFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFlatSuccessorFullActionGraph
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem conditionMapFamily_mem_of_actionGraph
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (graph : a.actionGraph s t ∈ M.sets) : a.conditionMapFamily s t ∈ M.sets := by
  have hg (g : G) := M.transitive group (t.encode_mem g)
  have sections (g : G) := M.actionGraph_section_mem a s t pairing unions powers separation carrier graph g (hg g)
  let params := extend (a.actionGraph s t) (extend s.carrier Fin.elim0)
  apply M.definable_image_mem separation collection actionMapPairFormula params
    (Fin.cases graph (Fin.cases carrier (fun j => Fin.elim0 j))) group
  · intro z hz
    obtain ⟨g, eq⟩ := ZFSet.mem_range.1 hz
    exact eq ▸ M.orderedPair_mem pairing (hg g) (sections g)
  · intro z hz
    change z ∈ ZFSet.range (fun g : G => ZFSet.pair (t.encode g) (s.graph s (a.iso g))) ↔ _
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨g, eq⟩
      exact ⟨t.encode g, t.encode_mem g,
        (M.realize_actionMapPairFormula a s t g z (hg g) hz graph carrier (sections g)).2 eq.symm⟩
    · rintro ⟨x, hx, rel⟩
      obtain ⟨g, rfl⟩ := (t.mem_carrier x).1 hx
      exact ⟨g, ((M.realize_actionMapPairFormula a s t g z (hg g) hz graph carrier (sections g)).1 rel).symm⟩
  · intro x hx y hy z hz rely relz
    obtain ⟨g, rfl⟩ := (t.mem_carrier x).1 hx
    exact ((M.realize_actionMapPairFormula a s t g y (hg g) hy graph carrier (sections g)).1 rely).trans
      ((M.realize_actionMapPairFormula a s t g z (hg g) hz graph carrier (sections g)).1 relz).symm

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundOrdinalPartitionInjectionAssembly
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def definableRelationEntryFormula {n} (φ : SetFormula (n + 2)) : SetFormula (n + 3) :=
  ex (.conj (.mem 0 2) (ex (.conj (.mem 0 4)
    (.conj (BoundedFormula.orderedPairFormula 2 1 0).toFormula
      (binaryApplication φ (fun i => i.succ.succ.succ.succ.succ) 1 0)))))
end SetFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNiceNameGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem niceNameCandidates_eq_selection (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}} (valid : ∀ z ∈ T, IsName s z)
    (i : I) (hi : b.encode i ∈ M.sets) :
    M.niceNameCandidates a s T (K i) =
      ZFSet.sep (fun z => Realize M.sets nameSupportFormula
        (extend z (extend (b.encode i) (extend s.carrier (extend t.carrier
          (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0)))))))
        (M.groundRelations T s.carrier) := by
  apply ZFSet.ext
  intro z
  rw [niceNameCandidates, ZFSet.mem_sep, ZFSet.mem_sep]
  apply and_congr_right
  intro hz
  have data := (M.mem_groundRelations T s.carrier z).1 hz
  let τ := Name.ofSubset valid data.2
  have fixed := M.realize_nameSupportFormula a s t b K pairing unions powers separation collection
    carrier group supports maps i hi τ data.1
  change NiceNameCode a s T (K i) τ.val ↔ Realize M.sets nameSupportFormula _
  refine Iff.trans ?_ fixed.symm
  constructor
  · rintro ⟨σ, eq, _, h⟩
    have same : σ = τ := Subtype.ext eq
    exact same ▸ h
  · intro h
    exact ⟨τ, rfl, data.2, h⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNameSequenceForcingWitness
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula SetRealization
universe u

namespace SetFormula

def nameSequenceDecisionFormula : SetFormula 7 :=
  ex (ex (.conj (orderedPairFormula 1 3 4)
    (.conj (binaryApplication uniformCheckFormula (extend 8 Fin.elim0) 1 0)
      (forcingTranslation (ordinaryGroundPrimitives 0 1) (.mem 0 1)
        (extend 6 (extend 7 Fin.elim0)) 2 (extend 0 (extend 5 Fin.elim0))))))

end SetFormula

namespace SetFormula

def nameSequenceDecisionEntryFormula : SetFormula 7 :=
  ex (ex (ex (.conj (.mem 2 7) (.conj (.mem 1 4) (.conj (.mem 0 5)
    (.conj (BoundedFormula.orderedTripleFormula 3 2 1 0).toFormula
      (reindex (extend 2 (extend 1 (extend 0 (extend 6
        (extend 7 (extend 8 (extend 9 Fin.elim0))))))) nameSequenceDecisionFormula)))))))

end SetFormula

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRefinementValidityForcing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_refinementValidityForcing
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {n : Nat} (ui fi ci ti pi oi qi : Fin n) (env : Fin n → ZFSet.{u})
    (nameEnv : Assignment (M.nameDomain s) 4) (p : P)
    (hU : env ui = (nameEnv 0).val.val) (hRf : env fi = (nameEnv 1).val.val)
    (hRc : env ci = (nameEnv 2).val.val) (hT : env ti = (nameEnv 3).val.val)
    (hP : env pi = s.carrier) (hO : env oi = s.conditionOrder) (hQ : env qi = s.encode p) :
    Realize M.sets (refinementValidityForcingFormula ui fi ci ti pi oi qi) env ↔
      Forces (M.nameDomain s) BoundedFormula.refinementValidityFormula.toFormula nameEnv p := by
  exact M.realize_ordinaryGroundForcing s pairing unions powers separation collection carrier order
    (0 : Fin 2) 1 BoundedFormula.refinementValidityFormula.toFormula
    (extend pi (extend oi Fin.elim0)) qi
    (extend ui (extend fi (extend ci (extend ti Fin.elim0)))) env hP hO p nameEnv hQ
    (Fin.cases hU (Fin.cases hRf (Fin.cases hRc (Fin.cases hT (fun i => Fin.elim0 i)))))

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundIndexedGraphNameFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

def indexedGraphNamePairFormula : SetFormula 4 :=
  ex (ex (ex (ex (.conj (.mem 3 6)
    (.conj (orderedPairFormula 4 3 2)
      (.conj (checkNameCodeFormula 1 3 7)
        (.conj (orderedPairNameCodeFormula 0 1 2 7)
          (orderedPairFormula 5 0 7))))))))

def indexedGraphNameCodeFormula : SetFormula 4 :=
  exactSetFormula 0 (reindex (extend 0 (extend 4 (extend 3 (extend 2 Fin.elim0))))
    (relationImageFormula indexedGraphNamePairFormula))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_indexedGraphNamePairFormula {one I r z : ZFSet.{u}}
    (hone : one ∈ M.sets) (hI : I ∈ M.sets) (hr : r ∈ M.sets) (hz : z ∈ M.sets) :
    Realize M.sets indexedGraphNamePairFormula (extend r (extend z (extend I (extend one Fin.elim0)))) ↔
      ∃ i ∈ I, ∃ v, r = ZFSet.pair i v ∧
        z = ZFSet.pair (orderedPairNameCode one (checkNameCode one i) v) one := by
  rw [indexedGraphNamePairFormula, realize_ex]
  constructor
  · rintro ⟨i, hiM, rest⟩
    obtain ⟨v, hv, rest⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨k, hk, rest⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨w, hw, hi, input, checked, named, output⟩ := (realize_ex M.sets _ _).1 rest
    have members : ∀ j, (extend w (extend k (extend v (extend i
        (extend r (extend z (extend I (extend one Fin.elim0)))))))) j ∈ M.sets :=
      Fin.cases hw (Fin.cases hk (Fin.cases hv (Fin.cases hiM (Fin.cases hr
        (Fin.cases hz (Fin.cases hI (Fin.cases hone (fun j => Fin.elim0 j))))))))
    have key := (M.realize_checkNameCodeFormula pairing unions powers separation collection 1 3 7 _ members).1 checked
    have name := (M.realize_orderedPairNameCodeFormula pairing 0 1 2 7 _ members).1 named
    have inp := (M.realize_orderedPairFormula pairing 4 3 2 _ hr hiM hv).1 input
    have out := (M.realize_orderedPairFormula pairing 5 0 7 _ hz hw hone).1 output
    refine ⟨i, hi, v, inp, ?_⟩
    exact out.trans (congrArg (fun a => ZFSet.pair a one)
      (name.trans (congrArg (fun a => orderedPairNameCode one a v) key)))
  · rintro ⟨i, hi, v, input, output⟩
    have hiM := M.transitive hI hi
    have hv := M.pair_right (input ▸ hr)
    have hk := M.checkNameCode_mem pairing unions powers separation collection hone hiM
    have hw := M.orderedPairNameCode_mem pairing hone hk hv
    refine ⟨i, hiM, ?_⟩
    rw [realize_ex]
    refine ⟨v, hv, ?_⟩
    rw [realize_ex]
    refine ⟨checkNameCode one i, hk, ?_⟩
    rw [realize_ex]
    have members : ∀ j, (extend (orderedPairNameCode one (checkNameCode one i) v)
      (extend (checkNameCode one i) (extend v (extend i
        (extend r (extend z (extend I (extend one Fin.elim0)))))))) j ∈ M.sets :=
      Fin.cases hw (Fin.cases hk (Fin.cases hv (Fin.cases hiM (Fin.cases hr
        (Fin.cases hz (Fin.cases hI (Fin.cases hone (fun j => Fin.elim0 j))))))))
    exact ⟨_, hw, hi, (M.realize_orderedPairFormula pairing 4 3 2 _ hr hiM hv).2 input,
      (M.realize_checkNameCodeFormula pairing unions powers separation collection 1 3 7 _ members).2 rfl,
      (M.realize_orderedPairNameCodeFormula pairing 0 1 2 7 _ members).2 rfl,
      (M.realize_orderedPairFormula pairing 5 0 7 _ hz hw hone).2 output⟩

theorem indexedGraphNameCode_mem {one I f : ZFSet.{u}}
    (hone : one ∈ M.sets) (hI : I ∈ M.sets) (hf : f ∈ M.sets) :
    indexedGraphNameCode one I f ∈ M.sets := by
  let params := extend I (extend one Fin.elim0)
  apply M.definable_image_mem separation collection indexedGraphNamePairFormula params
    (Fin.cases hI (Fin.cases hone (fun j => Fin.elim0 j))) hf
  · intro z hz
    obtain ⟨i, hi, v, entry, rfl⟩ := (mem_indexedGraphNameCode one I f z).1 hz
    exact M.orderedPair_mem pairing (M.orderedPairNameCode_mem pairing hone
      (M.checkNameCode_mem pairing unions powers separation collection hone (M.transitive hI hi))
      (M.pair_right (M.transitive hf entry))) hone
  · intro z hz
    rw [mem_indexedGraphNameCode]
    constructor
    · rintro ⟨i, hi, v, entry, equal⟩
      exact ⟨ZFSet.pair i v, entry,
        (M.realize_indexedGraphNamePairFormula pairing unions powers separation collection
          hone hI (M.transitive hf entry) hz).2 ⟨i, hi, v, rfl, equal⟩⟩
    · rintro ⟨r, hr, formula⟩
      obtain ⟨i, hi, v, shape, equal⟩ :=
        (M.realize_indexedGraphNamePairFormula pairing unions powers separation collection
          hone hI (M.transitive hf hr) hz).1 formula
      exact ⟨i, hi, v, shape ▸ hr, equal⟩
  · intro r hr y hy z hz first second
    obtain ⟨i, _, v, input, output⟩ :=
      (M.realize_indexedGraphNamePairFormula pairing unions powers separation collection
        hone hI (M.transitive hf hr) hy).1 first
    obtain ⟨j, _, w, input', output'⟩ :=
      (M.realize_indexedGraphNamePairFormula pairing unions powers separation collection
        hone hI (M.transitive hf hr) hz).1 second
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 (input.symm.trans input')
    exact output.trans output'.symm

theorem realize_indexedGraphNameCodeFormula {one I f z : ZFSet.{u}}
    (hone : one ∈ M.sets) (hI : I ∈ M.sets) (hf : f ∈ M.sets) (hz : z ∈ M.sets) :
    Realize M.sets indexedGraphNameCodeFormula (extend z (extend one (extend I (extend f Fin.elim0)))) ↔
      z = indexedGraphNameCode one I f := by
  apply M.realize_exactSetFormula 0 _ _ hz
    (fun _ member => M.transitive (M.indexedGraphNameCode_mem pairing unions powers separation collection hone hI hf) member)
  intro w hw
  rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_empty]
  change Realize M.sets (relationImageFormula indexedGraphNamePairFormula)
    (extend w (extend f (extend I (extend one Fin.elim0)))) ↔ w ∈ indexedGraphNameCode one I f
  rw [M.realize_relationImageFormula indexedGraphNamePairFormula (extend I (extend one Fin.elim0)) f w hf,
    mem_indexedGraphNameCode]
  constructor
  · rintro ⟨r, hr, formula⟩
    obtain ⟨i, hi, v, shape, equal⟩ :=
      (M.realize_indexedGraphNamePairFormula pairing unions powers separation collection
        hone hI (M.transitive hf hr) hw).1 formula
    exact ⟨i, hi, v, shape ▸ hr, equal⟩
  · rintro ⟨i, hi, v, entry, equal⟩
    exact ⟨ZFSet.pair i v, entry,
      (M.realize_indexedGraphNamePairFormula pairing unions powers separation collection
        hone hI (M.transitive hf entry) hw).2 ⟨i, hi, v, rfl, equal⟩⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

noncomputable def definable_indexedGraphNameCode : GroundDefinableFunction M
    (fun env : Fin 3 → ZFSet.{u} => indexedGraphNameCode (env 0) (env 1) (env 2)) where
  formula := indexedGraphNameCodeFormula
  closed := fun _ members => M.indexedGraphNameCode_mem pairing unions powers separation collection
    (members 0) (members 1) (members 2)
  correct := by
    intro env members z hz
    have equal : env = extend (env 0) (extend (env 1) (extend (env 2) Fin.elim0)) := by
      funext j
      refine Fin.cases rfl (fun j => ?_) j
      refine Fin.cases rfl (fun j => ?_) j
      exact Fin.cases rfl (fun i => Fin.elim0 i) j
    have result := M.realize_indexedGraphNameCodeFormula pairing unions powers separation collection
      (members 0) (members 1) (members 2) hz
    rw [← equal] at result
    exact result

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RenamedPairNameFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def renamedNameFamilyPairFormula : SetFormula 5 :=
  .ex (.conj (domainApplication uniformNameFormula (extend 3 Fin.elim0) 0)
    (.conj (binaryApplication uniformRenameFormula (extend 4 (extend 5 Fin.elim0)) 1 0)
      (orderedPairFormula 2 1 0)))

end PartitionPilot.Forcing.SetFormula

end

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace SetFormula

def termActionEntryFormula : SetFormula 5 :=
  .ex (.ex (.conj (.mem 1 4) (.conj (.mem 0 4)
    (.conj (orderedPairFormula 2 1 0) (reindex ![3, 1, 0, 5, 6] nameActionFormula)))))

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets) (hT : T ∈ M.sets)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
include pairing unions powers separation collection carrier group maps hT closed

theorem realize_termActionEntryFormula (g : G) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets termActionEntryFormula ![z, t.encode g, T, s.carrier, a.conditionMapFamily s t] ↔
      z ∈ Name.renameFamilyGraph s (a.iso g) T valid := by
  let env : Fin 5 → ZFSet.{u} := ![z, t.encode g, T, s.carrier, a.conditionMapFamily s t]
  have args (x y : ZFSet.{u}) :
      (fun j : Fin 5 => (extend y (extend x env)) (![3, 1, 0, 5, 6] j)) =
        ![t.encode g, x, y, s.carrier, a.conditionMapFamily s t] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (fun k => Fin.elim0 k))))) j
  change Realize M.sets termActionEntryFormula env ↔ _
  simp only [termActionEntryFormula, realize_ex]
  constructor
  · rintro ⟨x, hxm, y, hym, hx, hy, paired, acted⟩
    let w : Name s := ⟨x, valid x hx⟩
    let v : Name s := ⟨y, valid y hy⟩
    have equal := (M.realize_orderedPairFormula pairing 2 1 0 _ hz hxm hym).1 paired
    change z = ZFSet.pair x y at equal
    rw [realize_reindex, args] at acted
    have action := (M.realize_nameActionFormula a s t pairing unions powers separation collection
      carrier group maps g w v hxm hym).1 acted
    exact equal.symm ▸ (Name.pair_mem_renameFamilyGraph s (a.iso g) T valid w y).2
      ⟨hx, congrArg Subtype.val action.symm⟩
  · intro entry
    obtain ⟨w, hw, rfl⟩ := (Name.mem_renameFamilyGraph s (a.iso g) T valid z).1 entry
    have hwm := M.transitive hT hw
    have actedT := closed g w hw
    have actedGround := M.transitive hT actedT
    refine ⟨w.val, hwm, (a.act s g w).val, actedGround, hw, actedT,
      (M.realize_orderedPairFormula pairing 2 1 0 _ hz hwm actedGround).2 rfl, ?_⟩
    rw [realize_reindex, args]
    exact (M.realize_nameActionFormula a s t pairing unions powers separation collection
      carrier group maps g w (a.act s g w) hwm actedGround).2 rfl

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMixtureDensityRecovery
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

variable [OrderTop P]

theorem act_niceVisibilityName {L : Type u} [PartialOrder L]
    (t : Presentation G) (d : PosetAction G L)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}}
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
    (g : G) (v : L) :
    a.act s g (M.niceVisibilityName a s T (d.principalFix v)) =
      M.niceVisibilityName a s T (d.principalFix (d.iso g v)) := by
  apply Name.act_familySet_transport a
  exact M.niceNameCandidates_principal_act_iff a s t pairing unions powers separation collection
    carrier maps closed d g v

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRenamedNameFamilyBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

noncomputable def stageOneClassName (R w : (M.nameDomain s).names) : (M.nameDomain s).names :=
  ⟨Name.refinementClass T valid R.val w.val,
    M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid
      R.val w.val R.property w.property⟩

noncomputable def stageOneMapName (U Rf Rc : (M.nameDomain s).names) : (M.nameDomain s).names :=
  ⟨Name.refinementNaturalMap T valid U.val Rf.val Rc.val,
    M.refinementNaturalMap_mem s pairing unions powers separation collection carrier order hT valid
      U.val Rf.val Rc.val U.property Rf.property Rc.property⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNiceRefinementVisibility
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)

theorem niceRefinementIndex_mem_iff
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (level T1 T2 : ZFSet.{u}) (valid : ∀ z ∈ T1, IsName s z)
    (familyGround : (Name.familySet ⊤ T1 valid).val ∈ M.sets)
    (C E : L) (U Rf Rc : (M.nameDomain s).names) :
    refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T1 T2 valid ↔
    C < E ∧ U.val.val ∈ M.niceNameCandidates a s T1 (d.principalFix C) ∧
      Rf.val.val ∈ M.niceNameCandidates a s T2 (d.principalFix C) ∧
      Rc.val.val ∈ M.niceNameCandidates a s T2 (d.principalFix C) ∧
      Forces (M.nameDomain s) BoundedFormula.refinementValidityFormula.toFormula
        (extend U (extend Rf (extend Rc (extend ⟨Name.familySet ⊤ T1 valid, familyGround⟩ Fin.elim0)))) ⊤ := by
  let T : (M.nameDomain s).names := ⟨Name.familySet ⊤ T1 valid, familyGround⟩
  let names := extend U (extend Rf (extend Rc (extend T Fin.elim0)))
  have forcing := M.realize_refinementValidityForcing s pairing unions powers separation collection carrier order
    0 1 2 3 4 5 6 ![U.val.val, Rf.val.val, Rc.val.val, T.val.val, s.carrier, s.conditionOrder, s.encode ⊤]
    names ⊤ rfl rfl rfl rfl rfl rfl rfl
  rw [niceRefinementIndices, M.refinementIndexCode_mem_indices]
  constructor
  · rintro ⟨_, _, _, _, _, edge, strict, N, V, first, hU, second, hf, hc, forced⟩
    have nEq := (M.pair_mem_niceNameCandidateGraph a s b T1 d.principalFix C N).1 first
    have vEq := (M.pair_mem_niceNameCandidateGraph a s b T2 d.principalFix C V).1 second
    subst N
    subst V
    have lower := (b.pair_mem_conditionOrder C E).1 edge
    have different : C ≠ E := fun eq => strict (congrArg b.encode eq)
    exact ⟨lt_of_le_of_ne lower different, hU, hf, hc, forcing.1 forced⟩
  · rintro ⟨strict, hU, hf, hc, forced⟩
    refine ⟨b.encode_mem C, b.encode_mem E, M.niceNameCandidates_subset a s T1 _ hU,
      M.niceNameCandidates_subset a s T2 _ hf, M.niceNameCandidates_subset a s T2 _ hc,
      (b.pair_mem_conditionOrder C E).2 strict.le,
      (fun eq => strict.ne (b.injective eq)), M.niceNameCandidates a s T1 (d.principalFix C),
      M.niceNameCandidates a s T2 (d.principalFix C), ?_, hU, ?_, hf, hc, forcing.2 forced⟩
    · exact (M.pair_mem_niceNameCandidateGraph a s b T1 d.principalFix C _).2 rfl
    · exact (M.pair_mem_niceNameCandidateGraph a s b T2 d.principalFix C _).2 rfl

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStageOneAssignmentUnions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

def stageOneCollisionTest (Rf Rc u u' w w' : (M.nameDomain s).names) (p : P) : Prop :=
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  Forces (M.nameDomain s) refinementCollisionFormula ![cls Rc u, cls Rc u', cls Rf w, cls Rf w'] p

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

def stageOneSingleTests (C E : L) (U Rf Rc u w : (M.nameDomain s).names) (p : P) : Prop :=
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
  Forces (M.nameDomain s) refinementActivityFormula ![u, w, U] p ∧
    (∀ v : L, E ≤ v →
      Forces (M.nameDomain s) refinementProfileFormula ![cls Rc u, cls Rf w, vis v] p) ∧
    Forces (M.nameDomain s) refinementCompatibilityFormula ![cls Rf w, vis C, cls Rc u, map] p

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

theorem stageOneCollisionTest_mono (Rf Rc u u' w w' : (M.nameDomain s).names)
    {p q : P} (forced : M.stageOneCollisionTest s pairing unions powers separation collection
      carrier order hT valid Rf Rc u u' w w' p) (below : q ≤ p) :
    M.stageOneCollisionTest s pairing unions powers separation collection
      carrier order hT valid Rf Rc u u' w w' q :=
  forces_mono (M.nameDomain s) _ _ forced below

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

theorem stageOneSingleTests_mono (C E : L) (U Rf Rc u w : (M.nameDomain s).names)
    {p q : P} (forced : M.stageOneSingleTests s pairing unions powers separation collection
      carrier order hT valid a b d base directed system C E U Rf Rc u w p) (below : q ≤ p) :
    M.stageOneSingleTests s pairing unions powers separation collection
      carrier order hT valid a b d base directed system C E U Rf Rc u w q :=
  ⟨forces_mono (M.nameDomain s) _ _ forced.1 below,
    fun v above => forces_mono (M.nameDomain s) _ _ (forced.2.1 v above) below,
    forces_mono (M.nameDomain s) _ _ forced.2.2 below⟩

end TransitiveGround

open SetRealization SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRepresentedDomainConditions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem stageOneRawForces_iff {P : Type u} [Preorder P] (s : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {n : Nat} (phi : SetFormula n) (p : P) (names : Assignment (M.nameDomain s) n) :
    stageOneRawForces M s.carrier s.conditionOrder (s.encode p) phi
      (fun j => (names j).val.val) ↔ Forces (M.nameDomain s) phi names p := by
  exact M.realize_ordinaryGroundForcing s pairing unions powers separation collection carrier order
    (0 : Fin 2) 1 phi (extend 1 (extend 2 Fin.elim0)) 0 (fun j => j.succ.succ.succ)
    _ rfl rfl p names rfl (fun _ => rfl)

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStandardInaccessible
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u




namespace GroundStandardInaccessible
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (standard : GroundStandardInaccessible M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hK : K ∈ M.sets)
include standard pairing unions powers separation hK

theorem to_conditions : GroundInaccessibleConditions M K :=
  ⟨standard.1.1, standard.omega_mem pairing unions powers separation hK,
    standard.2.2.1.regular standard.1.1,
    standard.2.2.2.to_groundStrongLimit pairing unions powers separation hK standard.1.1⟩

end GroundStandardInaccessible

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBatchEmbeddingRecognition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def definable_doubleUnion (unions : Realize M.sets SetFormula.union Fin.elim0) :
    GroundDefinableFunction M (fun env : Fin 1 → ZFSet.{u} => ZFSet.sUnion (ZFSet.sUnion (env 0))) :=
  (M.definable_sUnion unions).comp (fun _ => M.definable_sUnion unions)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

noncomputable def definable_codedAttachmentOrder : GroundDefinableFunction M
    (fun env : Fin 6 → ZFSet.{u} => codedAttachmentOrder
      (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) := by
  let aux := (M.definable_taggedExtension pairing unions powers separation).reindex
    (Fin.cases (0 : Fin 6) (Fin.cases 1 Fin.elim0))
  refine aux.withAux (codedAttachmentOrderSetFormula 1 0 2 3 4 5 6 7) ?_ ?_
  · intro env members
    exact M.codedAttachmentOrder_mem pairing unions powers separation
      (members 0) (members 1) (members 2) (members 3) (members 4) (members 5)
  · intro env members z hz
    exact M.realize_codedAttachmentOrderSetFormula pairing unions powers separation 1 0 2 3 4 5 6 7
      _ (Fin.cases (aux.closed env members) (Fin.cases hz members)) rfl

noncomputable def definable_pairSecondField : GroundDefinableFunction M
    (fun env : Fin 4 → ZFSet.{u} => pairSecondField (env 0) (env 1) (env 2) (env 3)) := by
  let aux := (M.definable_doubleUnion unions).reindex (fun _ : Fin 1 => (3 : Fin 4))
  refine aux.withAux (pairFieldSetFormula false 1 2 3 4 0 5) ?_ ?_
  · intro env members
    exact M.pairFieldGraph_mem pairing unions powers separation false
      (members 0) (members 1) (members 2) (aux.closed env members) (members 3)
  · intro env members z hz
    exact M.realize_pairSecondFieldSetFormula pairing unions powers separation 1 2 3 4 0 5
      _ (Fin.cases (aux.closed env members) (Fin.cases hz members)) rfl

noncomputable def definable_indexedFresh : GroundDefinableFunction M
    (fun env : Fin 4 → ZFSet.{u} => indexedAttachmentFresh (env 0) (env 1) (env 2) (env 3)) := by
  let aux := fun j : Fin 3 => (M.definable_doubleUnion unions).reindex (fun _ : Fin 1 => j.succ)
  refine GroundDefinableFunction.withAuxFamily aux (indexedFreshSetFormula 3 4 5 6 7 0 1 2) ?_ ?_
  · intro env members
    exact M.indexedAttachmentFresh_mem pairing unions powers separation
      (members 0) (members 1) (members 2) (members 3)
  · intro env members z hz
    exact M.realize_indexedFreshSetFormula pairing unions powers separation 3 4 5 6 7 0 1 2 _
      (extendMany_members 3 _ _ (fun j => (aux j).closed env members) (Fin.cases hz members)) rfl rfl rfl

noncomputable def definable_batchInside : GroundDefinableFunction M
    (fun env : Fin 3 → ZFSet.{u} => batchAttachmentInsideGraph (env 0) (env 1) (env 2)) := by
  let aux := fun j : Fin 2 => (M.definable_doubleUnion unions).reindex (fun _ : Fin 1 => j.succ)
  refine GroundDefinableFunction.withAuxFamily aux (batchInsideSetFormula 2 3 4 5 0 1) ?_ ?_
  · intro env members
    exact M.batchAttachmentInsideGraph_mem pairing unions powers separation (members 0) (members 1) (members 2)
  · intro env members z hz
    exact M.realize_batchInsideSetFormula pairing unions powers separation 2 3 4 5 0 1 _
      (extendMany_members 2 _ _ (fun j => (aux j).closed env members) (Fin.cases hz members)) rfl rfl

noncomputable def definable_batchUpper : GroundDefinableFunction M
    (fun env : Fin 4 → ZFSet.{u} => batchAttachmentUpperGraph (env 0) (env 1) (env 2) (env 3)) := by
  let slots : Fin 2 → Fin 4 := Fin.cases 2 (Fin.cases 3 Fin.elim0)
  let aux := fun j : Fin 2 => (M.definable_doubleUnion unions).reindex (fun _ : Fin 1 => slots j)
  refine GroundDefinableFunction.withAuxFamily aux (batchUpperSetFormula 2 3 4 5 6 0 1) ?_ ?_
  · intro env members
    exact M.batchAttachmentUpperGraph_mem pairing unions powers separation
      (members 0) (members 1) (members 2) (members 3)
  · intro env members z hz
    exact M.realize_batchUpperSetFormula pairing unions powers separation 2 3 4 5 6 0 1 _
      (extendMany_members 2 _ _ (fun j => (aux j).closed env members) (Fin.cases hz members)) rfl rfl

noncomputable def definable_batchShadow : GroundDefinableFunction M
    (fun env : Fin 6 → ZFSet.{u} => batchAttachmentShadowGraph
      (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) := by
  let slots : Fin 4 → Fin 6 := Fin.cases 2 (Fin.cases 3 (Fin.cases 4 (Fin.cases 5 Fin.elim0)))
  let aux := fun j : Fin 4 => (M.definable_doubleUnion unions).reindex (fun _ : Fin 1 => slots j)
  refine GroundDefinableFunction.withAuxFamily aux (batchShadowSetFormula 4 5 6 7 8 9 10 0 1 2 3) ?_ ?_
  · intro env members
    exact M.batchAttachmentShadowGraph_mem pairing unions powers separation
      (members 0) (members 1) (members 2) (members 3) (members 4) (members 5)
  · intro env members z hz
    exact M.realize_batchShadowSetFormula pairing unions powers separation 4 5 6 7 8 9 10 0 1 2 3 _
      (extendMany_members 4 _ _ (fun j => (aux j).closed env members) (Fin.cases hz members)) rfl rfl rfl rfl

end TransitiveGround

namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def definable_liftedCompressionFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 13 → ZFSet.{u} =>
      M.groundLiftedCompressionFamily (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)
        (env 6) (env 7) (env 8) (env 9) (env 10) (env 11) (env 12)) := by
  let doubleUnion : GroundDefinableFunction M
      (fun env : Fin 1 → ZFSet.{u} => ZFSet.sUnion (ZFSet.sUnion (env 0))) :=
    (M.definable_sUnion unions).comp (fun _ => M.definable_sUnion unions)
  let bounds : Fin 2 → (Fin 13 → ZFSet.{u}) → ZFSet.{u} :=
    ![(fun env => ZFSet.sUnion (ZFSet.sUnion (env 7))),
      (fun env => ZFSet.sUnion (ZFSet.sUnion (env 9)))]
  have definedBounds : ∀ j, GroundDefinableFunction M (bounds j) := by
    intro j
    exact Fin.cases (doubleUnion.reindex (fun _ => 7))
      (Fin.cases (doubleUnion.reindex (fun _ => 9)) (fun k => Fin.elim0 k)) j
  refine GroundDefinableFunction.withAuxFamily definedBounds
    (liftedCompressionFamilyFormula 2 3 4 5 6 7 8 9 10 11 12 13 14 15 0 1) ?_ ?_
  · intro env members
    exact (M.groundLiftedCompressionFamily_spec pairing unions powers separation
      (members 0) (members 1) (members 2) (members 3) (members 4) (members 5) (members 6)
      (members 7) (members 8) (members 9) (members 10) (members 11) (members 12)).1
  · intro env members z hz
    exact M.realize_liftedCompressionFamilyFormula pairing unions powers separation
      2 3 4 5 6 7 8 9 10 11 12 13 14 15 0 1
      (extend (ZFSet.sUnion (ZFSet.sUnion (env 7)))
        (extend (ZFSet.sUnion (ZFSet.sUnion (env 9))) (extend z env)))
      (Fin.cases (M.union_mem unions (M.union_mem unions (members 7)))
        (Fin.cases (M.union_mem unions (M.union_mem unions (members 9)))
          (Fin.cases hz members))) rfl rfl

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundDefinableRelationProducts
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundSetTerm

def app {M : TransitiveGround.{u}} {n k : Nat}
    {f : (Fin k → ZFSet.{u}) → ZFSet.{u}}
    (operation : GroundDefinableFunction M f) (args : Fin k → GroundSetTerm M n) :
    GroundSetTerm M n :=
  ⟨fun env => f (fun i => (args i).eval env),
    operation.comp (fun i => (args i).definition)⟩

end GroundSetTerm

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundDefinableRefinementNameGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u})

variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation collection carrier order

theorem refinementOutput_mem_bound (kind : Fin 3) {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s)
    (hU : U.val ∈ M.sets) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets) :
    (Name.refinementOutput kind T valid U Rf Rc).val ∈ M.refinementNameBound T s.carrier (s.encode ⊤) := by
  let B := M.groundRelations T s.carrier
  let C := B ∪ orderedPairNameFamily (s.encode ⊤) B B
  have classBound (R : Name s) (hR : R.val ∈ M.sets) (w : Name s) (hw : w.val ∈ T) :
      (Name.refinementClass T valid R w).val ∈ B :=
    (M.mem_groundRelations T s.carrier _).2
      ⟨M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid R w hR
        (M.transitive hT hw), Name.refinementClass_subset T valid R w⟩
  have quotient (R : Name s) (hR : R.val ∈ M.sets) :
      (Name.refinementQuotient T valid U R).val ∈ M.groundRelations C s.carrier := by
    apply (M.mem_groundRelations C s.carrier _).2
    exact ⟨M.refinementQuotient_mem s pairing unions powers separation collection carrier order hT valid U R hU hR,
      Name.activeImage_subset T valid U _ C (fun w hw => ZFSet.mem_union.2 (Or.inl (classBound R hR w hw)))⟩
  have natural : (Name.refinementNaturalMap T valid U Rf Rc).val ∈ M.groundRelations C s.carrier := by
    apply (M.mem_groundRelations C s.carrier _).2
    refine ⟨M.refinementNaturalMap_mem s pairing unions powers separation collection carrier order hT valid U Rf Rc hU hRf hRc,
      Name.activeImage_subset T valid U _ C ?_⟩
    intro w hw
    exact ZFSet.mem_union.2 (Or.inr ((mem_orderedPairNameFamily _ B B _).2
      ⟨_, classBound Rf hRf w hw, _, classBound Rc hRc w hw, Name.orderedPair_code ⊤ _ _⟩))
  exact Fin.cases (quotient Rf hRf) (Fin.cases (quotient Rc hRc)
    (Fin.cases natural (fun j => Fin.elim0 j))) kind

theorem realize_refinementOutputCodeFormula (kind : Fin 3) {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s)
    (hU : U.val ∈ M.sets) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets)
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets (refinementOutputCodeFormula kind)
      (extend z (extend T (extend U.val (extend Rf.val (extend Rc.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))))) ↔
      z = (Name.refinementOutput kind T valid U Rf Rc).val := by
  let env := extend z (extend T (extend U.val (extend Rf.val (extend Rc.val
    (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))))
  have firstArgs : (fun j : Fin 7 => env (![0, 1, 2, 3, 5, 6, 7] j)) =
      extend z (extend T (extend U.val (extend Rf.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
  have secondArgs : (fun j : Fin 7 => env (![0, 1, 2, 4, 5, 6, 7] j)) =
      extend z (extend T (extend U.val (extend Rc.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) kind
  · change Realize M.sets (reindex _ refinementQuotientCodeFormula) env ↔ _
    rw [realize_reindex, firstArgs]
    exact M.realize_refinementQuotientCodeFormula s pairing unions powers separation collection carrier order hT valid U Rf hU hRf z hz
  · change Realize M.sets (reindex _ refinementQuotientCodeFormula) env ↔ _
    rw [realize_reindex, secondArgs]
    exact M.realize_refinementQuotientCodeFormula s pairing unions powers separation collection carrier order hT valid U Rc hU hRc z hz
  · exact M.realize_refinementMapCodeFormula s pairing unions powers separation collection carrier order hT valid U Rf Rc hU hRf hRc z hz

end TransitiveGround



namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_refinementIndexNameGraphFormula (kind : Fin 3)
    (env : Fin 9 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (refinementIndexNameGraphFormula kind) env ↔
      ∃ w : Fin 5 → ZFSet.{u}, (∀ j, w j ∈ M.sets) ∧
        w 0 ∈ env 1 ∧ env 0 = ZFSet.pair (w 0) (w 1) ∧
        ZFSet.pair (w 0) (w 2) ∈ env 2 ∧ ZFSet.pair (w 0) (w 3) ∈ env 3 ∧
        ZFSet.pair (w 0) (w 4) ∈ env 4 ∧
        Realize M.sets (refinementOutputCodeFormula kind)
          (extend (w 1) (extend (env 5) (extend (w 2) (extend (w 3) (extend (w 4)
            (extend (env 6) (extend (env 7) (extend (env 8) Fin.elim0)))))))) := by
  rw [refinementIndexNameGraphFormula, realize_exBlock]
  apply exists_congr
  intro w
  apply and_congr_right
  intro ground
  have args : (fun j : Fin 8 => extendMany 5 w env
      (![prefixIndex 9 5 1, suffixIndex 9 5 5, prefixIndex 9 5 2,
        prefixIndex 9 5 3, prefixIndex 9 5 4, suffixIndex 9 5 6,
        suffixIndex 9 5 7, suffixIndex 9 5 8] j)) =
      extend (w 1) (extend (env 5) (extend (w 2) (extend (w 3) (extend (w 4)
        (extend (env 6) (extend (env 7) (extend (env 8) Fin.elim0))))))) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (fun k => Fin.elim0 k)))))))) j
  simp only [Realize, BoundedFormula.realize_toFormula M _ _
    (extendMany_members 5 w env ground members), BoundedFormula.truth_orderedPairFormula,
    BoundedFormula.truth_pairMembershipFormula, extendMany_prefix, extendMany_suffix,
    realize_reindex, args]

variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

theorem refinementIndexNameGraph_entry (kind : Fin 3)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {I UF FF CF T : ZFSet.{u}} (hI : I ∈ M.sets) (hUF : UF ∈ M.sets)
    (hFF : FF ∈ M.sets) (hCF : CF ∈ M.sets) (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s)
    (hU : U.val ∈ M.sets) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets)
    {i : ZFSet.{u}} (hi : i ∈ I)
    (uEntry : ∀ z, ZFSet.pair i z ∈ UF ↔ z = U.val)
    (fEntry : ∀ z, ZFSet.pair i z ∈ FF ↔ z = Rf.val)
    (cEntry : ∀ z, ZFSet.pair i z ∈ CF ↔ z = Rc.val) (y : ZFSet.{u}) :
    ZFSet.pair i y ∈ M.refinementIndexNameGraph kind I UF FF CF T s.carrier s.conditionOrder (s.encode ⊤) ↔
      y = (Name.refinementOutput kind T valid U Rf Rc).val := by
  have ht := M.transitive carrier (s.encode_mem ⊤)
  have hB := M.refinementNameBound_mem pairing unions powers separation hT carrier ht
  have hidx := M.transitive hI hi
  let params : Fin 8 → ZFSet.{u} := ![I, UF, FF, CF, T, s.carrier, s.conditionOrder, s.encode ⊤]
  have hp : ∀ j, params j ∈ M.sets := Fin.cases hI (Fin.cases hUF (Fin.cases hFF
    (Fin.cases hCF (Fin.cases hT (Fin.cases carrier (Fin.cases order
      (Fin.cases ht (fun j => Fin.elim0 j))))))))
  rw [refinementIndexNameGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨_, hyB⟩, recognized⟩
    have hy := M.transitive hB hyB
    have hpair := M.orderedPair_mem pairing hidx hy
    obtain ⟨w, ground, _, equal, hu, hf, hc, output⟩ :=
      (M.realize_refinementIndexNameGraphFormula kind (extend (ZFSet.pair i y) params)
        (Fin.cases hpair hp)).1 recognized
    have eq : ZFSet.pair i y = ZFSet.pair (w 0) (w 1) := equal
    obtain ⟨idx, val⟩ := ZFSet.pair_inj.1 eq
    have ue : w 2 = U.val := (uEntry _).1 (idx.symm ▸ hu)
    have fe : w 3 = Rf.val := (fEntry _).1 (idx.symm ▸ hf)
    have ce : w 4 = Rc.val := (cEntry _).1 (idx.symm ▸ hc)
    change Realize M.sets (refinementOutputCodeFormula kind)
      (extend (w 1) (extend T (extend (w 2) (extend (w 3) (extend (w 4)
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))))) at output
    rw [← val, ue, fe, ce] at output
    exact (M.realize_refinementOutputCodeFormula s pairing unions powers separation collection
      carrier order kind hT valid U Rf Rc hU hRf hRc y hy).1 output
  · intro equal
    subst y
    have bound := M.refinementOutput_mem_bound s pairing unions powers separation collection
      carrier order kind hT valid U Rf Rc hU hRf hRc
    have hy := M.transitive hB bound
    refine ⟨⟨hi, bound⟩, ?_⟩
    apply (M.realize_refinementIndexNameGraphFormula kind (extend _ params)
      (Fin.cases (M.orderedPair_mem pairing hidx hy) hp)).2
    refine ⟨![i, (Name.refinementOutput kind T valid U Rf Rc).val, U.val, Rf.val, Rc.val],
      Fin.cases hidx (Fin.cases hy (Fin.cases hU (Fin.cases hRf (Fin.cases hRc
        (fun j => Fin.elim0 j))))), hi, rfl, (uEntry _).2 rfl, (fEntry _).2 rfl,
      (cEntry _).2 rfl, ?_⟩
    exact (M.realize_refinementOutputCodeFormula s pairing unions powers separation collection
      carrier order kind hT valid U Rf Rc hU hRf hRc _ hy).2 rfl

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)

variable {level T1 T2 : ZFSet.{u}} {valid1 : ∀ z ∈ T1, IsName s z} {valid2 : ∀ z ∈ T2, IsName s z}
variable (system : NiceRefinementIndexSystem M a s b d level T1 T2 valid1 valid2)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (hT1 : T1 ∈ M.sets) (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include system pairing unions powers separation collection hT1 carrier order in
theorem niceRefinementNameGraph_entry (kind : Fin 3)
    (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T1 T2 valid1) (y : ZFSet.{u}) :
    ZFSet.pair (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) y ∈
      M.niceRefinementNameGraph a s b d kind level T1 T2 valid1 ↔
      y = (Name.refinementOutput kind T1 valid1 U.val Rf.val Rc.val).val := by
  exact M.refinementIndexNameGraph_entry s kind pairing unions powers separation collection carrier order
    system.index_ground (system.field_ground 3) (system.field_ground 4) (system.field_ground 5)
    hT1 valid1 U.val Rf.val Rc.val U.property Rf.property Rc.property member
    (M.niceRefinementIndex_field_entry a s b d system C E U Rf Rc member 3)
    (M.niceRefinementIndex_field_entry a s b d system C E U Rf Rc member 4)
    (M.niceRefinementIndex_field_entry a s b d system C E U Rf Rc member 5) y

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RepresentativeIndexSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

noncomputable def classSelectionDefinition (phi : SetFormula 7) :
    GroundDefinableFunction M (fun env : Fin 6 → ZFSet.{u} =>
      ZFSet.sep (fun z => Realize M.sets phi (extend z ![env 0, env 1, env 2, env 3, env 4, env 5]))
        (ZFSet.prod (env 0) (M.groundRelations (env 2) (env 3)))) := by
  let v := GroundSetTerm.var M (n := 6)
  let names := GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![v 2, v 3]
  let bound := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 0, names]
  let term := GroundSetTerm.app (M.definable_separation separation phi)
    ![bound, v 0, v 1, v 2, v 3, v 4, v 5]
  refine term.definition.congr ?_
  intro env
  apply congrArg (fun params : Fin 6 → ZFSet.{u} => ZFSet.sep
    (fun z => Realize M.sets phi (extend z params))
      (ZFSet.prod (env 0) (M.groundRelations (env 2) (env 3))))
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) j

noncomputable def definable_assignmentClassGraph (side : Fin 2) :
    GroundDefinableFunction M (fun env : Fin 6 → ZFSet.{u} =>
      M.assignmentClassGraph side (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) := by
  unfold assignmentClassGraph
  exact classSelectionDefinition M pairing unions powers separation _

noncomputable def definable_assignmentOnIndices :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} =>
      assignmentOnIndices (env 0) (env 1) (env 2)) := by
  let v := GroundSetTerm.var M (n := 3)
  let pairs := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 1, v 1]
  let assignments := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 0, pairs]
  let term := GroundSetTerm.app (M.definable_separation separation (.mem 0 1)) ![v 2, assignments]
  exact term.definition

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def storedPreparationRequests (A : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u}) : ZFSet.{u} :=
  let selected := assignmentOnIndices (fields 0) (fields 6) A
  relationImage selected (fields 14) (M.storedAssignmentClassGraph A fields 0) ∪
    relationImage selected (fields 14) (M.storedAssignmentClassGraph A fields 1)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RefinementHistoryPrefixLevels
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

theorem refinementHistoryIndices_mem
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    {alpha history : ZFSet.{u}} (hAlpha : alpha ∈ M.sets) (hHistory : history ∈ M.sets) :
    refinementHistoryIndices alpha history ∈ M.sets :=
  M.union_mem unions (M.functionGraphRange_mem unions separation hAlpha hHistory)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem refinementHistoryLevels_mem {alpha history : ZFSet.{u}}
    (hAlpha : alpha ∈ M.sets) (hHistory : history ∈ M.sets) :
    refinementHistoryLevels alpha history ∈ M.sets :=
  M.refinementIndexFieldGraph_mem pairing unions powers separation
    (M.refinementHistoryIndices_mem unions separation hAlpha hHistory) hAlpha 0

theorem refinementHistoryAssignmentLevels_mem {alpha history T : ZFSet.{u}}
    (hAlpha : alpha ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets) :
    refinementHistoryAssignmentLevels alpha history T ∈ M.sets :=
  M.assignmentIndexLevels_mem pairing unions powers separation
    (M.refinementHistoryIndices_mem unions separation hAlpha hHistory) hT hAlpha
    (M.refinementHistoryLevels_mem pairing unions powers separation hAlpha hHistory)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def definable_historyUnion
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} =>
      refinementHistoryIndices (env 0) (env 1)) where
  formula := exactSetFormula 0 (.ex (.ex
    (.conj (.mem 1 4) (.conj (pairMembershipFormula 1 0 5) (.mem 2 0)))))
  closed := fun _ members => M.refinementHistoryIndices_mem unions separation (members 0) (members 1)
  correct := by
    intro env members z hz
    have ground := M.refinementHistoryIndices_mem unions separation (members 0) (members 1)
    apply M.realize_exactSetFormula 0 _ (extend z env) hz (fun _ h => M.transitive ground h)
    intro w _
    simp only [realize_ex]
    change (∃ a ∈ M.sets, ∃ Y ∈ M.sets, a ∈ env 0 ∧
      Realize M.sets (pairMembershipFormula 1 0 5)
        (extend Y (extend a (extend w (extend z env)))) ∧ w ∈ Y) ↔ _
    rw [mem_refinementHistoryIndices]
    constructor
    · rintro ⟨a, ha, Y, hY, member, entry, inside⟩
      exact ⟨a, member, Y,
        (M.realize_pairMembershipFormula pairing 1 0 5 (extend Y (extend a (extend w (extend z env)))) ha hY (members 1)).1 entry, inside⟩
    · rintro ⟨a, member, Y, entry, inside⟩
      have ha := M.transitive (members 0) member
      have hY := M.transitive (M.union_mem unions (M.union_mem unions (members 1)))
        (pair_second_mem_doubleUnion entry)
      exact ⟨a, ha, Y, hY, member,
        (M.realize_pairMembershipFormula pairing 1 0 5 (extend Y (extend a (extend w (extend z env)))) ha hY (members 1)).2 entry, inside⟩





end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialCompressionHistory
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

noncomputable def recursiveSuccessorTerm : GroundSetTerm M 18 :=
  let v : Fin 18 → GroundSetTerm M 18 := GroundSetTerm.var M
  let union (term : GroundSetTerm M 18) :=
    GroundSetTerm.app (M.definable_sUnion unions) (Fin.cases term Fin.elim0)
  let bound := union (union (union (v 4)))
  let oldFresh := GroundSetTerm.app
    (M.definable_indexedFresh pairing unions powers separation)
    (Fin.cases (v 3) (Fin.cases (v 4) (Fin.cases (v 5) (Fin.cases (v 7) (Fin.elim0)))))
  let carrier := GroundSetTerm.app
    (M.definable_taggedExtension pairing unions powers separation)
    (Fin.cases (v 0) (Fin.cases (oldFresh) (Fin.elim0)))
  let inside := GroundSetTerm.app
    (M.definable_batchInside pairing unions powers separation)
    (Fin.cases (v 3) (Fin.cases (v 4) (Fin.cases (v 5) (Fin.elim0))))
  let shadow := GroundSetTerm.app
    (M.definable_batchShadow pairing unions powers separation)
    (Fin.cases (v 3) (Fin.cases (v 0) (Fin.cases (v 4) (Fin.cases (v 6) (Fin.cases (v 7) (Fin.cases (v 8) (Fin.elim0)))))))
  let upper := GroundSetTerm.app
    (M.definable_batchUpper pairing unions powers separation)
    (Fin.cases (v 3) (Fin.cases (v 0) (Fin.cases (v 4) (Fin.cases (v 9) (Fin.elim0)))))
  let order := GroundSetTerm.app
    (M.definable_codedAttachmentOrder pairing unions powers separation)
    (Fin.cases (v 0) (Fin.cases (oldFresh) (Fin.cases (v 1) (Fin.cases (inside) (Fin.cases (shadow) (Fin.cases (upper) (Fin.elim0)))))))
  let meet := GroundSetTerm.app
    (M.definable_canonicalMeet pairing unions powers separation)
    (Fin.cases (carrier) (Fin.cases (order) (Fin.elim0)))
  let indices := GroundSetTerm.app
    (M.definable_recursiveIndices pairing unions powers separation)
    (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (v 0) (Fin.cases (union (union (v 9))) (Fin.cases (v 14) (Fin.cases (v 9) (Fin.elim0)))))))
  let spaces := GroundSetTerm.app
    (M.definable_pairSecondField pairing unions powers separation)
    (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (indices) (Fin.cases (v 4) (Fin.elim0)))))
  let relations := GroundSetTerm.app
    (M.definable_pairSecondField pairing unions powers separation)
    (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (indices) (Fin.cases (v 5) (Fin.elim0)))))
  let meets := GroundSetTerm.app
    (M.definable_pairSecondField pairing unions powers separation)
    (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (indices) (Fin.cases (v 6) (Fin.elim0)))))
  let anchors := GroundSetTerm.app
    (M.definable_pairSecondField pairing unions powers separation)
    (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (indices) (Fin.cases (v 7) (Fin.elim0)))))
  let fresh := GroundSetTerm.app
    (M.definable_indexedFresh pairing unions powers separation)
    (Fin.cases (indices) (Fin.cases (spaces) (Fin.cases (relations) (Fin.cases (anchors) (Fin.elim0)))))
  let nextCarrier := GroundSetTerm.app
    (M.definable_taggedExtension pairing unions powers separation)
    (Fin.cases (carrier) (Fin.cases (fresh) (Fin.elim0)))
  let embeddings := GroundSetTerm.app
    (M.definable_pairCompositions pairing unions powers separation)
    (Fin.cases (indices) (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (bound) (Fin.cases (v 0) (Fin.cases (carrier) (Fin.cases (v 8) (Fin.cases (v 11) (Fin.elim0)))))))))
  let filters := GroundSetTerm.app
    (M.definable_pairPushFilters pairing unions powers separation)
    (Fin.cases (indices) (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (carrier) (Fin.cases (order) (Fin.cases (v 11) (Fin.cases (v 9) (Fin.elim0))))))))
  let separators := GroundSetTerm.app
    (M.definable_recursiveSeparators pairing unions powers separation)
    (Fin.cases (indices) (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (v 0) (Fin.cases (carrier) (Fin.cases (v 11) (Fin.cases (v 10) (Fin.elim0))))))))
  let maps := GroundSetTerm.app
    (M.definable_liftedCompressionFamily pairing unions powers separation)
    (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (v 0) (Fin.cases (carrier) (Fin.cases (nextCarrier) (Fin.cases (oldFresh) (Fin.cases (bound) (Fin.cases (v 11) (Fin.cases (v 14) (Fin.cases (v 9) (Fin.cases (v 15) (Fin.cases (v 16) (Fin.cases (v 12) (Fin.elim0))))))))))))))
  let action := GroundSetTerm.app
    (M.definable_recursiveAction pairing unions powers separation)
    (Fin.cases (v 16) (Fin.cases (carrier) (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (indices) (Fin.cases (bound) (Fin.cases (fresh) (Fin.cases (v 12) (Fin.cases (v 17) (Fin.elim0))))))))))
  GroundSetTerm.app (M.definable_nonemptyTuple pairing 12)
    (Fin.cases (carrier) (Fin.cases (order) (Fin.cases (meet) (Fin.cases (indices) (Fin.cases (spaces) (Fin.cases (relations) (Fin.cases (meets) (Fin.cases (anchors) (Fin.cases (embeddings) (Fin.cases (filters) (Fin.cases (separators) (Fin.cases (maps) (Fin.cases (action) (Fin.elim0))))))))))))))

theorem recursiveSuccessorTerm_eval (env : Fin 18 → ZFSet.{u}) :
    (M.recursiveSuccessorTerm pairing unions powers separation).eval env =
      RecursiveStateData.successorCodeFromEnvironment M env := by
  rfl

noncomputable def definable_recursiveSuccessorCode :
    GroundDefinableFunction M (RecursiveStateData.successorCodeFromEnvironment M) :=
  (M.recursiveSuccessorTerm pairing unions powers separation).definition.congr
    (M.recursiveSuccessorTerm_eval pairing unions powers separation)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
noncomputable def compressionSuccessorFormula (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) : SetFormula 7 :=
  decodedSuccessorFormula (M.definable_recursiveSuccessorCode pairing unions powers separation).formula

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundSerializedChronologyTimeEquality
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundSerializedChronology
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M T C D rD)

noncomputable def layerWitness (s t : ZFSet.{u}) : ZFSet.{u} :=
  (show FunctionGraphOn (chronologyPairs T) serial.layers from
    ⟨serial.layerBound, serial.layer_function⟩).totalValue (ZFSet.pair s t)

theorem layerWitness_entry {s t : ZFSet.{u}} (hs : s ∈ T) (ht : t ∈ T)
    (earlier : t = s ∨ t ∈ s) :
    ZFSet.pair (ZFSet.pair s t) (serial.layerWitness s t) ∈ serial.layers :=
  (show FunctionGraphOn (chronologyPairs T) serial.layers from
    ⟨serial.layerBound, serial.layer_function⟩).totalValue_entry
      ((pair_mem_chronologyPairs T s t).2 ⟨hs, ht, earlier⟩)

theorem layerWitness_ground (s t : ZFSet.{u}) : serial.layerWitness s t ∈ M.sets :=
  (show FunctionGraphOn (chronologyPairs T) serial.layers from
    ⟨serial.layerBound, serial.layer_function⟩).totalValue_ground M serial.layers_ground _

noncomputable def decodedLayer {s t : ZFSet.{u}} (hs : s ∈ T) (ht : t ∈ T)
    (earlier : t = s ∨ t ∈ s) :
    CodedGrowthLayer M (serial.fields.value 0) (serial.fields.value 1) (serial.fields.value 2)
      (serial.fields.value 0 s) (serial.fields.value 1 s) (serial.fields.value 2 s)
        (serial.fields.value 3 s) t :=
  (serial.layer_code s hs t ht earlier _ (serial.layerWitness_entry hs ht earlier)).toLayer
    (serial.layerWitness_ground s t) (serial.fields.value 0) (serial.fields.value 1)
      (serial.fields.value 2) rfl (fun a ha =>
        ⟨serial.fields.value_entry 0 (serial.ordinal.1 t ht a ha),
          serial.fields.value_entry 1 (serial.ordinal.1 t ht a ha),
          serial.fields.value_entry 2 (serial.ordinal.1 t ht a ha)⟩)

noncomputable def toHistory : GroundChronologicalHistory M T C D rD :=
  serial.fields.toHistory serial.core (fun _ hs _ ht earlier => serial.decodedLayer hs ht earlier)

end GroundSerializedChronology
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRawNiceNameGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def rawNiceNameCandidates (i T P G basis maps : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => Realize M.sets nameSupportFormula
    (extend z (extend i (extend P (extend G (extend basis (extend maps Fin.elim0)))))))
      (M.groundRelations T P)

noncomputable def rawNiceNameCandidateGraph (nodes T P G basis maps : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph (fun i : nodes => i.val)
    (fun i => M.rawNiceNameCandidates i.val T P G basis maps)

noncomputable def rawNiceVisibilityGraph (nodes T P G basis maps top : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph (fun i : nodes => i.val)
    (fun i => ZFSet.prod (M.rawNiceNameCandidates i.val T P G basis maps) {top})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_rawNiceNameCandidates :
    GroundDefinableFunction M (fun env : Fin 6 → ZFSet.{u} =>
      M.rawNiceNameCandidates (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) := by
  let v := GroundSetTerm.var M (n := 6)
  let bound := GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![v 1, v 2]
  let term := GroundSetTerm.app (M.definable_separation separation nameSupportFormula)
    ![bound, v 0, v 2, v 3, v 4, v 5]
  refine term.definition.congr ?_
  intro env
  apply congrArg (fun params : Fin 5 → ZFSet.{u} =>
    ZFSet.sep (fun z => Realize M.sets nameSupportFormula (extend z params))
      (M.groundRelations (env 1) (env 2)))
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (fun k => Fin.elim0 k))))) j

variable (collection : CollectionSchema M.sets)

noncomputable def definable_rawNiceNameCandidateGraph :
    GroundDefinableFunction M (fun env : Fin 6 → ZFSet.{u} =>
      M.rawNiceNameCandidateGraph (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) :=
  (M.definable_rawNiceNameCandidates pairing unions powers separation).definable_graph
    pairing separation collection

variable {I H Q : Type u} [Group H] [PartialOrder Q]
variable (a : PosetAction H Q) (s : Presentation Q) (t : Presentation H) (b : Presentation I)
variable (K : I → Subgroup H)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (valid : ∀ z ∈ T, IsName s z)
include pairing unions powers separation collection carrier group supports maps valid

theorem rawNiceNameCandidates_eq (i : I) (hi : b.encode i ∈ M.sets) :
    M.rawNiceNameCandidates (b.encode i) T s.carrier t.carrier (supportBasisCode b t K)
      (a.conditionMapFamily s t) = M.niceNameCandidates a s T (K i) :=
  (M.niceNameCandidates_eq_selection a s t b K pairing unions powers separation collection
    carrier group supports maps valid i hi).symm

theorem rawNiceNameCandidateGraph_eq (nodes : b.carrier ∈ M.sets) :
    M.rawNiceNameCandidateGraph b.carrier T s.carrier t.carrier (supportBasisCode b t K)
      (a.conditionMapFamily s t) = M.niceNameCandidateGraph a s b T K := by
  apply ZFSet.ext
  intro z
  rw [rawNiceNameCandidateGraph, mem_familyCodeGraph, M.mem_niceNameCandidateGraph]
  constructor
  · rintro ⟨i, equal⟩
    obtain ⟨j, eq⟩ := (b.mem_carrier i.val).1 i.property
    refine ⟨j, ?_⟩
    rw [← eq, M.rawNiceNameCandidates_eq pairing unions powers separation collection a s t b K
      carrier group supports maps valid j (M.transitive nodes (b.encode_mem j))] at equal
    exact equal.symm
  · rintro ⟨i, equal⟩
    refine ⟨⟨b.encode i, b.encode_mem i⟩, ?_⟩
    change ZFSet.pair (b.encode i) (M.rawNiceNameCandidates _ _ _ _ _ _) = z
    rw [M.rawNiceNameCandidates_eq pairing unions powers separation collection a s t b K
      carrier group supports maps valid i (M.transitive nodes (b.encode_mem i))]
    exact equal.symm

theorem rawNiceVisibilityGraph_eq [OrderTop Q] (nodes : b.carrier ∈ M.sets) :
    M.rawNiceVisibilityGraph b.carrier T s.carrier t.carrier (supportBasisCode b t K)
      (a.conditionMapFamily s t) (s.encode ⊤) = M.niceVisibilityGraph a s b T K := by
  apply ZFSet.ext
  intro z
  rw [rawNiceVisibilityGraph, mem_familyCodeGraph, M.mem_niceVisibilityGraph]
  constructor
  · rintro ⟨i, equal⟩
    obtain ⟨j, eq⟩ := (b.mem_carrier i.val).1 i.property
    refine ⟨j, ?_⟩
    rw [← eq, M.rawNiceNameCandidates_eq pairing unions powers separation collection a s t b K
      carrier group supports maps valid j (M.transitive nodes (b.encode_mem j))] at equal
    rw [M.niceVisibilityName_code]
    exact equal.symm
  · rintro ⟨i, equal⟩
    refine ⟨⟨b.encode i, b.encode_mem i⟩, ?_⟩
    change ZFSet.pair (b.encode i) (ZFSet.prod (M.rawNiceNameCandidates _ _ _ _ _ _) _) = z
    rw [M.rawNiceNameCandidates_eq pairing unions powers separation collection a s t b K
      carrier group supports maps valid i (M.transitive nodes (b.encode_mem i))]
    rw [M.niceVisibilityName_code] at equal
    exact equal.symm

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRawRowAssignmentActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_rowAssignmentActionGraph :
    GroundDefinableFunction M (fun env : Fin 7 → ZFSet.{u} =>
      rowAssignmentActionGraph (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)) := by
  let v := GroundSetTerm.var M (n := 7)
  let product (x y : GroundSetTerm M 7) :=
    GroundSetTerm.app (M.definable_product pairing unions powers separation) ![x, y]
  let rowRange := GroundSetTerm.app (M.definable_doubleUnion unions) ![v 5]
  let assignmentRange := GroundSetTerm.app (M.definable_doubleUnion unions) ![v 6]
  let bound := product (product (v 0) (v 1)) (v 1)
  let formula : SetFormula 10 := (BoundedFormula.rowAssignmentActionEntryFormula 0 1 2 3 4 5 6 7 8 9).toFormula
  let term := GroundSetTerm.app (M.definable_separation separation formula)
    ![bound, v 0, v 1, v 2, v 3, v 4, rowRange, assignmentRange, v 5, v 6]
  refine { formula := term.definition.formula
           closed := fun env members => M.rowAssignmentActionGraph_mem pairing unions powers separation
             (members 0) (members 1) (members 2) (members 3) (members 4) (members 5) (members 6)
           correct := ?_ }
  intro env members z hz
  rw [term.definition.correct env members z hz]
  have args : (fun j : Fin 9 =>
      (![bound, v 0, v 1, v 2, v 3, v 4, rowRange, assignmentRange, v 5, v 6] j.succ).eval env) =
      ![env 0, env 1, env 2, env 3, env 4, ⋃₀ ⋃₀ env 5, ⋃₀ ⋃₀ env 6, env 5, env 6] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))))) j
  have equal : term.eval env = rowAssignmentActionGraph
      (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) := by
    change ZFSet.sep (fun w => Realize M.sets formula (extend w _)) (bound.eval env) = _
    rw [args]
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_sep, rowAssignmentActionGraph, ZFSet.mem_sep]
    apply and_congr_right
    intro hw
    rw [BoundedFormula.realize_toFormula M _ _
      (Fin.cases (M.transitive (bound.ground env members) hw)
        (Fin.cases (members 0) (Fin.cases (members 1) (Fin.cases (members 2)
          (Fin.cases (members 3) (Fin.cases (members 4)
            (Fin.cases (M.union_mem unions (M.union_mem unions (members 5)))
              (Fin.cases (M.union_mem unions (M.union_mem unions (members 6)))
                (Fin.cases (members 5) (Fin.cases (members 6) (fun k => Fin.elim0 k))))))))))),
      BoundedFormula.truth_rowAssignmentActionEntryFormula]
    rfl
  rw [equal]

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_rawActionMapFamily (collection : CollectionSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} => rawActionMapFamily (env 0) (env 1) (env 2)) :=
  (M.definable_rawActionSection pairing unions powers separation).definable_graph pairing separation collection

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

noncomputable def definable_rawRowAssignmentActionGraph :
    GroundDefinableFunction M (fun env : Fin 7 → ZFSet.{u} =>
      rawRowAssignmentActionGraph (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)) := by
  let v := GroundSetTerm.var M (n := 7)
  let maps := M.definable_rawActionMapFamily pairing unions powers separation collection
  let rowMaps := GroundSetTerm.app maps ![v 0, v 5, v 2]
  let assignmentMaps := GroundSetTerm.app maps ![v 0, v 6, v 4]
  exact (GroundSetTerm.app (M.definable_rowAssignmentActionGraph pairing unions powers separation)
    ![v 0, v 1, v 2, v 3, v 4, rowMaps, assignmentMaps]).definition

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRawRefinementDataIdentification
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def rawRefinementFormulaData
    (P order top actionGraph G nodes nodeOrder basis T T2 level : ZFSet.{u}) : Fin 15 → ZFSet.{u} :=
  let maps := rawActionMapFamily G actionGraph P
  let first := M.rawNiceNameCandidateGraph nodes T P G basis maps
  let second := M.rawNiceNameCandidateGraph nodes T2 P G basis maps
  let I := M.refinementIndices level nodes nodeOrder first second T T2 (ZFSet.prod T {top}) P order top
  let B1 := M.groundRelations T P
  let B2 := M.groundRelations T2 P
  let F1 := refinementIndexFieldGraph I nodes 1
  let F2 := refinementIndexFieldGraph I nodes 2
  let F3 := refinementIndexFieldGraph I B1 3
  let F4 := refinementIndexFieldGraph I B2 4
  let F5 := refinementIndexFieldGraph I B2 5
  ![I, F1, F2, F3, F4, F5, T, P, order, top, nodes, nodeOrder,
    M.refinementIndexNameGraph 2 I F3 F4 F5 T P order top,
    M.rawNiceVisibilityGraph nodes T P G basis maps top, B1]

noncomputable def rawRefinementFormulaDataCode
    (P order top actionGraph G nodes nodeOrder basis T T2 level : ZFSet.{u}) : ZFSet.{u} :=
  refinementFormulaDataCode (M.rawRefinementFormulaData P order top actionGraph G nodes nodeOrder basis T T2 level)

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
include pairing unions powers separation collection carrier group nodes supports maps valid valid2

theorem rawRefinementFormulaData_eq :
    M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t)
      t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level =
        M.refinementLevelFormulaData a s b d level T T2 valid := by
  unfold rawRefinementFormulaData
  dsimp only
  rw [rawActionMapFamily_eq,
    M.rawNiceNameCandidateGraph_eq pairing unions powers separation collection a s t b d.principalFix
      carrier group supports maps valid nodes,
    M.rawNiceNameCandidateGraph_eq pairing unions powers separation collection a s t b d.principalFix
      carrier group supports maps valid2 nodes,
    M.rawNiceVisibilityGraph_eq pairing unions powers separation collection a s t b d.principalFix
      carrier group supports maps valid nodes]
  rw [← Name.familySet_code (s := s) ⊤ T valid]
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (fun k => Fin.elim0 k))))))))))))))) j

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialMainStage
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}

noncomputable def initialBirth (stage : GroundMainStage M C D rD) : ZFSet.{u} :=
  constantFamilyGraph stage.carrier ∅

theorem initialBirth_function (stage : GroundMainStage M C D rD) :
    ZFSet.IsFunc stage.carrier (insert (∅ : ZFSet.{u}) ∅) stage.initialBirth :=
  constantFamilyGraph_function stage.carrier ∅

theorem initialBirth_entry (stage : GroundMainStage M C D rD) (x t : ZFSet.{u}) :
    ZFSet.pair x t ∈ stage.initialBirth ↔ x ∈ stage.carrier ∧ t = ∅ :=
  pair_mem_constantFamilyGraph stage.carrier ∅ x t

theorem initialBirth_ground (stage : GroundMainStage M C D rD)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    stage.initialBirth ∈ M.sets :=
  M.constantFamilyGraph_mem pairing unions powers separation stage.carrier_ground
    (M.empty_mem ⟨stage.carrier, stage.carrier_ground⟩)

theorem initialBirth_old_meet (stage : GroundMainStage M C D rD) :
    OldMeetCode stage.order stage.meetGraph stage.initialBirth := by
  intro x y z a b c _ bornX earlier
  have equal := ((stage.initialBirth_entry x b).1 bornX).2
  exact False.elim (ZFSet.notMem_empty a (equal ▸ earlier))

noncomputable def initialHistory (stage : GroundMainStage M C D rD)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (small : M.groundEmbeddable stage.carrier ZFSet.omega) :
    GroundChronologicalHistory M (insert (∅ : ZFSet.{u}) ∅) C D rD where
  space := fun _ => stage.carrier
  order := fun _ => stage.order
  meetGraph := fun _ => stage.meetGraph
  birth := fun _ => stage.initialBirth
  height := fun _ => stage.height
  space_mem := fun _ _ => stage.carrier_ground
  order_mem := fun _ _ => stage.order_ground
  meet_mem := fun _ _ => stage.meet_ground
  birth_mem := fun _ _ => stage.initialBirth_ground pairing unions powers separation
  height_mem := fun _ _ => stage.height_ground
  meet_order := fun _ _ => stage.meet
  birth_function := fun _ _ => stage.initialBirth_function
  birth_bound := by
    intro s hs x _ t entry
    have zero : s = ∅ := by simpa only [ZFSet.mem_insert_iff, ZFSet.notMem_empty,
      or_false] using hs
    exact Or.inl (((stage.initialBirth_entry x t).1 entry).2.trans zero.symm)
  old_meet := fun _ _ => stage.initialBirth_old_meet
  strict_height := fun _ _ => stage.height_code
  layer := fun _ _ _ _ _ =>
    .countablePoints stage.carrier stage.carrier_ground small (fun _ hx _ => hx)

noncomputable def initialChronological (stage : GroundMainStage M C D rD)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (small : M.groundEmbeddable stage.carrier ZFSet.omega) :
    GroundChronologicalMainStage M C D rD where
  stage := stage
  cutoff := ∅
  cutoff_ground := M.empty_mem ⟨stage.carrier, stage.carrier_ground⟩
  cutoff_ordinal := ordinalSetProperty_empty
  history := stage.initialHistory pairing unions powers separation small
  carrier_eq := rfl
  order_eq := rfl
  meet_eq := rfl
  height_eq := rfl

noncomputable def initialChronologyField (stage : GroundMainStage M C D rD) : Fin 5 → ZFSet.{u} :=
  Fin.cases stage.carrier (Fin.cases stage.order (Fin.cases stage.meetGraph
    (Fin.cases stage.initialBirth (Fin.cases stage.height Fin.elim0))))

noncomputable def initialChronologyGraph (stage : GroundMainStage M C D rD)
    (j : Fin 5) : ZFSet.{u} :=
  constantFamilyGraph (insert (∅ : ZFSet.{u}) ∅) (stage.initialChronologyField j)

theorem initialChronologyGraph_entry (stage : GroundMainStage M C D rD)
    (j : Fin 5) (t x : ZFSet.{u}) :
    ZFSet.pair t x ∈ stage.initialChronologyGraph j ↔
      t = ∅ ∧ x = stage.initialChronologyField j := by
  simp only [initialChronologyGraph, pair_mem_constantFamilyGraph,
    ZFSet.mem_insert_iff, ZFSet.notMem_empty, or_false]

theorem initialChronologyGraphs_ground (stage : GroundMainStage M C D rD)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (j : Fin 5) : stage.initialChronologyGraph j ∈ M.sets ∧
      ZFSet.IsFunc (insert (∅ : ZFSet.{u}) ∅) {stage.initialChronologyField j}
        (stage.initialChronologyGraph j) := by
  have zero := M.empty_mem ⟨stage.carrier, stage.carrier_ground⟩
  have field : stage.initialChronologyField j ∈ M.sets :=
    Fin.cases stage.carrier_ground (Fin.cases stage.order_ground (Fin.cases stage.meet_ground
      (Fin.cases (stage.initialBirth_ground pairing unions powers separation)
        (Fin.cases stage.height_ground (fun i => Fin.elim0 i))))) j
  exact ⟨M.constantFamilyGraph_mem pairing unions powers separation
    (M.insert_mem pairing unions zero zero) field, constantFamilyGraph_function _ _⟩

end GroundMainStage

namespace GroundMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD)

noncomputable def initialChronologyBound : ZFSet.{u} :=
  ZFSet.range stage.initialChronologyField

theorem mem_initialChronologyBound (x : ZFSet.{u}) :
    x ∈ stage.initialChronologyBound ↔ ∃ j : Fin 5, stage.initialChronologyField j = x :=
  ZFSet.mem_range

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem initialChronologyBound_ground : stage.initialChronologyBound ∈ M.sets := by
  apply M.finite_range_mem pairing unions ⟨stage.carrier, stage.carrier_ground⟩
  exact Fin.cases stage.carrier_ground (Fin.cases stage.order_ground (Fin.cases stage.meet_ground
    (Fin.cases (stage.initialBirth_ground pairing unions powers separation)
      (Fin.cases stage.height_ground (fun i => Fin.elim0 i)))))

noncomputable def initialGroundChronologyFields :
    GroundChronologyFields M (insert (∅ : ZFSet.{u}) ∅) where
  time_ground := M.insert_mem pairing unions
    (M.empty_mem ⟨stage.carrier, stage.carrier_ground⟩)
    (M.empty_mem ⟨stage.carrier, stage.carrier_ground⟩)
  bound := stage.initialChronologyBound
  bound_ground := stage.initialChronologyBound_ground pairing unions powers separation
  graph := stage.initialChronologyGraph
  graph_ground := fun j => (stage.initialChronologyGraphs_ground pairing unions powers separation j).1
  function := by
    intro j
    have actual := (stage.initialChronologyGraphs_ground pairing unions powers separation j).2
    refine ⟨?_, actual.2⟩
    intro z hz
    obtain ⟨s, hs, x, hx, rfl⟩ := ZFSet.mem_prod.1 (actual.1 hz)
    have equal : x = stage.initialChronologyField j := ZFSet.mem_singleton.1 hx
    exact ZFSet.pair_mem_prod.2 ⟨hs,
      (stage.mem_initialChronologyBound x).2 ⟨j, equal.symm⟩⟩

theorem initialGroundChronologyFields_value (j : Fin 5) {s : ZFSet.{u}}
    (hs : s ∈ (insert (∅ : ZFSet.{u}) ∅ : ZFSet.{u})) :
    (stage.initialGroundChronologyFields pairing unions powers separation).value j s =
      stage.initialChronologyField j := by
  apply (stage.initialGroundChronologyFields pairing unions powers separation).value_eq_of_entry j
  apply (stage.initialChronologyGraph_entry j s (stage.initialChronologyField j)).2
  exact ⟨by simpa only [ZFSet.mem_insert_iff, ZFSet.notMem_empty, or_false] using hs, rfl⟩

end GroundMainStage

namespace GroundMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem initialChronologyCore :
    ChronologyCoreCode (insert (∅ : ZFSet.{u}) ∅) stage.initialChronologyBound C D rD
      stage.initialChronologyGraph := by
  refine ⟨(stage.initialGroundChronologyFields pairing unions powers separation).function, ?_⟩
  intro s hs L r μ birth height eL er eμ eb eh
  have zero : s = ∅ := by
    simpa only [ZFSet.mem_insert_iff, ZFSet.notMem_empty, or_false] using hs
  have lEq : L = stage.carrier := ((stage.initialChronologyGraph_entry 0 s L).1 eL).2
  have rEq : r = stage.order := ((stage.initialChronologyGraph_entry 1 s r).1 er).2
  have mEq : μ = stage.meetGraph := ((stage.initialChronologyGraph_entry 2 s μ).1 eμ).2
  have bEq : birth = stage.initialBirth := ((stage.initialChronologyGraph_entry 3 s birth).1 eb).2
  have hEq : height = stage.height := ((stage.initialChronologyGraph_entry 4 s height).1 eh).2
  subst s L r μ birth height
  exact ⟨stage.meet, stage.initialBirth_function,
    fun x _ t entry => Or.inl (((stage.initialBirth_entry x t).1 entry).2),
    stage.initialBirth_old_meet, stage.height_code⟩

end GroundMainStage

namespace GroundMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {injection : ZFSet.{u}} (hInjection : injection ∈ M.sets)
variable (injected : InjectionCode stage.carrier ZFSet.omega injection)

noncomputable def initialSerializedChronology :
    GroundSerializedChronology M (insert (∅ : ZFSet.{u}) ∅) C D rD where
  fields := stage.initialGroundChronologyFields pairing unions powers separation
  ordinal := ordinalSetProperty_succ ordinalSetProperty_empty
  core := stage.initialChronologyCore pairing unions powers separation
  layerBound := {countableLayerWitness stage.carrier injection}
  layer_bound_ground := by
    have ground := M.countableLayerWitness_mem pairing stage.carrier_ground hInjection
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing ground ground
  layers := constantFamilyGraph (chronologyPairs (insert (∅ : ZFSet.{u}) ∅))
    (countableLayerWitness stage.carrier injection)
  layers_ground := M.constantFamilyGraph_mem pairing unions powers separation
    (M.chronologyPairs_mem pairing unions powers separation
      (stage.initialGroundChronologyFields pairing unions powers separation).time_ground)
    (M.countableLayerWitness_mem pairing stage.carrier_ground hInjection)
  layer_function := constantFamilyGraph_function _ _
  layer_code := by
    intro s hs t _ _ z entry
    have equal : z = countableLayerWitness stage.carrier injection :=
      ((pair_mem_constantFamilyGraph _ _ _ _).1 entry).2
    refine Or.inl ⟨stage.carrier, injection, equal, injected, ?_⟩
    intro x hx _
    have carrier : (stage.initialGroundChronologyFields pairing unions powers separation).value
        0 s = stage.carrier :=
      stage.initialGroundChronologyFields_value pairing unions powers separation 0 hs
    exact carrier ▸ hx

end GroundMainStage

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_SerializedChronologyCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace SerializedChronologyCode
variable {M : TransitiveGround.{u}} {T V C D rD N W layers : ZFSet.{u}}
variable {graphs : Fin 5 → ZFSet.{u}}

noncomputable def toGround (code : SerializedChronologyCode T V C D rD N graphs W layers)
    (hT : T ∈ M.sets) (hV : V ∈ M.sets) (hGraphs : ∀ j, graphs j ∈ M.sets)
    (hW : W ∈ M.sets) (hLayers : layers ∈ M.sets) (omega : N = ZFSet.omega) :
    GroundSerializedChronology M T C D rD where
  fields := ⟨hT, V, hV, graphs, hGraphs, code.core.function⟩
  ordinal := code.ordinal
  core := code.core
  layerBound := W
  layer_bound_ground := hW
  layers := layers
  layers_ground := hLayers
  layer_function := code.function
  layer_code := by
    intro s hs t ht earlier z entry
    let fields : GroundChronologyFields M T := ⟨hT, V, hV, graphs, hGraphs, code.core.function⟩
    exact omega ▸ code.entries s hs t ht earlier _ _ _ _ z
      (fields.value_entry 0 hs) (fields.value_entry 1 hs)
      (fields.value_entry 2 hs) (fields.value_entry 3 hs) entry

end SerializedChronologyCode

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PreparedCertificateCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing
open SetFormula
universe u

def PreparedCertificateCode (M : TransitiveGround.{u})
    (P order q nodes nodeOrder meet N visibility top omega z F B f e names : ZFSet.{u}) : Prop :=
  MeetFilterCode nodes nodeOrder meet F ∧
  CoinitialBelowCode nodeOrder F F B ∧ B.Nonempty ∧
  SynchronizedEnumerationCode omega N B f e names ∧
  (∀ v tau, ZFSet.pair v tau ∈ f →
    ZFSet.pair v tau ∈ visibilitySupportIncidence nodes N visibility top) ∧
  PreparationForcingCode M P order q nodes visibility z F f

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialMainSeedSuccessorSerialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.GroundSerializedChronology
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {s C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M (insert s s) C D rD)

noncomputable def fixedTopValues (newHeight : ZFSet.{u}) : Fin 5 → ZFSet.{u} :=
  Fin.cases (fixedTopCarrier (serial.fields.value 0 s))
    (Fin.cases (fixedTopOrder (serial.fields.value 0 s) (serial.fields.value 1 s))
      (Fin.cases (fixedTopMeet (serial.fields.value 0 s) (serial.fields.value 1 s))
        (Fin.cases (fixedTopBirth (serial.fields.value 0 s) (serial.fields.value 3 s) s)
          (fun _ => newHeight))))

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (newHeight : ZFSet.{u}) (hHeight : newHeight ∈ M.sets)
include pairing unions powers separation hHeight

theorem fixedTopValues_ground : ∀ j, serial.fixedTopValues newHeight j ∈ M.sets := by
  have hP := serial.fields.value_ground 0 s
  have hr := serial.fields.value_ground 1 s
  have hs := M.transitive serial.fields.time_ground (ZFSet.mem_insert s s)
  exact Fin.cases (M.fixedTopCarrier_mem pairing unions hP)
    (Fin.cases (M.fixedTopOrder_mem pairing unions powers separation hP hr)
      (Fin.cases (M.fixedTopMeet_mem pairing unions powers separation hP hr)
        (Fin.cases (M.fixedTopBirth_mem pairing unions hP (serial.fields.value_ground 3 s) hs)
          (fun _ => hHeight))))

noncomputable def fixedTopFields : GroundChronologyFields M (insert s s) :=
  serial.fields.replaceTerminal pairing unions separation (serial.fixedTopValues newHeight)
    (serial.fixedTopValues_ground pairing unions powers separation newHeight hHeight)

end PartitionPilot.Forcing.GroundSerializedChronology



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundSerializedBoundNormalization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundSerializedChronology
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M T C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets)

noncomputable def normalizeBounds : GroundSerializedChronology M T C D rD where
  fields := serial.fields.normalizeBound pairing unions separation
  ordinal := serial.ordinal
  core := serial.fields.normalizeBound_core pairing unions separation serial.core
  layerBound := functionGraphRange (chronologyPairs T) serial.layers
  layer_bound_ground := M.functionGraphRange_mem unions separation
    (M.chronologyPairs_mem pairing unions powers separation serial.fields.time_ground)
    serial.layers_ground
  layers := serial.layers
  layers_ground := serial.layers_ground
  layer_function := functionGraphRange_function ⟨serial.layerBound, serial.layer_function⟩
  layer_code := serial.layer_code

end PartitionPilot.Forcing.GroundSerializedChronology

end

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
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def supportedEqualityCertificateBound (nodes N : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod (M.groundPower nodes)
    (ZFSet.prod (M.groundSmallSubsets nodes ZFSet.omega) (M.groundRelations nodes N))

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCertificateProfileImageFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def synchronizedEnumerationBound (nodes N : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod (M.groundRelations ZFSet.omega nodes) (M.groundRelations ZFSet.omega N)

noncomputable def certificateEnumerationRelation (J nodes N k : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ j ∈ J, ∃ e ∈ M.groundRelations ZFSet.omega nodes,
    ∃ names ∈ M.groundRelations ZFSet.omega N,
      z = ZFSet.pair j (ZFSet.pair e names) ∧
      ∃ F B f, ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧
        SynchronizedEnumerationCode ZFSet.omega N B f e names)
    (ZFSet.prod J (M.synchronizedEnumerationBound nodes N))

end TransitiveGround

section
open SetFormula
universe u

def PreparedCertificateFamilyCode (M : TransitiveGround.{u})
    (P order q nodes nodeOrder meet N visibility top omega J C E k enumerations : ZFSet.{u}) : Prop :=
  ZFSet.IsFunc J C k ∧ ZFSet.IsFunc J E enumerations ∧
  ∀ z F B f e names, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
    ZFSet.pair z (ZFSet.pair e names) ∈ enumerations →
    PreparedCertificateCode M P order q nodes nodeOrder meet N visibility top omega z F B f e names

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def certificateProfileGraph (J nodes W k : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose J (M.supportedEqualityCertificateBound nodes W) (M.groundPower nodes) k
    (productFirst (M.groundPower nodes)
      (ZFSet.prod (M.groundSmallSubsets nodes ZFSet.omega) (M.groundRelations nodes W)))

noncomputable def certificateProfileImage (J nodes W k : ZFSet.{u}) : ZFSet.{u} :=
  relationImage J (M.groundPower nodes) (M.certificateProfileGraph J nodes W k)

noncomputable def certificateProfileImageFamily (nodes W : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph
    (fun k : M.groundRelations W (M.supportedEqualityCertificateBound nodes W) => k.val)
    (fun k => M.certificateProfileImage W nodes W k.val)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNicePreparationWitnessBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def preparationWitnessBound (nodes T Q : ZFSet.{u}) : ZFSet.{u} :=
  let W := M.groundRelations T Q
  ZFSet.prod Q (ZFSet.prod
    (M.groundRelations W (M.supportedEqualityCertificateBound nodes W))
    (M.groundRelations W (M.synchronizedEnumerationBound nodes W)))

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RefinementIndexActionFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def refinementIndexActionRawFormula {n}
    (x y g P maps nodeMaps : Fin n) (w : Fin 13 → Fin n) : SetFormula n :=
  .conj (BoundedFormula.nonemptyTupleFormula 5 x (fun j => w (j.castAdd 7))).toFormula
  (.conj (BoundedFormula.nonemptyTupleFormula 5 y (fun j => w ((Fin.natAdd 6 j).castAdd 1))).toFormula
  (.conj (.equal (w 0) (w 6))
  (.conj (pairMembershipFormula g (w 12) nodeMaps)
  (.conj (pairMembershipFormula (w 1) (w 7) (w 12))
  (.conj (pairMembershipFormula (w 2) (w 8) (w 12))
  (.conj (atomicApplication nameActionFormula (extend P (extend maps Fin.elim0)) g (w 3) (w 9))
  (.conj (atomicApplication nameActionFormula (extend P (extend maps Fin.elim0)) g (w 4) (w 10))
    (atomicApplication nameActionFormula (extend P (extend maps Fin.elim0)) g (w 5) (w 11)))))))))

def refinementIndexActionFormula {n} (x y g P maps nodeMaps : Fin n) : SetFormula n :=
  let old := suffixIndex n 13
  exBlock 13 (refinementIndexActionRawFormula (old x) (old y) (old g) (old P)
    (old maps) (old nodeMaps) (prefixIndex n 13))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_refinementIndexActionRawFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (x y g P maps nodeMaps : Fin n) (w : Fin 13 → Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (refinementIndexActionRawFormula x y g P maps nodeMaps w) env ↔
      env x = nonemptyTupleCode 5 (fun j => env (w (j.castAdd 7))) ∧
      env y = nonemptyTupleCode 5 (fun j => env (w ((Fin.natAdd 6 j).castAdd 1))) ∧
      env (w 0) = env (w 6) ∧ ZFSet.pair (env g) (env (w 12)) ∈ env nodeMaps ∧
      ZFSet.pair (env (w 1)) (env (w 7)) ∈ env (w 12) ∧
      ZFSet.pair (env (w 2)) (env (w 8)) ∈ env (w 12) ∧
      Realize M.sets nameActionFormula (extend (env g) (extend (env (w 3))
        (extend (env (w 9)) (extend (env P) (extend (env maps) Fin.elim0))))) ∧
      Realize M.sets nameActionFormula (extend (env g) (extend (env (w 4))
        (extend (env (w 10)) (extend (env P) (extend (env maps) Fin.elim0))))) ∧
      Realize M.sets nameActionFormula (extend (env g) (extend (env (w 5))
        (extend (env (w 11)) (extend (env P) (extend (env maps) Fin.elim0))))) := by
  simp only [refinementIndexActionRawFormula, Realize,
    BoundedFormula.realize_toFormula M _ env members, BoundedFormula.truth_nonemptyTupleFormula,
    M.realize_pairMembershipFormula pairing _ _ _ env (members _) (members _) (members _),
    realize_atomicApplication, map_extend, map_empty]

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNiceRefinementIndexActionLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)

include pairing unions powers separation collection carrier order maps in
theorem niceRefinementIndex_act_iff (level T1 T2 : ZFSet.{u})
    (valid : ∀ z ∈ T1, IsName s z)
    (closed1 : ∀ g (w : Name s), w.val ∈ T1 → (a.act s g w).val ∈ T1)
    (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
    (familyGround : (Name.familySet ⊤ T1 valid).val ∈ M.sets)
    (g : G) (C E : L) (U Rf Rc : (M.nameDomain s).names) :
    refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val ∈
        M.niceRefinementIndices a s b d level T1 T2 valid ↔
      refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices a s b d level T1 T2 valid := by
  let groundClosed := fun g (w : Name s) (hw : w ∈ (M.nameDomain s).names) =>
    M.act_mem s a t pairing unions powers separation collection carrier maps g w hw
  let moved := a.domainEquiv s (M.nameDomain s) groundClosed g
  let whole : (M.nameDomain s).names := ⟨Name.familySet ⊤ T1 valid, familyGround⟩
  let env := extend U (extend Rf (extend Rc (extend whole Fin.elim0)))
  have sameWhole : moved whole = whole :=
    Subtype.ext (Name.act_familySet a T1 valid closed1 g)
  have envEq : a.actAssignment s (M.nameDomain s) groundClosed g env =
      extend (moved U) (extend (moved Rf) (extend (moved Rc) (extend whole Fin.elim0))) := by
    funext j
    refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases ?_
      (fun k => Fin.elim0 k)))) j
    exact sameWhole
  have force := a.formula_forces_act_iff s (M.nameDomain s) groundClosed g
    BoundedFormula.refinementValidityFormula.toFormula env ⊤
  rw [(a.iso g).map_top, envEq] at force
  change refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (moved U).val.val (moved Rf).val.val (moved Rc).val.val ∈
        M.niceRefinementIndices a s b d level T1 T2 valid ↔ _
  rw [M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation collection
      carrier order level T1 T2 valid familyGround (d.iso g C) (d.iso g E)
      (moved U) (moved Rf) (moved Rc),
    M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation collection
      carrier order level T1 T2 valid familyGround C E U Rf Rc]
  exact and_congr (d.iso g).lt_iff_lt
    (and_congr (M.niceNameCandidates_principal_act_iff a s t pairing unions powers separation
      collection carrier maps closed1 d g C U.val)
    (and_congr (M.niceNameCandidates_principal_act_iff a s t pairing unions powers separation
      collection carrier maps closed2 d g C Rf.val)
    (and_congr (M.niceNameCandidates_principal_act_iff a s t pairing unions powers separation
      collection carrier maps closed2 d g C Rc.val) force)))

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u}
variable [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)

noncomputable def stageOneNameAction (g : G) : (M.nameDomain s).names ≃ (M.nameDomain s).names :=
  a.domainEquiv s (M.nameDomain s)
    (fun g w hw => M.act_mem s a t pairing unions powers separation collection carrier maps g w hw) g

theorem stageOneNameAction_val (g : G) (w : (M.nameDomain s).names) :
    (M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g w).val =
      a.act s g w.val := rfl

theorem stageOneNameAction_forces_iff (g : G) {n : Nat} (φ : SetFormula n)
    (env : Assignment (M.nameDomain s) n) (p : P) :
    Forces (M.nameDomain s) φ
      (fun j => M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g (env j))
      (a.iso g p) ↔ Forces (M.nameDomain s) φ env p :=
  a.formula_forces_act_iff s (M.nameDomain s)
    (fun g w hw => M.act_mem s a t pairing unions powers separation collection carrier maps g w hw)
    g φ env p

variable [OrderTop P] (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)

include closed in
theorem stageOneNameAction_class (g : G) (R w : (M.nameDomain s).names) :
    M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g
      (M.stageOneClassName s pairing unions powers separation collection carrier order hT valid R w) =
    M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
      (M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g R)
      (M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g w) :=
  Subtype.ext (Name.act_refinementClass a T valid closed g R.val w.val)

include closed in
theorem stageOneNameAction_map (g : G) (U Rf Rc : (M.nameDomain s).names) :
    M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g
      (M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc) =
    M.stageOneMapName s pairing unions powers separation collection carrier order hT valid
      (M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g U)
      (M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g Rf)
      (M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g Rc) :=
  Subtype.ext (Name.act_refinementNaturalMap a T valid closed g U.val Rf.val Rc.val)

variable {L : Type u} [PartialOrder L]
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem stageOneNameAction_visibility (system : NiceNameSystem M a s b d base directed T valid)
    (g : G) (v : L) :
    M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g
      (M.stageOneVisibilityName s valid a b d base directed system v) =
      M.stageOneVisibilityName s valid a b d base directed system (d.iso g v) :=
  Subtype.ext (system.visibility_action g v)

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "move" => M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
local notation "cls" => M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
local notation "vis" => M.stageOneVisibilityName s valid a b d base directed system
local notation "mapName" => M.stageOneMapName s pairing unions powers separation collection carrier order hT valid

omit [OrderTop P] in
theorem stageOneActivity_act_iff (g : G) (U u w : (M.nameDomain s).names) (p : P) :
    Forces (M.nameDomain s) refinementActivityFormula ![move g u, move g w, move g U] (a.iso g p) ↔
      Forces (M.nameDomain s) refinementActivityFormula ![u, w, U] p := by
  have envEq : (fun j => move g (![u, w, U] j)) =
      ![move g u, move g w, move g U] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j
  have law := M.stageOneNameAction_forces_iff a s t pairing unions powers separation collection
    carrier maps g refinementActivityFormula ![u, w, U] p
  rw [envEq] at law
  exact law

include closed in
theorem stageOneProfile_act_iff (g : G) (Rc Rf u w : (M.nameDomain s).names) (v : L) (p : P) :
    Forces (M.nameDomain s) refinementProfileFormula ![cls (move g Rc) (move g u), cls (move g Rf) (move g w), vis (d.iso g v)] (a.iso g p) ↔
      Forces (M.nameDomain s) refinementProfileFormula ![cls Rc u, cls Rf w, vis v] p := by
  have envEq : (fun j => move g (![cls Rc u, cls Rf w, vis v] j)) =
      ![cls (move g Rc) (move g u), cls (move g Rf) (move g w), vis (d.iso g v)] := by
    funext j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) j
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
    · exact M.stageOneNameAction_visibility a s t pairing unions powers separation collection carrier maps valid b d base directed system g _
  have law := M.stageOneNameAction_forces_iff a s t pairing unions powers separation collection
    carrier maps g refinementProfileFormula ![cls Rc u, cls Rf w, vis v] p
  rw [envEq] at law
  exact law

include closed in
theorem stageOneCompatibility_act_iff (g : G) (U Rf Rc u w : (M.nameDomain s).names) (C : L) (p : P) :
    Forces (M.nameDomain s) refinementCompatibilityFormula ![cls (move g Rf) (move g w), vis (d.iso g C), cls (move g Rc) (move g u), mapName (move g U) (move g Rf) (move g Rc)] (a.iso g p) ↔
      Forces (M.nameDomain s) refinementCompatibilityFormula ![cls Rf w, vis C, cls Rc u, mapName U Rf Rc] p := by
  have envEq : (fun j => move g (![cls Rf w, vis C, cls Rc u, mapName U Rf Rc] j)) =
      ![cls (move g Rf) (move g w), vis (d.iso g C), cls (move g Rc) (move g u), mapName (move g U) (move g Rf) (move g Rc)] := by
    funext j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))) j
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
    · exact M.stageOneNameAction_visibility a s t pairing unions powers separation collection carrier maps valid b d base directed system g _
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
    · exact M.stageOneNameAction_map a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _ _
  have law := M.stageOneNameAction_forces_iff a s t pairing unions powers separation collection
    carrier maps g refinementCompatibilityFormula ![cls Rf w, vis C, cls Rc u, mapName U Rf Rc] p
  rw [envEq] at law
  exact law

include closed in
theorem stageOneCollisionTest_act_iff (g : G) (Rf Rc u u' w w' : (M.nameDomain s).names) (p : P) :
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      (move g Rf) (move g Rc) (move g u) (move g u') (move g w) (move g w') (a.iso g p) ↔
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid Rf Rc u u' w w' p := by
  change Forces (M.nameDomain s) refinementCollisionFormula ![cls (move g Rc) (move g u), cls (move g Rc) (move g u'), cls (move g Rf) (move g w), cls (move g Rf) (move g w')] (a.iso g p) ↔
    Forces (M.nameDomain s) refinementCollisionFormula ![cls Rc u, cls Rc u', cls Rf w, cls Rf w'] p
  have envEq : (fun j => move g (![cls Rc u, cls Rc u', cls Rf w, cls Rf w'] j)) =
      ![cls (move g Rc) (move g u), cls (move g Rc) (move g u'), cls (move g Rf) (move g w), cls (move g Rf) (move g w')] := by
    funext j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))) j
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
  have law := M.stageOneNameAction_forces_iff a s t pairing unions powers separation collection
    carrier maps g refinementCollisionFormula ![cls Rc u, cls Rc u', cls Rf w, cls Rf w'] p
  rw [envEq] at law
  exact law

include closed in
theorem stageOneSingleTests_act_iff (g : G) (C E : L)
    (U Rf Rc u w : (M.nameDomain s).names) (p : P) :
    M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system (d.iso g C) (d.iso g E)
        (move g U) (move g Rf) (move g Rc) (move g u) (move g w) (a.iso g p) ↔
    M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system C E U Rf Rc u w p := by
  have activity := M.stageOneActivity_act_iff a s t pairing unions powers separation collection
    carrier maps g U u w p
  have compatible := M.stageOneCompatibility_act_iff a s t pairing unions powers separation collection
    carrier order maps hT valid closed b d base directed system g U Rf Rc u w C p
  have profile := fun v => M.stageOneProfile_act_iff a s t pairing unions powers separation collection
    carrier order maps hT valid closed b d base directed system g Rc Rf u w v p
  constructor
  · intro tests
    refine ⟨activity.mp tests.1, ?_, compatible.mp tests.2.2⟩
    intro v above
    exact (profile v).mp (tests.2.1 (d.iso g v) ((d.iso g).monotone above))
  · intro tests
    refine ⟨activity.mpr tests.1, ?_, compatible.mpr tests.2.2⟩
    intro v above
    obtain ⟨v, rfl⟩ := (d.iso g).surjective v
    exact (profile v).mpr (tests.2.1 v ((d.iso g).le_iff_le.mp above))

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T1 T2 : ZFSet.{u})
variable (valid1 : ∀ z ∈ T1, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)

theorem niceRefinementIndexActionGraph_entry (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (closed1 : ∀ g (w : Name s), w.val ∈ T1 → (a.act s g w).val ∈ T1)
    (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
    (familyGround : (Name.familySet ⊤ T1 valid1).val ∈ M.sets)
    (g : G) (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (source : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T1 T2 valid1) (y : ZFSet.{u}) :
    ZFSet.pair (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) y ∈
      M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g ↔
    y = refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val := by
  have input := ((M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation collection
    carrier order level T1 T2 valid1 familyGround C E U Rf Rc).1 source)
  have hU := M.niceNameCandidates_subset a s T1 _ input.2.1
  have hf := M.niceNameCandidates_subset a s T2 _ input.2.2.1
  have hc := M.niceNameCandidates_subset a s T2 _ input.2.2.2.1
  have domainValid : ∀ z ∈ M.groundRelations T1 s.carrier, IsName s z :=
    fun z hz => Name.isName_of_subset valid1 ((M.mem_groundRelations T1 s.carrier z).1 hz).2
  have relationValid : ∀ z ∈ M.groundRelations T2 s.carrier, IsName s z :=
    fun z hz => Name.isName_of_subset valid2 ((M.mem_groundRelations T2 s.carrier z).1 hz).2
  constructor
  · intro entry
    have target := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 entry).1).2
    obtain ⟨C', E', U', Rf', Rc', rfl⟩ :=
      M.exists_niceRefinementIndex_fields a s b d level T1 T2 valid1 valid2 target
    have coordinates := ((M.pair_mem_niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g
      ![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val]
      ![level, b.encode C', b.encode E', U'.val.val, Rf'.val.val, Rc'.val.val]).1 entry).2.2
    have nodeC := (b.pair_mem_graph b (d.iso g) C C').1 (coordinates 1)
    have nodeE := (b.pair_mem_graph b (d.iso g) E E').1 (coordinates 2)
    have domain := ((Name.pair_mem_renameFamilyGraph s (a.iso g) _ domainValid U.val U'.val.val).1
      (coordinates 3)).2
    have fine := ((Name.pair_mem_renameFamilyGraph s (a.iso g) _ relationValid Rf.val Rf'.val.val).1
      (coordinates 4)).2
    have coarse := ((Name.pair_mem_renameFamilyGraph s (a.iso g) _ relationValid Rc.val Rc'.val.val).1
      (coordinates 5)).2
    rw [← nodeC, ← nodeE, domain, fine, coarse]
    rfl
  · rintro rfl
    apply (M.pair_mem_niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g
      ![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val]
      ![level, b.encode (d.iso g C), b.encode (d.iso g E), (a.act s g U.val).val,
        (a.act s g Rf.val).val, (a.act s g Rc.val).val]).2
    refine ⟨source, (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
      carrier order maps level T1 T2 valid1 closed1 closed2 familyGround g C E U Rf Rc).2 source, ?_⟩
    refine Fin.cases ((pair_mem_identityFunctionGraph {level} level level).2
      ⟨rfl, ZFSet.mem_singleton.2 rfl⟩) (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
        (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))))))
    · exact (b.pair_mem_graph b (d.iso g) C _).2 rfl
    · exact (b.pair_mem_graph b (d.iso g) E _).2 rfl
    · exact (Name.pair_mem_renameFamilyGraph s (a.iso g) _ domainValid U.val _).2 ⟨hU, rfl⟩
    · exact (Name.pair_mem_renameFamilyGraph s (a.iso g) _ relationValid Rf.val _).2 ⟨hf, rfl⟩
    · exact (Name.pair_mem_renameFamilyGraph s (a.iso g) _ relationValid Rc.val _).2 ⟨hc, rfl⟩

theorem niceRefinementIndexActionGraph_function (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (closed1 : ∀ g (w : Name s), w.val ∈ T1 → (a.act s g w).val ∈ T1)
    (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
    (familyGround : (Name.familySet ⊤ T1 valid1).val ∈ M.sets) (g : G) :
    ZFSet.IsFunc (M.niceRefinementIndices a s b d level T1 T2 valid1)
      (M.niceRefinementIndices a s b d level T1 T2 valid1)
      (M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d level T1 T2 valid1 valid2 hx
  have meaning := M.niceRefinementIndexActionGraph_entry a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier order maps closed1 closed2 familyGround
    g C E U Rf Rc hx
  exact ⟨_, (meaning _).2 rfl, fun y hy => (meaning y).1 hy⟩

end

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T1 T2 : ZFSet.{u})
variable (valid1 : ∀ z ∈ T1, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (closed1 : ∀ g (w : Name s), w.val ∈ T1 → (a.act s g w).val ∈ T1)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T1 valid1).val ∈ M.sets)
local notation "I" => M.niceRefinementIndices a s b d level T1 T2 valid1
local notation "graph" => M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2
include pairing unions powers separation collection carrier order maps closed1 closed2 familyGround

theorem inverse_edge (g : G) {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ graph g) : ZFSet.pair y x ∈ graph g⁻¹ := by
  have shape := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 entry).1
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d level T1 T2 valid1 valid2 shape.1
  have equal := (M.niceRefinementIndexActionGraph_entry a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier order maps closed1 closed2 familyGround
    g C E U Rf Rc shape.1 y).1 entry
  subst y
  let move (w : (M.nameDomain s).names) : (M.nameDomain s).names :=
    ⟨a.act s g w.val, M.act_mem s a t pairing unions powers separation collection carrier maps g w.val w.property⟩
  apply (M.niceRefinementIndexActionGraph_entry a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier order maps closed1 closed2 familyGround
    g⁻¹ (d.iso g C) (d.iso g E) (move U) (move Rf) (move Rc) shape.2 _).2
  change refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val =
    refinementIndexCode level (b.encode (d.iso g⁻¹ (d.iso g C))) (b.encode (d.iso g⁻¹ (d.iso g E)))
      (a.act s g⁻¹ (a.act s g U.val)).val (a.act s g⁻¹ (a.act s g Rf.val)).val
      (a.act s g⁻¹ (a.act s g Rc.val)).val
  rw [a.act_inv_left, a.act_inv_left, a.act_inv_left, ← d.mul, ← d.mul, inv_mul_cancel,
    d.one, d.one]

theorem niceRefinementIndexActionGraph_inverse_iff (g : G) (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ graph g ↔ ZFSet.pair y x ∈ graph g⁻¹ := by
  constructor
  · exact M.inverse_edge a s b d level T1 T2 valid1 valid2 t pairing unions powers separation
      collection carrier order maps closed1 closed2 familyGround g
  · intro entry
    simpa only [inv_inv] using M.inverse_edge a s b d level T1 T2 valid1 valid2 t pairing unions powers separation
      collection carrier order maps closed1 closed2 familyGround g⁻¹ entry

theorem niceRefinementIndexActionGraph_injection (g : G) : InjectionCode I I (graph g) := by
  refine ⟨M.niceRefinementIndexActionGraph_function a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier order maps closed1 closed2 familyGround g, ?_⟩
  intro x y z first second
  have back := M.niceRefinementIndexActionGraph_function a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier order maps closed1 closed2 familyGround g⁻¹
  have zx := (M.niceRefinementIndexActionGraph_inverse_iff a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier order maps closed1 closed2 familyGround g x z).1 first
  have zy := (M.niceRefinementIndexActionGraph_inverse_iff a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier order maps closed1 closed2 familyGround g y z).1 second
  obtain ⟨v, _, unique⟩ := back.2 z (ZFSet.pair_mem_prod.1 (back.1 zx)).1
  exact (unique x zx).trans (unique y zy).symm

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRefinementAssignmentActionFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)

theorem realize_refinementIndexActionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets) (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (level : ZFSet.{u}) (hl : level ∈ M.sets) (g : G) (C E C' E' : L)
    (U Rf Rc U' Rf' Rc' : (M.nameDomain s).names) :
    Realize M.sets (refinementIndexActionFormula 0 1 2 3 4 5)
      ![refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val,
        refinementIndexCode level (b.encode C') (b.encode E') U'.val.val Rf'.val.val Rc'.val.val,
        t.encode g, s.carrier, a.conditionMapFamily s t, d.conditionMapFamily b t] ↔
      d.iso g C = C' ∧ d.iso g E = E' ∧ a.act s g U.val = U'.val ∧
        a.act s g Rf.val = Rf'.val ∧ a.act s g Rc.val = Rc'.val := by
  let oldFields : Fin 6 → ZFSet.{u} := ![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val]
  let newFields : Fin 6 → ZFSet.{u} := ![level, b.encode C', b.encode E', U'.val.val, Rf'.val.val, Rc'.val.val]
  have groundNodes (c : L) := M.transitive nodes (b.encode_mem c)
  have oldGround : ∀ j, oldFields j ∈ M.sets :=
    Fin.cases hl (Fin.cases (groundNodes C) (Fin.cases (groundNodes E)
      (Fin.cases U.property (Fin.cases Rf.property (Fin.cases Rc.property (fun j => Fin.elim0 j))))))
  have newGround : ∀ j, newFields j ∈ M.sets :=
    Fin.cases hl (Fin.cases (groundNodes C') (Fin.cases (groundNodes E')
      (Fin.cases U'.property (Fin.cases Rf'.property (Fin.cases Rc'.property (fun j => Fin.elim0 j))))))
  let env : Fin 6 → ZFSet.{u} := ![nonemptyTupleCode 5 oldFields, nonemptyTupleCode 5 newFields,
    t.encode g, s.carrier, a.conditionMapFamily s t, d.conditionMapFamily b t]
  have envGround : ∀ j, env j ∈ M.sets :=
    Fin.cases (M.nonemptyTupleCode_mem pairing 5 oldFields oldGround)
      (Fin.cases (M.nonemptyTupleCode_mem pairing 5 newFields newGround)
      (Fin.cases (M.transitive group (t.encode_mem g)) (Fin.cases carrier
      (Fin.cases maps (Fin.cases nodeMaps (fun j => Fin.elim0 j))))))
  change Realize M.sets (refinementIndexActionFormula 0 1 2 3 4 5) env ↔ _
  rw [refinementIndexActionFormula, realize_exBlock]
  have raw (w : Fin 13 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :=
    M.realize_refinementIndexActionRawFormula pairing
      (suffixIndex 6 13 0) (suffixIndex 6 13 1) (suffixIndex 6 13 2)
      (suffixIndex 6 13 3) (suffixIndex 6 13 4) (suffixIndex 6 13 5)
      (prefixIndex 6 13) (extendMany 13 w env) (extendMany_members 13 w env ground envGround)
  simp only [extendMany_prefix, extendMany_suffix] at raw
  constructor
  · rintro ⟨w, ground, formula⟩
    obtain ⟨oldEq, newEq, _, nodeEntry, ce, ee, ue, fe, re⟩ := (raw w ground).1 formula
    have oldAt (j : Fin 6) : w (j.castAdd 7) = oldFields j :=
      (congrFun (nonemptyTupleCode_injective 5 oldEq) j).symm
    have newAt (j : Fin 6) : w ((Fin.natAdd 6 j).castAdd 1) = newFields j :=
      (congrFun (nonemptyTupleCode_injective 5 newEq) j).symm
    have graphEq := (d.pair_mem_conditionMapFamily b t g (w 12)).1 nodeEntry
    have cEq : w 1 = b.encode C := oldAt 1
    have eEq : w 2 = b.encode E := oldAt 2
    have uEq : w 3 = U.val.val := oldAt 3
    have fEq : w 4 = Rf.val.val := oldAt 4
    have rEq : w 5 = Rc.val.val := oldAt 5
    have cEq' : w 7 = b.encode C' := newAt 1
    have eEq' : w 8 = b.encode E' := newAt 2
    have uEq' : w 9 = U'.val.val := newAt 3
    have fEq' : w 10 = Rf'.val.val := newAt 4
    have rEq' : w 11 = Rc'.val.val := newAt 5
    rw [cEq, cEq', graphEq] at ce
    rw [eEq, eEq', graphEq] at ee
    rw [uEq, uEq'] at ue
    rw [fEq, fEq'] at fe
    rw [rEq, rEq'] at re
    exact ⟨(b.pair_mem_graph b (d.iso g) C C').1 ce,
      (b.pair_mem_graph b (d.iso g) E E').1 ee,
      (M.realize_nameActionFormula a s t pairing unions powers separation collection
        carrier group maps g U.val U'.val U.property U'.property).1 ue,
      (M.realize_nameActionFormula a s t pairing unions powers separation collection
        carrier group maps g Rf.val Rf'.val Rf.property Rf'.property).1 fe,
      (M.realize_nameActionFormula a s t pairing unions powers separation collection
        carrier group maps g Rc.val Rc'.val Rc.property Rc'.property).1 re⟩
  · rintro ⟨ce, ee, ue, fe, re⟩
    let w : Fin 13 → ZFSet.{u} := ![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val,
      level, b.encode C', b.encode E', U'.val.val, Rf'.val.val, Rc'.val.val, b.graph b (d.iso g)]
    have ground : ∀ j, w j ∈ M.sets :=
      Fin.cases hl (Fin.cases (groundNodes C) (Fin.cases (groundNodes E)
      (Fin.cases U.property (Fin.cases Rf.property (Fin.cases Rc.property
      (Fin.cases hl (Fin.cases (groundNodes C') (Fin.cases (groundNodes E')
      (Fin.cases U'.property (Fin.cases Rf'.property (Fin.cases Rc'.property
      (Fin.cases (M.conditionMap_graph_mem d b t nodeMaps g) (fun j => Fin.elim0 j)))))))))))))
    refine ⟨w, ground, (raw w ground).2 ⟨?_, ?_, rfl,
      (d.pair_mem_conditionMapFamily b t g _).2 rfl,
      (b.pair_mem_graph b (d.iso g) C C').2 ce,
      (b.pair_mem_graph b (d.iso g) E E').2 ee, ?_, ?_, ?_⟩⟩
    · apply congrArg (nonemptyTupleCode 5)
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) j
    · apply congrArg (nonemptyTupleCode 5)
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) j
    · exact (M.realize_nameActionFormula a s t pairing unions powers separation collection
        carrier group maps g U.val U'.val U.property U'.property).2 ue
    · exact (M.realize_nameActionFormula a s t pairing unions powers separation collection
        carrier group maps g Rf.val Rf'.val Rf.property Rf'.property).2 fe
    · exact (M.realize_nameActionFormula a s t pairing unions powers separation collection
        carrier group maps g Rc.val Rc'.val Rc.property Rc'.property).2 re

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace SetFormula

def refinementIndexActionEntryFormula : SetFormula 6 :=
  .ex (.ex (.conj (.mem 1 4) (.conj (.mem 0 4)
    (.conj (orderedPairFormula 2 1 0)
      (reindex ![1, 0, 3, 5, 6, 7] (refinementIndexActionFormula 0 1 2 3 4 5))))))

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets) (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (level T1 T2 : ZFSet.{u}) (hl : level ∈ M.sets)
variable (valid1 : ∀ z ∈ T1, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (closed1 : ∀ g (w : Name s), w.val ∈ T1 → (a.act s g w).val ∈ T1)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T1 valid1).val ∈ M.sets)
variable (indexGround : M.niceRefinementIndices a s b d level T1 T2 valid1 ∈ M.sets)
include pairing unions powers separation collection carrier group nodes order maps nodeMaps hl closed1 closed2 familyGround indexGround

theorem realize_refinementIndexActionEntryFormula (g : G) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets refinementIndexActionEntryFormula
      ![z, t.encode g, M.niceRefinementIndices a s b d level T1 T2 valid1,
        s.carrier, a.conditionMapFamily s t, d.conditionMapFamily b t] ↔
      z ∈ M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g := by
  let I := M.niceRefinementIndices a s b d level T1 T2 valid1
  have action (x y : ZFSet.{u}) (hx : x ∈ I) (hy : y ∈ I) :
      Realize M.sets (refinementIndexActionFormula 0 1 2 3 4 5)
        ![x, y, t.encode g, s.carrier, a.conditionMapFamily s t, d.conditionMapFamily b t] ↔
      ZFSet.pair x y ∈ M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g := by
    obtain ⟨C, E, U, Rf, Rc, rfl⟩ := M.exists_niceRefinementIndex_fields a s b d level T1 T2 valid1 valid2 hx
    obtain ⟨C', E', U', Rf', Rc', rfl⟩ := M.exists_niceRefinementIndex_fields a s b d level T1 T2 valid1 valid2 hy
    rw [M.realize_refinementIndexActionFormula a s t b d pairing unions powers separation collection
      carrier group nodes maps nodeMaps level hl g C E C' E' U Rf Rc U' Rf' Rc',
      M.niceRefinementIndexActionGraph_entry a s b d level T1 T2 valid1 valid2 t
        pairing unions powers separation collection carrier order maps closed1 closed2 familyGround
        g C E U Rf Rc hx, refinementIndexCode_eq_iff]
    constructor
    · rintro ⟨ce, ee, ue, fe, re⟩
      exact ⟨rfl, congrArg b.encode ce.symm, congrArg b.encode ee.symm,
        congrArg Subtype.val ue.symm, congrArg Subtype.val fe.symm, congrArg Subtype.val re.symm⟩
    · rintro ⟨_, ce, ee, ue, fe, re⟩
      exact ⟨b.injective ce.symm, b.injective ee.symm,
        Subtype.ext ue.symm, Subtype.ext fe.symm, Subtype.ext re.symm⟩
  let env : Fin 6 → ZFSet.{u} := ![z, t.encode g, I, s.carrier, a.conditionMapFamily s t, d.conditionMapFamily b t]
  have args (x y : ZFSet.{u}) :
      (fun j : Fin 6 => (extend y (extend x env)) (![1, 0, 3, 5, 6, 7] j)) =
      ![x, y, t.encode g, s.carrier, a.conditionMapFamily s t, d.conditionMapFamily b t] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) j
  change Realize M.sets refinementIndexActionEntryFormula env ↔ _
  simp only [refinementIndexActionEntryFormula, realize_ex]
  constructor
  · rintro ⟨x, hxm, y, hym, hx, hy, paired, acted⟩
    have eq := (M.realize_orderedPairFormula pairing 2 1 0 _ hz hxm hym).1 paired
    change z = ZFSet.pair x y at eq
    rw [realize_reindex, args] at acted
    exact eq.symm ▸ (action x y hx hy).1 acted
  · intro entry
    obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 entry).1
    have hxm := M.transitive indexGround hx
    have hym := M.transitive indexGround hy
    refine ⟨x, hxm, y, hym, hx, hy,
      (M.realize_orderedPairFormula pairing 2 1 0 _ hz hxm hym).2 eq, ?_⟩
    rw [realize_reindex, args]
    exact (action x y hx hy).2 (eq ▸ entry)

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
local notation "I" => M.niceRefinementIndices a s b d level T T2 valid
local notation "J" => stageOneAssignments I T

variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)

variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets)

include closed closed2 familyGround pairing unions powers separation collection carrier order maps in
theorem refinementAssignmentActionGraph_function (g : G) :
    ZFSet.IsFunc J J (M.refinementAssignmentActionGraph a s b d level T T2 valid valid2 g) :=
  relationProduct_function
    (M.niceRefinementIndexActionGraph_function a s b d level T T2 valid valid2 t
      pairing unions powers separation collection carrier order maps closed closed2 familyGround g)
    (relationProduct_function (stageOneTermAction_function a s T valid closed g)
      (stageOneTermAction_function a s T valid closed g))

include closed closed2 familyGround pairing unions powers separation collection carrier order maps in
theorem refinementAssignmentActionGraph_entry (g : G) (C E : L)
    (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I)
    (hu : u.val ∈ T) (hw : w.val ∈ T) (y : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val) y ∈
      M.refinementAssignmentActionGraph a s b d level T T2 valid valid2 g ↔
    y = stageOneAssignment (refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val)
      (a.act s g u).val (a.act s g w).val := by
  have idx := M.niceRefinementIndexActionGraph_entry a s b d level T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround g C E U Rf Rc index
  constructor
  · intro entry
    have func := M.refinementAssignmentActionGraph_function a s b d level T T2 valid valid2 closed t
      pairing unions powers separation collection carrier order maps closed2 familyGround g
    obtain ⟨i', _, u', _, w', _, rfl⟩ := (mem_stageOneAssignments I T y).1
      (ZFSet.pair_mem_prod.1 (func.1 entry)).2
    obtain ⟨_, _, _, _, _, _, ei, eu, ew⟩ :=
      (M.pair_mem_refinementAssignmentActionGraph a s b d level T T2 valid valid2 g _ _ _ _ _ _).1 entry
    rw [(idx i').1 ei, ((Name.pair_mem_renameFamilyGraph s (a.iso g) T valid u u').1 eu).2,
      ((Name.pair_mem_renameFamilyGraph s (a.iso g) T valid w w').1 ew).2]
    rfl
  · rintro rfl
    apply (M.pair_mem_refinementAssignmentActionGraph a s b d level T T2 valid valid2 g _ _ _ _ _ _).2
    refine ⟨index, hu, hw, ?_, closed g u hu, closed g w hw, (idx _).2 rfl, ?_, ?_⟩
    · exact (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
        carrier order maps level T T2 valid closed closed2 familyGround g C E U Rf Rc).2 index
    · exact (Name.pair_mem_renameFamilyGraph s (a.iso g) T valid u _).2 ⟨hu, rfl⟩
    · exact (Name.pair_mem_renameFamilyGraph s (a.iso g) T valid w _).2 ⟨hw, rfl⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRefinementAssignmentImages
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
local notation "I" => M.niceRefinementIndices a s b d level T T2 valid
local notation "J" => stageOneAssignments I T
local notation "graph" => M.refinementAssignmentActionGraph a s b d level T T2 valid valid2

variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets)

include pairing unions powers separation collection carrier order maps closed closed2 familyGround in
theorem refinementAssignmentActionGraph_injection (g : G) : InjectionCode J J (graph g) :=
  relationProduct_injection
    (M.niceRefinementIndexActionGraph_injection a s b d level T T2 valid valid2 t
      pairing unions powers separation collection carrier order maps closed closed2 familyGround g)
    (relationProduct_injection (stageOneTermAction_injection a s T valid closed g)
      (stageOneTermAction_injection a s T valid closed g))

include pairing unions powers separation collection carrier order maps closed closed2 familyGround in
theorem refinementAssignmentImage_entry (g : G) (C E : L)
    (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I)
    (hu : u.val ∈ T) (hw : w.val ∈ T) (A : ZFSet.{u}) :
    stageOneAssignment (refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val)
      (a.act s g u).val (a.act s g w).val ∈
        M.refinementAssignmentImage a s b d level T T2 valid valid2 g A ↔
    stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ A := by
  have entry := (M.refinementAssignmentActionGraph_entry a s b d level T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 familyGround
    g C E U Rf Rc u w index hu hw _).2 rfl
  have injection := M.refinementAssignmentActionGraph_injection a s b d level T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround g
  constructor
  · intro hy
    obtain ⟨_, x, hx, xy⟩ := (mem_relationImage A J (graph g) _).1 hy
    have equal := injection.injective _ _ _ xy entry
    exact equal ▸ hx
  · intro hx
    exact (mem_relationImage A J (graph g) _).2
      ⟨(ZFSet.pair_mem_prod.1 (injection.function.1 entry)).2, _, hx, entry⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundStageOneRawNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

theorem stageOneRawClass_iff (R w : (M.nameDomain s).names) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) R.val.val w.val.val z ↔
      z = (M.stageOneClassName s pairing unions powers separation collection carrier order hT valid R w).val.val :=
  M.realize_refinementClassCodeFormula s pairing unions powers separation collection carrier order
    hT valid R.val w.val R.property w.property z hz

theorem stageOneClassName_mem_bound (R w : (M.nameDomain s).names) :
    (M.stageOneClassName s pairing unions powers separation collection carrier order hT valid R w).val.val ∈
      M.groundRelations T s.carrier :=
  (M.mem_groundRelations T s.carrier _).2
    ⟨(M.stageOneClassName s pairing unions powers separation collection carrier order hT valid R w).property,
      Name.refinementClass_subset T valid R.val w.val⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPreparedPositionCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable {T2 : ZFSet.{u}} {valid2 : ∀ z ∈ T2, IsName s z}
variable (level : ZFSet.{u})
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include indices in
theorem refinementLevelFormulaData_fields (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid) :
    let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    let data := M.refinementLevelFormulaData a s b d level T T2 valid
    (∀ z, ZFSet.pair idx z ∈ data 1 ↔ z = b.encode C) ∧
    (∀ z, ZFSet.pair idx z ∈ data 2 ↔ z = b.encode E) ∧
    (∀ z, ZFSet.pair idx z ∈ data 3 ↔ z = U.val.val) ∧
    (∀ z, ZFSet.pair idx z ∈ data 4 ↔ z = Rf.val.val) ∧
    (∀ z, ZFSet.pair idx z ∈ data 5 ↔ z = Rc.val.val) :=
  ⟨M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 1,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 2,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 3,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 4,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 5⟩

include indices in
theorem refinementLevelFormulaData_map (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid) (z : ZFSet.{u}) :
    ZFSet.pair (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) z ∈
      M.refinementLevelFormulaData a s b d level T T2 valid 12 ↔
      z = (M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc).val.val :=
  M.niceRefinementNameGraph_entry a s b d indices pairing unions powers separation collection hT carrier order
    2 C E U Rf Rc member z

variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

theorem refinementLevelFormulaData_visibility (v : L) (z : ZFSet.{u}) :
    ZFSet.pair (b.encode v) z ∈ M.refinementLevelFormulaData a s b d level T T2 valid 13 ↔
      z = (M.stageOneVisibilityName s valid a b d base directed system v).val.val :=
  system.visibility_entries v z

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include indices in
theorem refinementLevelRawCollision_iff (C E : L) (U Rf Rc u u' w w' : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid) (p : P) :
    stageOneRawCollision M (M.refinementLevelFormulaData a s b d level T T2 valid)
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val.val u'.val.val w.val.val w'.val.val (s.encode p) ↔
      M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid Rf Rc u u' w w' p := by
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let env : Assignment (M.nameDomain s) 4 := ![cls Rc u, cls Rc u', cls Rf w, cls Rf w']
  have codes : (fun j => (env j).val.val) =
      ![(cls Rc u).val.val, (cls Rc u').val.val, (cls Rf w).val.val, (cls Rf w').val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) j
  have forcing := M.stageOneRawForces_iff s pairing unions powers separation collection carrier order
    refinementCollisionFormula p env
  rw [codes] at forcing
  have fields := M.refinementLevelFormulaData_fields s valid a b d level indices C E U Rf Rc member
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨_, _, _, _, ff, fr, bu, bu', aw, aw', forced⟩ := body
    have ef := (fields.2.2.2.1 _).1 ff
    have er := (fields.2.2.2.2 _).1 fr
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 1) u.val.val (f 2) at bu
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 1) u'.val.val (f 3) at bu'
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 0) w.val.val (f 4) at aw
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 0) w'.val.val (f 5) at aw'
    rw [er] at bu bu'
    rw [ef] at aw aw'
    have eb := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rc u _ (ground 2)).1 bu
    have eb' := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rc u' _ (ground 3)).1 bu'
    have ea := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rf w _ (ground 4)).1 aw
    have ea' := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rf w' _ (ground 5)).1 aw'
    rw [eb, eb', ea, ea'] at forced
    exact forcing.1 forced
  · intro forced
    refine ⟨![Rf.val.val, Rc.val.val, (cls Rc u).val.val, (cls Rc u').val.val,
      (cls Rf w).val.val, (cls Rf w').val.val], ?_, ?_⟩
    · exact Fin.cases Rf.property (Fin.cases Rc.property (Fin.cases (cls Rc u).property
        (Fin.cases (cls Rc u').property (Fin.cases (cls Rf w).property
          (Fin.cases (cls Rf w').property (fun j => Fin.elim0 j))))))
    · refine ⟨M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rc u,
        M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rc u',
        M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rf w,
        M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rf w',
        (fields.2.2.2.1 _).2 rfl, (fields.2.2.2.2 _).2 rfl, ?_, ?_, ?_, ?_, forcing.2 forced⟩
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rc u _ (cls Rc u).property).2 rfl
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rc u' _ (cls Rc u').property).2 rfl
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rf w _ (cls Rf w).property).2 rfl
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rf w' _ (cls Rf w').property).2 rfl

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRefinementLevelSingleCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include nodes indices in
theorem refinementLevelRawSingle_codes (C E : L) (U Rf Rc u w : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid) (p : P) :
    let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    let data := M.refinementLevelFormulaData a s b d level T T2 valid
    let bu := (M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rc u).val.val
    let aw := (M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rf w).val.val
    stageOneRawSingle M data idx u.val.val w.val.val (s.encode p) ↔
      stageOneRawForces M (data 7) (data 8) (s.encode p) refinementActivityFormula ![u.val.val, w.val.val, U.val.val] ∧
      stageOneRawProfile M (data 7) (data 8) (s.encode p) (data 10) (data 11) (data 13) (b.encode E) bu aw ∧
      stageOneRawCompatibility M (data 7) (data 8) (s.encode p) (data 13) (data 12) (b.encode C) idx bu aw := by
  let data := M.refinementLevelFormulaData a s b d level T T2 valid
  let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let bu := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rc u
  let aw := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rf w
  have fields := M.refinementLevelFormulaData_fields s valid a b d level indices C E U Rf Rc member
  dsimp only
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨_, _, _, _, fc, fe, fu, ff, fr, coarse, fine, active, profile, compatible⟩ := body
    have ec := (fields.1 _).1 fc
    have ee := (fields.2.1 _).1 fe
    have eu := (fields.2.2.1 _).1 fu
    have ef := (fields.2.2.2.1 _).1 ff
    have er := (fields.2.2.2.2 _).1 fr
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 4) u.val.val (f 5) at coarse
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 3) w.val.val (f 6) at fine
    rw [er] at coarse
    rw [ef] at fine
    have eb := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid
      Rc u (f 5) (ground 5)).1 coarse
    have ea := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid
      Rf w (f 6) (ground 6)).1 fine
    rw [eu] at active
    rw [ee, eb, ea] at profile
    rw [ec, eb, ea] at compatible
    exact ⟨active, profile, compatible⟩
  · rintro ⟨active, profile, compatible⟩
    refine ⟨![b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val, bu.val.val, aw.val.val], ?_, ?_⟩
    · exact Fin.cases (M.transitive nodes (b.encode_mem C))
        (Fin.cases (M.transitive nodes (b.encode_mem E)) (Fin.cases U.property
          (Fin.cases Rf.property (Fin.cases Rc.property (Fin.cases bu.property
            (Fin.cases aw.property (fun j => Fin.elim0 j)))))))
    · refine ⟨b.encode_mem C, b.encode_mem E,
        M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rc u,
        M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rf w,
        (fields.1 _).2 rfl, (fields.2.1 _).2 rfl, (fields.2.2.1 _).2 rfl,
        (fields.2.2.2.1 _).2 rfl, (fields.2.2.2.2 _).2 rfl, ?_, ?_, active, profile, compatible⟩
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid
          Rc u bu.val.val bu.property).2 rfl
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid
          Rf w aw.val.val aw.property).2 rfl

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (level : ZFSet.{u})
variable {T2 : ZFSet.{u}} {valid2 : ∀ z ∈ T2, IsName s z}
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

include pairing unions powers separation collection carrier order

omit [OrderTop P] in
theorem raw_four_p0 (phi : SetFormula 4) (p : P) (x y z w : (M.nameDomain s).names) :
    stageOneRawForces M s.carrier s.conditionOrder (s.encode p) phi ![x.val.val, y.val.val, z.val.val, w.val.val] ↔
      Forces (M.nameDomain s) phi ![x, y, z, w] p := by
  have equal : (fun j : Fin 4 => ((![x, y, z, w] : Assignment (M.nameDomain s) 4) j).val.val) =
      ![x.val.val, y.val.val, z.val.val, w.val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) j
  rw [← equal]
  exact M.stageOneRawForces_iff s pairing unions powers separation collection carrier order phi p ![x, y, z, w]

variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include indices in
theorem refinementLevelRawCompatibility_iff (C E : L) (U Rf Rc bu aw : (M.nameDomain s).names) (p : P)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid) :
    let data := M.refinementLevelFormulaData a s b d level T T2 valid
    let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    stageOneRawCompatibility M (data 7) (data 8) (s.encode p) (data 13) (data 12)
      (b.encode C) idx bu.val.val aw.val.val ↔
      Forces (M.nameDomain s) refinementCompatibilityFormula
        ![aw, M.stageOneVisibilityName s valid a b d base directed system C, bu,
          M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc] p := by
  change stageOneRawCompatibility M s.carrier s.conditionOrder (s.encode p)
    (M.refinementLevelFormulaData a s b d level T T2 valid 13) (M.refinementLevelFormulaData a s b d level T T2 valid 12)
    (b.encode C) (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
    bu.val.val aw.val.val ↔ _
  constructor
  · rintro ⟨V, hV, D, hD, visible, mapped, forced⟩
    have equalV := (M.refinementLevelFormulaData_visibility s valid a b d level (T2 := T2) base directed system C V).1 visible
    have equalD := (M.refinementLevelFormulaData_map s pairing unions powers separation collection carrier order
      hT valid a b d level indices C E U Rf Rc member D).1 mapped
    subst V
    subst D
    exact (raw_four_p0 M s pairing unions powers separation collection carrier order
      refinementCompatibilityFormula p aw (M.stageOneVisibilityName s valid a b d base directed system C) bu
      (M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc)).1 forced
  · intro forced
    let V := M.stageOneVisibilityName s valid a b d base directed system C
    let D := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
    refine ⟨V.val.val, V.property, D.val.val, D.property, ?_, ?_, ?_⟩
    · exact (M.refinementLevelFormulaData_visibility s valid a b d level (T2 := T2) base directed system C V.val.val).2 rfl
    · exact (M.refinementLevelFormulaData_map s pairing unions powers separation collection carrier order
        hT valid a b d level indices C E U Rf Rc member D.val.val).2 rfl
    · exact (raw_four_p0 M s pairing unions powers separation collection carrier order
        refinementCompatibilityFormula p aw V bu D).2 forced

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStageOneTestEquivalence
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable {T2 : ZFSet.{u}} {valid2 : ∀ z ∈ T2, IsName s z}
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

include pairing unions powers separation collection carrier order

omit [OrderTop P] in
theorem raw_three (phi : SetFormula 3) (p : P) (x y z : (M.nameDomain s).names) :
    stageOneRawForces M s.carrier s.conditionOrder (s.encode p) phi ![x.val.val, y.val.val, z.val.val] ↔
      Forces (M.nameDomain s) phi ![x, y, z] p := by
  have equal : (fun j : Fin 3 => ((![x, y, z] : Assignment (M.nameDomain s) 3) j).val.val) =
      ![x.val.val, y.val.val, z.val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j
  rw [← equal]
  exact M.stageOneRawForces_iff s pairing unions powers separation collection carrier order phi p ![x, y, z]

theorem stageOneRawProfile_iff (E : L) (bu aw : (M.nameDomain s).names) (p : P) :
    let data := M.stageOneFormulaData a s b d T T2 valid
    stageOneRawProfile M (data 7) (data 8) (s.encode p) (data 10) (data 11) (data 13)
      (b.encode E) bu.val.val aw.val.val ↔
      ∀ v : L, E ≤ v → Forces (M.nameDomain s) refinementProfileFormula
        ![bu, aw, M.stageOneVisibilityName s valid a b d base directed system v] p := by
  change stageOneRawProfile M s.carrier s.conditionOrder (s.encode p) b.carrier b.conditionOrder
    (M.stageOneFormulaData a s b d T T2 valid 13) (b.encode E) bu.val.val aw.val.val ↔ _
  constructor
  · intro raw v below
    obtain ⟨V, hV, entry, forced⟩ := raw (b.encode v) (b.encode_mem v)
      ((b.pair_mem_conditionOrder E v).2 below)
    have equal := (M.stageOneFormulaData_visibility s valid a b d (T2 := T2) base directed system v V).1 entry
    subst V
    exact (raw_three M s pairing unions powers separation collection carrier order
      refinementProfileFormula p bu aw (M.stageOneVisibilityName s valid a b d base directed system v)).1 forced
  · intro typed v hv below
    obtain ⟨v, rfl⟩ := (b.mem_carrier v).1 hv
    let V := M.stageOneVisibilityName s valid a b d base directed system v
    refine ⟨V.val.val, V.property, ?_, ?_⟩
    · exact (M.stageOneFormulaData_visibility s valid a b d (T2 := T2) base directed system v V.val.val).2 rfl
    · exact (raw_three M s pairing unions powers separation collection carrier order
        refinementProfileFormula p bu aw V).2 (typed v ((b.pair_mem_conditionOrder E v).1 below))

end

open SetRealization SetFormula
universe u

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRefinementRawTestMonotonicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

def refinementLevelTests (level T2 A : ZFSet.{u}) (p : P) : Prop :=
  ∀ (C E : L) (U Rf Rc : (M.nameDomain s).names),
    let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    idx ∈ M.niceRefinementIndices a s b d level T T2 valid →
    (∀ u w : (M.nameDomain s).names, u.val.val ∈ T → w.val.val ∈ T →
      stageOneAssignment idx u.val.val w.val.val ∈ A →
      M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
        a b d base directed system C E U Rf Rc u w p) ∧
    (∀ u u' w w' : (M.nameDomain s).names,
      u.val.val ∈ T → u'.val.val ∈ T → w.val.val ∈ T → w'.val.val ∈ T →
      stageOneAssignment idx u.val.val w.val.val ∈ A →
      stageOneAssignment idx u'.val.val w'.val.val ∈ A →
      M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        Rf Rc u u' w w' p)

theorem refinementLevelTests_mono (level T2 A : ZFSet.{u}) {p q : P}
    (tests : M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 A p) (below : q ≤ p) :
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 A q := by
  intro C E U Rf Rc
  dsimp only
  intro member
  obtain ⟨single, collision⟩ := tests C E U Rf Rc member
  refine ⟨?_, ?_⟩
  · intro u w hu hw entry
    exact M.stageOneSingleTests_mono s pairing unions powers separation collection carrier order hT valid
      a b d base directed system C E U Rf Rc u w (single u w hu hw entry) below
  · intro u u' w w' hu hu' hw hw' entry entry'
    exact M.stageOneCollisionTest_mono s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u' w w' (collision u u' w w' hu hu' hw hw' entry entry') below

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

theorem refinementLevelTests_union (level T2 : ZFSet.{u}) (family : Nat → ZFSet.{u}) (rows : Nat → P) (p : P)
    (increasing : ∀ n m, n ≤ m → family n ⊆ family m)
    (below : ∀ n, p ≤ rows n)
    (tests : ∀ n, M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 (family n) (rows n)) :
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 (stageOneAssignmentUnion family) p := by
  intro C E U Rf Rc
  dsimp only
  intro index
  refine ⟨?_, ?_⟩
  · intro u w hu hw entry
    obtain ⟨n, hn⟩ := (mem_stageOneAssignmentUnion family _).1 entry
    exact M.stageOneSingleTests_mono s pairing unions powers separation collection carrier order hT valid
      a b d base directed system C E U Rf Rc u w ((tests n C E U Rf Rc index).1 u w hu hw hn) (below n)
  · intro u u' w w' hu hu' hw hw' entry entry'
    obtain ⟨n, hn⟩ := (mem_stageOneAssignmentUnion family _).1 entry
    obtain ⟨m, hm⟩ := (mem_stageOneAssignmentUnion family _).1 entry'
    have first := increasing n (max n m) (Nat.le_max_left n m) hn
    have second := increasing m (max n m) (Nat.le_max_right n m) hm
    exact M.stageOneCollisionTest_mono s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u' w w' ((tests (max n m) C E U Rf Rc index).2 u u' w w' hu hu' hw hw' first second)
      (below (max n m))

end

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

include nodes indices in
theorem refinementLevelRawSingle_iff (C E : L) (U Rf Rc u w : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid) (p : P) :
    stageOneRawSingle M (M.refinementLevelFormulaData a s b d level T T2 valid)
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val.val w.val.val (s.encode p) ↔
      M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
        a b d base directed system C E U Rf Rc u w p := by
  have meaning := M.refinementLevelRawSingle_codes a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices C E U Rf Rc u w member p
  let bu := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rc u
  let aw := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rf w
  have codes : (fun j : Fin 3 => ((![u, w, U] : Assignment (M.nameDomain s) 3) j).val.val) =
      ![u.val.val, w.val.val, U.val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j
  have activity := M.stageOneRawForces_iff s pairing unions powers separation collection carrier order
    refinementActivityFormula p ![u, w, U]
  rw [codes] at activity
  have profile := M.stageOneRawProfile_iff s pairing unions powers separation collection carrier order
    valid a b d (T2 := T2) base directed system E bu aw p
  change stageOneRawProfile M s.carrier s.conditionOrder (s.encode p) b.carrier b.conditionOrder
    (M.niceVisibilityGraph a s b T d.principalFix) (b.encode E) bu.val.val aw.val.val ↔ _ at profile
  have compatible := M.refinementLevelRawCompatibility_iff s pairing unions powers separation collection carrier order
    hT valid a b d level base directed system indices C E U Rf Rc bu aw p member
  exact meaning.trans (and_congr activity (and_congr profile compatible))

include nodes indices in
theorem refinementLevelRawTests_iff (A : ZFSet.{u}) (p : P) :
    stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A (s.encode p) ↔
      M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
        a b d base directed system level T2 A p := by
  have single := M.refinementLevelRawSingle_iff a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices base directed system
  have collision := M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT valid indices
  let lift (r : ZFSet.{u}) (hr : r ∈ T) : (M.nameDomain s).names :=
    ⟨⟨r, valid r hr⟩, M.transitive hT hr⟩
  constructor
  · intro raw C E U Rf Rc
    dsimp only
    intro member
    refine ⟨?_, ?_⟩
    · intro u w hu hw entry
      exact (single C E U Rf Rc u w member p).1
        (raw.1 _ member u.val.val hu w.val.val hw entry)
    · intro u u' w w' hu hu' hw hw' entry entry'
      exact (collision C E U Rf Rc u u' w w' member p).1
        (raw.2 _ member u.val.val hu u'.val.val hu' w.val.val hw w'.val.val hw' entry entry')
  · intro typed
    refine ⟨?_, ?_⟩
    · intro t ht rawU hu rawW hw entry
      obtain ⟨C, E, U, Rf, Rc, rfl⟩ := indices.decoded t ht
      exact (single C E U Rf Rc (lift rawU hu) (lift rawW hw) ht p).2
        ((typed C E U Rf Rc ht).1 (lift rawU hu) (lift rawW hw) hu hw entry)
    · intro t ht rawU hu rawU' hu' rawW hw rawW' hw' entry entry'
      obtain ⟨C, E, U, Rf, Rc, rfl⟩ := indices.decoded t ht
      exact (collision C E U Rf Rc (lift rawU hu) (lift rawU' hu') (lift rawW hw) (lift rawW' hw') ht p).2
        ((typed C E U Rf Rc ht).2 (lift rawU hu) (lift rawU' hu') (lift rawW hw) (lift rawW' hw')
          hu hu' hw hw' entry entry')

include pairing unions powers separation collection carrier order nodes hT indices system

theorem refinementLevelRawTests_mono (A : ZFSet.{u}) {p q : P}
    (tests : stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A (s.encode p))
    (below : q ≤ p) :
    stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A (s.encode q) := by
  have meaning := M.refinementLevelRawTests_iff a s b d level pairing unions powers separation
    collection carrier order nodes hT valid indices base directed system
  exact (meaning A q).2 (M.refinementLevelTests_mono s pairing unions powers separation collection
    carrier order hT valid a b d base directed system level T2 A ((meaning A p).1 tests) below)

theorem refinementLevelRawTests_order_mono (A : ZFSet.{u}) {p q : ZFSet.{u}}
    (tests : stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A p)
    (below : ZFSet.pair q p ∈ s.conditionOrder) :
    stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A q := by
  rw [Presentation.conditionOrder, Presentation.mem_subset] at below
  obtain ⟨⟨q', p'⟩, below, equal⟩ := below
  change ZFSet.pair (s.encode q') (s.encode p') = ZFSet.pair q p at equal
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  exact M.refinementLevelRawTests_mono a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices base directed system A tests below

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_StageTwoAssignmentTestActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (hT : T ∈ M.sets)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "move" => M.stageOneNameAction a s t pairing unions powers separation collection carrier maps

include maps closed closed2 familyGround in
theorem refinementLevelTests_image_iff (g : G) (A : ZFSet.{u}) (p : P) :
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 (M.refinementAssignmentImage a s b d level T T2 valid valid2 g A) (a.iso g p) ↔
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 A p := by
  have term (w : (M.nameDomain s).names) : (move g w).val.val ∈ T ↔ w.val.val ∈ T := by
    constructor
    · intro member
      have original := closed g⁻¹ (a.act s g w.val) member
      simpa only [a.act_inv_left] using original
    · exact closed g w.val
  have index := M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
    carrier order maps level T T2 valid closed closed2 familyGround g
  have image := M.refinementAssignmentImage_entry a s b d level T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround g
  have single := M.stageOneSingleTests_act_iff a s t pairing unions powers separation collection
    carrier order maps hT valid closed b d base directed system g
  have collision := M.stageOneCollisionTest_act_iff a s t pairing unions powers separation collection
    carrier order maps hT valid closed g
  constructor
  · intro tests C E U Rf Rc
    dsimp only
    intro member
    obtain ⟨hs, hc⟩ := tests (d.iso g C) (d.iso g E) (move g U) (move g Rf) (move g Rc)
      ((index C E U Rf Rc).mpr member)
    refine ⟨?_, ?_⟩
    · intro u w hu hw entry
      exact (single C E U Rf Rc u w p).mp
        (hs (move g u) (move g w) ((term u).mpr hu) ((term w).mpr hw)
          ((image C E U Rf Rc u.val w.val member hu hw A).mpr entry))
    · intro u u' w w' hu hu' hw hw' entry entry'
      exact (collision Rf Rc u u' w w' p).mp
        (hc (move g u) (move g u') (move g w) (move g w')
          ((term u).mpr hu) ((term u').mpr hu') ((term w).mpr hw) ((term w').mpr hw')
          ((image C E U Rf Rc u.val w.val member hu hw A).mpr entry)
          ((image C E U Rf Rc u'.val w'.val member hu' hw' A).mpr entry'))
  · intro tests C E U Rf Rc
    obtain ⟨C, rfl⟩ := (d.iso g).surjective C
    obtain ⟨E, rfl⟩ := (d.iso g).surjective E
    obtain ⟨U, rfl⟩ := (move g).surjective U
    obtain ⟨Rf, rfl⟩ := (move g).surjective Rf
    obtain ⟨Rc, rfl⟩ := (move g).surjective Rc
    dsimp only
    intro member
    have old := (index C E U Rf Rc).mp member
    obtain ⟨hs, hc⟩ := tests C E U Rf Rc old
    refine ⟨?_, ?_⟩
    · intro u w hu hw entry
      obtain ⟨u, rfl⟩ := (move g).surjective u
      obtain ⟨w, rfl⟩ := (move g).surjective w
      have hu := (term u).mp hu
      have hw := (term w).mp hw
      exact (single C E U Rf Rc u w p).mpr
        (hs u w hu hw ((image C E U Rf Rc u.val w.val old hu hw A).mp entry))
    · intro u u' w w' hu hu' hw hw' entry entry'
      obtain ⟨u, rfl⟩ := (move g).surjective u
      obtain ⟨u', rfl⟩ := (move g).surjective u'
      obtain ⟨w, rfl⟩ := (move g).surjective w
      obtain ⟨w', rfl⟩ := (move g).surjective w'
      have hu := (term u).mp hu
      have hu' := (term u').mp hu'
      have hw := (term w).mp hw
      have hw' := (term w').mp hw'
      exact (collision Rf Rc u u' w w' p).mpr
        (hc u u' w w' hu hu' hw hw'
          ((image C E U Rf Rc u.val w.val old hu hw A).mp entry)
          ((image C E U Rf Rc u'.val w'.val old hu' hw' A).mp entry'))

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundBinaryRowStageOneRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure RefinementStageSystem (M : TransitiveGround.{u}) (a : PosetAction G P)
    (s : Presentation P) (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (level T T2 : ZFSet.{u}) : Prop where
  valid1 : ∀ z ∈ T, IsName s z
  valid2 : ∀ z ∈ T2, IsName s z
  terms_hs : ∀ τ : Name s, τ.val ∈ T →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) τ
  pairs_hs : ∀ τ : Name s, τ.val ∈ T2 →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) τ
  first : NiceNameSystem M a s b d base directed T valid1
  second : NiceNameSystem M a s b d base directed T2 valid2
  indices : NiceRefinementIndexSystem M a s b d level T T2 valid1 valid2
  inputs : StageOneActionParameters M a s t b d T T2 valid1

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RefinementAssignmentActionLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets)
local notation "I" => M.niceRefinementIndices a s b d level T T2 valid
local notation "J" => stageOneAssignments I T
local notation "graph" => M.refinementAssignmentActionGraph a s b d level T T2 valid valid2
local notation "move" => M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
include pairing unions powers separation collection carrier order maps closed closed2 familyGround

theorem refinementAssignmentActionGraph_one {x : ZFSet.{u}} (hx : x ∈ J) (y : ZFSet.{u}) :
    ZFSet.pair x y ∈ graph 1 ↔ y = x := by
  obtain ⟨idx, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I T x).1 hx
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d level T T2 valid valid2 hi
  have entry := M.refinementAssignmentActionGraph_entry a s b d level T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 familyGround 1 C E U Rf Rc
    ⟨u, valid u hu⟩ ⟨w, valid w hw⟩ hi hu hw y
  rw [a.act_one s ⟨u, valid u hu⟩, a.act_one s ⟨w, valid w hw⟩] at entry
  simpa only [d.one, a.act_one] using entry

theorem refinementAssignmentActionGraph_mul (g h : G) {x : ZFSet.{u}} (hx : x ∈ J) (z : ZFSet.{u}) :
    ZFSet.pair x z ∈ graph (g * h) ↔
      ∃ y ∈ J, ZFSet.pair x y ∈ graph h ∧ ZFSet.pair y z ∈ graph g := by
  obtain ⟨idx, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I T x).1 hx
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d level T T2 valid valid2 hi
  let nu : Name s := ⟨u, valid u hu⟩
  let nw : Name s := ⟨w, valid w hw⟩
  have indexH := (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
    carrier order maps level T T2 valid closed closed2 familyGround h C E U Rf Rc).mpr hi
  let y := stageOneAssignment (refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
    (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val)
    (a.act s h nu).val (a.act s h nw).val
  have hy : y ∈ J := (stageOneAssignment_mem_assignments I T _ _ _).2
    ⟨indexH, closed h nu hu, closed h nw hw⟩
  have atH := M.refinementAssignmentActionGraph_entry a s b d level T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 familyGround h C E U Rf Rc nu nw hi hu hw
  have atG := M.refinementAssignmentActionGraph_entry a s b d level T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 familyGround g
    (d.iso h C) (d.iso h E) (move h U) (move h Rf) (move h Rc)
    (a.act s h nu) (a.act s h nw) indexH (closed h nu hu) (closed h nw hw) z
  have atMul := M.refinementAssignmentActionGraph_entry a s b d level T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 familyGround (g * h)
    C E U Rf Rc nu nw hi hu hw z
  simp only [M.stageOneNameAction_val] at atG
  have same : ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u w) z ∈ graph (g * h) ↔
      ZFSet.pair y z ∈ graph g := by
    dsimp only [y]
    rw [atMul, atG]
    simp only [d.mul, a.act_mul]
  constructor
  · intro entry
    exact ⟨y, hy, (atH y).mpr rfl, same.mp entry⟩
  · rintro ⟨y', _, eh, eg⟩
    have equal : y' = y := (atH y').mp eh
    exact same.mpr (equal ▸ eg)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStageThreeAssignmentFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem refinementAssignment_relationLaws {G P L : Type u}
    [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
    (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
    (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (params : StageOneActionParameters M a s t b d T T2 valid) :
    RelationActionLaws G (stageOneAssignments (M.niceRefinementIndices a s b d level T T2 valid) T)
      (M.refinementAssignmentActionGraph a s b d level T T2 valid valid2) := by
  exact ⟨M.refinementAssignmentActionGraph_function a s b d level T T2 valid valid2 params.terms_closed t
      pairing unions powers separation collection carrier order params.condition_maps params.pairs_closed params.family_ground,
    M.refinementAssignmentActionGraph_injection a s b d level T T2 valid valid2 t
      pairing unions powers separation collection carrier order params.condition_maps params.terms_closed params.pairs_closed params.family_ground,
    fun _ hx => M.refinementAssignmentActionGraph_one a s b d level T T2 valid valid2 t
      pairing unions powers separation collection carrier order params.condition_maps params.terms_closed params.pairs_closed params.family_ground hx,
    fun g h _ hx => M.refinementAssignmentActionGraph_mul a s b d level T T2 valid valid2 t
      pairing unions powers separation collection carrier order params.condition_maps params.terms_closed params.pairs_closed params.family_ground g h hx⟩

end

open SetFormula SetRealization
universe u

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRawStageRefinementTestActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

noncomputable def rawRefinementIndexActionGraph (g I P maps nodeMaps : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => Realize M.sets refinementIndexActionEntryFormula ![z,g,I,P,maps,nodeMaps])
    (ZFSet.prod I I)

noncomputable def rawTermActionGraph (g T P maps : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => Realize M.sets termActionEntryFormula ![z,g,T,P,maps]) (ZFSet.prod T T)

end

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets) (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (level T1 T2 : ZFSet.{u}) (hl : level ∈ M.sets)
variable (valid1 : ∀ z ∈ T1, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (closed1 : ∀ g (w : Name s), w.val ∈ T1 → (a.act s g w).val ∈ T1)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T1 valid1).val ∈ M.sets)
variable (indexGround : M.niceRefinementIndices a s b d level T1 T2 valid1 ∈ M.sets)
include pairing unions powers separation collection carrier group nodes order maps nodeMaps hl closed1 closed2 familyGround indexGround

theorem rawRefinementIndexActionGraph_eq (g : G) :
    M.rawRefinementIndexActionGraph (t.encode g)
      (M.niceRefinementIndices a s b d level T1 T2 valid1) s.carrier
      (a.conditionMapFamily s t) (d.conditionMapFamily b t) =
      M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g := by
  have bound := M.prod_mem pairing unions powers separation indexGround indexGround
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨hz, entry⟩ := ZFSet.mem_sep.1 hz
    exact (M.realize_refinementIndexActionEntryFormula a s t b d pairing unions powers separation
      collection carrier group nodes order maps nodeMaps level T1 T2 hl valid1 valid2
      closed1 closed2 familyGround indexGround g z (M.transitive bound hz)).1 entry
  · intro hz
    have bounded := (ZFSet.mem_sep.1 hz).1
    exact ZFSet.mem_sep.2 ⟨bounded,
      (M.realize_refinementIndexActionEntryFormula a s t b d pairing unions powers separation
        collection carrier group nodes order maps nodeMaps level T1 T2 hl valid1 valid2
        closed1 closed2 familyGround indexGround g z (M.transitive bound bounded)).2 hz⟩

omit [OrderTop P] nodes order nodeMaps hl closed2 familyGround indexGround in
include pairing unions powers separation collection carrier group maps closed1 in
theorem rawTermActionGraph_eq (hT1 : T1 ∈ M.sets) (g : G) :
    M.rawTermActionGraph (t.encode g) T1 s.carrier (a.conditionMapFamily s t) =
      Name.renameFamilyGraph s (a.iso g) T1 valid1 := by
  have bound := M.prod_mem pairing unions powers separation hT1 hT1
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨hz, entry⟩ := ZFSet.mem_sep.1 hz
    exact (M.realize_termActionEntryFormula a s t T1 valid1 pairing unions powers separation
      collection carrier group maps hT1 closed1 g z (M.transitive bound hz)).1 entry
  · intro hz
    have bounded : z ∈ ZFSet.prod T1 T1 := by
      obtain ⟨w, hw, rfl⟩ := (Name.mem_renameFamilyGraph s (a.iso g) T1 valid1 z).1 hz
      exact ZFSet.pair_mem_prod.2 ⟨hw, closed1 g w hw⟩
    exact ZFSet.mem_sep.2 ⟨bounded,
      (M.realize_termActionEntryFormula a s t T1 valid1 pairing unions powers separation
        collection carrier group maps hT1 closed1 g z (M.transitive bound bounded)).2 hz⟩

end

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

noncomputable def rawRefinementAssignmentActionGraph (g I T P maps nodeMaps : ZFSet.{u}) : ZFSet.{u} :=
  relationProduct I (ZFSet.prod T T) I (ZFSet.prod T T)
    (M.rawRefinementIndexActionGraph g I P maps nodeMaps)
    (relationProduct T T T T (M.rawTermActionGraph g T P maps) (M.rawTermActionGraph g T P maps))

noncomputable def rawStageRefinementAssignmentActionGraph
    (g P order top actionGraph G nodes nodeOrder nodeAction basis T T2 level : ZFSet.{u}) : ZFSet.{u} :=
  M.rawRefinementAssignmentActionGraph g
    (M.rawRefinementFormulaData P order top actionGraph G nodes nodeOrder basis T T2 level 0)
    T P (rawActionMapFamily G actionGraph P) (rawActionMapFamily G nodeAction nodes)

end

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets) (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (level T T2 : ZFSet.{u}) (hl : level ∈ M.sets) (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets)
variable (indexGround : M.niceRefinementIndices a s b d level T T2 valid ∈ M.sets)
include pairing unions powers separation collection carrier group nodes order maps nodeMaps supports hl hT closed closed2 familyGround indexGround

theorem rawStageRefinementAssignmentActionGraph_eq (g : G) :
    M.rawStageRefinementAssignmentActionGraph (t.encode g) s.carrier s.conditionOrder
      (s.encode ⊤) (a.actionGraph s t) t.carrier b.carrier b.conditionOrder
      (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level =
      M.refinementAssignmentActionGraph a s b d level T T2 valid valid2 g := by
  unfold rawStageRefinementAssignmentActionGraph
  rw [M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
    carrier group nodes supports maps level T T2 valid valid2, rawActionMapFamily_eq, rawActionMapFamily_eq]
  change M.rawRefinementAssignmentActionGraph (t.encode g)
    (M.niceRefinementIndices a s b d level T T2 valid) T s.carrier
    (a.conditionMapFamily s t) (d.conditionMapFamily b t) = _
  unfold rawRefinementAssignmentActionGraph refinementAssignmentActionGraph
  rw [M.rawRefinementIndexActionGraph_eq a s t b d pairing unions powers separation collection
    carrier group nodes order maps nodeMaps level T T2 hl valid valid2 closed closed2 familyGround indexGround g,
    M.rawTermActionGraph_eq (a := a) (s := s) (t := t) (pairing := pairing) (unions := unions)
      (powers := powers) (separation := separation) (collection := collection) (carrier := carrier)
      (group := group) (maps := maps) (T1 := T) (valid1 := valid) (closed1 := closed) hT g]

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (order : s.conditionOrder ∈ M.sets) (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (params : StageOneActionParameters M a s t b d T T2 valid)
variable (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
variable (indexGround : M.niceRefinementIndices a s b d level T T2 valid ∈ M.sets)
local notation "data" => M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤)
  (a.actionGraph s t) t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level
local notation "branch" => fun g => M.rawStageRefinementAssignmentActionGraph (t.encode g)
  s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t) t.carrier b.carrier b.conditionOrder
  (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level
include pairing unions powers separation collection carrier group nodes order supports valid2 params hLevel hT indexGround

theorem rawStageRefinement_relationLaws :
    RelationActionLaws G (stageOneAssignments (data 0) T) branch := by
  have graphs : branch = M.refinementAssignmentActionGraph a s b d level T T2 valid valid2 :=
    funext (fun g => M.rawStageRefinementAssignmentActionGraph_eq a s t b d pairing unions powers separation
      collection carrier group nodes order params.condition_maps params.node_maps supports level T T2 hLevel hT
      valid valid2 params.terms_closed params.pairs_closed params.family_ground indexGround g)
  rw [graphs, M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
    carrier group nodes supports params.condition_maps level T T2 valid valid2]
  exact M.refinementAssignment_relationLaws a s b d level T T2 valid valid2 t
    pairing unions powers separation collection carrier order params

theorem rawStageRefinement_image_eq (g : G) (A : ZFSet.{u}) :
    relationImage A (stageOneAssignments (data 0) T) (branch g) =
      M.refinementAssignmentImage a s b d level T T2 valid valid2 g A := by
  dsimp only
  rw [M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
    carrier group nodes supports params.condition_maps level T T2 valid valid2,
    M.rawStageRefinementAssignmentActionGraph_eq a s t b d pairing unions powers separation
      collection carrier group nodes order params.condition_maps params.node_maps supports level T T2 hLevel hT
      valid valid2 params.terms_closed params.pairs_closed params.family_ground indexGround g]
  rfl

end

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (order : s.conditionOrder ∈ M.sets) (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (params : StageOneActionParameters M a s t b d T T2 valid)
variable (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
variable (indexGround : M.niceRefinementIndices a s b d level T T2 valid ∈ M.sets)
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "data" => M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤)
  (a.actionGraph s t) t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level
local notation "branch" => fun g => M.rawStageRefinementAssignmentActionGraph (t.encode g)
  s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t) t.carrier b.carrier b.conditionOrder
  (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level
include pairing unions powers separation collection carrier group nodes order supports params hLevel hT indexGround indices system

theorem rawStageRefinementTests_image_iff (g : G) (A : ZFSet.{u}) (p : P) :
    stageOneRawTests M data (relationImage A (stageOneAssignments (data 0) T) (branch g)) (s.encode (a.iso g p)) ↔
      stageOneRawTests M data A (s.encode p) := by
  rw [M.rawStageRefinement_image_eq a s t b d pairing unions powers separation collection
    carrier group nodes order supports level T T2 valid valid2 params hLevel hT indexGround,
    M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
      carrier group nodes supports params.condition_maps level T T2 valid valid2]
  rw [M.refinementLevelRawTests_iff a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices base directed system,
    M.refinementLevelRawTests_iff a s b d level pairing unions powers separation collection
      carrier order nodes hT valid indices base directed system]
  exact M.refinementLevelTests_image_iff a s b d level T T2 valid valid2 t pairing unions powers separation
    collection carrier order params.condition_maps hT params.terms_closed params.pairs_closed params.family_ground
    base directed system g A p

theorem rawStageRefinementTests_actionGraph_iff (g : G) (A p q : ZFSet.{u})
    (edge : ZFSet.pair (ZFSet.pair (t.encode g) p) q ∈ a.actionGraph s t) :
    stageOneRawTests M data (relationImage A (stageOneAssignments (data 0) T) (branch g)) q ↔
      stageOneRawTests M data A p := by
  obtain ⟨⟨g', p'⟩, equal⟩ := ((t.product s).mem_graph s (fun x => a.iso x.1 x.2) _).1 edge
  obtain ⟨inputs, output⟩ := ZFSet.pair_inj.1 equal.symm
  obtain ⟨actors, source⟩ := ZFSet.pair_inj.1 inputs
  have actor : g = g' := t.injective actors
  have target : q = s.encode (a.iso g p') := by
    simpa only [← actor] using output
  rw [source, target]
  exact M.rawStageRefinementTests_image_iff a s t b d pairing unions powers separation collection
    carrier group nodes order supports level T T2 valid valid2 params hLevel hT indexGround
    indices base directed system g A p'

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRawRefinementStageWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {G L : Type u} [Group G] [PartialOrder L]

def RawRefinementStageWitness (M : TransitiveGround.{u})
    (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 level P order top action : ZFSet.{u}) : Prop :=
  ∃ (orderLaw : PartialOrderCode P order) (topMem : top ∈ P)
    (greatest : ∀ p ∈ P, ZFSet.pair p top ∈ order),
    letI := orderLaw.toPartialOrder
    letI := orderLaw.toOrderTop top topMem greatest
    ∃ e : PosetAction G (SetMembers P),
      e.actionGraph (SetMembers.presentation P) t = action ∧
      RefinementStageSystem M e (SetMembers.presentation P) t b d base directed level T T2

namespace RawRefinementStageWitness
variable {M : TransitiveGround.{u}} {t : Presentation G} {b : Presentation L}
variable {d : PosetAction G L} {base : L} {directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z}
variable {T T2 level P order top action : ZFSet.{u}}
variable (witness : RawRefinementStageWitness M t b d base directed T T2 level P order top action)
include witness

theorem action_code : PosetActionCode t.carrier P
    ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1) order action := by
  obtain ⟨orderLaw, topMem, greatest, e, graph, _system⟩ := witness
  let := orderLaw.toPartialOrder
  let := orderLaw.toOrderTop top topMem greatest
  have code := e.actionGraph_code (SetMembers.presentation P) t
  rw [orderLaw.conditionOrder_eq, graph] at code
  exact code

theorem action_function : ZFSet.IsFunc (ZFSet.prod t.carrier P) P action :=
  witness.action_code.function

end RawRefinementStageWitness

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.RawRefinementStageWitness
open SetRealization SetFormula
universe u
variable {G L : Type u} [Group G] [PartialOrder L]
variable {M : TransitiveGround.{u}} {t : Presentation G} {b : Presentation L}
variable {d : PosetAction G L} {base : L} {directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z}
variable {T T2 level P order top action : ZFSet.{u}}
variable (witness : RawRefinementStageWitness M t b d base directed T T2 level P order top action)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : P ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (groundOrder : order ∈ M.sets) (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets)
local notation "data" => M.rawRefinementFormulaData P order top action
  t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level
include witness pairing unions powers separation collection carrier group nodes groundOrder supports hT

theorem rawTests_order_mono (A p q : ZFSet.{u})
    (tests : stageOneRawTests M data A p) (below : ZFSet.pair q p ∈ data 8) :
    stageOneRawTests M data A q := by
  obtain ⟨orderLaw, topMem, greatest, e, graph, system⟩ := witness
  let := orderLaw.toPartialOrder
  let := orderLaw.toOrderTop top topMem greatest
  have nextOrder : (SetMembers.presentation P).conditionOrder ∈ M.sets := by
    rw [orderLaw.conditionOrder_eq]
    exact groundOrder
  have topEq : (SetMembers.presentation P).encode ⊤ = top := SetMembers.raw_ofMem top topMem
  have dataEq : data = M.refinementLevelFormulaData e (SetMembers.presentation P) b d
      level T T2 system.valid1 := by
    have equal := M.rawRefinementFormulaData_eq e (SetMembers.presentation P) t b d
      pairing unions powers separation collection carrier group nodes supports
      system.inputs.condition_maps level T T2 system.valid1 system.valid2
    have carrierEq : (SetMembers.presentation P).carrier = P := rfl
    simpa only [carrierEq, orderLaw.conditionOrder_eq, topEq, graph] using equal
  have typedBelow : ZFSet.pair q p ∈ (SetMembers.presentation P).conditionOrder := by
    rw [orderLaw.conditionOrder_eq]
    exact below
  rw [dataEq] at tests ⊢
  exact M.refinementLevelRawTests_order_mono e (SetMembers.presentation P) b d level
    pairing unions powers separation collection carrier nextOrder nodes hT
    system.valid1 system.indices base directed system.first A tests typedBelow

end PartitionPilot.Forcing.RawRefinementStageWitness



namespace PartitionPilot.Forcing.RawRefinementStageWitness
open SetRealization SetFormula
universe u
variable {G L : Type u} [Group G] [PartialOrder L]
variable {M : TransitiveGround.{u}} {t : Presentation G} {b : Presentation L}
variable {d : PosetAction G L} {base : L} {directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z}
variable {T T2 level P order top action : ZFSet.{u}}
variable (witness : RawRefinementStageWitness M t b d base directed T T2 level P order top action)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : P ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (groundOrder : order ∈ M.sets) (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets)
local notation "data" => M.rawRefinementFormulaData P order top action
  t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level
include witness pairing unions powers separation collection carrier group nodes groundOrder supports hT

theorem rawTests_union (family rows : Nat → ZFSet.{u}) (q : ZFSet.{u})
    (increasing : ∀ n m, n ≤ m → family n ⊆ family m)
    (below : ∀ n, ZFSet.pair q (rows n) ∈ data 8)
    (tests : ∀ n, stageOneRawTests M data (family n) (rows n)) :
    stageOneRawTests M data (stageOneAssignmentUnion family) q := by
  obtain ⟨orderLaw, topMem, greatest, e, graph, system⟩ := witness
  let := orderLaw.toPartialOrder
  let := orderLaw.toOrderTop top topMem greatest
  have nextOrder : (SetMembers.presentation P).conditionOrder ∈ M.sets := by
    rw [orderLaw.conditionOrder_eq]
    exact groundOrder
  have topEq : (SetMembers.presentation P).encode ⊤ = top := SetMembers.raw_ofMem top topMem
  have dataEq : data = M.refinementLevelFormulaData e (SetMembers.presentation P) b d
      level T T2 system.valid1 := by
    have equal := M.rawRefinementFormulaData_eq e (SetMembers.presentation P) t b d
      pairing unions powers separation collection carrier group nodes supports
      system.inputs.condition_maps level T T2 system.valid1 system.valid2
    have carrierEq : (SetMembers.presentation P).carrier = P := rfl
    simpa only [carrierEq, orderLaw.conditionOrder_eq, topEq, graph] using equal
  have bounds (n : Nat) : q ∈ P ∧ rows n ∈ P := ZFSet.pair_mem_prod.1 (orderLaw.relation (below n))
  let lower : SetMembers P := SetMembers.ofMem q (bounds 0).1
  let sequence : Nat → SetMembers P := fun n => SetMembers.ofMem (rows n) (bounds n).2
  have lowerCode : (SetMembers.presentation P).encode lower = q := SetMembers.raw_ofMem _ _
  have sequenceCode (n : Nat) : (SetMembers.presentation P).encode (sequence n) = rows n := SetMembers.raw_ofMem _ _
  have meaning := M.refinementLevelRawTests_iff e (SetMembers.presentation P) b d level
    pairing unions powers separation collection carrier nextOrder nodes hT system.valid1
    system.indices base directed system.first
  rw [dataEq] at tests ⊢
  rw [← lowerCode]
  apply (meaning _ lower).2
  apply M.refinementLevelTests_union (SetMembers.presentation P) pairing unions powers separation
    collection carrier nextOrder hT system.valid1 e b d base directed system.first
    level T2 family sequence lower increasing
  · intro n
    change ZFSet.pair ((SetMembers.presentation P).encode lower)
      ((SetMembers.presentation P).encode (sequence n)) ∈ order
    rw [lowerCode, sequenceCode]
    exact below n
  · intro n
    apply (meaning (family n) (sequence n)).1
    rw [sequenceCode]
    exact tests n

end PartitionPilot.Forcing.RawRefinementStageWitness



namespace PartitionPilot.Forcing.RawRefinementStageWitness
open SetRealization SetFormula
universe u
variable {G L : Type u} [Group G] [PartialOrder L]
variable {M : TransitiveGround.{u}} {t : Presentation G} {b : Presentation L}
variable {d : PosetAction G L} {base : L} {directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z}
variable {T T2 level P order top action : ZFSet.{u}}
variable (witness : RawRefinementStageWitness M t b d base directed T T2 level P order top action)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : P ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (groundOrder : order ∈ M.sets) (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
local notation "data" => M.rawRefinementFormulaData P order top action
  t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level
local notation "branch" => fun g => M.rawStageRefinementAssignmentActionGraph (t.encode g)
  P order top action t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 level
include witness pairing unions powers separation collection carrier group nodes groundOrder supports hLevel hT

theorem relationLaws : RelationActionLaws G (stageOneAssignments (data 0) T) branch := by
  obtain ⟨orderLaw, topMem, greatest, e, graph, system⟩ := witness
  let := orderLaw.toPartialOrder
  let := orderLaw.toOrderTop top topMem greatest
  have nextOrder : (SetMembers.presentation P).conditionOrder ∈ M.sets := by
    rw [orderLaw.conditionOrder_eq]
    exact groundOrder
  have topEq : (SetMembers.presentation P).encode ⊤ = top := SetMembers.raw_ofMem top topMem
  have laws := M.rawStageRefinement_relationLaws e (SetMembers.presentation P) t b d
    pairing unions powers separation collection carrier group nodes nextOrder supports
    level T T2 system.valid1 system.valid2 system.inputs hLevel hT system.indices.index_ground
  have carrierEq : (SetMembers.presentation P).carrier = P := rfl
  simpa only [carrierEq, orderLaw.conditionOrder_eq, topEq, graph] using laws

theorem rawTests_actionGraph_iff (g : G) (A p q : ZFSet.{u})
    (edge : ZFSet.pair (ZFSet.pair (t.encode g) p) q ∈ action) :
    stageOneRawTests M data (relationImage A (stageOneAssignments (data 0) T) (branch g)) q ↔
      stageOneRawTests M data A p := by
  obtain ⟨orderLaw, topMem, greatest, e, graph, system⟩ := witness
  let := orderLaw.toPartialOrder
  let := orderLaw.toOrderTop top topMem greatest
  have nextOrder : (SetMembers.presentation P).conditionOrder ∈ M.sets := by
    rw [orderLaw.conditionOrder_eq]
    exact groundOrder
  have topEq : (SetMembers.presentation P).encode ⊤ = top := SetMembers.raw_ofMem top topMem
  have typedEdge : ZFSet.pair (ZFSet.pair (t.encode g) p) q ∈ e.actionGraph (SetMembers.presentation P) t :=
    graph.symm ▸ edge
  have tests := M.rawStageRefinementTests_actionGraph_iff e (SetMembers.presentation P) t b d
    pairing unions powers separation collection carrier group nodes nextOrder supports
    level T T2 system.valid1 system.valid2 system.inputs hLevel hT system.indices.index_ground
    system.indices base directed system.first g A p q typedEdge
  have carrierEq : (SetMembers.presentation P).carrier = P := rfl
  simpa only [carrierEq, orderLaw.conditionOrder_eq, topEq, graph] using tests

end PartitionPilot.Forcing.RawRefinementStageWitness

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStructuralHistoryTestUnions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem refinementDataHistoryField_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {stages history : ZFSet.{u}} (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (j : Fin 15) : refinementDataHistoryField stages history j ∈ M.sets := by
  have bound := M.prod_mem pairing unions powers separation hStages
    (M.tupleFieldBound_mem pairing unions 14 (M.union_mem unions (M.union_mem unions hHistory)))
  let params := extend stages (extend history Fin.elim0)
  have ground := M.bounded_separation_mem separation
    (BoundedFormula.refinementDataHistoryFieldFormula 1 2 0 j) params
    (Fin.cases hStages (Fin.cases hHistory (fun i => Fin.elim0 i))) bound
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.refinementDataHistoryFieldFormula 1 2 0 j) (extend z params))
      (ZFSet.prod stages (tupleFieldBound 14 (⋃₀ ⋃₀ history))) =
        refinementDataHistoryField stages history j := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, refinementDataHistoryField, ZFSet.mem_sep]
    exact and_congr_right (fun _ => BoundedFormula.truth_refinementDataHistoryFieldFormula 1 2 0 j _)
  exact equal ▸ ground

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem refinementDataHistoryLevels_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {stages history T : ZFSet.{u}} (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (hT : T ∈ M.sets) : refinementDataHistoryLevels stages history T ∈ M.sets :=
  M.refinementHistoryAssignmentLevels_mem pairing unions powers separation hStages
    (M.refinementDataHistoryField_mem pairing unions powers separation hStages hHistory 0) hT

end TransitiveGround




end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.RefinementDataHistory
universe u
variable {stages history T : ZFSet.{u}} (valid : RefinementDataHistory stages history T)
variable {beta : ZFSet.{u}} {d : Fin 15 → ZFSet.{u}}
variable (entry : ZFSet.pair beta (refinementFormulaDataCode d) ∈ history)
include valid entry

theorem rawTests_splice_below (M : TransitiveGround.{u}) (alpha Aq Ap lower : ZFSet.{u})
    (inside : beta ∈ alpha) :
    stageOneRawTests M d (assignmentSplice (refinementDataHistoryLevels stages history T) alpha Aq Ap) lower ↔
      stageOneRawTests M d Aq lower := by
  apply stageOneRawTests_congr
  intro t ht u hu w hw
  have chosen : ∃ xi ∈ alpha, ZFSet.pair (stageOneAssignment t u w) xi ∈
      refinementDataHistoryLevels stages history T :=
    ⟨beta, inside, (valid.assignment_level_iff entry t ht u hu w hw beta).2 rfl⟩
  rw [mem_assignmentSplice]
  exact ⟨fun h => h.elim And.left (fun upper => False.elim (upper.2 chosen)),
    fun member => Or.inl ⟨member, chosen⟩⟩

theorem rawTests_splice_above (M : TransitiveGround.{u}) (alpha Aq Ap lower : ZFSet.{u})
    (outside : beta ∉ alpha) :
    stageOneRawTests M d (assignmentSplice (refinementDataHistoryLevels stages history T) alpha Aq Ap) lower ↔
      stageOneRawTests M d Ap lower := by
  apply stageOneRawTests_congr
  intro t ht u hu w hw
  have absent : ¬ ∃ xi ∈ alpha, ZFSet.pair (stageOneAssignment t u w) xi ∈
      refinementDataHistoryLevels stages history T := by
    rintro ⟨xi, hxi, member⟩
    exact outside ((valid.assignment_level_iff entry t ht u hu w hw xi).1 member ▸ hxi)
  rw [mem_assignmentSplice]
  exact ⟨fun h => h.elim (fun lower => False.elim (absent lower.2)) And.left,
    fun member => Or.inr ⟨member, absent⟩⟩

end PartitionPilot.Forcing.RefinementDataHistory



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

def StoredPreparationCode (upperOrder cutGraph meet omega C E : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u}) (p y : ZFSet.{u}) : Prop :=
  ∃ row A r k enumerations q,
    p = ZFSet.pair row A ∧ y = ZFSet.pair r (ZFSet.pair k enumerations) ∧
    ZFSet.pair r p ∈ upperOrder ∧ ZFSet.pair r q ∈ cutGraph ∧
    PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
      meet (fields 14) (fields 13) (fields 9) omega (M.storedPreparationRequests A fields)
      C E k enumerations

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

def VaryingPreparationCode (packed Q upperOrder nodes T levels omega C E z : ZFSet.{u}) : Prop :=
  ∃ alpha p y, ∃ fields : Fin 15 → ZFSet.{u},
    z = ZFSet.pair (ZFSet.pair alpha p) y ∧
    ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
    fields 6 = T ∧ fields 10 = nodes ∧
    MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
    M.StoredPreparationCode upperOrder (rowAssignmentCutGraph Q (fields 7) levels alpha)
      (canonicalMeetGraph (fields 10) (fields 11)) omega C E fields p y

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def varyingPreparationRelation
    (stages packed Q upperOrder nodes T : ZFSet.{u}) : ZFSet.{u} :=
  let W := M.groundRelations T Q
  let C := M.supportedEqualityCertificateBound nodes W
  let E := M.synchronizedEnumerationBound nodes W
  let levels := refinementDataHistoryLevels stages packed T
  ZFSet.sep (M.VaryingPreparationCode packed Q upperOrder nodes T levels ZFSet.omega C E)
    (ZFSet.prod (ZFSet.prod stages Q) (M.preparationWitnessBound nodes T Q))

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RefinementBirthEnumerationFairness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def refinementHistoryForcing (rows T stages history : ZFSet.{u}) : ZFSet.{u} :=
  M.forcingHistoryConditions rows (refinementDataHistoryIndices stages history) T stages history
    (refinementDataHistoryLevels stages history T)

theorem mem_refinementHistoryForcing (rows T stages history z : ZFSet.{u}) :
    z ∈ M.refinementHistoryForcing rows T stages history ↔
      z ∈ M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T ∧
        ForcingHistoryConditionCode M stages history (refinementDataHistoryLevels stages history T) z :=
  M.mem_forcingHistoryConditions _ _ _ _ _ _ _

noncomputable def birthLevelEnumerationRelation (Q stages levels : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ row A e, z = ZFSet.pair (ZFSet.pair row A) e ∧
    BirthLevelEnumerationCode ZFSet.omega stages A levels e)
    (ZFSet.prod Q (M.groundRelations ZFSet.omega stages))

end TransitiveGround

section
universe u

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem refinementDataHistoryCandidate_prefix {stages history rows T alpha row A : ZFSet.{u}}
    (subset : alpha ⊆ stages)
    (candidate : ZFSet.pair row A ∈ M.stageOneCandidateBound rows
      (refinementDataHistoryIndices alpha (graphRestriction alpha history)) T) :
    ZFSet.pair row A ∈ M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T := by
  obtain ⟨hrow, ground, data, small⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate
  exact (M.pair_mem_stageOneCandidateBound _ _ _ _ _).2
    ⟨hrow, ground, fun _ h => refinementDataHistoryAssignments_subset subset T (data h), small⟩

theorem refinementDataHistoryCandidate_cut (separation : SeparationSchema M.sets)
    {stages history rows T alpha row A : ZFSet.{u}}
    (valid : RefinementDataHistory stages history T) (subset : alpha ⊆ stages)
    (hLevels : refinementDataHistoryLevels stages history T ∈ M.sets)
    (hAlpha : alpha ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (candidate : ZFSet.pair row A ∈ M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T) :
    ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages history T) alpha A) ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices alpha (graphRestriction alpha history)) T := by
  have checked := M.refinementHistoryCandidate_cut separation valid.index_function valid.index_literal
    subset hLevels hAlpha omega candidate
  change ZFSet.pair row _ ∈ M.stageOneCandidateBound rows
    (refinementHistoryIndices alpha (refinementDataHistoryField alpha (graphRestriction alpha history) 0)) T
  rw [refinementDataHistoryIndices_prefix subset (fun _ h => h)]
  exact checked

theorem refinementDataHistoryCandidate_splice
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {stages history rows T alpha q Aq p Ap : ZFSet.{u}}
    (subset : alpha ⊆ stages) (hLevels : refinementDataHistoryLevels stages history T ∈ M.sets)
    (hAlpha : alpha ∈ M.sets)
    (lower : ZFSet.pair q Aq ∈ M.stageOneCandidateBound rows
      (refinementDataHistoryIndices alpha (graphRestriction alpha history)) T)
    (upper : ZFSet.pair p Ap ∈ M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T) :
    ZFSet.pair q (assignmentSplice (refinementDataHistoryLevels stages history T) alpha Aq Ap) ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T := by
  have first := ZFSet.pair_mem_prod.1 (M.refinementDataHistoryCandidate_prefix subset lower)
  have second := ZFSet.pair_mem_prod.1 upper
  exact ZFSet.pair_mem_prod.2 ⟨first.1,
    M.assignmentSplice_mem_groundSmallSubsets pairing unions powers separation infinite choice
      hLevels hAlpha first.2 second.2⟩

end TransitiveGround

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundForcingHistoryOrders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def refinementHistoryOrder (rows rowOrder T stages history : ZFSet.{u}) : ZFSet.{u} :=
  rowAssignmentOrder (M.refinementHistoryForcing rows T stages history) rows
    (M.groundSmallSubsets (stageOneAssignments (refinementDataHistoryIndices stages history) T) ZFSet.omega)
    rowOrder

theorem refinementHistoryForcing_shape (rows T stages history : ZFSet.{u}) :
    M.refinementHistoryForcing rows T stages history ⊆
      ZFSet.prod rows (M.groundSmallSubsets
        (stageOneAssignments (refinementDataHistoryIndices stages history) T) ZFSet.omega) :=
  fun z member => (M.mem_refinementHistoryForcing rows T stages history z).1 member |>.1

theorem refinementHistoryOrder_partialOrder {rows rowOrder : ZFSet.{u}}
    (order : PartialOrderCode rows rowOrder) (T stages history : ZFSet.{u}) :
    PartialOrderCode (M.refinementHistoryForcing rows T stages history)
      (M.refinementHistoryOrder rows rowOrder T stages history) :=
  rowAssignmentOrder_partialOrder (M.refinementHistoryForcing_shape rows T stages history) order

theorem pair_mem_refinementHistoryOrder (rows rowOrder T stages history q A p D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∈ M.refinementHistoryOrder rows rowOrder T stages history ↔
      ZFSet.pair q A ∈ M.refinementHistoryForcing rows T stages history ∧
        ZFSet.pair p D ∈ M.refinementHistoryForcing rows T stages history ∧
        ZFSet.pair q p ∈ rowOrder ∧ D ⊆ A := by
  rw [refinementHistoryOrder, pair_mem_rowAssignmentOrder]
  constructor
  · rintro ⟨hq, hp, _, _, _, _, below, data⟩
    exact ⟨hq, hp, below, data⟩
  · rintro ⟨hq, hp, below, data⟩
    have qShape := ZFSet.pair_mem_prod.1 (M.refinementHistoryForcing_shape rows T stages history hq)
    have pShape := ZFSet.pair_mem_prod.1 (M.refinementHistoryForcing_shape rows T stages history hp)
    exact ⟨hq, hp, qShape.1, qShape.2, pShape.1, pShape.2, below, data⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundDefinableRowAssignmentOrders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_rowAssignmentOrder :
    GroundDefinableFunction M (fun env : Fin 4 → ZFSet.{u} =>
      rowAssignmentOrder (env 0) (env 1) (env 2) (env 3)) := by
  let v := GroundSetTerm.var M (n := 4)
  let bound := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 0, v 0]
  let formula : SetFormula 4 := (BoundedFormula.rowAssignmentOrderFormula 0 1 2 3).toFormula
  let term := GroundSetTerm.app (M.definable_separation separation formula) ![bound, v 1, v 2, v 3]
  refine { formula := term.definition.formula
           closed := fun env members => M.rowAssignmentOrder_mem pairing unions powers separation
             (members 0) (members 1) (members 2) (members 3)
           correct := ?_ }
  intro env members z hz
  rw [term.definition.correct env members z hz]
  have args : (fun j : Fin 3 => (![bound, v 1, v 2, v 3] j.succ).eval env) =
      ![env 1, env 2, env 3] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j
  have equal : term.eval env = rowAssignmentOrder (env 0) (env 1) (env 2) (env 3) := by
    change ZFSet.sep (fun w => Realize M.sets formula (extend w _)) (bound.eval env) = _
    rw [args]
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_sep, mem_rowAssignmentOrder]
    apply and_congr_right
    intro hw
    change Realize M.sets (BoundedFormula.rowAssignmentOrderFormula 0 1 2 3).toFormula
      (extend w ![env 1, env 2, env 3]) ↔ _
    rw [BoundedFormula.realize_toFormula M _ (extend w ![env 1, env 2, env 3])
      (Fin.cases (M.transitive (bound.ground env members) hw)
        (Fin.cases (members 1) (Fin.cases (members 2) (Fin.cases (members 3) (fun j => Fin.elim0 j))))),
      BoundedFormula.truth_rowAssignmentOrderFormula]
    rfl
  rw [equal]

noncomputable def definable_rawRowAssignmentOrder :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} => rawRowAssignmentOrder (env 0) (env 1)) := by
  let v := GroundSetTerm.var M (n := 2)
  let fields := GroundSetTerm.app (M.definable_doubleUnion unions) ![v 0]
  exact (GroundSetTerm.app (M.definable_rowAssignmentOrder pairing unions powers separation)
    ![v 0, fields, fields, v 1]).definition

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundRecursiveRefinementBinaryUnions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

structure RecursiveRefinementDataHistory (M : TransitiveGround.{u})
    (rows T stages history : ZFSet.{u}) : Prop where
  data : RefinementDataHistory stages history T
  carrier : ∀ beta (d : Fin 15 → ZFSet.{u}),
    ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      d 7 = M.refinementHistoryForcing rows T beta (graphRestriction beta history)

namespace RecursiveRefinementDataHistory
variable {M : TransitiveGround.{u}} {rows T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M rows T stages history)
include run

theorem cut_mem {row A : ZFSet.{u}}
    (member : ZFSet.pair row A ∈ M.refinementHistoryForcing rows T stages history)
    {beta : ZFSet.{u}} (hbeta : beta ∈ stages) :
    ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages history T) beta A) ∈
      M.refinementHistoryForcing rows T beta (graphRestriction beta history) := by
  have checked := ((M.mem_refinementHistoryForcing rows T stages history _).1 member).2
  obtain ⟨code, entry, d, equal, tests⟩ := checked beta hbeta
  rw [equal] at entry
  have lower := (stageTwoConditionCode_pair_iff M d _ beta row A).1 tests |>.1
  exact run.carrier beta d entry ▸ lower

theorem restrict {earlier : ZFSet.{u}} (ordinal : ordinalSetProperty earlier)
    (subset : earlier ⊆ stages) :
    RecursiveRefinementDataHistory M rows T earlier (graphRestriction earlier history) := by
  refine ⟨run.data.restrict subset, ?_⟩
  intro beta d entry
  have packed := (pair_mem_graphRestriction.1 entry).1
  have hbeta := (pair_mem_graphRestriction.1 entry).2
  rw [graphRestriction_restrict (ordinal.1 beta hbeta)]
  exact run.carrier beta d packed

end RecursiveRefinementDataHistory




end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure RecursiveRefinementOrderHistory (M : TransitiveGround.{u})
    (rows rowOrder T stages history : ZFSet.{u}) : Prop where
  carriers : RecursiveRefinementDataHistory M rows T stages history
  order : ∀ beta (d : Fin 15 → ZFSet.{u}),
    ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      d 8 = M.refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history)

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRecursiveRowNameActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
universe u

theorem stageOneRawTests_empty (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    (lower : ZFSet.{u}) : stageOneRawTests M d ∅ lower :=
  ⟨fun _ _ _ _ _ _ member => False.elim (ZFSet.notMem_empty _ member),
    fun _ _ _ _ _ _ _ _ _ _ member _ => False.elim (ZFSet.notMem_empty _ member)⟩

namespace RecursiveRefinementDataHistory
variable {M : TransitiveGround.{u}} {rows T stages history : ZFSet.{u}}

theorem empty_assignments (run : RecursiveRefinementDataHistory M rows T stages history)
    (ordinal : ordinalSetProperty stages) (hRows : rows ∈ M.sets)
    {row : ZFSet.{u}} (hrow : row ∈ rows) :
    ZFSet.pair row ∅ ∈ M.refinementHistoryForcing rows T stages history := by
  induction stages using ZFSet.inductionOn generalizing history with
  | h stages ih =>
    apply (M.mem_refinementHistoryForcing rows T stages history _).2
    refine ⟨M.stageOneCandidateBound_empty hRows hrow, ?_⟩
    intro beta hbeta
    obtain ⟨code, entry⟩ := run.data.function.total hbeta
    obtain ⟨d, rfl⟩ := run.data.decoded beta code entry
    refine ⟨refinementFormulaDataCode d, entry, ?_⟩
    rw [packedSuccessorConditionCode_code_iff, stageTwoConditionCode_pair_iff, assignmentCut_empty_data]
    have earlierOrdinal := ordinalSetProperty_member ordinal hbeta
    have earlier := ih beta hbeta (run.restrict earlierOrdinal (ordinal.1 beta hbeta)) earlierOrdinal
    exact ⟨(run.carrier beta d entry).symm ▸ earlier, stageOneRawTests_empty M d _⟩

end RecursiveRefinementDataHistory

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RecursiveRefinementUnionConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable {alpha p Ap q Aq : ZFSet.{u}}
local notation "levels" => refinementDataHistoryLevels stages history T
local notation "spliced" => assignmentSplice levels alpha Aq Ap
include run

theorem splice_mem_of_candidates (ordinal : ordinalSetProperty stages)
    (cutOrdinal : ordinalSetProperty alpha) (cutSubset : alpha ⊆ stages)
    (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ A lower stronger, stageOneRawTests M d A lower →
        ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d A stronger)
    (upper : ZFSet.pair p Ap ∈ M.refinementHistoryForcing rows T stages history)
    (lower : ZFSet.pair q Aq ∈ M.refinementHistoryForcing rows T alpha (graphRestriction alpha history))
    (rowsBelow : ZFSet.pair q p ∈ rowOrder)
    (contains : assignmentCut levels alpha Ap ⊆ assignmentCut levels alpha Aq)
    (candidate : ZFSet.pair q spliced ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T)
    (candidates : ∀ gamma ∈ stages, ZFSet.pair q (assignmentCut levels gamma spliced) ∈
      M.stageOneCandidateBound rows
        (refinementDataHistoryIndices gamma (graphRestriction gamma history)) T) :
    ZFSet.pair q spliced ∈ M.refinementHistoryForcing rows T stages history := by
  have dataExtended : Ap ⊆ spliced := assignmentSplice_extends contains
  have oldTests := ((M.mem_refinementHistoryForcing rows T stages history _).1 upper).2
  have lowerTests := ((M.mem_refinementHistoryForcing rows T alpha (graphRestriction alpha history) _).1 lower).2
  have step (beta : ZFSet.{u}) (hbeta : beta ∈ stages) (d : Fin 15 → ZFSet.{u})
      (entry : ZFSet.pair beta (refinementFormulaDataCode d) ∈ history)
      (proved : ZFSet.pair q (assignmentCut levels beta spliced) ∈
        M.refinementHistoryForcing rows T beta (graphRestriction beta history)) :
      stageOneRawTests M d spliced (ZFSet.pair q (assignmentCut levels beta spliced)) := by
    by_cases inside : beta ∈ alpha
    · have stored := (forcingHistoryConditionCode_lookup_iff
        (run.carriers.data.function.restrict cutSubset)).1 lowerTests beta inside
        (refinementFormulaDataCode d) (pair_mem_graphRestriction.2 ⟨entry, inside⟩)
      have checked := (stageTwoConditionCode_pair_iff M d _ beta q Aq).1
        ((packedSuccessorConditionCode_code_iff M _ beta d _).1 stored)
      have sameCut := run.carriers.data.prefix_cut cutSubset (cutOrdinal.1 beta inside) Aq
      rw [sameCut] at checked
      have sameSplice : assignmentCut levels beta spliced = assignmentCut levels beta Aq :=
        assignmentCut_splice_below (cutOrdinal.1 beta inside) Aq Ap
      rw [sameSplice]
      exact (run.carriers.data.rawTests_splice_below entry M alpha Aq Ap _ inside).2 checked.2
    · have stored := (forcingHistoryConditionCode_lookup_iff run.carriers.data.function).1 oldTests
        beta hbeta (refinementFormulaDataCode d) entry
      have checked := (stageTwoConditionCode_pair_iff M d _ beta p Ap).1
        ((packedSuccessorConditionCode_code_iff M _ beta d _).1 stored)
      have order : ZFSet.pair (ZFSet.pair q (assignmentCut levels beta spliced))
          (ZFSet.pair p (assignmentCut levels beta Ap)) ∈ d 8 := by
        rw [run.order beta d entry]
        exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history)
          _ _ _ _).2 ⟨proved, run.carriers.cut_mem upper hbeta, rowsBelow, assignmentCut_mono dataExtended⟩
      exact (run.carriers.data.rawTests_splice_above entry M alpha Aq Ap _ inside).2
        (mono beta d entry Ap _ _ checked.2 order)
  have earlier : ∀ gamma ∈ stages, ZFSet.pair q (assignmentCut levels gamma spliced) ∈
      M.refinementHistoryForcing rows T gamma (graphRestriction gamma history) := by
    intro gamma
    induction gamma using ZFSet.inductionOn with
    | h gamma ih =>
      intro hgamma
      apply (M.mem_refinementHistoryForcing rows T gamma (graphRestriction gamma history) _).2
      refine ⟨candidates gamma hgamma, ?_⟩
      intro beta hbeta
      have betaFull := ordinal.1 gamma hgamma beta hbeta
      have betaSubset := ordinal.2 gamma hgamma beta hbeta
      obtain ⟨data, entry⟩ := run.carriers.data.function.total betaFull
      obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
      have proved := ih beta hbeta betaFull
      have sameCut := run.carriers.data.prefix_cut (ordinal.1 gamma hgamma) betaSubset
        (assignmentCut levels gamma spliced)
      refine ⟨refinementFormulaDataCode d, pair_mem_graphRestriction.2 ⟨entry, hbeta⟩, ?_⟩
      apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
      apply (stageTwoConditionCode_pair_iff M d _ beta q _).2
      rw [sameCut, assignmentCut_nested betaSubset]
      refine ⟨(run.carriers.carrier beta d entry).symm ▸ proved, ?_⟩
      exact stageOneRawTests_transfer M d _ (step beta betaFull d entry proved)
        (fun _ _ _ _ _ _ member => assignmentCut_subset levels gamma spliced member)
  apply (M.mem_refinementHistoryForcing rows T stages history _).2
  refine ⟨candidate, ?_⟩
  intro beta hbeta
  obtain ⟨data, entry⟩ := run.carriers.data.function.total hbeta
  obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
  refine ⟨refinementFormulaDataCode d, entry, ?_⟩
  apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
  apply (stageTwoConditionCode_pair_iff M d _ beta q _).2
  exact ⟨(run.carriers.carrier beta d entry).symm ▸ earlier beta hbeta,
    step beta hbeta d entry (earlier beta hbeta)⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory



namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
local notation "levels" => refinementDataHistoryLevels stages history T
include run

theorem union_lower_bound_of_candidates (ordinal : ordinalSetProperty stages)
    (unionTests : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ (family lower : Nat → ZFSet.{u}) q,
        (∀ n m, n ≤ m → family n ⊆ family m) →
        (∀ n, ZFSet.pair q (lower n) ∈ d 8) →
        (∀ n, stageOneRawTests M d (family n) (lower n)) →
        stageOneRawTests M d (stageOneAssignmentUnion family) q)
    (family row : Nat → ZFSet.{u}) (q : ZFSet.{u})
    (members : ∀ n, ZFSet.pair (row n) (family n) ∈ M.refinementHistoryForcing rows T stages history)
    (increasing : ∀ n m, n ≤ m → family n ⊆ family m)
    (rowsBelow : ∀ n, ZFSet.pair q (row n) ∈ rowOrder)
    (candidate : ZFSet.pair q (stageOneAssignmentUnion family) ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T)
    (candidates : ∀ gamma ∈ stages,
      ZFSet.pair q (assignmentCut levels gamma (stageOneAssignmentUnion family)) ∈
        M.stageOneCandidateBound rows (refinementDataHistoryIndices gamma (graphRestriction gamma history)) T) :
    ZFSet.pair q (stageOneAssignmentUnion family) ∈ M.refinementHistoryForcing rows T stages history ∧
      ∀ n, ZFSet.pair (ZFSet.pair q (stageOneAssignmentUnion family)) (ZFSet.pair (row n) (family n)) ∈
        M.refinementHistoryOrder rows rowOrder T stages history := by
  have step (beta : ZFSet.{u}) (hbeta : beta ∈ stages) (d : Fin 15 → ZFSet.{u})
      (entry : ZFSet.pair beta (refinementFormulaDataCode d) ∈ history)
      (proved : ZFSet.pair q (assignmentCut levels beta (stageOneAssignmentUnion family)) ∈
        M.refinementHistoryForcing rows T beta (graphRestriction beta history)) :
      stageOneRawTests M d (stageOneAssignmentUnion family)
        (ZFSet.pair q (assignmentCut levels beta (stageOneAssignmentUnion family))) := by
    apply unionTests beta d entry family
      (fun n => ZFSet.pair (row n) (assignmentCut levels beta (family n))) _ increasing
    · intro n
      rw [run.order beta d entry]
      exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history)
        _ _ _ _).2 ⟨proved, run.carriers.cut_mem (members n) hbeta, rowsBelow n,
          assignmentCut_mono (stageOneAssignmentUnion_contains family n)⟩
    · intro n
      have oldTests := ((M.mem_refinementHistoryForcing rows T stages history _).1 (members n)).2
      have stored := (forcingHistoryConditionCode_lookup_iff run.carriers.data.function).1 oldTests
        beta hbeta (refinementFormulaDataCode d) entry
      exact ((stageTwoConditionCode_pair_iff M d _ beta (row n) (family n)).1
        ((packedSuccessorConditionCode_code_iff M _ beta d _).1 stored)).2
  have earlier : ∀ gamma ∈ stages,
      ZFSet.pair q (assignmentCut levels gamma (stageOneAssignmentUnion family)) ∈
        M.refinementHistoryForcing rows T gamma (graphRestriction gamma history) := by
    intro gamma
    induction gamma using ZFSet.inductionOn with
    | h gamma ih =>
      intro hgamma
      apply (M.mem_refinementHistoryForcing rows T gamma (graphRestriction gamma history) _).2
      refine ⟨candidates gamma hgamma, ?_⟩
      intro beta hbeta
      have betaFull := ordinal.1 gamma hgamma beta hbeta
      have betaSubset := ordinal.2 gamma hgamma beta hbeta
      obtain ⟨data, entry⟩ := run.carriers.data.function.total betaFull
      obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
      have proved := ih beta hbeta betaFull
      have sameCut := run.carriers.data.prefix_cut (ordinal.1 gamma hgamma) betaSubset
        (assignmentCut levels gamma (stageOneAssignmentUnion family))
      refine ⟨refinementFormulaDataCode d, pair_mem_graphRestriction.2 ⟨entry, hbeta⟩, ?_⟩
      apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
      apply (stageTwoConditionCode_pair_iff M d _ beta q _).2
      rw [sameCut, assignmentCut_nested betaSubset]
      refine ⟨(run.carriers.carrier beta d entry).symm ▸ proved, ?_⟩
      exact stageOneRawTests_transfer M d _ (step beta betaFull d entry proved)
        (fun _ _ _ _ _ _ member => assignmentCut_subset levels gamma (stageOneAssignmentUnion family) member)
  have member : ZFSet.pair q (stageOneAssignmentUnion family) ∈ M.refinementHistoryForcing rows T stages history := by
    apply (M.mem_refinementHistoryForcing rows T stages history _).2
    refine ⟨candidate, ?_⟩
    intro beta hbeta
    obtain ⟨data, entry⟩ := run.carriers.data.function.total hbeta
    obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
    refine ⟨refinementFormulaDataCode d, entry, ?_⟩
    apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
    apply (stageTwoConditionCode_pair_iff M d _ beta q _).2
    exact ⟨(run.carriers.carrier beta d entry).symm ▸ earlier beta hbeta,
      step beta hbeta d entry (earlier beta hbeta)⟩
  exact ⟨member, fun n => (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history _ _ _ _).2
    ⟨member, members n, rowsBelow n, stageOneAssignmentUnion_contains family n⟩⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundRecursiveRowCompleteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization
universe u
namespace RecursiveRefinementDataHistory
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history top : ZFSet.{u}}

theorem greatest (run : RecursiveRefinementDataHistory M rows T stages history)
    (ordinal : ordinalSetProperty stages) (hRows : rows ∈ M.sets)
    (topMem : top ∈ rows) (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder) :
    ∀ z ∈ M.refinementHistoryForcing rows T stages history,
      ZFSet.pair z (ZFSet.pair top ∅) ∈ M.refinementHistoryOrder rows rowOrder T stages history :=
  rowAssignmentOrder_top (M.refinementHistoryForcing_shape rows T stages history) topRows
    (run.empty_assignments ordinal hRows topMem)

end RecursiveRefinementDataHistory
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {rows rowOrder : ZFSet.{u}}
variable (order : PartialOrderCode rows rowOrder) (T stages history : ZFSet.{u})

@[instance_reducible] noncomputable def refinementHistoryPartialOrder :
    PartialOrder (SetMembers (M.refinementHistoryForcing rows T stages history)) :=
  (M.refinementHistoryOrder_partialOrder order T stages history).toPartialOrder

@[instance_reducible] noncomputable def refinementHistoryOrderTop
    (run : RecursiveRefinementDataHistory M rows T stages history)
    (ordinal : ordinalSetProperty stages) (hRows : rows ∈ M.sets)
    (top : ZFSet.{u}) (topMem : top ∈ rows)
    (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder) :
    letI := M.refinementHistoryPartialOrder order T stages history
    OrderTop (SetMembers (M.refinementHistoryForcing rows T stages history)) :=
  (M.refinementHistoryOrder_partialOrder order T stages history).toOrderTop (ZFSet.pair top ∅)
    (run.empty_assignments ordinal hRows topMem) (run.greatest ordinal hRows topMem topRows)

end TransitiveGround

end

namespace RecursiveRefinementOrderHistory
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
variable {alpha p Ap q Aq : ZFSet.{u}} (hAlpha : alpha ∈ M.sets)
variable (ordinal : ordinalSetProperty stages) (cutOrdinal : ordinalSetProperty alpha)
variable (cutSubset : alpha ⊆ stages)
variable (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
  ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
  ∀ A lower stronger, stageOneRawTests M d A lower →
    ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d A stronger)
include run pairing unions powers separation infinite choice hStages hHistory hT hAlpha ordinal cutOrdinal cutSubset mono
local notation "levels" => refinementDataHistoryLevels stages history T
local notation "spliced" => assignmentSplice levels alpha Aq Ap

theorem splice_mem
    (upper : ZFSet.pair p Ap ∈ M.refinementHistoryForcing rows T stages history)
    (lower : ZFSet.pair q Aq ∈ M.refinementHistoryForcing rows T alpha (graphRestriction alpha history))
    (rowsBelow : ZFSet.pair q p ∈ rowOrder)
    (contains : assignmentCut levels alpha Ap ⊆ assignmentCut levels alpha Aq) :
    ZFSet.pair q spliced ∈ M.refinementHistoryForcing rows T stages history := by
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hHistory hT
  have candidate := M.refinementDataHistoryCandidate_splice pairing unions powers separation infinite choice
    cutSubset hLevels hAlpha
    ((M.mem_refinementHistoryForcing rows T alpha (graphRestriction alpha history) _).1 lower).1
    ((M.mem_refinementHistoryForcing rows T stages history _).1 upper).1
  exact run.splice_mem_of_candidates ordinal cutOrdinal cutSubset mono upper lower rowsBelow contains candidate
    (fun beta hbeta => M.refinementDataHistoryCandidate_cut separation run.carriers.data
      (ordinal.1 beta hbeta) hLevels (M.transitive hStages hbeta) (M.omega_mem separation infinite) candidate)

theorem splice_lifting
    (upper : ZFSet.pair p Ap ∈ M.refinementHistoryForcing rows T stages history)
    (below : ZFSet.pair (ZFSet.pair q Aq) (ZFSet.pair p (assignmentCut levels alpha Ap)) ∈
      M.refinementHistoryOrder rows rowOrder T alpha (graphRestriction alpha history)) :
    ZFSet.pair q spliced ∈ M.refinementHistoryForcing rows T stages history ∧
      ZFSet.pair (ZFSet.pair q spliced) (ZFSet.pair p Ap) ∈
        M.refinementHistoryOrder rows rowOrder T stages history ∧
      assignmentCut levels alpha spliced = Aq := by
  obtain ⟨lower, _, rowsBelow, contains⟩ :=
    (M.pair_mem_refinementHistoryOrder rows rowOrder T alpha (graphRestriction alpha history) _ _ _ _).1 below
  have lowerData := ((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1
    ((M.mem_refinementHistoryForcing rows T alpha (graphRestriction alpha history) _).1 lower).1).2.2.1
  have fullLower := run.carriers.data.prefix_assignments_cut cutSubset lowerData
  have retained : assignmentCut levels alpha Ap ⊆ assignmentCut levels alpha Aq := by
    rw [fullLower]
    exact contains
  have member := run.splice_mem pairing unions powers separation infinite choice hStages hHistory hT hAlpha
    ordinal cutOrdinal cutSubset mono upper lower rowsBelow retained
  refine ⟨member, (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history _ _ _ _).2
    ⟨member, upper, rowsBelow, assignmentSplice_extends retained⟩, ?_⟩
  rw [assignmentCut_splice, fullLower]

end RecursiveRefinementOrderHistory

namespace RecursiveRefinementOrderHistory
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history alpha : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (ordinal : ordinalSetProperty stages) (cutOrdinal : ordinalSetProperty alpha)
variable (subset : alpha ⊆ stages)
include run ordinal cutOrdinal subset

theorem cut_mem_le {row A : ZFSet.{u}}
    (member : ZFSet.pair row A ∈ M.refinementHistoryForcing rows T stages history) :
    ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages history T) alpha A) ∈
      M.refinementHistoryForcing rows T alpha (graphRestriction alpha history) := by
  have compare : alpha ∈ stages ∨ alpha = stages := by
    obtain ⟨a, ea⟩ := (ordinalSetProperty_iff alpha).1 cutOrdinal
    obtain ⟨b, eb⟩ := (ordinalSetProperty_iff stages).1 ordinal
    have below := (ordinalCode_subset_iff a b).1 (ea ▸ eb ▸ subset)
    rcases lt_or_eq_of_le below with less | equal
    · exact Or.inl (ea ▸ eb ▸ (mem_ordinalCode_iff a b).2 less)
    · exact Or.inr (ea.trans ((congrArg ordinalCode equal).trans eb.symm))
  rcases compare with earlier | rfl
  · exact run.carriers.cut_mem member earlier
  · rw [run.carriers.data.function.restriction_eq]
    have data := ((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1
      ((M.mem_refinementHistoryForcing rows T _ history _).1 member).1).2.2.1
    rw [assignmentCut_full run.carriers.data.levels_function data]
    exact member

theorem cut_order_le {q A p D : ZFSet.{u}}
    (below : ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∈
      M.refinementHistoryOrder rows rowOrder T stages history) :
    ZFSet.pair
      (ZFSet.pair q (assignmentCut (refinementDataHistoryLevels stages history T) alpha A))
      (ZFSet.pair p (assignmentCut (refinementDataHistoryLevels stages history T) alpha D)) ∈
      M.refinementHistoryOrder rows rowOrder T alpha (graphRestriction alpha history) := by
  obtain ⟨hq, hp, rowBelow, data⟩ := (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history _ _ _ _).1 below
  exact (M.pair_mem_refinementHistoryOrder rows rowOrder T alpha (graphRestriction alpha history) _ _ _ _).2
    ⟨run.cut_mem_le ordinal cutOrdinal subset hq, run.cut_mem_le ordinal cutOrdinal subset hp,
      rowBelow, assignmentCut_mono data⟩

theorem include_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
    (hAlpha : alpha ∈ M.sets) (hRows : rows ∈ M.sets)
    (top : ZFSet.{u}) (topMem : top ∈ rows) (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder)
    (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ A lower stronger, stageOneRawTests M d A lower →
        ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d A stronger)
    {q Aq : ZFSet.{u}}
    (lower : ZFSet.pair q Aq ∈ M.refinementHistoryForcing rows T alpha (graphRestriction alpha history)) :
    ZFSet.pair q Aq ∈ M.refinementHistoryForcing rows T stages history := by
  have lowerFacts := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1
    ((M.mem_refinementHistoryForcing rows T alpha (graphRestriction alpha history) _).1 lower).1
  have fullLower := run.carriers.data.prefix_assignments_cut subset lowerFacts.2.2.1
  have member := run.splice_mem pairing unions powers separation infinite choice hStages hHistory hT hAlpha
    ordinal cutOrdinal subset mono (run.carriers.empty_assignments ordinal hRows topMem) lower
    (topRows q lowerFacts.1) (by
      rw [assignmentCut_empty_data]
      exact fun z impossible => False.elim (ZFSet.notMem_empty z impossible))
  have equal : assignmentSplice (refinementDataHistoryLevels stages history T) alpha Aq ∅ = Aq := by
    rw [assignmentSplice, fullLower]
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_union, mem_assignmentUpper]
    exact ⟨fun h => h.elim id (fun h => False.elim (ZFSet.notMem_empty z h.1)), Or.inl⟩
  exact equal ▸ member

end RecursiveRefinementOrderHistory

namespace RecursiveRefinementOrderHistory
open SetRealization
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history alpha : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (ordinal : ordinalSetProperty stages) (cutOrdinal : ordinalSetProperty alpha)
variable (subset : alpha ⊆ stages)
local notation "U" => M.refinementHistoryForcing rows T stages history
local notation "L" => M.refinementHistoryForcing rows T alpha (graphRestriction alpha history)
local notation "levels" => refinementDataHistoryLevels stages history T
local notation "sU" => SetMembers.presentation U
local notation "sL" => SetMembers.presentation L
include run ordinal cutOrdinal subset

theorem restrictionGraph_function :
    ZFSet.IsFunc U L (rowAssignmentCutGraph U L levels alpha) :=
  rowAssignmentCutGraph_function U L levels alpha
    (fun z member => by
      obtain ⟨row, _, A, _, equal⟩ := ZFSet.mem_prod.1 (M.refinementHistoryForcing_shape rows T stages history member)
      exact ⟨row, A, equal⟩)
    (fun _ _ member => run.cut_mem_le ordinal cutOrdinal subset member)

noncomputable def restrictionFunction : SetMembers U → SetMembers L :=
  (sU).decodeFunction sL (rowAssignmentCutGraph U L levels alpha)
    (run.restrictionGraph_function ordinal cutOrdinal subset)

theorem restrictionFunction_raw (x : SetMembers U) (row A : ZFSet.{u})
    (code : SetMembers.raw x = ZFSet.pair row A) :
    SetMembers.raw (run.restrictionFunction ordinal cutOrdinal subset x) =
      ZFSet.pair row (assignmentCut levels alpha A) := by
  have entry := (sU).decodeFunction_mem sL (rowAssignmentCutGraph U L levels alpha)
    (run.restrictionGraph_function ordinal cutOrdinal subset) x
  change ZFSet.pair (SetMembers.raw x)
    (SetMembers.raw (run.restrictionFunction ordinal cutOrdinal subset x)) ∈ _ at entry
  rw [code] at entry
  exact ((pair_mem_rowAssignmentCutGraph U L levels alpha row A _).1 entry).2.2

noncomputable def restriction (order : PartialOrderCode rows rowOrder) :
    letI := M.refinementHistoryPartialOrder order T stages history
    letI := M.refinementHistoryPartialOrder order T alpha (graphRestriction alpha history)
    SetMembers U →o SetMembers L := by
  letI := M.refinementHistoryPartialOrder order T stages history
  letI := M.refinementHistoryPartialOrder order T alpha (graphRestriction alpha history)
  refine { toFun := run.restrictionFunction ordinal cutOrdinal subset, monotone' := ?_ }
  intro x y below
  obtain ⟨q, _, A, _, xCode⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape rows T stages history (SetMembers.raw_mem x))
  obtain ⟨p, _, D, _, yCode⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape rows T stages history (SetMembers.raw_mem y))
  change ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ _ at below
  change ZFSet.pair (SetMembers.raw (run.restrictionFunction ordinal cutOrdinal subset x))
    (SetMembers.raw (run.restrictionFunction ordinal cutOrdinal subset y)) ∈ _
  rw [run.restrictionFunction_raw ordinal cutOrdinal subset x q A xCode,
    run.restrictionFunction_raw ordinal cutOrdinal subset y p D yCode]
  rw [xCode, yCode] at below
  exact run.cut_order_le ordinal cutOrdinal subset below

end RecursiveRefinementOrderHistory

namespace RecursiveRefinementOrderHistory
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history alpha : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (ordinal : ordinalSetProperty stages) (cutOrdinal : ordinalSetProperty alpha)
variable (subset : alpha ⊆ stages)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
variable (hAlpha : alpha ∈ M.sets) (hRows : rows ∈ M.sets)
variable (top : ZFSet.{u}) (topMem : top ∈ rows) (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder)
variable (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
  ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
  ∀ A lower stronger, stageOneRawTests M d A lower →
    ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d A stronger)
local notation "U" => M.refinementHistoryForcing rows T stages history
local notation "L" => M.refinementHistoryForcing rows T alpha (graphRestriction alpha history)
include run ordinal cutOrdinal subset pairing unions powers separation infinite choice hStages hHistory hT hAlpha hRows topMem topRows mono

noncomputable def inclusionFunction (x : SetMembers L) : SetMembers U :=
  SetMembers.ofMem (SetMembers.raw x) (by
    obtain ⟨row, _, A, _, equal⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T alpha (graphRestriction alpha history) (SetMembers.raw_mem x))
    rw [equal]
    exact run.include_mem ordinal cutOrdinal subset pairing unions powers separation infinite choice
      hStages hHistory hT hAlpha hRows top topMem topRows mono (equal ▸ SetMembers.raw_mem x))

local notation "inc" => run.inclusionFunction ordinal cutOrdinal subset pairing unions powers separation infinite choice
  hStages hHistory hT hAlpha hRows top topMem topRows mono

theorem inclusionFunction_raw (x : SetMembers L) : SetMembers.raw (inc x) = SetMembers.raw x :=
  SetMembers.raw_ofMem _ _

noncomputable def inclusion (order : PartialOrderCode rows rowOrder) :
    letI := M.refinementHistoryPartialOrder order T stages history
    letI := M.refinementHistoryPartialOrder order T alpha (graphRestriction alpha history)
    SetMembers L ↪o SetMembers U := by
  letI := M.refinementHistoryPartialOrder order T stages history
  letI := M.refinementHistoryPartialOrder order T alpha (graphRestriction alpha history)
  have raw := run.inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation infinite choice
    hStages hHistory hT hAlpha hRows top topMem topRows mono
  refine { toFun := inc, inj' := ?_, map_rel_iff' := ?_ }
  · intro x y equal
    apply SetMembers.raw_injective L
    exact (raw x).symm.trans ((congrArg SetMembers.raw equal).trans (raw y))
  · intro x y
    change ZFSet.pair (SetMembers.raw (inc x)) (SetMembers.raw (inc y)) ∈ _ ↔
      ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ _
    rw [raw x, raw y]
    have hx := SetMembers.raw_mem x
    have hy := SetMembers.raw_mem y
    have ux := SetMembers.raw_mem (inc x)
    have uy := SetMembers.raw_mem (inc y)
    rw [raw x] at ux
    rw [raw y] at uy
    obtain ⟨q, _, A, _, xCode⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T alpha (graphRestriction alpha history) hx)
    obtain ⟨p, _, D, _, yCode⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T alpha (graphRestriction alpha history) hy)
    rw [xCode] at hx ux
    rw [yCode] at hy uy
    rw [xCode, yCode, M.pair_mem_refinementHistoryOrder, M.pair_mem_refinementHistoryOrder]
    simp only [hx, hy, ux, uy, true_and]

end RecursiveRefinementOrderHistory

namespace RecursiveRefinementOrderHistory
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history alpha : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (ordinal : ordinalSetProperty stages) (cutOrdinal : ordinalSetProperty alpha)
variable (subset : alpha ⊆ stages)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
variable (hAlpha : alpha ∈ M.sets) (hRows : rows ∈ M.sets)
variable (top : ZFSet.{u}) (topMem : top ∈ rows) (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder)
variable (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
  ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
  ∀ A lower stronger, stageOneRawTests M d A lower →
    ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d A stronger)
local notation "U" => M.refinementHistoryForcing rows T stages history
local notation "L" => M.refinementHistoryForcing rows T alpha (graphRestriction alpha history)
local notation "levels" => refinementDataHistoryLevels stages history T
local notation "res" => run.restrictionFunction ordinal cutOrdinal subset
local notation "inc" => run.inclusionFunction ordinal cutOrdinal subset pairing unions powers separation infinite choice
  hStages hHistory hT hAlpha hRows top topMem topRows mono
include run ordinal cutOrdinal subset pairing unions powers separation infinite choice hStages hHistory hT hAlpha hRows topMem topRows mono

theorem completeProjection (order : PartialOrderCode rows rowOrder) :
    letI := M.refinementHistoryPartialOrder order T stages history
    letI := M.refinementHistoryPartialOrder order T alpha (graphRestriction alpha history)
    CompleteProjection (run.restriction ordinal cutOrdinal subset order)
      (run.inclusion ordinal cutOrdinal subset pairing unions powers separation infinite choice
        hStages hHistory hT hAlpha hRows top topMem topRows mono order) := by
  let := M.refinementHistoryPartialOrder order T stages history
  let := M.refinementHistoryPartialOrder order T alpha (graphRestriction alpha history)
  have incRaw := run.inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation infinite choice
    hStages hHistory hT hAlpha hRows top topMem topRows mono
  have resRaw := run.restrictionFunction_raw ordinal cutOrdinal subset
  have lowerFixed : ∀ (x : SetMembers L) row A, SetMembers.raw x = ZFSet.pair row A →
      assignmentCut levels alpha A = A := by
    intro x row A code
    have member := SetMembers.raw_mem x
    rw [code] at member
    exact run.carriers.data.prefix_assignments_cut subset
      (((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1
        ((M.mem_refinementHistoryForcing rows T alpha (graphRestriction alpha history) _).1 member).1).2.2.1)
  refine ⟨?_, ?_, ?_⟩
  · intro q
    change res (inc q) = q
    obtain ⟨row, _, A, _, code⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T alpha (graphRestriction alpha history) (SetMembers.raw_mem q))
    apply SetMembers.raw_injective L
    rw [resRaw (inc q) row A ((incRaw q).trans code), lowerFixed q row A code, code]
  · intro p q
    obtain ⟨rowP, _, Ap, _, pCode⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T stages history (SetMembers.raw_mem p))
    obtain ⟨rowQ, _, Aq, _, qCode⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T alpha (graphRestriction alpha history) (SetMembers.raw_mem q))
    have hp := SetMembers.raw_mem p
    have hq := SetMembers.raw_mem q
    have hinc := SetMembers.raw_mem (inc q)
    have hres := SetMembers.raw_mem (res p)
    rw [pCode] at hp
    rw [qCode] at hq
    rw [incRaw q, qCode] at hinc
    rw [resRaw p rowP Ap pCode] at hres
    change ZFSet.pair (SetMembers.raw p) (SetMembers.raw (inc q)) ∈ _ ↔
      ZFSet.pair (SetMembers.raw (res p)) (SetMembers.raw q) ∈ _
    rw [incRaw q, resRaw p rowP Ap pCode, pCode, qCode,
      M.pair_mem_refinementHistoryOrder, M.pair_mem_refinementHistoryOrder]
    simp only [hp, hq, hinc, hres, true_and]
    constructor
    · rintro ⟨rowsBelow, data⟩
      refine ⟨rowsBelow, ?_⟩
      have cutData : assignmentCut levels alpha Aq ⊆ assignmentCut levels alpha Ap := assignmentCut_mono data
      rwa [lowerFixed q rowQ Aq qCode] at cutData
    · rintro ⟨rowsBelow, data⟩
      exact ⟨rowsBelow, fun _ member => assignmentCut_subset levels alpha Ap (data member)⟩
  · intro p q below
    obtain ⟨rowP, _, Ap, _, pCode⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T stages history (SetMembers.raw_mem p))
    obtain ⟨rowQ, _, Aq, _, qCode⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T alpha (graphRestriction alpha history) (SetMembers.raw_mem q))
    have hp := SetMembers.raw_mem p
    rw [pCode] at hp
    change ZFSet.pair (SetMembers.raw q) (SetMembers.raw (res p)) ∈ _ at below
    rw [resRaw p rowP Ap pCode, qCode] at below
    obtain ⟨member, stronger, exactCut⟩ := run.splice_lifting pairing unions powers separation infinite choice
      hStages hHistory hT hAlpha ordinal cutOrdinal subset mono hp below
    let r : SetMembers U := SetMembers.ofMem (ZFSet.pair rowQ (assignmentSplice levels alpha Aq Ap)) member
    have rCode : SetMembers.raw r = ZFSet.pair rowQ (assignmentSplice levels alpha Aq Ap) :=
      SetMembers.raw_ofMem _ _
    refine ⟨r, ?_, ?_⟩
    · change ZFSet.pair (SetMembers.raw r) (SetMembers.raw p) ∈ _
      rwa [rCode, pCode]
    · change res r = q
      apply SetMembers.raw_injective L
      rw [resRaw r rowQ (assignmentSplice levels alpha Aq Ap) rCode, exactCut, qCode]

end RecursiveRefinementOrderHistory

end PartitionPilot.Forcing

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



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def definable_emptyFromGround :
    GroundDefinableFunction M (fun _env : Fin 1 → ZFSet.{u} => (∅ : ZFSet.{u})) where
  formula := (BoundedFormula.emptyFormula 0).toFormula
  closed := fun env members => M.empty_mem ⟨env 0, members 0⟩
  correct := by
    intro env members z hz
    exact (BoundedFormula.realize_toFormula M _ (extend z env) (Fin.cases hz members)).trans
      (BoundedFormula.truth_emptyFormula 0 _)

noncomputable def definable_rawFlatForcingStage
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 8 → ZFSet.{u} =>
      rawFlatForcingStage (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7)) := by
  let v := GroundSetTerm.var M (n := 8)
  let order := GroundSetTerm.app (M.definable_rawRowAssignmentOrder pairing unions powers separation) ![v 0, v 2]
  let emptyData := GroundSetTerm.app M.definable_emptyFromGround ![v 0]
  let top := GroundSetTerm.app (M.definable_nonemptyTuple pairing 1) ![v 3, emptyData]
  let dataBound := GroundSetTerm.app (M.definable_doubleUnion unions) ![v 0]
  let action := GroundSetTerm.app (M.definable_rawRowAssignmentActionGraph pairing unions powers separation collection)
    ![v 5, v 0, v 1, dataBound, v 6, v 4, v 7]
  exact (GroundSetTerm.app (M.definable_nonemptyTuple pairing 3) ![v 0, order, top, action]).definition

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundStoredPreparationFamilyPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization
universe u

structure StoredPreparationEnvironment (M : TransitiveGround.{u})
    (fields : Fin 15 → ZFSet.{u}) : Prop where
  order : PartialOrderCode (fields 7) (fields 8)
  ground : ∀ j, fields j ∈ M.sets
  names_valid : ∀ z ∈ fields 14, IsName (SetMembers.presentation (fields 7)) z
  visibility_valid : ∀ v V, ZFSet.pair v V ∈ fields 13 → v ∈ fields 10 →
    IsName (SetMembers.presentation (fields 7)) V

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPreparedWitnessSelections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

def StoredPreparedConditionCode (M : TransitiveGround.{u})
    (rows T stages history nodes p : ZFSet.{u}) : Prop :=
  let Q := M.refinementHistoryForcing rows T stages history
  ∀ row A, p = ZFSet.pair row A → ∀ x ∈ A,
    ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history ∧
      fields 6 = T ∧ fields 10 = nodes ∧
      MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
      StoredPreparationEnvironment M fields ∧
    ∃ sourceRow sourceA, sourceA ∈ M.sets ∧ ZFSet.pair sourceRow sourceA ∈ Q ∧
      sourceA ⊆ A ∧ x ∈ assignmentOnIndices (fields 0) T sourceA ∧
    ∃ k ∈ M.sets, ∃ enumerations ∈ M.sets, ∃ q ∈ fields 7,
      ZFSet.pair p q ∈ rowAssignmentCutGraph Q (fields 7)
        (refinementDataHistoryLevels stages history T) alpha ∧
      PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
        (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
        ZFSet.omega (M.storedPreparationRequests sourceA fields)
        (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) k enumerations





def StoredSupportPreparedConditionCode (M : TransitiveGround.{u})
    (rows T stages history nodes p S : ZFSet.{u}) : Prop :=
  let Q := M.refinementHistoryForcing rows T stages history
  ∀ row A, p = ZFSet.pair row A → ∀ x ∈ A,
    ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history ∧
      fields 6 = T ∧ fields 10 = nodes ∧
      MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
      StoredPreparationEnvironment M fields ∧
    ∃ sourceRow sourceA, sourceA ∈ M.sets ∧ ZFSet.pair sourceRow sourceA ∈ Q ∧
      sourceA ⊆ A ∧ x ∈ assignmentOnIndices (fields 0) T sourceA ∧
    ∃ k ∈ M.sets, ∃ enumerations ∈ M.sets, ∃ q ∈ fields 7,
      ZFSet.pair p q ∈ rowAssignmentCutGraph Q (fields 7)
        (refinementDataHistoryLevels stages history T) alpha ∧
      PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
        (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
        ZFSet.omega (M.storedPreparationRequests sourceA fields)
        (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) k enumerations ∧
      certificateUsedSupports nodes k ⊆ S

end PartitionPilot.Forcing




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCertificateBasisUnions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def certificateBasisGraph (J nodes N k : ZFSet.{u}) : ZFSet.{u} :=
  let bases := M.groundSmallSubsets nodes ZFSet.omega
  let functions := M.groundRelations nodes N
  let tail := ZFSet.prod bases functions
  relationCompose J tail bases
    (relationCompose J (M.supportedEqualityCertificateBound nodes N) tail k
      (productSecond (M.groundPower nodes) tail))
    (productFirst bases functions)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundOrdinaryEqualityDecisionFusion
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def definable_ordinaryEqualityDecisions (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 4 → ZFSet.{u} =>
      M.ordinaryEqualityDecisions (env 1) (env 2) (env 0) (env 3)) := by
  let defined := (M.definable_separation separation
    (ordinaryEqualityDecisionFormula 1 2 0 3 4)).reindex (![1, 1, 2, 0, 3] : Fin 5 → Fin 4)
  refine defined.congr ?_
  intro env
  apply congrArg (fun params : Fin 4 → ZFSet.{u} =>
    ZFSet.sep (fun z => Realize M.sets (ordinaryEqualityDecisionFormula 1 2 0 3 4)
      (extend z params)) (env 1))
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) j

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPreparedAlignedReferenceCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)





def TypedPreparedCertificate (nodeOrder meet omega : ZFSet.{u})
    (z : Name s) (p : P) (F B f e names : ZFSet.{u}) : Prop :=
  MeetFilterCode b.carrier nodeOrder meet F ∧
  CoinitialBelowCode nodeOrder F F B ∧ B.Nonempty ∧
  SynchronizedEnumerationCode omega (M.niceSupportNameCodes a s T K) B f e names ∧
  f ⊆ M.niceSupportRelation a s b T K ∧
  M.DecidesVisibilityProfile a s b K T F z p ∧
  ∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T K →
    ZFSet.pair v tau.val ∈ f → Name.ForcesEq p z tau

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundFairPreparationLimitCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v

def FairPreparationLowerBoundResult (M : TransitiveGround.{u})
    {R : Type u} [PartialOrder R] (c : Presentation R)
    (T stages packed nodes p : ZFSet.{u}) : Prop :=
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  let upperOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let relation := M.varyingPreparationRelation stages packed upperQ upperOrder nodes T
  let B := M.groundSmallSubsets
    (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
  let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
  let data := flatCarrierData c upperQ B shape
    ∃ enumSelector ∈ M.sets,
        ZFSet.IsFunc upperQ (M.groundRelations ZFSet.omega stages) enumSelector ∧
        enumSelector ⊆ M.birthLevelEnumerationRelation upperQ stages
          (refinementDataHistoryLevels stages packed T) ∧
      ∃ E0 ∈ M.sets, ZFSet.IsFunc upperQ E0 enumSelector ∧
      ∃ prepSelector ∈ M.sets,
        ZFSet.IsFunc (ZFSet.prod stages upperQ)
          (M.preparationWitnessBound nodes T upperQ) prepSelector ∧
        prepSelector ⊆ relation ∧
      ∃ seq : Nat → SetMembers upperQ, SetMembers.raw (seq 0) = p ∧
        groundSequenceGraph seq ∈ M.sets ∧
        (∀ i j : Nat, i ≤ j → ZFSet.pair (SetMembers.raw (seq j)) (SetMembers.raw (seq i)) ∈ upperOrder) ∧
      ∃ e ∈ E0, ZFSet.pair p e ∈ enumSelector ∧
      ∃ clocks births events : Nat → ZFSet.{u},
        clocks 0 = ∅ ∧ births 0 = {ZFSet.pair ∅ e} ∧ events 0 = ∅ ∧
        (∀ k, FairPreparationStepCode ZFSet.omega E0 stages
          (M.preparationWitnessBound nodes T upperQ) enumSelector prepSelector
          (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv)
          (ZFSet.pair (clocks k) (ZFSet.pair (SetMembers.raw (seq k)) (ZFSet.pair (births k) (events k))))
          (ZFSet.pair (clocks (k + 1))
            (ZFSet.pair (SetMembers.raw (seq (k + 1))) (ZFSet.pair (births (k + 1)) (events (k + 1)))))) ∧
      ∃ limit : SetMembers upperQ,
        (∀ n, ZFSet.pair (SetMembers.raw limit) (SetMembers.raw (seq n)) ∈ upperOrder) ∧
        SetMembers.raw (data limit) = stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∧
        stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∈ M.sets ∧
        (∀ z, z ∈ SetMembers.raw (data limit) ↔ ∃ n, z ∈ SetMembers.raw (data (seq n))) ∧
        ∀ x ∈ SetMembers.raw (data limit),
          ∃ i j : Nat, ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
            Nat.unpair (Nat.pair i j) = (i, j) ∧ i ≤ Nat.pair i j ∧
            x ∈ SetMembers.raw (data (seq i)) ∧
            ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
            ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages packed T ∧
            (∀ k, Nat.pair i j ≤ k →
              x ∈ assignmentOnIndices (fields 0) T (SetMembers.raw (data (seq k)))) ∧
            ∃ y ∈ M.preparationWitnessBound nodes T upperQ, ∃ payload,
              y = ZFSet.pair (SetMembers.raw (seq (Nat.pair i j + 1))) payload ∧
              ZFSet.pair (ZFSet.pair alpha (SetMembers.raw (seq (Nat.pair i j)))) y ∈ prepSelector ∧
              events (Nat.pair i j + 1) = ZFSet.pair alpha y

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalStructuralCommonSupportInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


section

namespace PartitionPilot.Forcing.SetFormula

def rectangleBodyFormula : SetFormula 15 :=
  .conj rectangleOrderFormula.toFormula
    (.conj (atomicApplication codedNameActionFormula (extend 10 (extend 14 Fin.elim0)) 3 6 8)
      (.conj (atomicApplication codedNameActionFormula (extend 10 (extend 14 Fin.elim0)) 2 6 9)
        (ex (.conj
          (atomicApplication codedNameActionFormula (extend 11 (extend 15 Fin.elim0)) 4 8 0)
          (atomicApplication codedNameActionFormula (extend 11 (extend 15 Fin.elim0)) 3 8 0)))))

def rectangleWitnessFormula : SetFormula 11 :=
  exConditions 8 (exConditions 9 (exConditions 8 (exConditions 9 rectangleBodyFormula)))

end PartitionPilot.Forcing.SetFormula

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalStructuralSupportPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v

def GroundSupportPreparedStrengtheningResult (M : TransitiveGround.{u})
    {R : Type u} [PartialOrder R] (c : Presentation R)
    (T stages packed nodes p : ZFSet.{u}) : Prop :=
  let Q := M.refinementHistoryForcing c.carrier T stages packed
  ∃ q ∈ Q,
    ZFSet.pair q p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
    ∃ S ∈ M.sets, S ⊆ nodes ∧ M.groundEmbeddable S ZFSet.omega ∧
      StoredSupportPreparedConditionCode M c.carrier T stages packed nodes q S

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundMainFinalGraphValueCandidateAvailability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def graphValueCandidateCodes (K : Subgroup G) (tau : Name s) : ZFSet.{u} :=
  Name.supportedFamilyCodes a s K
    (a.orbitCodes s (M.nameDomain s) (Name.descendantFamilyCodes s tau 4))

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v

def GraphValueCandidateDensity (M : TransitiveGround.{u})
    {G P : Type u} [Group G] [PartialOrder P] (action : PosetAction G P)
    (presentation : Presentation P) (support : Subgroup G)
    (z beta : (M.nameDomain presentation).names) (base : P) : Prop :=
  DenseBelow base {q | ∃ tau : (M.nameDomain presentation).names,
    tau.val.val ∈ M.graphValueCandidateCodes action presentation support z.val ∧
    Forces (M.nameDomain presentation) (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula
      (extend tau (extend z (extend beta Fin.elim0))) q}

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundOrdinaryMembershipAntichainFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def definable_ordinaryMembershipDecisions (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 4 → ZFSet.{u} =>
      M.ordinaryMembershipDecisions (env 1) (env 2) (env 0) (env 3)) := by
  let defined := (M.definable_separation separation
    (ordinaryMembershipDecisionFormula 1 2 0 3 4)).reindex (![1, 1, 2, 0, 3] : Fin 5 → Fin 4)
  refine defined.congr ?_
  intro env
  apply congrArg (fun params : Fin 4 → ZFSet.{u} =>
    ZFSet.sep (fun z => Realize M.sets (ordinaryMembershipDecisionFormula 1 2 0 3 4)
      (extend z params)) (env 1))
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) j

end PartitionPilot.Forcing.TransitiveGround

end OAI
end


