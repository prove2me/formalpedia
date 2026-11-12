-- Prove2me | Definitions.Def_OAIQ253P009
-- name    : OAIQ253P009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T06:05:14.494204+00:00
-- url     : https://prove2.me/theorems/48a208e2-7661-4b30-b82d-acaeb0ba5be0
-- title:
--   Definitions bundle OAIQ253P009 of the split of OpenAI, The Partition Principle does not imply Choice
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 370 declarations of OpenAI's Lean: 102 definitions, 7 inductive types or structures and 261 theorems. The definitions and types are `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FixedTopStage`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FixedTopStage.RankedChronology`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FixedTopStage.RankedChronology.cone`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FixedTopStage.RankedChronology.linked`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FixedTopStage.RankedChronology.main`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FixedTopStage.RankedChronology.transition`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FixedTopStage.chronologyValues`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FixedTopStage.transition`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.LimitAct`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.LimitBirthValue`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.LimitCoverage`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.LimitInv`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.LimitLE`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.LimitMeet`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.LimitMul`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.actorPresentation`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.appendCone`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.appendKey`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.appendLast`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.appendLinked`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.appendSourceBound`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.appendTransitionGraph`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.finalGeometry`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.finalInclusions`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.finalInsertionActors`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.finalInsertionCaps`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.heightRangeFamily`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.heightRangeValues`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.limitActorMap`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.limitBottom`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.limitHeightRange`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.limitIdentity`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.limitInverse`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.limitMultiplication`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.limitPointMap`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.ofFinite`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.pointPresentation`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.pointStageCover` and 69 more.
--
--   **Sources.** They come from these modules of lean/OAI/SetTheory, in whole or in part: `PartitionPrinciple_Definability_GroundDefinableRelationProducts`, `PartitionPrinciple_Definability_GroundNiceVisibilityGraphs`, `PartitionPrinciple_Definability_GroundPrincipalNiceSupportCodes`, `PartitionPrinciple_Definability_GroundRefinementPairClassGraphs`, `PartitionPrinciple_Definability_GroundSelectedSupportTupleFamilies`, `PartitionPrinciple_Definability_GroundSemanticAugmentedClassRequests`, `PartitionPrinciple_Definability_GroundSemanticFairPreparationLimits`, `PartitionPrinciple_Definability_GroundSemanticFairPreparationRecordedLimits`, `PartitionPrinciple_Definability_GroundSemanticStructuralDataSupport`, `PartitionPrinciple_Definability_GroundVaryingPreparationRelations`, `PartitionPrinciple_Definability_LinkedProfileTransitionRawCodes`, `PartitionPrinciple_Definability_SeparationEntryFormulas`, `PartitionPrinciple_Definability_StructuralAssignmentActionFormulas`, `PartitionPrinciple_Definability_StructuralRefinementHistoryFormulas`, `PartitionPrinciple_Forcing_FinitePrincipalNameSupports`, `PartitionPrinciple_Forcing_GroundDefinableRefinementNameGraphs`, `PartitionPrinciple_Forcing_GroundForcingHistoryOrders`, `PartitionPrinciple_Forcing_GroundGraphValueDescendantWitnesses`, `PartitionPrinciple_Forcing_GroundMainFinalSupportConstruction`, `PartitionPrinciple_Forcing_GroundMainPrefixInsertionFamilyTransport`, `PartitionPrinciple_Forcing_GroundMainPrefixLimitActionLaws`, `PartitionPrinciple_Forcing_GroundNameSequenceForcingWitness`, `PartitionPrinciple_Forcing_GroundNiceNameGraphs`, `PartitionPrinciple_Forcing_GroundNiceNameNormalization`, `PartitionPrinciple_Forcing_GroundNiceSupportEvaluation`, `PartitionPrinciple_Forcing_GroundPreparationForcing`, `PartitionPrinciple_Forcing_GroundPreparedWitnessSelections`, `PartitionPrinciple_Forcing_GroundRawNiceNameGraphs`, `PartitionPrinciple_Forcing_GroundRawRowAssignmentActions`, `PartitionPrinciple_Forcing_GroundRawStageRefinementTestActions`, `PartitionPrinciple_Forcing_GroundRecursiveRowNameActions`, `PartitionPrinciple_Forcing_GroundRenamedNameFamilyBounds`, `PartitionPrinciple_Forcing_GroundSharedConditionalNames`, `PartitionPrinciple_Forcing_GroundStructuralForcingActionGraphs`, `PartitionPrinciple_Forcing_GroundStructuralForcingHistoryConstruction`, `PartitionPrinciple_Forcing_IndexedTupleNames`, `PartitionPrinciple_Forcing_StructuralAssignmentActionGraphs`, `PartitionPrinciple_Forcing_StructuralAssignmentActionLaws`, `PartitionPrinciple_Forcing_StructuralForcingStageWitnessStep`, `PartitionPrinciple_Geometry_GroundDefinableIndexBounds`, `PartitionPrinciple_Geometry_GroundDefinableRowAssignmentOrders`, `PartitionPrinciple_Geometry_GroundHartogs`, `PartitionPrinciple_Geometry_GroundLinkedTransitionRetarget`, `PartitionPrinciple_Geometry_GroundMainFinalFulfillmentConstruction`, `PartitionPrinciple_Geometry_GroundMainFinalRowTerms`, `PartitionPrinciple_Geometry_GroundMixtureDensityRecovery`, `PartitionPrinciple_Geometry_GroundNiceRefinementVisibility`, `PartitionPrinciple_Geometry_GroundOmegaOneRowModel`, `PartitionPrinciple_Geometry_GroundPreparedSelectionProfiles`, `PartitionPrinciple_Geometry_GroundRawRefinementDataIdentification`, `PartitionPrinciple_Geometry_GroundSharedRefinementValidity`, `PartitionPrinciple_Geometry_RepresentativeIndexSteps`, `PartitionPrinciple_Geometry_StructuralPreparationSourceImages`, `PartitionPrinciple_Transfinite_CodedMainPrefixSystems`, `PartitionPrinciple_Transfinite_GroundBinaryRowStageOneRefinement`, `PartitionPrinciple_Transfinite_GroundDefinableRefinementHistories`, `PartitionPrinciple_Transfinite_GroundHistoryUnionBounds`, `PartitionPrinciple_Transfinite_GroundInitialMainStage`, `PartitionPrinciple_Transfinite_GroundMainFinalChronology`, `PartitionPrinciple_Transfinite_GroundMainPrefixConePreservation`, `PartitionPrinciple_Transfinite_GroundMainPrefixDecoding`, `PartitionPrinciple_Transfinite_GroundMainPrefixFieldFamilies`, `PartitionPrinciple_Transfinite_GroundMainPrefixFinalInsertion`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitBottom`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitChronologyCore`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitCoverageConstruction`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitCoverageGraph`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitGroupLaws`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitSizes`, `PartitionPrinciple_Transfinite_GroundMainPrefixPreservedSeeds`, `PartitionPrinciple_Transfinite_GroundMainPrefixPriorFields`, `PartitionPrinciple_Transfinite_GroundMainPrefixTopColumns`, `PartitionPrinciple_Transfinite_GroundRecursiveRefinementInternalClosure`, `PartitionPrinciple_Transfinite_GroundRecursiveRowCompleteProjection`, `PartitionPrinciple_Transfinite_GroundStructuralHistoryTestUnions`, `PartitionPrinciple_Transfinite_GroundStructuralRefinementHistories`, `PartitionPrinciple_Transfinite_MainPrefixHistoryUnionRecognition`, `PartitionPrinciple_Transfinite_RecursiveStructuralRefinementHistories`, `PartitionPrinciple_Transfinite_RefinementBirthEnumerationFairness`.
--
--   **Imports.** It imports the published bundle `Def_PartitionPrinciple`; the bundles `OAIQ253P006`, `OAIQ253P007` and `OAIQ253P008` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ253P011`; the statements `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.exists_groundConditionalPrefixFunction`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalChronology.final_insertion_of_trace`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment.structural_bounds_with`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_compatible_insertion_unions`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_support_prepared_strengthening`, `OAI.PartitionPilot.Forcing.TransitiveGround.binaryRowStructuralAssignmentImage_dataBound`, `OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialMainSuccessor`, `OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundMainFinalFulfillment`, `OAI.PartitionPilot.Forcing.TransitiveGround.exists_initialRecursionSeed`, `OAI.PartitionPilot.Forcing.TransitiveGround.omegaOne_taskBearingSuccessor_total`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralFairPreparation_supported_lower_bound`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_preparationEvent_certificate_domain`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_commonPowerAntichains`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_storedPreparation_request_bounds` and `OAI.PartitionPilot.Forcing.TransitiveGround.structuralAssignment_prepared_insertion_collision`; the proofs of `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.exists_groundConditionalPrefixFunction`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalChronology.final_insertion_of_trace`, `OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialMainSuccessor`, `OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundMainFinalFulfillment`, `OAI.PartitionPilot.Forcing.TransitiveGround.exists_initialRecursionSeed`, `OAI.PartitionPilot.Forcing.TransitiveGround.omegaOne_taskBearingSuccessor_total`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralFairPreparation_supported_lower_bound` and `OAI.PartitionPilot.Forcing.TransitiveGround.structuralAssignment_prepared_insertion_collision`.
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
import Definitions.Def_OAIQ253P006
import Definitions.Def_OAIQ253P007
import Definitions.Def_OAIQ253P008

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SeparationEntryFormulas
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

theorem realize_separationEntryFormula (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k n m : Nat} (A : ForcingPrimitives k) (φ : SetFormula (n + 1))
    (params : Fin k → Fin m) (names : Fin n → Fin m) (zi ti : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params A.carrier) = s.carrier) (ho : env (params A.order) = s.conditionOrder)
    (atomic : M.EqualityMeaning s D A.equality (fun j => env (params j)))
    (domain : M.DomainMeaning s D A.domain (fun j => env (params j)))
    (nameEnv : Assignment D n) (hnames : ∀ i, env (names i) = (nameEnv i).val.val)
    (τ : D.names) (hτ : env ti = τ.val.val) (hz : env zi ∈ M.sets) :
    Realize M.sets (separationEntryFormula A φ params names zi ti) env ↔
      env zi ∈ (Name.separationName D φ nameEnv τ.val).val := by
  have hτM : env ti ∈ M.sets := hτ ▸ ground τ.val τ.property
  rw [separationEntryFormula, realize_ex]
  constructor
  · rintro ⟨x, hx, rest⟩
    obtain ⟨p, rest⟩ := (M.realize_exConditions s (params A.carrier).succ _ (extend x env) carrier hc).1 rest
    obtain ⟨r, shape, old, pr, forced⟩ := (M.realize_exConditions s (params A.carrier).succ.succ _
      (extend (s.encode p) (extend x env)) carrier hc).1 rest
    let e := extend (s.encode r) (extend (s.encode p) (extend x env))
    have raw := (M.realize_pairMembershipFormula pairing 2 0 ti.succ.succ.succ e hx
      (M.transitive carrier (s.encode_mem r)) hτM).1 old
    change ZFSet.pair x (s.encode r) ∈ env ti at raw
    rw [hτ] at raw
    let σ : Name s := ⟨x, Name.isName_of_pair_mem τ.val x r raw⟩
    have hσ : σ ∈ D.names := D.children τ.property raw
    have eq := (M.realize_orderedPairFormula pairing zi.succ.succ.succ 2 1 e hz hx
      (M.transitive carrier (s.encode_mem p))).1 shape
    have forcing := (M.realize_forcingTranslation s D ground pairing carrier order A φ
      (fun j => (params j).succ.succ.succ) 1 (extend 2 (fun i => (names i).succ.succ.succ))
      e hc ho atomic domain p (extend ⟨σ, hσ⟩ nameEnv) rfl
      (fun i => Fin.cases rfl (fun j => hnames j) i)).1 forced
    change env zi = ZFSet.pair x (s.encode p) at eq
    rw [eq]
    exact (Name.entry_separationName D φ nameEnv τ.val σ p).2
      ⟨r, raw, (M.realize_conditionLE s pairing carrier order 1 0 (params A.order).succ.succ.succ
        e p r rfl rfl ho).1 pr, hσ, forcing⟩
  · intro member
    obtain ⟨σ, p, eq⟩ := Name.entries_cover (Name.separationName D φ nameEnv τ.val) member
    have entry : Name.Entry σ (Name.separationName D φ nameEnv τ.val) p := by
      change ZFSet.pair σ.val (s.encode p) ∈ (Name.separationName D φ nameEnv τ.val).val
      rw [← eq]
      exact member
    obtain ⟨r, old, pr, hσ, forced⟩ := (Name.entry_separationName D φ nameEnv τ.val σ p).1 entry
    refine ⟨σ.val, ground σ hσ, ?_⟩
    apply (M.realize_exConditions s (params A.carrier).succ _ (extend σ.val env) carrier hc).2
    refine ⟨p, ?_⟩
    apply (M.realize_exConditions s (params A.carrier).succ.succ _
      (extend (s.encode p) (extend σ.val env)) carrier hc).2
    let e := extend (s.encode r) (extend (s.encode p) (extend σ.val env))
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing zi.succ.succ.succ 2 1 e hz (ground σ hσ)
        (M.transitive carrier (s.encode_mem p))).2 eq
    · apply (M.realize_pairMembershipFormula pairing 2 0 ti.succ.succ.succ e (ground σ hσ)
        (M.transitive carrier (s.encode_mem r)) hτM).2
      change ZFSet.pair σ.val (s.encode r) ∈ env ti
      rw [hτ]
      exact old
    · exact (M.realize_conditionLE s pairing carrier order 1 0 (params A.order).succ.succ.succ
        e p r rfl rfl ho).2 pr
    · exact (M.realize_forcingTranslation s D ground pairing carrier order A φ
        (fun j => (params j).succ.succ.succ) 1 (extend 2 (fun i => (names i).succ.succ.succ))
        e hc ho atomic domain p (extend ⟨σ, hσ⟩ nameEnv) rfl
        (fun i => Fin.cases rfl (fun j => hnames j) i)).2 forced

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_FinitePrincipalNameSupports
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem niceNameCandidates_mem {I : Type u} (t : Presentation G) (b : Presentation I)
    (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (i : I) (hi : b.encode i ∈ M.sets) :
    M.niceNameCandidates a s T (K i) ∈ M.sets := by
  let B := M.groundRelations T s.carrier
  have hB : B ∈ M.sets := M.groundRelations_mem pairing unions powers separation hT carrier
  let params := extend (b.encode i) (extend s.carrier (extend t.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0))))
  have selected := M.separation_mem separation nameSupportFormula params
    (Fin.cases hi (Fin.cases carrier (Fin.cases group (Fin.cases supports
      (Fin.cases maps (fun j => Fin.elim0 j)))))) hB
  have equal : ZFSet.sep (fun z => Realize M.sets nameSupportFormula (extend z params)) B =
      M.niceNameCandidates a s T (K i) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, niceNameCandidates, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    have data := (M.mem_groundRelations T s.carrier z).1 hz
    let τ := Name.ofSubset valid data.2
    have fixed := M.realize_nameSupportFormula a s t b K pairing unions powers separation collection
      carrier group supports maps i hi τ data.1
    change Realize M.sets nameSupportFormula (extend τ.val params) ↔ NiceNameCode a s T (K i) τ.val
    rw [fixed]
    constructor
    · intro h
      exact ⟨τ, rfl, data.2, h⟩
    · rintro ⟨σ, eq, _, h⟩
      have same : σ = τ := Subtype.ext eq
      exact same ▸ h
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

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


section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem separationName_mem (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k n m : Nat} (A : ForcingPrimitives k) (φ : SetFormula (n + 1))
    (params : Fin k → Fin m) (names : Fin n → Fin m) (context : Fin m → ZFSet.{u})
    (members : ∀ i, context i ∈ M.sets)
    (hc : context (params A.carrier) = s.carrier) (ho : context (params A.order) = s.conditionOrder)
    (atomic : M.EqualityMeaning s D A.equality (fun j => context (params j)))
    (domain : M.DomainMeaning s D A.domain (fun j => context (params j)))
    (nameEnv : Assignment D n) (hnames : ∀ i, context (names i) = (nameEnv i).val.val) (τ : D.names) :
    (Name.separationName D φ nameEnv τ.val).val ∈ M.sets := by
  have hτ := ground τ.val τ.property
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers
    (M.union_mem unions (M.union_mem unions hτ)) carrier
  have bound : (Name.separationName D φ nameEnv τ.val).val ⊆ B := by
    intro z hz
    obtain ⟨σ, p, rfl⟩ := Name.entries_cover (Name.separationName D φ nameEnv τ.val) hz
    obtain ⟨r, old, _, _⟩ := (Name.entry_separationName D φ nameEnv τ.val σ p).1 hz
    exact pairBound σ.val (Name.child_mem_doubleUnion old) (s.encode p) (s.encode_mem p)
  let selected := separationEntryFormula A φ (fun j => (params j).succ.succ)
    (fun i => (names i).succ.succ) 0 1
  let fullContext := extend τ.val.val context
  have correct : ∀ z ∈ M.sets, Realize M.sets selected (extend z fullContext) ↔
      z ∈ (Name.separationName D φ nameEnv τ.val).val := by
    intro z hz
    exact M.realize_separationEntryFormula s D ground pairing carrier order A φ
      (fun j => (params j).succ.succ) (fun i => (names i).succ.succ) 0 1 (extend z fullContext)
      hc ho atomic domain nameEnv hnames τ rfl hz
  have selectedM := M.separation_mem separation selected fullContext (Fin.cases hτ members) hB
  have eq : ZFSet.sep (fun z => Realize M.sets selected (extend z fullContext)) B =
      (Name.separationName D φ nameEnv τ.val).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (correct z (M.transitive hB hz)).1 rel
    · intro hz
      exact ⟨bound hz, (correct z (M.transitive hB (bound hz))).2 hz⟩
  exact eq ▸ selectedM

end PartitionPilot.Forcing.TransitiveGround



end


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


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P) (one : P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (hone : s.encode one ∈ M.sets)
include pairing unions powers separation collection hone

theorem realize_indexedGraphValueFormula {I f : ZFSet.{u}}
    (hf : f ∈ M.sets) (function : FunctionGraphOn I f) (i : I.toSet)
    (hi : i.val ∈ M.sets) (w : ZFSet.{u}) (hw : w ∈ M.sets) :
    Realize M.sets indexedGraphValueFormula
      (extend i.val (extend w (extend f (extend (s.encode one) Fin.elim0)))) ↔
      w = orderedPairNameCode (s.encode one) (Name.check s one i.val).val (function.value i) := by
  rw [indexedGraphValueFormula, realize_ex]
  constructor
  · rintro ⟨v, hv, rest⟩
    obtain ⟨k, hk, entry, checked, shape⟩ := (realize_ex M.sets _ _).1 rest
    have ev := function.value_eq_of_entry i
      ((M.realize_pairMembershipFormula pairing 2 1 4 _ hi hv hf).1 entry)
    rw [realize_binaryApplication, map_extend, map_empty] at checked
    have ek := (M.realize_uniformCheckFormula s one pairing unions powers separation collection
      hone i.val k hi hk).1 checked
    have all : ∀ j, (extend k (extend v (extend i.val
        (extend w (extend f (extend (s.encode one) Fin.elim0)))))) j ∈ M.sets :=
      Fin.cases hk (Fin.cases hv (Fin.cases hi (Fin.cases hw (Fin.cases hf
        (Fin.cases hone (fun j => Fin.elim0 j))))))
    have eq := (M.realize_orderedPairNameCodeFormula pairing 3 0 1 5 _ all).1 shape
    exact eq.trans (congrArg₂ (orderedPairNameCode (s.encode one)) ek ev.symm)
  · intro equal
    have hv := function.value_mem M hf i
    have hk := M.check_mem s one pairing unions powers separation collection hone i.val hi
    refine ⟨function.value i, hv, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.check s one i.val).val, hk, ?_, ?_, ?_⟩
    · exact (M.realize_pairMembershipFormula pairing 2 1 4 _ hi hv hf).2 (function.value_entry i)
    · rw [realize_binaryApplication, map_extend, map_empty]
      exact (M.realize_uniformCheckFormula s one pairing unions powers separation collection
        hone i.val _ hi hk).2 rfl
    · have all : ∀ j, (extend (Name.check s one i.val).val (extend (function.value i)
          (extend i.val (extend w (extend f (extend (s.encode one) Fin.elim0)))))) j ∈ M.sets :=
        Fin.cases hk (Fin.cases hv (Fin.cases hi (Fin.cases hw (Fin.cases hf
          (Fin.cases hone (fun j => Fin.elim0 j))))))
      exact (M.realize_orderedPairNameCodeFormula pairing 3 0 1 5 _ all).2 equal

theorem realize_indexedGraphNameEntryFormula {I f : ZFSet.{u}}
    (hI : I ∈ M.sets) (hf : f ∈ M.sets) (function : FunctionGraphOn I f)
    (names : ∀ i, IsName s (function.value i)) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets indexedGraphNameEntryFormula
      (extend z (extend I (extend f (extend (s.encode one) Fin.elim0)))) ↔
      z ∈ (Name.indexedGraphName one function names).val := by
  rw [indexedGraphNameEntryFormula, realize_ex, Name.mem_indexedGraphName_code]
  constructor
  · rintro ⟨i, hiM, rest⟩
    obtain ⟨w, hw, hi, code, shape⟩ := (realize_ex M.sets _ _).1 rest
    rw [realize_binaryApplication, map_extend, map_extend, map_empty] at code
    have eq := (M.realize_indexedGraphValueFormula s one pairing unions powers separation collection
      hone hf function ⟨i, hi⟩ hiM w hw).1 code
    have shapeEq := (M.realize_orderedPairFormula pairing 2 0 5 _ hz hw hone).1 shape
    exact ⟨⟨i, hi⟩, shapeEq.trans (congrArg (fun v => ZFSet.pair v (s.encode one)) eq)⟩
  · rintro ⟨i, shape⟩
    have hiM := M.transitive hI i.property
    have hw := M.orderedPairNameCode_mem pairing hone
      (M.check_mem s one pairing unions powers separation collection hone i.val hiM)
      (function.value_mem M hf i)
    refine ⟨i.val, hiM, ?_⟩
    rw [realize_ex]
    refine ⟨orderedPairNameCode (s.encode one) (Name.check s one i.val).val (function.value i),
      hw, i.property, ?_, ?_⟩
    · rw [realize_binaryApplication, map_extend, map_extend, map_empty]
      exact (M.realize_indexedGraphValueFormula s one pairing unions powers separation collection
        hone hf function i hiM _ hw).2 rfl
    · exact (M.realize_orderedPairFormula pairing 2 0 5 _ hz hw hone).2 shape

theorem indexedGraphName_mem {I f : ZFSet.{u}}
    (hI : I ∈ M.sets) (hf : f ∈ M.sets) (function : FunctionGraphOn I f)
    (names : ∀ i, IsName s (function.value i)) :
    (Name.indexedGraphName one function names).val ∈ M.sets := by
  let params := extend f (extend (s.encode one) Fin.elim0)
  have members : ∀ j, params j ∈ M.sets := Fin.cases hf (Fin.cases hone (fun j => Fin.elim0 j))
  have witnesses : ∀ i ∈ I, ∃ w ∈ M.sets,
      Realize M.sets indexedGraphValueFormula (extend i (extend w params)) := by
    intro i hi
    let j : I.toSet := ⟨i, hi⟩
    have hiM := M.transitive hI hi
    have hw := M.orderedPairNameCode_mem pairing hone
      (M.check_mem s one pairing unions powers separation collection hone i hiM)
      (function.value_mem M hf j)
    exact ⟨_, hw, (M.realize_indexedGraphValueFormula s one pairing unions powers separation collection
      hone hf function j hiM _ hw).2 rfl⟩
  obtain ⟨W, hW, covers⟩ := M.collection_witness collection indexedGraphValueFormula params members hI witnesses
  have inW (i : I.toSet) :
      orderedPairNameCode (s.encode one) (Name.check s one i.val).val (function.value i) ∈ W := by
    obtain ⟨w, hw, code⟩ := covers i.val i.property
    have eq := (M.realize_indexedGraphValueFormula s one pairing unions powers separation collection
      hone hf function i (M.transitive hI i.property) w (M.transitive hW hw)).1 code
    exact eq ▸ hw
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers hW
    (M.unorderedPair_mem pairing hone hone)
  have bound : (Name.indexedGraphName one function names).val ⊆ B := by
    intro z hz
    obtain ⟨i, rfl⟩ := (Name.mem_indexedGraphName_code one function names z).1 hz
    exact pairBound _ (inW i) _ (ZFSet.mem_pair.2 (Or.inl rfl))
  let entryParams := extend I (extend f (extend (s.encode one) Fin.elim0))
  have selected := M.separation_mem separation indexedGraphNameEntryFormula entryParams
    (Fin.cases hI (Fin.cases hf (Fin.cases hone (fun j => Fin.elim0 j)))) hB
  have equal : ZFSet.sep (fun z => Realize M.sets indexedGraphNameEntryFormula
      (extend z entryParams)) B = (Name.indexedGraphName one function names).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, code⟩
      exact (M.realize_indexedGraphNameEntryFormula s one pairing unions powers separation collection
        hone hI hf function names z (M.transitive hB hz)).1 code
    · intro hz
      exact ⟨bound hz, (M.realize_indexedGraphNameEntryFormula s one pairing unions powers separation collection
        hone hI hf function names z (M.transitive hB (bound hz))).2 hz⟩
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)

theorem inputEvaluationName_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (carrier : s.carrier ∈ M.sets)
    {J : ZFSet.{u}} (hJ : J ∈ M.sets) (valid : ∀ z ∈ J, IsName s z) :
    (Name.inputEvaluationName s J valid).val ∈ M.sets :=
  M.indexedGraphName_mem s ⊤ pairing unions powers separation collection
    (M.transitive carrier (s.encode_mem ⊤)) hJ
    (M.identityFunctionGraph_mem pairing unions powers separation hJ) _ _

end TransitiveGround

end PartitionPilot.Forcing



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

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundHartogs
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {N : ZFSet.{u}} (hN : N ∈ M.sets) :
    ∃ C ∈ M.sets, ordinalSetProperty C ∧
      (∀ A : ZFSet.{u}, A ∈ C ↔ A ∈ M.sets ∧ ordinalSetProperty A ∧ M.groundEmbeddable A N) ∧
      ¬ M.groundEmbeddable C N := by
  let params := extend N Fin.elim0
  let D := ZFSet.sep (fun r => Realize M.sets representedOrdinalRelationFormula
    (extend r params)) (M.groundRelations N N)
  have hD : D ∈ M.sets := M.separation_mem separation representedOrdinalRelationFormula params
    (Fin.cases hN (fun i => Fin.elim0 i))
    (M.groundRelations_mem pairing unions powers separation hN hN)
  have total : ∀ r ∈ M.sets, r ∈ D → ∃ A ∈ M.sets,
      Realize M.sets ordinalImageWitnessFormula (extend r (extend A params)) ∧
      ∀ B ∈ M.sets, Realize M.sets ordinalImageWitnessFormula (extend r (extend B params)) → B = A := by
    intro r hr rD
    obtain ⟨A, hA, ordA, f, hf, injF, eqF⟩ :=
      (M.realize_representedOrdinalRelationFormula hr hN).1 (ZFSet.mem_sep.1 rD).2
    refine ⟨A, hA, (M.realize_ordinalImageWitnessFormula hr hA hN).2 ⟨ordA, f, hf, injF, eqF⟩, ?_⟩
    intro B hB relB
    obtain ⟨ordB, g, _, injG, eqG⟩ := (M.realize_ordinalImageWitnessFormula hr hB hN).1 relB
    exact ordinalImageOrder_domain_unique ordB ordA injG injF (eqG.symm.trans eqF)
  obtain ⟨C, hC, represented⟩ := replacement_of_collection_separation M.sets collection separation
    ordinalImageWitnessFormula params (Fin.cases hN (fun i => Fin.elim0 i)) D hD total
  have exactMembers (A : ZFSet.{u}) :
      A ∈ C ↔ A ∈ M.sets ∧ ordinalSetProperty A ∧ M.groundEmbeddable A N := by
    constructor
    · intro hAC
      have hA := M.transitive hC hAC
      obtain ⟨r, hr, _, rel⟩ := (represented A hA).1 hAC
      obtain ⟨ordA, f, hf, inj, _⟩ := (M.realize_ordinalImageWitnessFormula hr hA hN).1 rel
      exact ⟨hA, ordA, f, hf, inj⟩
    · rintro ⟨hA, ordA, f, hf, inj⟩
      let r := ordinalImageOrder A N f
      have hr : r ∈ M.sets := M.ordinalImageOrder_mem pairing unions powers separation hA hN hf
      have witness := (M.realize_ordinalImageWitnessFormula hr hA hN).2 ⟨ordA, f, hf, inj, rfl⟩
      have rD : r ∈ D := ZFSet.mem_sep.2
        ⟨(M.mem_groundRelations N N r).2 ⟨hr, ordinalImageOrder_subset A N f⟩,
          (M.realize_representedOrdinalRelationFormula hr hN).2 ⟨A, hA, ordA, f, hf, inj, rfl⟩⟩
      exact (represented A hA).2 ⟨r, hr, rD, witness⟩
  have ordinal : ordinalSetProperty C := by
    refine ⟨?_, fun A hA => ((exactMembers A).1 hA).2.1.1⟩
    intro A hAC B hBA
    obtain ⟨hA, ordA, smallA⟩ := (exactMembers A).1 hAC
    have hB := M.transitive hA hBA
    exact (exactMembers B).2 ⟨hB, ordinalSetProperty_member ordA hBA,
      M.groundEmbeddable_restrict separation hB hN (fun z hz => ordA.1 B hBA z hz) smallA⟩
  exact ⟨C, hC, ordinal, exactMembers,
    fun small => ZFSet.mem_irrefl C ((exactMembers C).2 ⟨hC, ordinal, small⟩)⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNiceNameNormalization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

omit [OrderTop P] in
include pairing unions powers separation collection carrier order in
theorem ordinarySeparationName_mem {n : Nat} (φ : SetFormula (n + 1))
    (nameEnv : Assignment (M.nameDomain s) n) (τ : (M.nameDomain s).names) :
    (Name.separationName (M.nameDomain s) φ nameEnv τ.val).val ∈ M.sets := by
  let context := extend s.carrier (extend s.conditionOrder (fun i => (nameEnv i).val.val))
  let params : Fin 2 → Fin (n + 2) := extend 0 (extend 1 Fin.elim0)
  have members : ∀ i, context i ∈ M.sets :=
    Fin.cases carrier (Fin.cases order (fun i => (nameEnv i).property))
  apply M.separationName_mem s (M.nameDomain s) (fun _ h => h)
    pairing unions powers separation carrier order (ordinaryGroundPrimitives 0 1)
    φ params (fun i => i.succ.succ) context members rfl rfl
  · exact M.equalityMeaning_lifted s (M.nameDomain s) (fun _ h => h)
      pairing unions powers separation collection carrier order 0 1 _ rfl rfl
  · exact M.domainMeaning_liftedNames s pairing unions powers separation collection carrier 0 _ rfl
  · exact fun _ => rfl

include pairing unions powers separation collection carrier order in
theorem niceNormalize_mem {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (τ : (M.nameDomain s).names) :
    (Name.niceNormalize (M.nameDomain s) T valid τ).val ∈ M.sets := by
  have family := M.familySet_mem s ⊤ pairing unions powers separation hT
    (M.transitive carrier (s.encode_mem ⊤)) valid
  exact M.ordinarySeparationName_mem s pairing unions powers separation collection carrier order
    (.mem 0 1) (extend τ Fin.elim0) ⟨Name.familySet ⊤ T valid, family⟩

end PartitionPilot.Forcing.TransitiveGround

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




section
open SetRealization SetFormula
universe u

namespace SetFormula
def orbitCodeEntryFormula : SetFormula 6 :=
  ex (binaryApplication orbitImageFormula
    (extend 2 (extend 4 (extend 5 (extend 6 Fin.elim0)))) 0 1)

def orbitCodeEqualityFormula : SetFormula 5 :=
  exactSetFormula 1 orbitCodeEntryFormula

end SetFormula

end



open SetRealization SetFormula
universe u


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundOmegaOneRowModel
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)

noncomputable def groundOmegaOne : ZFSet.{u} :=
  Classical.choose (M.exists_groundHartogs pairing unions powers separation collection
    (M.omega_mem separation infinite))

theorem groundOmegaOne_spec :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    C ∈ M.sets ∧ ordinalSetProperty C ∧
      (∀ A : ZFSet.{u}, A ∈ C ↔ A ∈ M.sets ∧ ordinalSetProperty A ∧
        M.groundEmbeddable A ZFSet.omega) ∧ ¬ M.groundEmbeddable C ZFSet.omega :=
  Classical.choose_spec (M.exists_groundHartogs pairing unions powers separation collection
    (M.omega_mem separation infinite))

end PartitionPilot.Forcing.TransitiveGround



end

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

theorem niceNameCandidateGraph_mem (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (indices : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) :
    M.niceNameCandidateGraph a s b T K ∈ M.sets := by
  let B := M.groundRelations T s.carrier
  have hB := M.groundRelations_mem pairing unions powers separation hT carrier
  let slots : Fin 6 → Fin 6 := ![1, 0, 2, 3, 4, 5]
  let defined := (M.definable_separation separation nameSupportFormula).reindex slots
  let params := extend B (extend s.carrier (extend t.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0))))
  have ground := defined.graph_mem pairing separation collection params
    (Fin.cases hB (Fin.cases carrier (Fin.cases group (Fin.cases supports
      (Fin.cases maps (fun j => Fin.elim0 j)))))) indices
  have value (i : I) :
      ZFSet.sep (fun z => Realize M.sets nameSupportFormula
        (extend z (fun j => (extend (b.encode i) params) (slots j.succ))))
          ((extend (b.encode i) params) (slots 0)) = M.niceNameCandidates a s T (K i) := by
    have args : (fun j : Fin 5 => (extend (b.encode i) params) (slots j.succ)) =
        extend (b.encode i) (extend s.carrier (extend t.carrier
          (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0)))) := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun k => Fin.elim0 k))))) j
    rw [args]
    exact (M.niceNameCandidates_eq_selection a s t b K pairing unions powers separation collection
      carrier group supports maps valid i (M.transitive indices (b.encode_mem i))).symm
  have equal : defined.graph params b.carrier = M.niceNameCandidateGraph a s b T K := by
    apply ZFSet.ext
    intro z
    rw [defined.mem_graph, M.mem_niceNameCandidateGraph]
    constructor
    · rintro ⟨x, hx, eq⟩
      obtain ⟨i, rfl⟩ := (b.mem_carrier x).1 hx
      exact ⟨i, eq.trans (congrArg (ZFSet.pair (b.encode i)) (value i))⟩
    · rintro ⟨i, eq⟩
      exact ⟨b.encode i, b.encode_mem i, eq.trans (congrArg (ZFSet.pair (b.encode i)) (value i).symm)⟩
  exact equal ▸ ground

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPrincipalNiceSupportCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
include b t pairing unions powers separation collection carrier group nodes supports maps hT valid

theorem niceSupportNameCodes_mem : M.niceSupportNameCodes a s T K ∈ M.sets := by
  have whole := M.niceNameCandidateGraph_mem a s t b K pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  have domain : ZFSet.range b.encode = b.carrier := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_range]
    exact (b.mem_carrier z).symm
  exact M.union_mem unions (M.familyCodeGraph_valueRange_mem unions separation b.encode
    (fun i => M.niceNameCandidates a s T (K i)) (domain.symm ▸ nodes) whole)

theorem niceSupportRelation_mem : M.niceSupportRelation a s b T K ∈ M.sets := by
  let graph := M.niceNameCandidateGraph a s b T K
  have hgraph := M.niceNameCandidateGraph_mem a s t b K pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  have hNames := M.niceSupportNameCodes_mem a s b T K t pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  let phi : SetFormula 2 := ex (ex (ex (.conj (orderedPairFormula 3 2 1)
    (.conj (pairMembershipFormula 2 0 4) (.mem 1 0)))))
  have meaning (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets phi (extend z (extend graph Fin.elim0)) ↔
        ∃ i tau, z = ZFSet.pair (b.encode i) tau ∧
          tau ∈ M.niceNameCandidates a s T (K i) := by
    simp only [phi, realize_ex]
    constructor
    · rintro ⟨v, hv, tau, htau, values, hvalues, shape, entry, member⟩
      have pair := (M.realize_orderedPairFormula pairing 3 2 1 _ hz hv htau).1 shape
      have edge : ZFSet.pair v values ∈ graph :=
        (M.realize_pairMembershipFormula pairing 2 0 4 _ hv hvalues hgraph).1 entry
      obtain ⟨i, eq⟩ := (M.mem_niceNameCandidateGraph a s b T K _).1 edge
      have parts := ZFSet.pair_inj.1 eq
      exact ⟨i, tau, pair.trans (congrArg (fun w => ZFSet.pair w tau) parts.1),
        parts.2 ▸ member⟩
    · rintro ⟨i, tau, shape, member⟩
      have hi := M.transitive nodes (b.encode_mem i)
      have hvalues := M.niceNameCandidates_mem a s t b K pairing unions powers separation
        collection carrier group supports maps hT valid i hi
      have htau := M.transitive hvalues member
      refine ⟨b.encode i, hi, tau, htau, M.niceNameCandidates a s T (K i), hvalues, ?_, ?_, member⟩
      · exact (M.realize_orderedPairFormula pairing 3 2 1 _ hz hi htau).2 shape
      · exact (M.realize_pairMembershipFormula pairing 2 0 4 _ hi hvalues hgraph).2
          ((M.pair_mem_niceNameCandidateGraph a s b T K i _).2 rfl)
  have selected := M.separation_mem separation phi (extend graph Fin.elim0)
    (Fin.cases hgraph (fun j => Fin.elim0 j)) (M.prod_mem pairing unions powers separation nodes hNames)
  have equal : ZFSet.sep (fun z => Realize M.sets phi (extend z (extend graph Fin.elim0)))
      (ZFSet.prod b.carrier (M.niceSupportNameCodes a s T K)) = M.niceSupportRelation a s b T K := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, niceSupportRelation, ZFSet.mem_sep]
    exact and_congr_right (fun member => meaning z
      (M.transitive (M.prod_mem pairing unions powers separation nodes hNames) member))
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNiceSupportEvaluation
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
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

variable [OrderTop P]

theorem niceSupportEvaluationName_mem (t : Presentation G) (b : Presentation I)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) :
    (M.niceSupportEvaluationName a s T K).val ∈ M.sets := by
  have hN := M.niceSupportNameCodes_mem a s b T K t pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  exact M.indexedGraphName_mem s ⊤ pairing unions powers separation collection
    (M.transitive carrier (s.encode_mem ⊤)) hN
    (M.identityFunctionGraph_mem pairing unions powers separation hN)
    (codeFunction (M.niceSupportNameCodes a s T K)) (codeIsName M a s T K)

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

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (carrier : s.carrier ∈ M.sets)

noncomputable def sequenceFunctionNameEnv {N U : ZFSet.{u}}
    (hN : N ∈ M.sets) (hU : U ∈ M.sets) (τ : (M.nameDomain s).names) :
    Assignment (M.nameDomain s) 3 :=
  extend ⟨Name.check s ⊤ N, M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) N hN⟩
    (extend ⟨Name.check s ⊤ U, M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) U hU⟩ (extend τ Fin.elim0))

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSelectedSupportTupleFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

noncomputable def definable_rowTupleCode : GroundDefinableFunction M
    (fun env : Fin 6 → ZFSet.{u} => rowTupleCode (env 1) (env 2) (env 3) (env 4) (env 5) (env 0)) := by
  let composed := (M.definable_relationCompose pairing unions powers separation).reindex
    (extend (2 : Fin 6) (extend 3 (extend 4 (extend 0 (extend 5 Fin.elim0)))))
  let inner (j : Fin 3) (env : Fin 6 → ZFSet.{u}) : ZFSet.{u} :=
    Fin.cases (env 1) (Fin.cases (env 2)
      (Fin.cases (relationCompose (env 2) (env 3) (env 4) (env 0) (env 5))
        (fun i => Fin.elim0 i))) j
  apply (M.definable_indexedGraphNameCode pairing unions powers separation collection).comp (g := inner)
  intro j
  refine Fin.cases (GroundDefinableFunction.projection M 1) (fun j => ?_) j
  refine Fin.cases (GroundDefinableFunction.projection M 2) (fun j => ?_) j
  exact Fin.cases composed (fun i => Fin.elim0 i) j

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

theorem niceVisibilityName_mem {I : Type u} (t : Presentation G) (b : Presentation I)
    (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (i : I) (hi : b.encode i ∈ M.sets) :
    (M.niceVisibilityName a s T (K i)).val ∈ M.sets :=
  M.familySet_mem s ⊤ pairing unions powers separation
    (M.niceNameCandidates_mem a s t b K pairing unions powers separation collection
      carrier group supports maps hT valid i hi)
    (M.transitive carrier (s.encode_mem ⊤)) _

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundNiceVisibilityGraphs
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
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem niceVisibilityGraph_mem (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (indices : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) :
    M.niceVisibilityGraph a s b T K ∈ M.sets := by
  let B := M.groundRelations T s.carrier
  have hB := M.groundRelations_mem pairing unions powers separation hT carrier
  have hone := M.transitive carrier (s.encode_mem ⊤)
  let slots : Fin 6 → Fin 7 := ![1, 0, 2, 3, 4, 5]
  let chosen (env : Fin 7 → ZFSet.{u}) :=
    ZFSet.sep (fun z => Realize M.sets nameSupportFormula (extend z (fun j => env (slots j.succ))))
      (env (slots 0))
  let selected := (M.definable_separation separation nameSupportFormula).reindex slots
  let inner (j : Fin 2) (env : Fin 7 → ZFSet.{u}) : ZFSet.{u} :=
    Fin.cases (chosen env) (Fin.cases (env 6) (fun k => Fin.elim0 k)) j
  let defined : GroundDefinableFunction M (fun env : Fin 7 → ZFSet.{u} =>
      ZFSet.prod (chosen env) {env 6}) := by
    apply (M.definable_familySetCode pairing unions powers separation).comp (g := inner)
    intro j
    exact Fin.cases selected (Fin.cases (GroundDefinableFunction.projection M 6)
      (fun k => Fin.elim0 k)) j
  let params := extend B (extend s.carrier (extend t.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t)
      (extend (s.encode ⊤) Fin.elim0)))))
  have ground := defined.graph_mem pairing separation collection params
    (Fin.cases hB (Fin.cases carrier (Fin.cases group (Fin.cases supports
      (Fin.cases maps (Fin.cases hone (fun j => Fin.elim0 j))))))) indices
  have value (i : I) : ZFSet.prod (chosen (extend (b.encode i) params)) {(extend (b.encode i) params) 6} =
      (M.niceVisibilityName a s T (K i)).val := by
    rw [M.niceVisibilityName_code]
    apply congrArg (fun X => ZFSet.prod X {s.encode ⊤})
    have args : (fun j : Fin 5 => (extend (b.encode i) params) (slots j.succ)) =
        extend (b.encode i) (extend s.carrier (extend t.carrier
          (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0)))) := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun k => Fin.elim0 k))))) j
    change ZFSet.sep _ _ = _
    rw [args]
    exact (M.niceNameCandidates_eq_selection a s t b K pairing unions powers separation collection
      carrier group supports maps valid i (M.transitive indices (b.encode_mem i))).symm
  have equal : defined.graph params b.carrier = M.niceVisibilityGraph a s b T K := by
    apply ZFSet.ext
    intro z
    rw [defined.mem_graph, M.mem_niceVisibilityGraph]
    constructor
    · rintro ⟨x, hx, eq⟩
      obtain ⟨i, rfl⟩ := (b.mem_carrier x).1 hx
      exact ⟨i, eq.trans (congrArg (ZFSet.pair (b.encode i)) (value i))⟩
    · rintro ⟨i, eq⟩
      exact ⟨b.encode i, b.encode_mem i, eq.trans (congrArg (ZFSet.pair (b.encode i)) (value i).symm)⟩
  exact equal ▸ ground

end PartitionPilot.Forcing.TransitiveGround

end

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

namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

namespace TransitiveGround
variable (M : TransitiveGround.{u}) (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (terms : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)

include pairing unions powers separation collection carrier order maps hT valid terms in
theorem niceNormalize_mem_niceNameCandidates (K : Subgroup G)
    (τ : (M.nameDomain s).names) (fixed : K ≤ a.stabilizer s τ.val) :
    (Name.niceNormalize (M.nameDomain s) T valid τ).val ∈ M.niceNameCandidates a s T K := by
  apply (M.mem_niceNameCandidates a s T K _).2
  refine ⟨M.niceNormalize_mem s pairing unions powers separation collection carrier order hT valid τ, ?_⟩
  exact Name.niceNormalize_niceNameCode a (M.nameDomain s)
    (fun g σ hσ => M.act_mem s a t pairing unions powers separation collection carrier maps g σ hσ)
    T valid terms τ K fixed

include pairing unions powers separation collection carrier order maps hT valid terms in
theorem niceNormalize_mem_eval_niceVisibilityName (K : Subgroup G)
    (τ : (M.nameDomain s).names) (fixed : K ≤ a.stabilizer s τ.val)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (subset : Name.eval {p | H.mem p} τ.val ⊆
      Name.eval {p | H.mem p} (Name.familySet ⊤ T valid)) :
    Name.eval {p | H.mem p} τ.val ∈ Name.eval {p | H.mem p} (M.niceVisibilityName a s T K) := by
  apply (M.mem_eval_niceVisibilityName a s T K {p | H.mem p} H.top_mem _).2
  refine ⟨Name.niceNormalize (M.nameDomain s) T valid τ,
    M.niceNormalize_mem_niceNameCandidates a s t pairing unions powers separation collection
      carrier order maps hT valid terms K τ fixed, ?_⟩
  exact Name.eval_niceNormalize_of_subset (M.nameDomain s) T valid τ
    (M.familySet_mem s ⊤ pairing unions powers separation hT
      (M.transitive carrier (s.encode_mem ⊤)) valid) H generic subset

include pairing unions powers separation collection carrier order maps hT valid terms in
theorem niceNameSystem (b : Presentation L) (d : PosetAction G L) (base : L)
    (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (children : ∀ σ : Name s, σ.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) σ) :
    NiceNameSystem M a s b d base directed T valid where
  candidate_graph_ground := M.niceNameCandidateGraph_mem a s t b d.principalFix
    pairing unions powers separation collection carrier group indices supports maps hT valid
  candidate_graph_function := M.niceNameCandidateGraph_function a s b T d.principalFix
  candidate_entries := M.pair_mem_niceNameCandidateGraph a s b T d.principalFix
  visibility_graph_ground := M.niceVisibilityGraph_mem a s t b d.principalFix
    pairing unions powers separation collection carrier group indices supports maps hT valid
  visibility_graph_function := M.niceVisibilityGraph_function a s b T d.principalFix
  visibility_entries := M.pair_mem_niceVisibilityGraph a s b T d.principalFix
  candidate_hs := fun v τ member => niceNameCode_principal_hs a s d base v directed children
    ((M.mem_niceNameCandidates a s T (d.principalFix v) τ.val).1 member).2
  visibility_ground := fun v => M.niceVisibilityName_mem a s t b d.principalFix
    pairing unions powers separation collection carrier group supports maps hT valid v
    (M.transitive indices (b.encode_mem v))
  visibility_support := fun v => M.niceVisibilityName_support a s T (d.principalFix v)
  visibility_hs := fun v => M.niceVisibilityName_principal_hs a s d base v directed T children
  visibility_action := M.act_niceVisibilityName a s t d pairing unions powers separation
    collection carrier maps terms
  normalization_candidate := fun v τ fixed =>
    M.niceNormalize_mem_niceNameCandidates a s t pairing unions powers separation collection
      carrier order maps hT valid terms (d.principalFix v) τ fixed
  normalization_visible := fun v τ fixed H generic subset =>
    M.niceNormalize_mem_eval_niceVisibilityName a s t pairing unions powers separation collection
      carrier order maps hT valid terms (d.principalFix v) τ fixed H generic subset

end TransitiveGround
end PartitionPilot.Forcing

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



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

namespace TransitiveGround
variable (M : TransitiveGround.{u}) (a : PosetAction G P) (s : Presentation P)
variable (b : Presentation L) (d : PosetAction G L)

theorem niceRefinementIndexSystem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {level T1 T2 : ZFSet.{u}} {valid1 : ∀ z ∈ T1, IsName s z} {valid2 : ∀ z ∈ T2, IsName s z}
    (hl : level ∈ M.sets) (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    {base : L} {directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z}
    (first : NiceNameSystem M a s b d base directed T1 valid1)
    (second : NiceNameSystem M a s b d base directed T2 valid2) :
    NiceRefinementIndexSystem M a s b d level T1 T2 valid1 valid2 := by
  have top := M.transitive carrier (s.encode_mem ⊤)
  have family := M.familySet_mem s ⊤ pairing unions powers separation hT1 top valid1
  refine ⟨M.niceRefinementIndices_mem a s b d pairing unions powers separation valid1 hl hT1 hT2
    carrier order nodes nodeOrder first.candidate_graph_ground second.candidate_graph_ground,
    family, first.candidate_graph_ground, second.candidate_graph_ground, ?_, ?_, ?_, ?_, ?_⟩
  · exact M.refinementIndices_fields_ground _ _ _ _ _ _ _ _ _ _ _ pairing unions powers separation
      hl nodes nodeOrder first.candidate_graph_ground second.candidate_graph_ground hT1 hT2 family carrier order top
  · exact M.refinementIndices_field_function _ _ _ _ _ _ _ _ _ _ _
  · exact M.refinementIndices_level_graph _ _ _ _ _ _ _ _ _ _ _
  · exact M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation collection
      carrier order level T1 T2 valid1 family
  · exact fun _ hz => M.exists_niceRefinementIndex_fields a s b d level T1 T2 valid1 valid2 hz

end TransitiveGround
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
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)

theorem niceVisibilityEvaluationName_mem (t : Presentation G) (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) :
    (M.niceVisibilityEvaluationName a s b T K).val ∈ M.sets := by
  exact M.indexedGraphName_mem s ⊤ pairing unions powers separation collection
    (M.transitive carrier (s.encode_mem ⊤)) nodes
    (M.niceVisibilityGraph_mem a s t b K pairing unions powers separation collection
      carrier group nodes supports maps hT valid)
    (M.niceVisibilityGraph_function a s b T K) (visibilityValues_isName M a s b T K)

end PartitionPilot.Forcing.TransitiveGround



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



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_relationProduct :
    GroundDefinableFunction M (fun env : Fin 6 → ZFSet.{u} =>
      relationProduct (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) := by
  let v := GroundSetTerm.var M (n := 6)
  let product (x y : GroundSetTerm M 6) :=
    GroundSetTerm.app (M.definable_product pairing unions powers separation) ![x,y]
  let bound := product (product (v 0) (v 1)) (product (v 2) (v 3))
  let formula : SetFormula 7 := (BoundedFormula.relationProductEntryFormula 0 1 2 3 4 5 6).toFormula
  let term := GroundSetTerm.app (M.definable_separation separation formula)
    ![bound,v 0,v 1,v 2,v 3,v 4,v 5]
  refine { formula := term.definition.formula
           closed := fun env members => M.relationProduct_mem pairing unions powers separation
             (members 0) (members 1) (members 2) (members 3) (members 4) (members 5)
           correct := ?_ }
  intro env members z hz
  rw [term.definition.correct env members z hz]
  have args : (fun j : Fin 6 => (![bound,v 0,v 1,v 2,v 3,v 4,v 5] j.succ).eval env) = env := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) j
  have equal : term.eval env = relationProduct (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) := by
    change ZFSet.sep (fun w => Realize M.sets formula (extend w _)) _ = _
    rw [args]
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_sep, relationProduct, ZFSet.mem_sep]
    apply and_congr_right
    intro hw
    rw [BoundedFormula.realize_toFormula M _ _
      (Fin.cases (M.transitive (bound.ground env members) hw) members),
      BoundedFormula.truth_relationProductEntryFormula]
    rfl
  rw [equal]

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundDefinableIndexBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

noncomputable def definable_refinementIndexBound :
    GroundDefinableFunction M (fun env : Fin 4 → ZFSet.{u} =>
      refinementIndexBound (env 0) (env 1) (env 2) (env 3)) := by
  let v := GroundSetTerm.var M (n := 4)
  let prod (x y : GroundSetTerm M 4) :=
    GroundSetTerm.app (M.definable_product pairing unions powers separation) ![x, y]
  exact (prod (v 0) (prod (v 1) (prod (v 1) (prod (v 2) (prod (v 3) (v 3)))))).definition

end PartitionPilot.Forcing.TransitiveGround

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




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_refinementNameBound :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} => M.refinementNameBound (env 0) (env 1) (env 2)) := by
  let v := GroundSetTerm.var M (n := 3)
  let classes := GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![v 0, v 1]
  let pairs := GroundSetTerm.app (M.definable_orderedPairNameFamily pairing unions powers separation)
    ![v 2, classes, classes]
  let children := GroundSetTerm.app (M.definable_binaryUnion pairing unions) ![classes, pairs]
  exact (GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![children, v 1]).definition

noncomputable def definable_refinementIndexNameGraph (kind : Fin 3) :
    GroundDefinableFunction M (fun env : Fin 8 → ZFSet.{u} =>
      M.refinementIndexNameGraph kind (env 0) (env 1) (env 2) (env 3)
        (env 4) (env 5) (env 6) (env 7)) := by
  let v := GroundSetTerm.var M (n := 8)
  let names := GroundSetTerm.app (M.definable_refinementNameBound pairing unions powers separation)
    ![v 4, v 5, v 7]
  let bound := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 0, names]
  let term := GroundSetTerm.app (M.definable_separation separation (refinementIndexNameGraphFormula kind))
    ![bound, v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7]
  refine term.definition.congr ?_
  intro env
  apply congrArg (fun params : Fin 8 → ZFSet.{u} =>
    ZFSet.sep (fun z => Realize M.sets (refinementIndexNameGraphFormula kind) (extend z params))
      (ZFSet.prod (env 0) (M.refinementNameBound (env 4) (env 5) (env 7))))
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))) j

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

noncomputable def definable_storedAssignmentClassGraph (side : Fin 2) :
    GroundDefinableFunction M (fun env : Fin 16 → ZFSet.{u} =>
      M.storedAssignmentClassGraph (env 0) (fun j => env j.succ) side) := by
  let v := GroundSetTerm.var M (n := 16)
  let selected := GroundSetTerm.app (M.definable_assignmentOnIndices pairing unions powers separation)
    ![v 1, v 7, v 0]
  let term := GroundSetTerm.app (M.definable_assignmentClassGraph pairing unions powers separation side)
    ![selected, v (Fin.cases 6 (fun _ => 5) side), v 7, v 8, v 9, v 10]
  refine term.definition.congr ?_
  intro env
  have shift : (Fin.cases 6 (fun _ => 5) side : Fin 16) =
      (Fin.cases 5 (fun _ => 4) side : Fin 15).succ :=
    Fin.cases rfl (fun _ => rfl) side
  change M.assignmentClassGraph side (assignmentOnIndices (env 1) (env 7) (env 0))
    (env (Fin.cases 6 (fun _ => 5) side)) (env 7) (env 8) (env 9) (env 10) =
    M.assignmentClassGraph side (assignmentOnIndices (env 1) (env 7) (env 0))
      (env (Fin.cases 5 (fun _ => 4) side : Fin 15).succ) (env 7) (env 8) (env 9) (env 10)
  rw [shift]

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_storedPreparationRequests :
    GroundDefinableFunction M (fun env : Fin 16 → ZFSet.{u} =>
      M.storedPreparationRequests (env 0) (fun j => env j.succ)) := by
  let v := GroundSetTerm.var M (n := 16)
  let selected := GroundSetTerm.app (M.definable_assignmentOnIndices pairing unions powers separation)
    ![v 1, v 7, v 0]
  let graph (side : Fin 2) := GroundSetTerm.app
    (M.definable_storedAssignmentClassGraph pairing unions powers separation side) v
  let image (side : Fin 2) := GroundSetTerm.app (relationImageDefinition M separation)
    ![selected, v 15, graph side]
  exact (GroundSetTerm.app (M.definable_binaryUnion pairing unions) ![image 0, image 1]).definition

end PartitionPilot.Forcing.TransitiveGround

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

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

variable (collection : CollectionSchema M.sets)

noncomputable def definable_rawNiceVisibilityGraph :
    GroundDefinableFunction M (fun env : Fin 7 → ZFSet.{u} =>
      M.rawNiceVisibilityGraph (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)) := by
  let v := GroundSetTerm.var M (n := 7)
  let chosen := GroundSetTerm.app (M.definable_rawNiceNameCandidates pairing unions powers separation)
    ![v 0, v 1, v 2, v 3, v 4, v 5]
  let name := GroundSetTerm.app (M.definable_familySetCode pairing unions powers separation) ![chosen, v 6]
  exact name.definition.definable_graph pairing separation collection

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

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

include pairing unions powers separation collection in
theorem rawRowAssignmentActionGraph_mem {G Q C B J rowAction assignmentAction : ZFSet.{u}}
    (hG : G ∈ M.sets) (hQ : Q ∈ M.sets) (hC : C ∈ M.sets) (hB : B ∈ M.sets)
    (hJ : J ∈ M.sets) (hRow : rowAction ∈ M.sets) (hAssignment : assignmentAction ∈ M.sets) :
    rawRowAssignmentActionGraph G Q C B J rowAction assignmentAction ∈ M.sets :=
  (M.definable_rawRowAssignmentActionGraph pairing unions powers separation collection).closed
    ![G, Q, C, B, J, rowAction, assignmentAction]
    (Fin.cases hG (Fin.cases hQ (Fin.cases hC (Fin.cases hB
      (Fin.cases hJ (Fin.cases hRow (Fin.cases hAssignment (fun j => Fin.elim0 j))))))))

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
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_refinementIndices :
    GroundDefinableFunction M (fun env : Fin 11 → ZFSet.{u} =>
      M.refinementIndices (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)
        (env 6) (env 7) (env 8) (env 9) (env 10)) := by
  let v := GroundSetTerm.var M (n := 11)
  let first := GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![v 5, v 8]
  let second := GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![v 6, v 8]
  let level := GroundSetTerm.app (M.definable_singleton pairing) ![v 0]
  let bound := GroundSetTerm.app (M.definable_refinementIndexBound pairing unions powers separation)
    ![level, v 1, first, second]
  let formula : SetFormula 9 := refinementIndexSelectionFormula 0 1 2 3 4 5 6 7 8
  let term := GroundSetTerm.app (M.definable_separation separation formula)
    ![bound, v 0, v 2, v 3, v 4, v 7, v 8, v 9, v 10]
  refine { formula := term.definition.formula
           closed := fun env members => M.refinementIndices_mem pairing unions powers separation
             (members 0) (members 1) (members 2) (members 3) (members 4) (members 5)
             (members 6) (members 7) (members 8) (members 9) (members 10)
           correct := ?_ }
  intro env members z hz
  rw [term.definition.correct env members z hz]
  have args : (fun j : Fin 8 => (![bound, v 0, v 2, v 3, v 4, v 7, v 8, v 9, v 10]
      (j.succ)).eval env) = ![env 0, env 2, env 3, env 4, env 7, env 8, env 9, env 10] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))) j
  have equal : term.eval env = M.refinementIndices (env 0) (env 1) (env 2) (env 3) (env 4)
      (env 5) (env 6) (env 7) (env 8) (env 9) (env 10) := by
    change ZFSet.sep (fun w => Realize M.sets formula (extend w _)) (bound.eval env) = _
    rw [args]
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_sep, M.mem_refinementIndices]
    apply and_congr_right
    intro hw
    exact M.realize_refinementIndexSelectionFormula 0 1 2 3 4 5 6 7 8 _
      (Fin.cases (M.transitive (bound.ground env members) hw)
        (Fin.cases (members 0) (Fin.cases (members 2) (Fin.cases (members 3)
          (Fin.cases (members 4) (Fin.cases (members 7) (Fin.cases (members 8)
            (Fin.cases (members 9) (Fin.cases (members 10) (fun j => Fin.elim0 j))))))))))
  rw [equal]

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def definable_rawRefinementFormulaDataCode
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 11 → ZFSet.{u} =>
      M.rawRefinementFormulaDataCode (env 0) (env 1) (env 2) (env 3) (env 4)
        (env 5) (env 6) (env 7) (env 8) (env 9) (env 10)) := by
  let v := GroundSetTerm.var M (n := 11)
  let maps := GroundSetTerm.app (M.definable_rawActionMapFamily pairing unions powers separation collection)
    ![v 4, v 3, v 0]
  let first := GroundSetTerm.app (M.definable_rawNiceNameCandidateGraph pairing unions powers separation collection)
    ![v 5, v 8, v 0, v 4, v 7, maps]
  let second := GroundSetTerm.app (M.definable_rawNiceNameCandidateGraph pairing unions powers separation collection)
    ![v 5, v 9, v 0, v 4, v 7, maps]
  let family := GroundSetTerm.app (M.definable_familySetCode pairing unions powers separation) ![v 8, v 2]
  let indices := GroundSetTerm.app (M.definable_refinementIndices pairing unions powers separation)
    ![v 10, v 5, v 6, first, second, v 8, v 9, family, v 0, v 1, v 2]
  let B1 := GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![v 8, v 0]
  let B2 := GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![v 9, v 0]
  let field (j : Fin 6) (bound : GroundSetTerm M 11) :=
    GroundSetTerm.app (M.definable_refinementIndexFieldGraph pairing unions powers separation j) ![indices, bound]
  let F1 := field 1 (v 5)
  let F2 := field 2 (v 5)
  let F3 := field 3 B1
  let F4 := field 4 B2
  let F5 := field 5 B2
  let mapNames := GroundSetTerm.app (M.definable_refinementIndexNameGraph pairing unions powers separation 2)
    ![indices, F3, F4, F5, v 8, v 0, v 1, v 2]
  let visibility := GroundSetTerm.app (M.definable_rawNiceVisibilityGraph pairing unions powers separation collection)
    ![v 5, v 8, v 0, v 4, v 7, maps, v 2]
  let term := GroundSetTerm.app (M.definable_nonemptyTuple pairing 14)
    ![indices, F1, F2, F3, F4, F5, v 8, v 0, v 1, v 2, v 5, v 6, mapNames, visibility, B1]
  refine term.definition.congr ?_
  intro env
  change nonemptyTupleCode 14 (fun j =>
    (![indices, F1, F2, F3, F4, F5, v 8, v 0, v 1, v 2, v 5, v 6, mapNames, visibility, B1] j).eval env) =
      nonemptyTupleCode 14 (M.rawRefinementFormulaData (env 0) (env 1) (env 2) (env 3) (env 4)
        (env 5) (env 6) (env 7) (env 8) (env 9) (env 10))
  congr 1
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (fun k => Fin.elim0 k))))))))))))))) j

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

theorem rawRefinementFormulaDataCode_eq :
    M.rawRefinementFormulaDataCode s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t)
      t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level =
        M.refinementLevelFormulaDataCode a s b d level T T2 valid :=
  congrArg refinementFormulaDataCode (M.rawRefinementFormulaData_eq a s t b d
    pairing unions powers separation collection carrier group nodes supports maps level T T2 valid valid2)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundHistoryUnionBounds
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
variable (separation : SeparationSchema M.sets)
variable {n : Nat} {f : (Fin (n + 1) → ZFSet.{u}) → ZFSet.{u}}

noncomputable def historyUnionStepDefinition (defined : GroundDefinableFunction M f) :
    GroundDefinableFunction M (fun env : Fin (n + 2) → ZFSet.{u} =>
      f (extend (refinementHistoryIndices (env 0) (env 1)) (fun j => env j.succ.succ))) := by
  let earlier := (M.definable_historyUnion pairing unions separation).reindex
    ![(0 : Fin (n + 2)), 1]
  exact defined.comp (Fin.cases earlier
    (fun j => GroundDefinableFunction.projection M j.succ.succ))

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

section
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable {C D rD c d0 d1 : ZFSet.{u}}
variable (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
variable (hc : c ∈ C) (h0 : d0 ∈ D) (h1 : d1 ∈ D) (gap : ZFSet.pair d0 d1 ∈ rD)

noncomputable def initialMainChronological : GroundChronologicalMainStage M C D rD :=
  (M.initialMainStage pairing unions powers separation infinite hC hD hrD hc h0 h1 gap).initialChronological
    pairing unions powers separation (M.natSetCode_countable pairing unions powers separation infinite 2)

end TransitiveGround

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_CodedMainPrefixSystems
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u v

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem transitionGraph_entry {i j : I} (before : i ≤ j) (z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (run.key j) (run.key i)) z ∈ run.transitionGraph ↔
      z = (run.diagram.transition before).map.code :=
  pair_mem_familyCodeGraph (mainTransitionIndexKey run.key) _
    (mainTransitionIndexKey_injective run.key run.key_injective) ⟨(i, j), before⟩ z

end GroundMainPrefix

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixFieldFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem indices_rank_le_code : ZFSet.rank run.indices ≤ ZFSet.rank run.code := by
  simpa only [code, Fin.cases_zero] using
    (rank_nonemptyTupleCode_field_le 2
      (Fin.cases run.indices (Fin.cases run.stageGraph (fun _ => run.transitionGraph))) 0)

theorem stageGraph_rank_le_code : ZFSet.rank run.stageGraph ≤ ZFSet.rank run.code := by
  simpa only [code, Fin.cases_zero, Fin.cases_succ] using
    (rank_nonemptyTupleCode_field_le 2
      (Fin.cases run.indices (Fin.cases run.stageGraph (fun _ => run.transitionGraph))) (0 : Fin 2).succ)

theorem actorMapFamily_ground : run.actorMapFamily ∈ M.sets := run.mapFamilies_ground.2

theorem pointMapFamily_function : FunctionGraphOn (chronologyPairs run.indices) run.pointMapFamily := by
  have function := familyCodeGraph_function (mainTransitionIndexKey run.key)
    (fun p => (run.diagram.transition p.property).map.points)
    (mainTransitionIndexKey_injective run.key run.key_injective)
  rw [mainTransitionIndex_range run.key run.key_order] at function
  exact function

theorem pointMapFamily_entry {i j : I} (before : i ≤ j) (z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (run.key j) (run.key i)) z ∈ run.pointMapFamily ↔
      z = (run.diagram.transition before).map.points :=
  pair_mem_familyCodeGraph (mainTransitionIndexKey run.key) _
    (mainTransitionIndexKey_injective run.key run.key_injective) ⟨(i, j), before⟩ z

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixConePreservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def appendKey : WithTop I → ZFSet.{u}
  | none => run.indices
  | some i => run.key i

theorem appendKey_injective : Function.Injective run.appendKey := by
  intro i j equal
  cases i with
  | top =>
    cases j with
    | top => rfl
    | coe j =>
      have h := ZFSet.rank_lt_of_mem (ZFSet.mem_range.2 ⟨j, rfl⟩ : run.key j ∈ run.indices)
      change run.indices = run.key j at equal
      exact False.elim ((ne_of_lt h) (congrArg ZFSet.rank equal).symm)
  | coe i =>
    cases j with
    | top =>
      have h := ZFSet.rank_lt_of_mem (ZFSet.mem_range.2 ⟨i, rfl⟩ : run.key i ∈ run.indices)
      exact False.elim ((ne_of_lt h) (congrArg ZFSet.rank equal))
    | coe j => exact congrArg (fun k : I => (k : WithTop I)) (run.key_injective equal)

theorem appendKey_order (i j : WithTop I) :
    i ≤ j ↔ run.appendKey i = run.appendKey j ∨ run.appendKey i ∈ run.appendKey j := by
  cases i with
  | top =>
    cases j with
    | top => exact iff_of_true le_rfl (Or.inl rfl)
    | coe j =>
      have lower := ZFSet.rank_lt_of_mem (ZFSet.mem_range.2 ⟨j, rfl⟩ : run.key j ∈ run.indices)
      constructor
      · exact fun h => False.elim (WithTop.not_top_le_coe j h)
      · rintro (equal | member)
        · exact False.elim ((ne_of_lt lower) (congrArg ZFSet.rank equal).symm)
        · exact False.elim (lt_asymm lower (ZFSet.rank_lt_of_mem member))
  | coe i =>
    cases j with
    | top => exact iff_of_true le_top (Or.inr (ZFSet.mem_range.2 ⟨i, rfl⟩))
    | coe j => exact WithTop.coe_le_coe.trans (run.key_order i j)

theorem appendKey_range : ZFSet.range run.appendKey = insert run.indices run.indices := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_range, ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | top => exact Or.inl rfl
    | coe i => exact Or.inr (ZFSet.mem_range.2 ⟨i, rfl⟩)
  · rintro (rfl | hz)
    · exact ⟨⊤, rfl⟩
    · obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hz
      exact ⟨(i : WithTop I), rfl⟩

def appendLinked (target : GroundLinkedMainStage M K Labels C D rD) :
    WithTop I → GroundLinkedMainStage M K Labels C D rD
  | none => target
  | some i => run.linked i

theorem appendStageGraph_eq (target : GroundLinkedMainStage M K Labels C D rD) :
    familyCodeGraph run.appendKey (fun i => (run.appendLinked target i).code) =
      insert (ZFSet.pair run.indices target.code) run.stageGraph := by
  apply ZFSet.ext
  intro z
  rw [mem_familyCodeGraph, ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | top => exact Or.inl rfl
    | coe i => exact Or.inr ((mem_familyCodeGraph _ _ _).2 ⟨i, rfl⟩)
  · rintro (rfl | hz)
    · exact ⟨⊤, rfl⟩
    · obtain ⟨i, rfl⟩ := (mem_familyCodeGraph _ _ _).1 hz
      exact ⟨(i : WithTop I), rfl⟩

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing
open SetFormula
universe u v

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_appendRow (last : I) (greatest : ∀ i, i ≤ last)
    (target : GroundLinkedMainStage M K Labels C D rD)
    (step : GroundChronologicalMainTransition (run.diagram.stage last) target.main) :
    ∃ row ∈ M.sets, FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row ∧
      ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
        z = ((run.diagram.transition (greatest i)).comp pairing unions powers separation step).map.code := by
  let V := ⋃₀ ⋃₀ run.transitionGraph
  let F := indexedRelationSection run.indices V run.transitionGraph (run.key last)
  have hV : V ∈ M.sets := M.union_mem unions (M.union_mem unions run.transitions_ground)
  have hLast := M.transitive run.indices_ground (ZFSet.mem_range.2 ⟨last, rfl⟩)
  have hF : F ∈ M.sets := M.indexedRelationSection_mem pairing unions powers separation
    run.indices_ground hV run.transitions_ground hLast
  have oldEntry (i : I) : ZFSet.pair (run.key i) (run.diagram.transition (greatest i)).map.code ∈ F := by
    have old := (run.transitionGraph_entry (greatest i) _).2 rfl
    exact (pair_mem_indexedRelationSection _ _ _ _ _ _).2
      ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, pair_second_mem_doubleUnion old, old⟩
  have oldUnique (i : I) (z : ZFSet.{u}) (entry : ZFSet.pair (run.key i) z ∈ F) :
      z = (run.diagram.transition (greatest i)).map.code :=
    (run.transitionGraph_entry (greatest i) z).1
      ((pair_mem_indexedRelationSection _ _ _ _ _ _).1 entry).2.2
  let R := ⋃₀ ⋃₀ ⋃₀ ⋃₀ F
  have hR : R ∈ M.sets := M.union_mem unions (M.union_mem unions
    (M.union_mem unions (M.union_mem unions hF)))
  have mapBounds (i : I) : (run.diagram.transition (greatest i)).map.points ∈ R ∧
      (run.diagram.transition (greatest i)).map.actors ∈ R :=
    ⟨pair_first_mem_doubleUnion (pair_second_mem_doubleUnion (oldEntry i)),
      pair_second_mem_doubleUnion (pair_second_mem_doubleUnion (oldEntry i))⟩
  have function : ZFSet.IsFunc run.indices (ZFSet.prod R R) F := by
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨i, hi, value, _, rfl, entry⟩ := (mem_indexedRelationSection _ _ _ _ z).1 hz
      obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hi
      have equal := (run.transitionGraph_entry (greatest i) value).1 entry
      rw [equal]
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_range.2 ⟨i, rfl⟩,
        ZFSet.pair_mem_prod.2 (mapBounds i)⟩
    · intro x hx
      obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
      exact ⟨_, oldEntry i, oldUnique i⟩
  obtain ⟨row, ground, func, entries⟩ := M.exists_pairedCompositionRow pairing unions powers separation
    run.indices_ground run.indices_ground hR
    (M.union_mem unions (M.union_mem unions (M.union_mem unions hR)))
    (run.diagram.stage last).stage.carrier_ground target.main.stage.carrier_ground
    (run.diagram.stage last).stage.actors_ground target.main.stage.actors_ground
    hF step.map.points_ground step.map.actors_ground function
  refine ⟨row, ground, func, ?_⟩
  intro i z
  have entry := entries (run.key i) _ _ z (oldEntry i)
  rw [relationCompose_uniformSource_eq (mapBounds i).1
      (run.diagram.transition (greatest i)).map.point_embedding.injection.function.1,
    relationCompose_uniformSource_eq (mapBounds i).2
      (run.diagram.transition (greatest i)).map.group_embedding.injection.function.1] at entry
  exact entry

end GroundMainPrefix

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable {S : ZFSet.{u}} (subset : S ⊆ run.indices)
include subset

theorem restrictedKey_range :
    ZFSet.range (fun i : {i // run.key i ∈ S} => run.key i.val) = S := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact i.property
  · intro hz
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 (subset hz)
    exact ⟨⟨i, hz⟩, rfl⟩

theorem restrictedStageGraph_eq :
    familyCodeGraph (fun i : {i // run.key i ∈ S} => run.key i.val)
      (fun i => (run.linked i.val).code) = graphRestriction S run.stageGraph := by
  have equal := familyCodeGraph_restrict run.key (fun i => (run.linked i).code)
    run.key_injective (fun i => run.key i ∈ S)
  rw [run.restrictedKey_range subset] at equal
  exact equal.symm

theorem restrictedTransitionGraph_eq :
    familyCodeGraph (mainTransitionIndexKey (fun i : {i // run.key i ∈ S} => run.key i.val))
      (fun p => (run.diagram.transition (show p.val.1.val ≤ p.val.2.val from p.property)).map.code) =
        graphRestriction (chronologyPairs S) run.transitionGraph := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨p, rfl⟩ := (mem_familyCodeGraph _ _ z).1 hz
    exact pair_mem_graphRestriction.2
      ⟨(run.transitionGraph_entry p.property _).2 rfl,
        (pair_mem_chronologyPairs S _ _).2
          ⟨p.val.2.property, p.val.1.property, (run.key_order _ _).1 p.property⟩⟩
  · intro hz
    obtain ⟨q, hq, value, rfl, entry⟩ := mem_graphRestriction.1 hz
    obtain ⟨target, ht, source, hs, rfl, before⟩ := (mem_chronologyPairs S q).1 hq
    obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 (subset ht)
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 (subset hs)
    have ordered := (run.key_order i j).2 before
    have equal := (run.transitionGraph_entry ordered value).1 entry
    exact (mem_familyCodeGraph _ _ _).2
      ⟨⟨(⟨i, hs⟩, ⟨j, ht⟩), ordered⟩,
        congrArg (ZFSet.pair (ZFSet.pair (run.key j) (run.key i))) equal.symm⟩

noncomputable def restrict (ground : S ∈ M.sets) (ordinal : ordinalSetProperty S) :
    GroundMainPrefix M K Labels C D rD pairing unions powers separation {i // run.key i ∈ S} where
  key i := run.key i.val
  key_injective := fun _ _ equal => Subtype.ext (run.key_injective equal)
  key_order i j := run.key_order i.val j.val
  indices_ground := (run.restrictedKey_range subset).symm ▸ ground
  indices_ordinal := (run.restrictedKey_range subset).symm ▸ ordinal
  diagram := run.diagram.reindex Subtype.val (fun _ _ before => before)
  linked i := run.linked i.val
  linked_main i := run.linked_main i.val
  coverage := fun before => run.coverage before
  stages_ground := (run.restrictedStageGraph_eq subset).symm ▸
    M.graphRestriction_mem unions separation ground run.stages_ground
  transitions_ground := (run.restrictedTransitionGraph_eq subset).symm ▸
    M.graphRestriction_mem unions separation
      (M.chronologyPairs_mem pairing unions powers separation ground) run.transitions_ground

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (target : GroundLinkedMainStage M K Labels C D rD) (cone : run.diagram.Cone target.main)

noncomputable def appendTransitionGraph : ZFSet.{u} :=
  familyCodeGraph (mainTransitionIndexKey run.appendKey)
    (fun p => (cone.append.transition p.property).map.code)

theorem appendTransitionGraph_eq {row : ZFSet.{u}}
    (function : FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row)
    (entries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔ z = (cone.leg i).map.code) :
    run.appendTransitionGraph target cone =
      insert (ZFSet.pair (ZFSet.pair run.indices run.indices)
        (GroundChronologicalMainTransition.identity pairing unions powers separation target.main).map.code)
        (run.transitionGraph ∪ row) := by
  apply ZFSet.ext
  intro z
  rw [appendTransitionGraph, mem_familyCodeGraph, ZFSet.mem_insert_iff, ZFSet.mem_union]
  constructor
  · rintro ⟨⟨⟨i, j⟩, before⟩, rfl⟩
    cases i with
    | top =>
      cases j with
      | top => exact Or.inl rfl
      | coe j => exact False.elim (WithTop.not_top_le_coe j before)
    | coe i =>
      cases j with
      | top => exact Or.inr (Or.inr ((entries i _).2 rfl))
      | coe j => exact Or.inr (Or.inl ((run.transitionGraph_entry (WithTop.coe_le_coe.mp before) _).2 rfl))
  · rintro (rfl | old | fresh)
    · exact ⟨⟨(⊤, ⊤), le_rfl⟩, rfl⟩
    · obtain ⟨⟨⟨i, j⟩, before⟩, rfl⟩ := (mem_familyCodeGraph _ _ _).1 old
      exact ⟨⟨((i : WithTop I), (j : WithTop I)), WithTop.coe_le_coe.mpr before⟩, rfl⟩
    · obtain ⟨key, keyMember, value, rfl⟩ := function.shape _ fresh
      obtain ⟨a, ha, x, hx, rfl⟩ := ZFSet.mem_prod.1 keyMember
      have equal := ZFSet.mem_singleton.1 ha
      subst a
      obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
      have valueEq := (entries i value).1 fresh
      exact ⟨⟨((i : WithTop I), ⊤), le_top⟩,
        congrArg (ZFSet.pair (ZFSet.pair run.indices (run.key i))) valueEq.symm⟩

noncomputable def appendCone {row : ZFSet.{u}} (ground : row ∈ M.sets)
    (function : FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row)
    (entries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔ z = (cone.leg i).map.code)
    (covered : cone.append.CoversOldBirths) :
    GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I) where
  key := run.appendKey
  key_injective := run.appendKey_injective
  key_order := run.appendKey_order
  indices_ground := run.appendKey_range.symm ▸ M.insert_mem pairing unions run.indices_ground run.indices_ground
  indices_ordinal := run.appendKey_range.symm ▸ ordinalSetProperty_succ run.indices_ordinal
  diagram := cone.append
  linked := run.appendLinked target
  linked_main := by
    intro i
    cases i with
    | top => rfl
    | coe i => exact run.linked_main i
  coverage := covered
  stages_ground := (run.appendStageGraph_eq target).symm ▸
    M.insert_mem pairing unions (M.orderedPair_mem pairing run.indices_ground (target.code_ground pairing)) run.stages_ground
  transitions_ground := by
    change run.appendTransitionGraph target cone ∈ M.sets
    rw [run.appendTransitionGraph_eq target cone function entries]
    exact M.insert_mem pairing unions (M.orderedPair_mem pairing
      (M.orderedPair_mem pairing run.indices_ground run.indices_ground)
      ((GroundChronologicalMainTransition.identity pairing unions powers separation target.main).map.code_mem pairing))
      (M.binary_union_mem pairing unions run.transitions_ground ground)

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (last : I) (greatest : ∀ i, i ≤ last)
variable (target : GroundLinkedMainStage M K Labels C D rD)
variable (step : GroundChronologicalMainTransition (run.diagram.stage last) target.main)
variable (covered : step.CoversOldBirths)

noncomputable def appendLast :
    GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I) := by
  let witnesses := run.exists_appendRow last greatest target step
  let row := Classical.choose witnesses
  have spec := Classical.choose_spec witnesses
  exact run.appendCone target (run.diagram.coneOfLast last greatest step) spec.1 spec.2.1 spec.2.2
    (run.diagram.coneOfLast_coverage last greatest step run.coverage covered)

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u v

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def appendSourceBound : ZFSet.{u} := by
  let V : ZFSet.{u} := ⋃₀ ⋃₀ run.transitionGraph
  let R : ZFSet.{u} := ⋃₀ ⋃₀ V
  exact ⋃₀ ⋃₀ ⋃₀ R

end GroundMainPrefix
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundLinkedTransitionRetarget
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

namespace LinkedMainTransitionCode
variable {M : TransitiveGround.{u}} {K Labels C D rD z : ZFSet.{u}}

theorem exists_at (source target : GroundLinkedMainStage M K Labels C D rD)
    (code : LinkedMainTransitionCode M K Labels C D rD source.code target.code z) :
    ∃ transition : GroundChronologicalMainTransition source.main target.main,
      transition.map.code = z ∧ transition.CoversOldBirths := by
  obtain ⟨first, second, sourceCode, targetCode, transition, equal, coverage⟩ := code
  exact ⟨transition.retargetLinked sourceCode targetCode,
    (transition.retargetLinked_code sourceCode targetCode).trans equal,
    transition.retargetLinked_coversOldBirths sourceCode targetCode coverage⟩

end LinkedMainTransitionCode

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixDecoding
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace MainPrefixGraphCode
open SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD T S E : ZFSet.{u}}
variable (raw : MainPrefixGraphCode M K Labels C D rD T S E)

noncomputable def decodedLinked (i : SetMembers T) : GroundLinkedMainStage M K Labels C D rD :=
  Classical.choose (raw.stage_valid (SetMembers.raw i) (decodedFamilyValue raw.stages i)
    (decodedFamilyValue_entry raw.stages i))

theorem decodedLinked_code (i : SetMembers T) :
    (raw.decodedLinked i).code = decodedFamilyValue raw.stages i :=
  Classical.choose_spec (raw.stage_valid (SetMembers.raw i) (decodedFamilyValue raw.stages i)
    (decodedFamilyValue_entry raw.stages i))

theorem decodedLinked_entry (i : SetMembers T) :
    ZFSet.pair (SetMembers.raw i) (raw.decodedLinked i).code ∈ S := by
  rw [raw.decodedLinked_code]
  exact decodedFamilyValue_entry raw.stages i

noncomputable def decodedTransitionCode (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) : ZFSet.{u} :=
  raw.transitions.value (decodedTransitionIndex i j before)

theorem decodedTransitionCode_entry (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) :
    ZFSet.pair (ZFSet.pair (SetMembers.raw j) (SetMembers.raw i))
      (raw.decodedTransitionCode i j before) ∈ E :=
  raw.transitions.value_entry (decodedTransitionIndex i j before)

theorem exists_decodedTransition (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) :
    ∃ transition : GroundChronologicalMainTransition (raw.decodedLinked i).main (raw.decodedLinked j).main,
      transition.map.code = raw.decodedTransitionCode i j before ∧ transition.CoversOldBirths :=
  LinkedMainTransitionCode.exists_at (raw.decodedLinked i) (raw.decodedLinked j)
    (raw.transition_valid _ _ _ _ _ (raw.decodedLinked_entry i) (raw.decodedLinked_entry j)
      (raw.decodedTransitionCode_entry i j before))

noncomputable def decodedTransition (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) :
    GroundChronologicalMainTransition (raw.decodedLinked i).main (raw.decodedLinked j).main :=
  Classical.choose (raw.exists_decodedTransition i j before)

theorem decodedTransition_code (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) :
    (raw.decodedTransition i j before).map.code = raw.decodedTransitionCode i j before :=
  (Classical.choose_spec (raw.exists_decodedTransition i j before)).1

theorem decodedTransition_coverage (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) :
    (raw.decodedTransition i j before).CoversOldBirths :=
  (Classical.choose_spec (raw.exists_decodedTransition i j before)).2

theorem decodedTransition_entry (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) :
    ZFSet.pair (ZFSet.pair (SetMembers.raw j) (SetMembers.raw i))
      (raw.decodedTransition i j before).map.code ∈ E := by
  rw [raw.decodedTransition_code]
  exact raw.decodedTransitionCode_entry i j before

end MainPrefixGraphCode

namespace MainPrefixGraphCode
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD T S E : ZFSet.{u}}
variable (raw : MainPrefixGraphCode M K Labels C D rD T S E)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

theorem decodedTransition_self (i : SetMembers T) :
    raw.decodedTransition i i (Or.inl rfl) =
      GroundChronologicalMainTransition.identity pairing unions powers separation (raw.decodedLinked i).main := by
  have diagonal := raw.identity (SetMembers.raw i) _ _ (raw.decodedTransition_entry i i (Or.inl rfl))
  apply GroundChronologicalMainTransition.ext
  apply GroundMainTransition.ext
  · exact diagonal.1.eq_identityFunctionGraph
      (raw.decodedTransition i i (Or.inl rfl)).map.point_embedding.injection.function
  · exact diagonal.2.eq_identityFunctionGraph
      (raw.decodedTransition i i (Or.inl rfl)).map.group_embedding.injection.function

theorem decodedTransition_comp (i j k : SetMembers T)
    (first : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j)
    (second : SetMembers.raw j = SetMembers.raw k ∨ SetMembers.raw j ∈ SetMembers.raw k) :
    raw.decodedTransition i k ((ordinalMainIndexPreorder raw.ordinal).le_trans i j k first second) =
      (raw.decodedTransition i j first).comp pairing unions powers separation (raw.decodedTransition j k second) := by
  have direct := (ordinalMainIndexPreorder raw.ordinal).le_trans i j k first second
  have coherent := raw.composition (SetMembers.raw i) (SetMembers.raw j) (SetMembers.raw k)
    _ _ _ _ _ _ (raw.decodedTransition_entry i j first) (raw.decodedTransition_entry j k second)
      (raw.decodedTransition_entry i k direct)
  apply GroundChronologicalMainTransition.ext
  apply GroundMainTransition.ext
  · exact coherent.1.eq_relationCompose
      (raw.decodedTransition i j first).map.point_embedding.injection.function
      (raw.decodedTransition i k direct).map.point_embedding.injection.function.1
  · exact coherent.2.eq_relationCompose
      (raw.decodedTransition i j first).map.group_embedding.injection.function
      (raw.decodedTransition i k direct).map.group_embedding.injection.function.1

noncomputable def decodedDiagram :
    letI := ordinalMainIndexPreorder raw.ordinal
    GroundChronologicalMainDiagram M C D rD pairing unions powers separation (SetMembers T) := by
  let := ordinalMainIndexPreorder raw.ordinal
  exact {
    stage := fun i => (raw.decodedLinked i).main
    transition := fun {i j} before => raw.decodedTransition i j before
    self := raw.decodedTransition_self pairing unions powers separation
    comp := fun {i j k} first second => raw.decodedTransition_comp pairing unions powers separation i j k first second
  }

theorem decodedDiagram_coverage :
    letI := ordinalMainIndexPreorder raw.ordinal
    (raw.decodedDiagram pairing unions powers separation).CoversOldBirths := by
  let := ordinalMainIndexPreorder raw.ordinal
  exact fun {i j} before => raw.decodedTransition_coverage i j before

end MainPrefixGraphCode

namespace MainPrefixGraphCode
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD T S E : ZFSet.{u}}
variable (raw : MainPrefixGraphCode M K Labels C D rD T S E)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hT : T ∈ M.sets) (hS : S ∈ M.sets) (hE : E ∈ M.sets)

noncomputable def decodedPrefix :
    letI := ordinalMainIndexPreorder raw.ordinal
    GroundMainPrefix M K Labels C D rD pairing unions powers separation (SetMembers T) := by
  let := ordinalMainIndexPreorder raw.ordinal
  exact {
    key := SetMembers.raw
    key_injective := SetMembers.raw_injective T
    key_order := fun i j => ordinalMainIndex_le_iff raw.ordinal i j
    indices_ground := (ordinalMainIndex_key_range T).symm ▸ hT
    indices_ordinal := (ordinalMainIndex_key_range T).symm ▸ raw.ordinal
    diagram := raw.decodedDiagram pairing unions powers separation
    linked := raw.decodedLinked
    linked_main := fun _ => rfl
    coverage := raw.decodedDiagram_coverage pairing unions powers separation
    stages_ground := familyCodeGraph_ground_of_entries hS raw.stages _ _
      (ordinalMainIndex_key_range T) raw.decodedLinked_entry
    transitions_ground := familyCodeGraph_ground_of_entries hE raw.transitions _ _
      (ordinalMainTransitionIndex_range raw.ordinal)
      (fun p => raw.decodedTransition_entry p.val.1 p.val.2 p.property)
  }

end MainPrefixGraphCode

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitCoverageGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

structure LimitCoverage (target : GroundChronologicalMainStage M C D rD)
    (cone : run.diagram.Cone target) : Prop where
  points : ∀ x, (x ∈ target.stage.carrier ∧ x ≠ target.stage.top) ↔
    ∃ i y, y ∈ (run.diagram.stage i).stage.carrier ∧ ZFSet.pair y x ∈ (cone.leg i).map.points
  actors : ∀ g, g ∈ target.stage.actors ↔
    ∃ i h, h ∈ (run.diagram.stage i).stage.actors ∧ ZFSet.pair h g ∈ (cone.leg i).map.actors
  strict_top : ∀ i x y, ZFSet.pair x y ∈ (cone.leg i).map.points →
    ZFSet.pair y target.stage.top ∈ target.stage.order ∧
      ZFSet.pair target.stage.top y ∉ target.stage.order
  cutoff : target.cutoff =
    ⋃₀ ZFSet.range (fun i => insert (run.diagram.stage i).cutoff (run.diagram.stage i).cutoff)
  top_birth : ∀ x, ZFSet.pair x target.cutoff ∈ target.birth ↔ x = target.stage.top

theorem actorUnion_ground : run.actorUnion ∈ M.sets := run.stageFieldUnion_ground 3

theorem stageFieldUnion_mem (j : Fin 11) (x : ZFSet.{u}) :
    x ∈ run.stageFieldUnion j ↔ ∃ i, x ∈ (run.diagram.stage i).stage.field j :=
  familyCodeGraph_valueUnion_mem_iff _ x

theorem carrierFamily_subset_union {i X : ZFSet.{u}}
    (entry : ZFSet.pair i X ∈ run.carrierFamily) : X ⊆ run.carrierUnion :=
  run.stageFieldFamily_subset_union 0 entry

theorem stageFieldFamily_rank_le_code (j : Fin 11) :
    ZFSet.rank (run.stageFieldFamily j) ≤ ZFSet.rank run.code := by
  apply (familyCodeGraph_rank_mono run.key _ (fun i => (run.linked i).code) ?_).trans
    run.stageGraph_rank_le_code
  intro i
  simpa only [run.linked_main] using (run.linked i).field_rank_le_linkedCode j

theorem stageFieldUnion_rank_le_code (j : Fin 11) :
    ZFSet.rank (run.stageFieldUnion j) ≤ ZFSet.rank run.code :=
  (familyCodeGraph_valueUnion_rank_le run.key _).trans (run.stageFieldFamily_rank_le_code j)

theorem carrierUnion_rank_le_code : ZFSet.rank run.carrierUnion ≤ ZFSet.rank run.code :=
  run.stageFieldUnion_rank_le_code 0

theorem actorUnion_rank_le_code : ZFSet.rank run.actorUnion ≤ ZFSet.rank run.code :=
  run.stageFieldUnion_rank_le_code 3

theorem cutoffFamily_function : FunctionGraphOn run.indices run.cutoffFamily :=
  familyCodeGraph_function run.key _ run.key_injective

theorem cutoffFamily_entry (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.cutoffFamily ↔ z = (run.diagram.stage i).cutoff :=
  pair_mem_familyCodeGraph run.key _ run.key_injective i z

theorem birthFamily_entry (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.birthFamily ↔ z = (run.diagram.stage i).birth :=
  pair_mem_familyCodeGraph run.key _ run.key_injective i z





noncomputable def pointPresentation : CodedDirectPresentation run.pointSystem
    run.indices run.carrierUnion run.carrierFamily run.pointMapFamily where
  key := run.key
  key_injective := run.key_injective
  key_range := rfl
  key_order := run.key_order
  carrier_function := run.carrierFamily_function
  carrier_entry i := (run.carrierFamily_entry i _).2 rfl
  map_function := run.pointMapFamily_function
  map_entry before := (run.pointMapFamily_entry before _).2 rfl
  carrier_bound i := run.carrierFamily_subset_union ((run.carrierFamily_entry i _).2 rfl)

noncomputable def actorPresentation : CodedDirectPresentation run.actorSystem
    run.indices run.actorUnion run.actorFamily run.actorMapFamily where
  key := run.key
  key_injective := run.key_injective
  key_range := rfl
  key_order := run.key_order
  carrier_function := run.actorFamily_function
  carrier_entry i := (run.actorFamily_entry i _).2 rfl
  map_function := run.actorMapFamily_function
  map_entry before := (run.actorMapFamily_entry before _).2 rfl
  carrier_bound i := run.actorFamily_subset_union ((run.actorFamily_entry i _).2 rfl)





end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem cutoff_mem_cutoffLimit (i : I) : (run.diagram.stage i).cutoff ∈ run.cutoffLimit :=
  (run.cutoffLimit_mem _).2 ⟨i, Or.inl rfl⟩

theorem birth_time_mem_cutoffLimit (i : I) {x t : ZFSet.{u}}
    (entry : ZFSet.pair x t ∈ (run.diagram.stage i).birth) : t ∈ run.cutoffLimit :=
  (run.cutoffLimit_mem t).2 ⟨i, (run.diagram.stage i).birth_bound entry⟩

theorem cutoffLimit_mem_inaccessible (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) : run.cutoffLimit ∈ K := by
  have family : ZFSet.IsFunc run.indices K run.cutoffFamily := by
    refine ⟨?_, run.cutoffFamily_function.to_isFunc.2⟩
    intro z hz
    obtain ⟨i, rfl⟩ := (mem_familyCodeGraph run.key (fun i => (run.diagram.stage i).cutoff) z).1 hz
    have cutoff : (run.diagram.stage i).cutoff ∈ K := by
      simpa only [run.linked_main] using (run.linked i).invariant.cutoff_mem
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, cutoff⟩
  obtain ⟨δ, hδ, bounded⟩ := (standard.2.2.1.regular standard.1.1).bound_small_domain
    pairing unions powers separation run.indices_ground hK run.cutoffFamily_ground indices family
  have ordinalδ := ordinalSetProperty_member standard.1.1 hδ
  have subset : run.cutoffLimit ⊆ δ := by
    intro t ht
    obtain ⟨i, before⟩ := (run.cutoffLimit_mem t).1 ht
    have cutoff := bounded (run.key i) (run.diagram.stage i).cutoff ((run.cutoffFamily_entry i _).2 rfl)
    rcases before with rfl | before
    · exact cutoff
    · exact ordinalδ.1 _ cutoff t before
  have coded : ordinalCode (ZFSet.rank run.cutoffLimit) ∈ ordinalCode (ZFSet.rank K) :=
    (mem_ordinalCode_iff _ _).2 ((ZFSet.rank_mono subset).trans_lt (ZFSet.rank_lt_of_mem hδ))
  exact (congrArg₂ (fun a b : ZFSet.{u} => a ∈ b)
    (ordinalSetProperty_eq_code_rank run.cutoffLimit run.cutoffLimit_ordinal)
    (ordinalSetProperty_eq_code_rank K standard.1.1)).mpr coded

end PartitionPilot.Forcing.GroundMainPrefix



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitGroupLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def limitPointMap (i : I) : ZFSet.{u} :=
  directLimitInclusion run.indices run.carrierUnion run.carrierFamily run.pointMapFamily (run.key i)

theorem limitPointMap_ground (i : I) : run.limitPointMap i ∈ M.sets :=
  M.indexedClassInclusion_mem pairing unions powers separation run.carrierUnion_ground
    run.limitPointLabels_ground run.limitPointRelation_ground
    (M.transitive run.indices_ground (ZFSet.mem_range.2 ⟨i, rfl⟩))

theorem limitPointMap_injection (i : I) :
    InjectionCode (run.diagram.stage i).stage.carrier run.limitPoints (run.limitPointMap i) :=
  run.pointPresentation.inclusion_injection i

theorem limitPointInclusions_function : FunctionGraphOn run.indices run.limitPointInclusions :=
  ⟨_, M.indexedClassInclusions_function pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.limitPointLabels_ground run.limitPointRelation_ground⟩

theorem limitPointInclusions_entry (i : I) (f : ZFSet.{u}) :
    ZFSet.pair (run.key i) f ∈ run.limitPointInclusions ↔ f = run.limitPointMap i := by
  exact (M.indexedClassInclusions_entries pairing unions powers separation (T := run.indices)
    run.indices_ground run.carrierUnion_ground run.limitPointLabels_ground run.limitPointRelation_ground
    (run.key i) f).trans (and_iff_right (show run.key i ∈ run.indices from ZFSet.mem_range.2 ⟨i, rfl⟩))

theorem limitPointMap_comp {i j : I} (before : i ≤ j) :
    relationCompose (run.diagram.stage i).stage.carrier (run.diagram.stage j).stage.carrier
      run.limitPoints (run.diagram.transition before).map.points
      (run.limitPointMap j) = run.limitPointMap i :=
  run.pointPresentation.inclusion_comp before

noncomputable def limitActorMap (i : I) : ZFSet.{u} :=
  directLimitInclusion run.indices run.actorUnion run.actorFamily run.actorMapFamily (run.key i)

theorem limitActorLabels_ground : run.limitActorLabels ∈ M.sets :=
  M.indexedCarrierLabels_mem pairing unions powers separation run.indices_ground
    run.actorUnion_ground run.actorFamily_ground

theorem limitActorRelation_ground : run.limitActorRelation ∈ M.sets :=
  M.directLimitRelation_mem pairing unions powers separation run.indices_ground
    run.actorUnion_ground run.actorMapFamily_ground run.limitActorLabels_ground

theorem limitActors_ground : run.limitActors ∈ M.sets :=
  M.equivalenceClasses_mem powers separation run.limitActorLabels_ground run.limitActorRelation_ground

theorem limitActorMap_ground (i : I) : run.limitActorMap i ∈ M.sets :=
  M.indexedClassInclusion_mem pairing unions powers separation run.actorUnion_ground
    run.limitActorLabels_ground run.limitActorRelation_ground
    (M.transitive run.indices_ground (ZFSet.mem_range.2 ⟨i, rfl⟩))

theorem limitActorInclusions_ground : run.limitActorInclusions ∈ M.sets :=
  M.indexedClassInclusions_mem pairing unions powers separation run.indices_ground
    run.actorUnion_ground run.limitActorLabels_ground run.limitActorRelation_ground

theorem limitActorMap_injection (i : I) :
    InjectionCode (run.diagram.stage i).stage.actors run.limitActors (run.limitActorMap i) :=
  run.actorPresentation.inclusion_injection i

theorem limitActorInclusions_function : FunctionGraphOn run.indices run.limitActorInclusions :=
  ⟨_, M.indexedClassInclusions_function pairing unions powers separation run.indices_ground
    run.actorUnion_ground run.limitActorLabels_ground run.limitActorRelation_ground⟩

theorem limitActorInclusions_entry (i : I) (f : ZFSet.{u}) :
    ZFSet.pair (run.key i) f ∈ run.limitActorInclusions ↔ f = run.limitActorMap i := by
  exact (M.indexedClassInclusions_entries pairing unions powers separation (T := run.indices)
    run.indices_ground run.actorUnion_ground run.limitActorLabels_ground run.limitActorRelation_ground
    (run.key i) f).trans (and_iff_right (show run.key i ∈ run.indices from ZFSet.mem_range.2 ⟨i, rfl⟩))

theorem limitActorMap_comp {i j : I} (before : i ≤ j) :
    relationCompose (run.diagram.stage i).stage.actors (run.diagram.stage j).stage.actors
      run.limitActors (run.diagram.transition before).map.actors
      (run.limitActorMap j) = run.limitActorMap i :=
  run.actorPresentation.inclusion_comp before

def LimitMul (g h k : ZFSet.{u}) : Prop :=
  ∃ i a b c, a ∈ (run.diagram.stage i).stage.actors ∧ b ∈ (run.diagram.stage i).stage.actors ∧
    c ∈ (run.diagram.stage i).stage.actors ∧ g = run.actorPresentation.limitPoint i a ∧
    h = run.actorPresentation.limitPoint i b ∧ k = run.actorPresentation.limitPoint i c ∧
    ZFSet.pair (ZFSet.pair a b) c ∈ (run.diagram.stage i).stage.multiplication

def LimitInv (g h : ZFSet.{u}) : Prop :=
  ∃ i a b, a ∈ (run.diagram.stage i).stage.actors ∧ b ∈ (run.diagram.stage i).stage.actors ∧
    g = run.actorPresentation.limitPoint i a ∧ h = run.actorPresentation.limitPoint i b ∧
    ZFSet.pair a b ∈ (run.diagram.stage i).stage.inverse

theorem limitMul_bounds {g h k : ZFSet.{u}} (mul : run.LimitMul g h k) :
    g ∈ run.limitActors ∧ h ∈ run.limitActors ∧ k ∈ run.limitActors := by
  obtain ⟨i, a, b, c, ha, hb, hc, rfl, rfl, rfl, _⟩ := mul
  exact ⟨run.actorPresentation.limitPoint_mem ha, run.actorPresentation.limitPoint_mem hb,
    run.actorPresentation.limitPoint_mem hc⟩

theorem limitMul_total {g h : ZFSet.{u}} (hg : g ∈ run.limitActors) (hh : h ∈ run.limitActors) :
    ∃ k ∈ run.limitActors, run.LimitMul g h k := by
  obtain ⟨i, a, b, ha, hb, rfl, rfl⟩ := run.actorPresentation.pair_coverage hg hh
  obtain ⟨c, entry, _⟩ := (run.diagram.stage i).stage.group_code.mul_function.2
    (ZFSet.pair a b) (ZFSet.pair_mem_prod.2 ⟨ha, hb⟩)
  have hc := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.mul_function.1 entry)).2
  exact ⟨run.actorPresentation.limitPoint i c, run.actorPresentation.limitPoint_mem hc,
    i, a, b, c, ha, hb, hc, rfl, rfl, rfl, entry⟩

theorem limitInv_total {g : ZFSet.{u}} (hg : g ∈ run.limitActors) :
    ∃ h ∈ run.limitActors, run.LimitInv g h := by
  obtain ⟨i, a, ha, rfl⟩ := run.actorPresentation.limitPoint_coverage hg
  obtain ⟨b, entry, _⟩ := (run.diagram.stage i).stage.group_code.inv_function.2 a ha
  have hb := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.inv_function.1 entry)).2
  exact ⟨run.actorPresentation.limitPoint i b, run.actorPresentation.limitPoint_mem hb,
    i, a, b, ha, hb, rfl, rfl, entry⟩

theorem limitMul_unique {g h k l : ZFSet.{u}}
    (first : run.LimitMul g h k) (second : run.LimitMul g h l) : k = l := by
  obtain ⟨i, a, b, c, ha, hb, hc, rfl, rfl, rfl, product⟩ := first
  obtain ⟨j, d, e, f, hd, he, hf, equalA, equalB, rfl, product'⟩ := second
  obtain ⟨m, im, jm⟩ := run.common_upper i j
  obtain ⟨a', aa'⟩ := run.actorSystem.map_entry_total im ha
  obtain ⟨b', bb'⟩ := run.actorSystem.map_entry_total im hb
  obtain ⟨c', cc'⟩ := run.actorSystem.map_entry_total im hc
  obtain ⟨d', dd'⟩ := run.actorSystem.map_entry_total jm hd
  obtain ⟨e', ee'⟩ := run.actorSystem.map_entry_total jm he
  obtain ⟨f', ff'⟩ := run.actorSystem.map_entry_total jm hf
  have sameA := (run.actorSystem.related_iff_common_images im jm aa' dd').1
    ((run.actorPresentation.limitPoint_eq_iff_related ha hd).1 equalA)
  have sameB := (run.actorSystem.related_iff_common_images im jm bb' ee').1
    ((run.actorPresentation.limitPoint_eq_iff_related hb he).1 equalB)
  subst d'
  subst e'
  have left := (run.diagram.transition im).map.group_embedding.mul a b c a' b' c' product aa' bb' cc'
  have right := (run.diagram.transition jm).map.group_embedding.mul d e f a' b' f' product' dd' ee' ff'
  have sameC : c' = f' :=
    (show FunctionGraphOn (ZFSet.prod (run.diagram.stage m).stage.actors (run.diagram.stage m).stage.actors)
      (run.diagram.stage m).stage.multiplication from
      ⟨_, (run.diagram.stage m).stage.group_code.mul_function⟩).unique left right
  apply (run.actorPresentation.limitPoint_eq_iff_related hc hf).2
  exact ⟨m, im, jm, c', cc', sameC.symm ▸ ff'⟩

theorem limitInv_unique {g h k : ZFSet.{u}}
    (first : run.LimitInv g h) (second : run.LimitInv g k) : h = k := by
  obtain ⟨i, a, b, ha, hb, rfl, rfl, inverse⟩ := first
  obtain ⟨j, c, d, hc, hd, equal, rfl, inverse'⟩ := second
  obtain ⟨m, im, jm⟩ := run.common_upper i j
  obtain ⟨a', aa'⟩ := run.actorSystem.map_entry_total im ha
  obtain ⟨b', bb'⟩ := run.actorSystem.map_entry_total im hb
  obtain ⟨c', cc'⟩ := run.actorSystem.map_entry_total jm hc
  obtain ⟨d', dd'⟩ := run.actorSystem.map_entry_total jm hd
  have sameA := (run.actorSystem.related_iff_common_images im jm aa' cc').1
    ((run.actorPresentation.limitPoint_eq_iff_related ha hc).1 equal)
  subst c'
  have left := (run.diagram.transition im).map.group_embedding.map_inv
    (run.diagram.stage i).stage.group_code (run.diagram.stage m).stage.group_code inverse aa' bb'
  have right := (run.diagram.transition jm).map.group_embedding.map_inv
    (run.diagram.stage j).stage.group_code (run.diagram.stage m).stage.group_code inverse' cc' dd'
  have sameB : b' = d' :=
    (show FunctionGraphOn (run.diagram.stage m).stage.actors (run.diagram.stage m).stage.inverse from
      ⟨_, (run.diagram.stage m).stage.group_code.inv_function⟩).unique left right
  apply (run.actorPresentation.limitPoint_eq_iff_related hb hd).2
  exact ⟨m, im, jm, b', bb', sameB.symm ▸ dd'⟩

theorem limitMul_at (i : I) {a b c : ZFSet.{u}}
    (ha : a ∈ (run.diagram.stage i).stage.actors) (hb : b ∈ (run.diagram.stage i).stage.actors)
    (hc : c ∈ (run.diagram.stage i).stage.actors) :
    run.LimitMul (run.actorPresentation.limitPoint i a) (run.actorPresentation.limitPoint i b)
      (run.actorPresentation.limitPoint i c) ↔
      ZFSet.pair (ZFSet.pair a b) c ∈ (run.diagram.stage i).stage.multiplication := by
  constructor
  · intro product
    obtain ⟨d, entry, _⟩ := (run.diagram.stage i).stage.group_code.mul_function.2
      (ZFSet.pair a b) (ZFSet.pair_mem_prod.2 ⟨ha, hb⟩)
    have hd := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.mul_function.1 entry)).2
    have canonical : run.LimitMul (run.actorPresentation.limitPoint i a)
        (run.actorPresentation.limitPoint i b) (run.actorPresentation.limitPoint i d) :=
      ⟨i, a, b, d, ha, hb, hd, rfl, rfl, rfl, entry⟩
    have equal := (run.actorPresentation.limitPoint_same_iff hc hd).1 (run.limitMul_unique product canonical)
    subst d
    exact entry
  · intro entry
    exact ⟨i, a, b, c, ha, hb, hc, rfl, rfl, rfl, entry⟩

theorem limitInv_at (i : I) {a b : ZFSet.{u}}
    (ha : a ∈ (run.diagram.stage i).stage.actors) (hb : b ∈ (run.diagram.stage i).stage.actors) :
    run.LimitInv (run.actorPresentation.limitPoint i a) (run.actorPresentation.limitPoint i b) ↔
      ZFSet.pair a b ∈ (run.diagram.stage i).stage.inverse := by
  constructor
  · intro inverse
    obtain ⟨c, entry, _⟩ := (run.diagram.stage i).stage.group_code.inv_function.2 a ha
    have hc := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.inv_function.1 entry)).2
    have canonical : run.LimitInv (run.actorPresentation.limitPoint i a) (run.actorPresentation.limitPoint i c) :=
      ⟨i, a, c, ha, hc, rfl, rfl, entry⟩
    have equal := (run.actorPresentation.limitPoint_same_iff hb hc).1 (run.limitInv_unique inverse canonical)
    subst c
    exact entry
  · intro entry
    exact ⟨i, a, b, ha, hb, rfl, rfl, entry⟩

noncomputable def limitIdentity (i : I) : ZFSet.{u} :=
  run.actorPresentation.limitPoint i (run.diagram.stage i).stage.identity

theorem limitIdentity_mem (i : I) : run.limitIdentity i ∈ run.limitActors :=
  run.actorPresentation.limitPoint_mem (run.diagram.stage i).stage.group_code.identity_mem

theorem limitIdentity_eq (i j : I) : run.limitIdentity i = run.limitIdentity j := by
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  apply (run.actorPresentation.limitPoint_eq_iff_related
    (run.diagram.stage i).stage.group_code.identity_mem (run.diagram.stage j).stage.group_code.identity_mem).2
  exact ⟨k, ik, jk, (run.diagram.stage k).stage.identity,
    (run.diagram.transition ik).map.group_embedding.one, (run.diagram.transition jk).map.group_embedding.one⟩

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitBottom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix

section
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

def LimitLE (p q : ZFSet.{u}) : Prop :=
  ∃ i x y, x ∈ (run.diagram.stage i).stage.carrier ∧
    y ∈ (run.diagram.stage i).stage.carrier ∧
    p = run.pointPresentation.limitPoint i x ∧ q = run.pointPresentation.limitPoint i y ∧
    ZFSet.pair x y ∈ (run.diagram.stage i).stage.order

theorem point_order_congr {i j : I} {x y a b : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier)
    (hy : y ∈ (run.diagram.stage i).stage.carrier)
    (ha : a ∈ (run.diagram.stage j).stage.carrier)
    (hb : b ∈ (run.diagram.stage j).stage.carrier)
    (first : run.pointPresentation.limitPoint i x = run.pointPresentation.limitPoint j a)
    (second : run.pointPresentation.limitPoint i y = run.pointPresentation.limitPoint j b) :
    ZFSet.pair x y ∈ (run.diagram.stage i).stage.order ↔
      ZFSet.pair a b ∈ (run.diagram.stage j).stage.order := by
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  obtain ⟨x', xx'⟩ := run.pointSystem.map_entry_total ik hx
  obtain ⟨y', yy'⟩ := run.pointSystem.map_entry_total ik hy
  obtain ⟨a', aa'⟩ := run.pointSystem.map_entry_total jk ha
  obtain ⟨b', bb'⟩ := run.pointSystem.map_entry_total jk hb
  have equalX := (run.pointSystem.related_iff_common_images ik jk xx' aa').1
    ((run.pointPresentation.limitPoint_eq_iff_related hx ha).1 first)
  have equalY := (run.pointSystem.related_iff_common_images ik jk yy' bb').1
    ((run.pointPresentation.limitPoint_eq_iff_related hy hb).1 second)
  subst a'
  subst b'
  exact ((run.diagram.transition ik).map.order_iff x y x' y' xx' yy').symm.trans
    ((run.diagram.transition jk).map.order_iff a b x' y' aa' bb')

theorem limitLE_bounds {p q : ZFSet.{u}} (lower : run.LimitLE p q) :
    p ∈ run.limitPoints ∧ q ∈ run.limitPoints := by
  obtain ⟨i, x, y, hx, hy, rfl, rfl, _⟩ := lower
  exact ⟨run.pointPresentation.limitPoint_mem hx, run.pointPresentation.limitPoint_mem hy⟩

theorem limitLE_at (i : I) {x y : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier)
    (hy : y ∈ (run.diagram.stage i).stage.carrier) :
    run.LimitLE (run.pointPresentation.limitPoint i x) (run.pointPresentation.limitPoint i y) ↔
      ZFSet.pair x y ∈ (run.diagram.stage i).stage.order := by
  constructor
  · rintro ⟨j, a, b, ha, hb, first, second, lower⟩
    exact (run.point_order_congr hx hy ha hb first second).2 lower
  · intro lower
    exact ⟨i, x, y, hx, hy, rfl, rfl, lower⟩

theorem limitLE_refl {p : ZFSet.{u}} (member : p ∈ run.limitPoints) : run.LimitLE p p := by
  obtain ⟨i, x, hx, rfl⟩ := run.pointPresentation.limitPoint_coverage member
  exact (run.limitLE_at i hx hx).2 ((run.diagram.stage i).stage.meet.order.refl x hx)

theorem limitLE_antisymm {p q : ZFSet.{u}}
    (first : run.LimitLE p q) (second : run.LimitLE q p) : p = q := by
  obtain ⟨i, x, y, hx, hy, rfl, rfl⟩ := run.pointPresentation.pair_coverage
    (run.limitLE_bounds first).1 (run.limitLE_bounds first).2
  have equal := (run.diagram.stage i).stage.meet.order.antisymm x hx y hy
    ((run.limitLE_at i hx hy).1 first) ((run.limitLE_at i hy hx).1 second)
  exact congrArg (run.pointPresentation.limitPoint i) equal

theorem limitLE_trans {p q r : ZFSet.{u}}
    (first : run.LimitLE p q) (second : run.LimitLE q r) : run.LimitLE p r := by
  obtain ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl⟩ := run.pointPresentation.triple_coverage
    (run.limitLE_bounds first).1 (run.limitLE_bounds first).2 (run.limitLE_bounds second).2
  exact (run.limitLE_at i hx hz).2 ((run.diagram.stage i).stage.meet.order.trans x hx y hy z hz
    ((run.limitLE_at i hx hy).1 first) ((run.limitLE_at i hy hz).1 second))

end

section
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank run.code < o)
include limit rank

theorem limitPointLabels_rank_lt : ZFSet.rank run.limitPointLabels < o :=
  indexedCarrierLabels_rank_lt limit run.carrierFamily
    (run.indices_rank_le_code.trans_lt rank) (run.carrierUnion_rank_le_code.trans_lt rank)

theorem limitPoints_rank_lt : ZFSet.rank run.limitPoints < o :=
  equivalenceClasses_rank_lt limit run.limitPointRelation (run.limitPointLabels_rank_lt limit rank)

theorem limitActorLabels_rank_lt : ZFSet.rank run.limitActorLabels < o :=
  indexedCarrierLabels_rank_lt limit run.actorFamily
    (run.indices_rank_le_code.trans_lt rank) (run.actorUnion_rank_le_code.trans_lt rank)

theorem limitActors_rank_lt : ZFSet.rank run.limitActors < o :=
  equivalenceClasses_rank_lt limit run.limitActorRelation (run.limitActorLabels_rank_lt limit rank)

end

section
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

def LimitMeet (p q r : ZFSet.{u}) : Prop :=
  ∃ i x y z, x ∈ (run.diagram.stage i).stage.carrier ∧
    y ∈ (run.diagram.stage i).stage.carrier ∧ z ∈ (run.diagram.stage i).stage.carrier ∧
    p = run.pointPresentation.limitPoint i x ∧ q = run.pointPresentation.limitPoint i y ∧
    r = run.pointPresentation.limitPoint i z ∧
    ZFSet.pair (ZFSet.pair x y) z ∈ (run.diagram.stage i).stage.meetGraph

theorem limitMeet_bounds {p q r : ZFSet.{u}} (meet : run.LimitMeet p q r) :
    p ∈ run.limitPoints ∧ q ∈ run.limitPoints ∧ r ∈ run.limitPoints := by
  obtain ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl, _⟩ := meet
  exact ⟨run.pointPresentation.limitPoint_mem hx, run.pointPresentation.limitPoint_mem hy,
    run.pointPresentation.limitPoint_mem hz⟩

theorem limitMeet_lower_left {p q r : ZFSet.{u}} (meet : run.LimitMeet p q r) :
    run.LimitLE r p := by
  obtain ⟨i, x, y, z, hx, _, hz, rfl, rfl, rfl, entry⟩ := meet
  exact (run.limitLE_at i hz hx).2 ((run.diagram.stage i).stage.meet.lower_left x y z entry)

theorem limitMeet_lower_right {p q r : ZFSet.{u}} (meet : run.LimitMeet p q r) :
    run.LimitLE r q := by
  obtain ⟨i, x, y, z, _, hy, hz, rfl, rfl, rfl, entry⟩ := meet
  exact (run.limitLE_at i hz hy).2 ((run.diagram.stage i).stage.meet.lower_right x y z entry)

theorem limitMeet_greatest {p q r w : ZFSet.{u}} (meet : run.LimitMeet p q r)
    (first : run.LimitLE w p) (second : run.LimitLE w q) : run.LimitLE w r := by
  obtain ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl, entry⟩ := meet
  obtain ⟨j, a, ha, rfl⟩ := run.pointPresentation.limitPoint_coverage (run.limitLE_bounds first).1
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  obtain ⟨x', xx'⟩ := run.pointSystem.map_entry_total ik hx
  obtain ⟨y', yy'⟩ := run.pointSystem.map_entry_total ik hy
  obtain ⟨z', zz'⟩ := run.pointSystem.map_entry_total ik hz
  obtain ⟨a', aa'⟩ := run.pointSystem.map_entry_total jk ha
  have hx' := (run.pointSystem.map_entry_bounds ik xx').2
  have hy' := (run.pointSystem.map_entry_bounds ik yy').2
  have hz' := (run.pointSystem.map_entry_bounds ik zz').2
  have ha' := (run.pointSystem.map_entry_bounds jk aa').2
  have mapped := (run.diagram.transition ik).map.point_embedding.map_meet
    x y z x' y' z' entry xx' yy' zz'
  have ax : run.LimitLE (run.pointPresentation.limitPoint k a')
      (run.pointPresentation.limitPoint k x') := by
    rw [← run.pointPresentation.limitPoint_transition jk aa',
      ← run.pointPresentation.limitPoint_transition ik xx']
    exact first
  have ay : run.LimitLE (run.pointPresentation.limitPoint k a')
      (run.pointPresentation.limitPoint k y') := by
    rw [← run.pointPresentation.limitPoint_transition jk aa',
      ← run.pointPresentation.limitPoint_transition ik yy']
    exact second
  rw [run.pointPresentation.limitPoint_transition jk aa',
    run.pointPresentation.limitPoint_transition ik zz']
  exact (run.limitLE_at k ha' hz').2 ((run.diagram.stage k).stage.meet.greatest
    x' y' z' a' ha' mapped ((run.limitLE_at k ha' hx').1 ax) ((run.limitLE_at k ha' hy').1 ay))

theorem limitMeet_total {p q : ZFSet.{u}} (hp : p ∈ run.limitPoints) (hq : q ∈ run.limitPoints) :
    ∃ r ∈ run.limitPoints, run.LimitMeet p q r := by
  obtain ⟨i, x, y, hx, hy, rfl, rfl⟩ := run.pointPresentation.pair_coverage hp hq
  obtain ⟨z, entry, _⟩ := (run.diagram.stage i).stage.meet.operation.2 (ZFSet.pair x y)
    (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
  have hz := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.meet.operation.1 entry)).2
  exact ⟨run.pointPresentation.limitPoint i z, run.pointPresentation.limitPoint_mem hz,
    i, x, y, z, hx, hy, hz, rfl, rfl, rfl, entry⟩

theorem limitMeet_unique {p q r s : ZFSet.{u}}
    (first : run.LimitMeet p q r) (second : run.LimitMeet p q s) : r = s :=
  run.limitLE_antisymm
    (run.limitMeet_greatest second (run.limitMeet_lower_left first) (run.limitMeet_lower_right first))
    (run.limitMeet_greatest first (run.limitMeet_lower_left second) (run.limitMeet_lower_right second))

theorem limitMeet_at (i : I) {x y z : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier)
    (hy : y ∈ (run.diagram.stage i).stage.carrier)
    (hz : z ∈ (run.diagram.stage i).stage.carrier) :
    run.LimitMeet (run.pointPresentation.limitPoint i x) (run.pointPresentation.limitPoint i y)
      (run.pointPresentation.limitPoint i z) ↔
      ZFSet.pair (ZFSet.pair x y) z ∈ (run.diagram.stage i).stage.meetGraph := by
  constructor
  · intro meet
    obtain ⟨w, entry, _⟩ := (run.diagram.stage i).stage.meet.operation.2 (ZFSet.pair x y)
      (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    have hw := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.meet.operation.1 entry)).2
    have canonical : run.LimitMeet (run.pointPresentation.limitPoint i x)
        (run.pointPresentation.limitPoint i y) (run.pointPresentation.limitPoint i w) :=
      ⟨i, x, y, w, hx, hy, hw, rfl, rfl, rfl, entry⟩
    have equal := (run.pointPresentation.limitPoint_same_iff hz hw).1
      (run.limitMeet_unique meet canonical)
    subst w
    exact entry
  · intro entry
    exact ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl, entry⟩

noncomputable def limitMultiplication : ZFSet.{u} :=
  indexedBinaryLift run.indices run.actorUnion run.limitActors (run.stageFieldFamily 4) run.limitActorInclusions

noncomputable def limitInverse : ZFSet.{u} :=
  indexedRelationLift run.indices run.actorUnion run.limitActors (run.stageFieldFamily 5) run.limitActorInclusions

theorem limitMultiplication_ground : run.limitMultiplication ∈ M.sets :=
  M.indexedBinaryLift_mem pairing unions powers separation run.indices_ground run.actorUnion_ground
    run.limitActors_ground (run.stageFieldFamily_ground 4) run.limitActorInclusions_ground

theorem limitInverse_ground : run.limitInverse ∈ M.sets :=
  M.indexedRelationLift_mem pairing unions powers separation run.indices_ground run.actorUnion_ground
    run.limitActors_ground (run.stageFieldFamily_ground 5) run.limitActorInclusions_ground

theorem limitMultiplication_entry (g h k : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g h) k ∈ run.limitMultiplication ↔ run.LimitMul g h k := by
  rw [limitMultiplication, triple_mem_indexedBinaryLift]
  constructor
  · rintro ⟨_, _, _, j, hj, m, e, a, _, b, _, c, _, operation, inclusion, first, second, third, mul⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hj
    have em : m = (run.diagram.stage i).stage.multiplication := (run.stageFieldFamily_entry 4 i m).1 operation
    have ee := (run.limitActorInclusions_entry i e).1 inclusion
    subst m
    subst e
    obtain ⟨ha, eg⟩ := (run.actorPresentation.inclusion_entry i a g).1 first
    obtain ⟨hb, eh⟩ := (run.actorPresentation.inclusion_entry i b h).1 second
    obtain ⟨hc, ek⟩ := (run.actorPresentation.inclusion_entry i c k).1 third
    exact ⟨i, a, b, c, ha, hb, hc, eg, eh, ek, mul⟩
  · rintro ⟨i, a, b, c, ha, hb, hc, rfl, rfl, rfl, mul⟩
    exact ⟨run.actorPresentation.limitPoint_mem ha, run.actorPresentation.limitPoint_mem hb,
      run.actorPresentation.limitPoint_mem hc, run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩,
      (run.diagram.stage i).stage.multiplication, run.limitActorMap i,
      a, run.actorPresentation.carrier_bound i ha, b, run.actorPresentation.carrier_bound i hb,
      c, run.actorPresentation.carrier_bound i hc,
      (run.stageFieldFamily_entry 4 i _).2 rfl, (run.limitActorInclusions_entry i _).2 rfl,
      (run.actorPresentation.inclusion_entry i a _).2 ⟨ha, rfl⟩,
      (run.actorPresentation.inclusion_entry i b _).2 ⟨hb, rfl⟩,
      (run.actorPresentation.inclusion_entry i c _).2 ⟨hc, rfl⟩, mul⟩

theorem limitInverse_entry (g h : ZFSet.{u}) :
    ZFSet.pair g h ∈ run.limitInverse ↔ run.LimitInv g h := by
  rw [limitInverse, pair_mem_indexedRelationLift]
  constructor
  · rintro ⟨_, _, j, hj, r, e, a, _, b, _, operation, inclusion, first, second, inverse⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hj
    have er : r = (run.diagram.stage i).stage.inverse := (run.stageFieldFamily_entry 5 i r).1 operation
    have ee := (run.limitActorInclusions_entry i e).1 inclusion
    subst r
    subst e
    obtain ⟨ha, eg⟩ := (run.actorPresentation.inclusion_entry i a g).1 first
    obtain ⟨hb, eh⟩ := (run.actorPresentation.inclusion_entry i b h).1 second
    exact ⟨i, a, b, ha, hb, eg, eh, inverse⟩
  · rintro ⟨i, a, b, ha, hb, rfl, rfl, inverse⟩
    exact ⟨run.actorPresentation.limitPoint_mem ha, run.actorPresentation.limitPoint_mem hb,
      run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩, (run.diagram.stage i).stage.inverse,
      run.limitActorMap i, a, run.actorPresentation.carrier_bound i ha,
      b, run.actorPresentation.carrier_bound i hb,
      (run.stageFieldFamily_entry 5 i _).2 rfl, (run.limitActorInclusions_entry i _).2 rfl,
      (run.actorPresentation.inclusion_entry i a _).2 ⟨ha, rfl⟩,
      (run.actorPresentation.inclusion_entry i b _).2 ⟨hb, rfl⟩, inverse⟩

theorem limitMultiplication_function :
    ZFSet.IsFunc (ZFSet.prod run.limitActors run.limitActors) run.limitActors run.limitMultiplication := by
  refine ⟨indexedBinaryLift_subset _ _ _ _ _, ?_⟩
  intro p hp
  obtain ⟨g, hg, h, hh, rfl⟩ := ZFSet.mem_prod.1 hp
  obtain ⟨k, _, product⟩ := run.limitMul_total hg hh
  refine ⟨k, (run.limitMultiplication_entry g h k).2 product, ?_⟩
  intro l entry
  exact run.limitMul_unique ((run.limitMultiplication_entry g h l).1 entry) product

theorem limitInverse_function : ZFSet.IsFunc run.limitActors run.limitActors run.limitInverse := by
  refine ⟨indexedRelationLift_subset _ _ _ _ _, ?_⟩
  intro g hg
  obtain ⟨h, _, inverse⟩ := run.limitInv_total hg
  refine ⟨h, (run.limitInverse_entry g h).2 inverse, ?_⟩
  intro k entry
  exact run.limitInv_unique ((run.limitInverse_entry g k).1 entry) inverse

theorem limitMultiplication_at (i : I) {a b c : ZFSet.{u}}
    (ha : a ∈ (run.diagram.stage i).stage.actors) (hb : b ∈ (run.diagram.stage i).stage.actors)
    (hc : c ∈ (run.diagram.stage i).stage.actors) :
    ZFSet.pair (ZFSet.pair (run.actorPresentation.limitPoint i a) (run.actorPresentation.limitPoint i b))
      (run.actorPresentation.limitPoint i c) ∈ run.limitMultiplication ↔
      ZFSet.pair (ZFSet.pair a b) c ∈ (run.diagram.stage i).stage.multiplication :=
  (run.limitMultiplication_entry _ _ _).trans (run.limitMul_at i ha hb hc)

theorem limitInverse_at (i : I) {a b : ZFSet.{u}}
    (ha : a ∈ (run.diagram.stage i).stage.actors) (hb : b ∈ (run.diagram.stage i).stage.actors) :
    ZFSet.pair (run.actorPresentation.limitPoint i a) (run.actorPresentation.limitPoint i b) ∈
      run.limitInverse ↔ ZFSet.pair a b ∈ (run.diagram.stage i).stage.inverse :=
  (run.limitInverse_entry _ _).trans (run.limitInv_at i ha hb)

end

open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitOrder_entry (p q : ZFSet.{u}) :
    ZFSet.pair p q ∈ run.limitOrder ↔ run.LimitLE p q := by
  rw [limitOrder, pair_mem_indexedRelationLift]
  constructor
  · rintro ⟨_, _, k, hk, r, e, x, _, y, _, relation, inclusion, first, second, lower⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hk
    have er : r = (run.diagram.stage i).stage.order := (run.stageFieldFamily_entry 1 i r).1 relation
    have ee := (run.limitPointInclusions_entry i e).1 inclusion
    subst r
    subst e
    obtain ⟨hx, ep⟩ := (run.pointPresentation.inclusion_entry i x p).1 first
    obtain ⟨hy, eq⟩ := (run.pointPresentation.inclusion_entry i y q).1 second
    exact ⟨i, x, y, hx, hy, ep, eq, lower⟩
  · rintro ⟨i, x, y, hx, hy, rfl, rfl, lower⟩
    exact ⟨run.pointPresentation.limitPoint_mem hx, run.pointPresentation.limitPoint_mem hy,
      run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩, (run.diagram.stage i).stage.order,
      run.limitPointMap i, x, run.pointPresentation.carrier_bound i hx,
      y, run.pointPresentation.carrier_bound i hy,
      (run.stageFieldFamily_entry 1 i _).2 rfl, (run.limitPointInclusions_entry i _).2 rfl,
      (run.pointPresentation.inclusion_entry i x _).2 ⟨hx, rfl⟩,
      (run.pointPresentation.inclusion_entry i y _).2 ⟨hy, rfl⟩, lower⟩

theorem limitMeetGraph_entry (p q v : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair p q) v ∈ run.limitMeetGraph ↔ run.LimitMeet p q v := by
  rw [limitMeetGraph, triple_mem_indexedBinaryLift]
  constructor
  · rintro ⟨_, _, _, k, hk, b, e, x, _, y, _, z, _, operation, inclusion, first, second, third, meet⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hk
    have eb : b = (run.diagram.stage i).stage.meetGraph := (run.stageFieldFamily_entry 2 i b).1 operation
    have ee := (run.limitPointInclusions_entry i e).1 inclusion
    subst b
    subst e
    obtain ⟨hx, ep⟩ := (run.pointPresentation.inclusion_entry i x p).1 first
    obtain ⟨hy, eq⟩ := (run.pointPresentation.inclusion_entry i y q).1 second
    obtain ⟨hz, ev⟩ := (run.pointPresentation.inclusion_entry i z v).1 third
    exact ⟨i, x, y, z, hx, hy, hz, ep, eq, ev, meet⟩
  · rintro ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl, meet⟩
    exact ⟨run.pointPresentation.limitPoint_mem hx, run.pointPresentation.limitPoint_mem hy,
      run.pointPresentation.limitPoint_mem hz, run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩,
      (run.diagram.stage i).stage.meetGraph, run.limitPointMap i,
      x, run.pointPresentation.carrier_bound i hx, y, run.pointPresentation.carrier_bound i hy,
      z, run.pointPresentation.carrier_bound i hz,
      (run.stageFieldFamily_entry 2 i _).2 rfl, (run.limitPointInclusions_entry i _).2 rfl,
      (run.pointPresentation.inclusion_entry i x _).2 ⟨hx, rfl⟩,
      (run.pointPresentation.inclusion_entry i y _).2 ⟨hy, rfl⟩,
      (run.pointPresentation.inclusion_entry i z _).2 ⟨hz, rfl⟩, meet⟩

theorem limitOrder_code : PartialOrderCode run.limitPoints run.limitOrder where
  relation := indexedRelationLift_subset _ _ _ _ _
  refl x hx := (run.limitOrder_entry x x).2 (run.limitLE_refl hx)
  antisymm x _ y _ first second := run.limitLE_antisymm
    ((run.limitOrder_entry x y).1 first) ((run.limitOrder_entry y x).1 second)
  trans x _ y _ z _ first second := (run.limitOrder_entry x z).2
    (run.limitLE_trans ((run.limitOrder_entry x y).1 first) ((run.limitOrder_entry y z).1 second))

theorem limitMeet_code : MeetOrderCode run.limitPoints run.limitOrder run.limitMeetGraph where
  order := run.limitOrder_code
  operation := by
    refine ⟨indexedBinaryLift_subset _ _ _ _ _, ?_⟩
    intro w hw
    obtain ⟨p, hp, q, hq, rfl⟩ := ZFSet.mem_prod.1 hw
    obtain ⟨v, _, meet⟩ := run.limitMeet_total hp hq
    refine ⟨v, (run.limitMeetGraph_entry p q v).2 meet, ?_⟩
    intro v' entry
    exact run.limitMeet_unique ((run.limitMeetGraph_entry p q v').1 entry) meet
  lower_left p q v entry := (run.limitOrder_entry v p).2
    (run.limitMeet_lower_left ((run.limitMeetGraph_entry p q v).1 entry))
  lower_right p q v entry := (run.limitOrder_entry v q).2
    (run.limitMeet_lower_right ((run.limitMeetGraph_entry p q v).1 entry))
  greatest p q v w _ entry first second := (run.limitOrder_entry w v).2
    (run.limitMeet_greatest ((run.limitMeetGraph_entry p q v).1 entry)
      ((run.limitOrder_entry w p).1 first) ((run.limitOrder_entry w q).1 second))

theorem limitPointMap_order_iff (i : I) (x y p q : ZFSet.{u})
    (first : ZFSet.pair x p ∈ run.limitPointMap i)
    (second : ZFSet.pair y q ∈ run.limitPointMap i) :
    ZFSet.pair p q ∈ run.limitOrder ↔ ZFSet.pair x y ∈ (run.diagram.stage i).stage.order := by
  obtain ⟨hx, rfl⟩ := (run.pointPresentation.inclusion_entry i x p).1 first
  obtain ⟨hy, rfl⟩ := (run.pointPresentation.inclusion_entry i y q).1 second
  exact (run.limitOrder_entry _ _).trans (run.limitLE_at i hx hy)

theorem limitPointMap_meetEmbedding (i : I) :
    MeetEmbeddingCode (run.diagram.stage i).stage.carrier run.limitPoints
      (run.diagram.stage i).stage.order run.limitOrder
      (run.diagram.stage i).stage.meetGraph run.limitMeetGraph (run.limitPointMap i) where
  injection := run.limitPointMap_injection i
  monotone x y p q lower first second := (run.limitPointMap_order_iff i x y p q first second).2 lower
  map_meet x y z p q v meet first second third := by
    obtain ⟨hx, rfl⟩ := (run.pointPresentation.inclusion_entry i x p).1 first
    obtain ⟨hy, rfl⟩ := (run.pointPresentation.inclusion_entry i y q).1 second
    obtain ⟨hz, rfl⟩ := (run.pointPresentation.inclusion_entry i z v).1 third
    exact (run.limitMeetGraph_entry _ _ _).2 ((run.limitMeet_at i hx hy hz).2 meet)

noncomputable def limitBottom (i : I) : ZFSet.{u} :=
  run.pointPresentation.limitPoint i (run.diagram.stage i).stage.bottom

theorem limitBottom_mem (i : I) : run.limitBottom i ∈ run.limitPoints :=
  run.pointPresentation.limitPoint_mem (run.diagram.stage i).stage.bottom_mem

theorem limitBottom_eq (i j : I) : run.limitBottom i = run.limitBottom j := by
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  exact (run.pointPresentation.limitPoint_transition ik (run.diagram.transition ik).map.bottom).trans
    (run.pointPresentation.limitPoint_transition jk (run.diagram.transition jk).map.bottom).symm

theorem limitBottom_least (i : I) (q : ZFSet.{u}) (member : q ∈ run.limitPoints) :
    ZFSet.pair (run.limitBottom i) q ∈ run.limitOrder := by
  obtain ⟨j, x, hx, rfl⟩ := run.pointPresentation.limitPoint_coverage member
  rw [run.limitBottom_eq i j]
  exact (run.limitOrder_entry _ _).2 ((run.limitLE_at j (run.diagram.stage j).stage.bottom_mem hx).2
    ((run.diagram.stage j).stage.least x hx))

theorem limitPointMap_bottom (i₀ i : I) :
    ZFSet.pair (run.diagram.stage i).stage.bottom (run.limitBottom i₀) ∈ run.limitPointMap i :=
  (run.pointPresentation.inclusion_entry i _ _).2
    ⟨(run.diagram.stage i).stage.bottom_mem, run.limitBottom_eq i₀ i⟩

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainPrefixLimitActionLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

def LimitAct (g p q : ZFSet.{u}) : Prop :=
  ∃ i a x y, a ∈ (run.diagram.stage i).stage.actors ∧
    x ∈ (run.diagram.stage i).stage.carrier ∧ y ∈ (run.diagram.stage i).stage.carrier ∧
    g = run.actorPresentation.limitPoint i a ∧ p = run.pointPresentation.limitPoint i x ∧
    q = run.pointPresentation.limitPoint i y ∧ ZFSet.pair (ZFSet.pair a x) y ∈ (run.diagram.stage i).stage.action

theorem limitAct_bounds {g p q : ZFSet.{u}} (act : run.LimitAct g p q) :
    g ∈ run.limitActors ∧ p ∈ run.limitPoints ∧ q ∈ run.limitPoints := by
  obtain ⟨i, a, x, y, ha, hx, hy, rfl, rfl, rfl, _⟩ := act
  exact ⟨run.actorPresentation.limitPoint_mem ha,
    run.pointPresentation.limitPoint_mem hx, run.pointPresentation.limitPoint_mem hy⟩

theorem limitAct_total {g p : ZFSet.{u}} (hg : g ∈ run.limitActors) (hp : p ∈ run.limitPoints) :
    ∃ q ∈ run.limitPoints, run.LimitAct g p q := by
  obtain ⟨i, a, x, ha, hx, rfl, rfl⟩ := run.actorPresentation.mixed_pair_coverage run.pointPresentation hg hp
  obtain ⟨y, entry, _⟩ := (run.diagram.stage i).stage.action_code.function.2
    (ZFSet.pair a x) (ZFSet.pair_mem_prod.2 ⟨ha, hx⟩)
  have hy := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.action_code.function.1 entry)).2
  exact ⟨run.pointPresentation.limitPoint i y, run.pointPresentation.limitPoint_mem hy,
    i, a, x, y, ha, hx, hy, rfl, rfl, rfl, entry⟩

theorem limitAct_unique {g p q r : ZFSet.{u}}
    (first : run.LimitAct g p q) (second : run.LimitAct g p r) : q = r := by
  obtain ⟨i, a, x, y, ha, hx, hy, rfl, rfl, rfl, act⟩ := first
  obtain ⟨j, b, u, v, hb, hu, hv, equalActor, equalPoint, rfl, act'⟩ := second
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  obtain ⟨a', aa⟩ := run.actorSystem.map_entry_total ik ha
  obtain ⟨b', bb⟩ := run.actorSystem.map_entry_total jk hb
  obtain ⟨x', xx⟩ := run.pointSystem.map_entry_total ik hx
  obtain ⟨u', uu⟩ := run.pointSystem.map_entry_total jk hu
  obtain ⟨y', yy⟩ := run.pointSystem.map_entry_total ik hy
  obtain ⟨v', vv⟩ := run.pointSystem.map_entry_total jk hv
  have actorEqual := (run.actorSystem.related_iff_common_images ik jk aa bb).1
    ((run.actorPresentation.limitPoint_eq_iff_related ha hb).1 equalActor)
  have pointEqual := (run.pointSystem.related_iff_common_images ik jk xx uu).1
    ((run.pointPresentation.limitPoint_eq_iff_related hx hu).1 equalPoint)
  subst b'
  subst u'
  have left := (run.diagram.transition ik).map.equivariant a a' x y x' y' aa xx yy act
  have right := (run.diagram.transition jk).map.equivariant b a' u v x' v' bb uu vv act'
  have function : FunctionGraphOn
      (ZFSet.prod (run.diagram.stage k).stage.actors (run.diagram.stage k).stage.carrier)
      (run.diagram.stage k).stage.action := ⟨_, (run.diagram.stage k).stage.action_code.function⟩
  have equal := function.unique left right
  exact (run.pointPresentation.limitPoint_transition ik yy).trans
    ((congrArg (run.pointPresentation.limitPoint k) equal).trans
      (run.pointPresentation.limitPoint_transition jk vv).symm)

theorem limitAct_at (i : I) {a x y : ZFSet.{u}}
    (ha : a ∈ (run.diagram.stage i).stage.actors)
    (hx : x ∈ (run.diagram.stage i).stage.carrier)
    (hy : y ∈ (run.diagram.stage i).stage.carrier) :
    run.LimitAct (run.actorPresentation.limitPoint i a)
      (run.pointPresentation.limitPoint i x) (run.pointPresentation.limitPoint i y) ↔
      ZFSet.pair (ZFSet.pair a x) y ∈ (run.diagram.stage i).stage.action := by
  constructor
  · intro act
    obtain ⟨z, entry, _⟩ := (run.diagram.stage i).stage.action_code.function.2
      (ZFSet.pair a x) (ZFSet.pair_mem_prod.2 ⟨ha, hx⟩)
    have hz := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.action_code.function.1 entry)).2
    have equal := (run.pointPresentation.limitPoint_same_iff hy hz).1
      (run.limitAct_unique act ⟨i, a, x, z, ha, hx, hz, rfl, rfl, rfl, entry⟩)
    subst z
    exact entry
  · intro entry
    exact ⟨i, a, x, y, ha, hx, hy, rfl, rfl, rfl, entry⟩

theorem limitAct_monotone {g p q r s : ZFSet.{u}}
    (first : run.LimitAct g p r) (second : run.LimitAct g q s) (lower : run.LimitLE p q) :
    run.LimitLE r s := by
  obtain ⟨i, a, x, y, ha, hx, hy, rfl, rfl, rfl⟩ :=
    run.actorPresentation.mixed_triple_coverage run.pointPresentation run.pointPresentation
      (run.limitAct_bounds first).1 (run.limitAct_bounds first).2.1 (run.limitAct_bounds second).2.1
  obtain ⟨z, left, _⟩ := (run.diagram.stage i).stage.action_code.function.2
    (ZFSet.pair a x) (ZFSet.pair_mem_prod.2 ⟨ha, hx⟩)
  obtain ⟨w, right, _⟩ := (run.diagram.stage i).stage.action_code.function.2
    (ZFSet.pair a y) (ZFSet.pair_mem_prod.2 ⟨ha, hy⟩)
  have hz := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.action_code.function.1 left)).2
  have hw := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.action_code.function.1 right)).2
  have er := run.limitAct_unique first ((run.limitAct_at i ha hx hz).2 left)
  have es := run.limitAct_unique second ((run.limitAct_at i ha hy hw).2 right)
  rw [er, es]
  exact (run.limitLE_at i hz hw).2 ((run.diagram.stage i).stage.action_code.monotone
    a ha x hx y hy z hz w hw left right ((run.limitLE_at i hx hy).1 lower))

theorem limitAction_ground : run.limitAction ∈ M.sets :=
  M.indexedMixedBinaryLift_mem pairing unions powers separation run.indices_ground
    run.actorUnion_ground run.carrierUnion_ground run.limitActors_ground run.limitPoints_ground
    (run.stageFieldFamily_ground 7) run.limitActorInclusions_ground run.limitPointInclusions_ground

theorem limitAction_entry (g p q : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g p) q ∈ run.limitAction ↔ run.LimitAct g p q := by
  rw [limitAction, triple_mem_indexedMixedBinaryLift]
  constructor
  · rintro ⟨_, _, _, k, hk, a, eG, eP, u, _, x, _, y, _,
      action, actors, points, actor, first, second, source⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hk
    have ea : a = (run.diagram.stage i).stage.action := (run.stageFieldFamily_entry 7 i a).1 action
    have eg := (run.limitActorInclusions_entry i eG).1 actors
    have ep := (run.limitPointInclusions_entry i eP).1 points
    subst a
    subst eG
    subst eP
    obtain ⟨hu, equalG⟩ := (run.actorPresentation.inclusion_entry i u g).1 actor
    obtain ⟨hx, equalP⟩ := (run.pointPresentation.inclusion_entry i x p).1 first
    obtain ⟨hy, equalQ⟩ := (run.pointPresentation.inclusion_entry i y q).1 second
    exact ⟨i, u, x, y, hu, hx, hy, equalG, equalP, equalQ, source⟩
  · rintro ⟨i, u, x, y, hu, hx, hy, rfl, rfl, rfl, source⟩
    exact ⟨run.actorPresentation.limitPoint_mem hu, run.pointPresentation.limitPoint_mem hx,
      run.pointPresentation.limitPoint_mem hy, run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩,
      (run.diagram.stage i).stage.action, run.limitActorMap i, run.limitPointMap i,
      u, run.actorPresentation.carrier_bound i hu, x, run.pointPresentation.carrier_bound i hx,
      y, run.pointPresentation.carrier_bound i hy,
      (run.stageFieldFamily_entry 7 i _).2 rfl, (run.limitActorInclusions_entry i _).2 rfl,
      (run.limitPointInclusions_entry i _).2 rfl,
      (run.actorPresentation.inclusion_entry i u _).2 ⟨hu, rfl⟩,
      (run.pointPresentation.inclusion_entry i x _).2 ⟨hx, rfl⟩,
      (run.pointPresentation.inclusion_entry i y _).2 ⟨hy, rfl⟩, source⟩

theorem limitAction_function :
    ZFSet.IsFunc (ZFSet.prod run.limitActors run.limitPoints) run.limitPoints run.limitAction := by
  refine ⟨indexedMixedBinaryLift_subset _ _ _ _ _ _ _ _, ?_⟩
  intro w hw
  obtain ⟨g, hg, p, hp, rfl⟩ := ZFSet.mem_prod.1 hw
  obtain ⟨q, _, action⟩ := run.limitAct_total hg hp
  refine ⟨q, (run.limitAction_entry g p q).2 action, ?_⟩
  intro q' entry
  exact run.limitAct_unique ((run.limitAction_entry g p q').1 entry) action

theorem limitAction_at (i : I) {a x y : ZFSet.{u}}
    (ha : a ∈ (run.diagram.stage i).stage.actors)
    (hx : x ∈ (run.diagram.stage i).stage.carrier)
    (hy : y ∈ (run.diagram.stage i).stage.carrier) :
    ZFSet.pair (ZFSet.pair (run.actorPresentation.limitPoint i a)
      (run.pointPresentation.limitPoint i x)) (run.pointPresentation.limitPoint i y) ∈ run.limitAction ↔
      ZFSet.pair (ZFSet.pair a x) y ∈ (run.diagram.stage i).stage.action :=
  (run.limitAction_entry _ _ _).trans (run.limitAct_at i ha hx hy)

theorem limitMaps_action_iff (i : I) (a g x y p q : ZFSet.{u})
    (actor : ZFSet.pair a g ∈ run.limitActorMap i)
    (first : ZFSet.pair x p ∈ run.limitPointMap i)
    (second : ZFSet.pair y q ∈ run.limitPointMap i) :
    ZFSet.pair (ZFSet.pair g p) q ∈ run.limitAction ↔
      ZFSet.pair (ZFSet.pair a x) y ∈ (run.diagram.stage i).stage.action := by
  obtain ⟨ha, rfl⟩ := (run.actorPresentation.inclusion_entry i a g).1 actor
  obtain ⟨hx, rfl⟩ := (run.pointPresentation.inclusion_entry i x p).1 first
  obtain ⟨hy, rfl⟩ := (run.pointPresentation.inclusion_entry i y q).1 second
  exact run.limitAction_at i ha hx hy

theorem limitMaps_equivariant (i : I) (a g x y p q : ZFSet.{u})
    (actor : ZFSet.pair a g ∈ run.limitActorMap i)
    (first : ZFSet.pair x p ∈ run.limitPointMap i)
    (second : ZFSet.pair y q ∈ run.limitPointMap i)
    (action : ZFSet.pair (ZFSet.pair a x) y ∈ (run.diagram.stage i).stage.action) :
    ZFSet.pair (ZFSet.pair g p) q ∈ run.limitAction :=
  (run.limitMaps_action_iff i a g x y p q actor first second).2 action

theorem limitMaps_agreement (i : I) (g h g' h' v v' : ZFSet.{u})
    (first : ZFSet.pair g g' ∈ run.limitActorMap i)
    (second : ZFSet.pair h h' ∈ run.limitActorMap i)
    (point : ZFSet.pair v v' ∈ run.limitPointMap i)
    (agree : ActionAgreementBelow (run.diagram.stage i).stage.carrier
      (run.diagram.stage i).stage.order (run.diagram.stage i).stage.action g h v) :
    ActionAgreementBelow run.limitPoints run.limitOrder run.limitAction g' h' v' := by
  obtain ⟨hg, rfl⟩ := (run.actorPresentation.inclusion_entry i g g').1 first
  obtain ⟨hh, rfl⟩ := (run.actorPresentation.inclusion_entry i h h').1 second
  obtain ⟨hv, rfl⟩ := (run.pointPresentation.inclusion_entry i v v').1 point
  intro x hx y hy lower
  obtain ⟨j, a, b, ha, hb, rfl, rfl⟩ := run.pointPresentation.pair_coverage hx hy
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  obtain ⟨G, gG⟩ := run.actorSystem.map_entry_total ik hg
  obtain ⟨H, hH⟩ := run.actorSystem.map_entry_total ik hh
  obtain ⟨V, vV⟩ := run.pointSystem.map_entry_total ik hv
  obtain ⟨A, aA⟩ := run.pointSystem.map_entry_total jk ha
  obtain ⟨B, bB⟩ := run.pointSystem.map_entry_total jk hb
  have hG := (run.actorSystem.map_entry_bounds ik gG).2
  have Hmem := (run.actorSystem.map_entry_bounds ik hH).2
  have hV := (run.pointSystem.map_entry_bounds ik vV).2
  have hA := (run.pointSystem.map_entry_bounds jk aA).2
  have hB := (run.pointSystem.map_entry_bounds jk bB).2
  have equalA := run.pointPresentation.limitPoint_transition jk aA
  have equalV := run.pointPresentation.limitPoint_transition ik vV
  rw [equalA, equalV] at lower
  have sourceLower := (run.limitLE_at k hA hV).1 ((run.limitOrder_entry _ _).1 lower)
  have later := (run.diagram.transition ik).map.agreement g h G H v V gG hH vV agree
  rw [run.actorPresentation.limitPoint_transition ik gG,
    run.actorPresentation.limitPoint_transition ik hH,
    equalA, run.pointPresentation.limitPoint_transition jk bB]
  exact (run.limitAction_at k hG hA hB).trans
    ((later A hA B hB sourceLower).trans (run.limitAction_at k Hmem hA hB).symm)

theorem limitAct_mul {g h k p q r : ZFSet.{u}}
    (product : run.LimitMul g h k) (first : run.LimitAct h p q) (second : run.LimitAct g q r) :
    run.LimitAct k p r := by
  obtain ⟨i, a, b, x, ha, hb, hx, rfl, rfl, rfl⟩ :=
    run.actorPresentation.mixed_triple_coverage run.actorPresentation run.pointPresentation
      (run.limitMul_bounds product).1 (run.limitMul_bounds product).2.1 (run.limitAct_bounds first).2.1
  obtain ⟨c, mul, _⟩ := (run.diagram.stage i).stage.group_code.mul_function.2
    (ZFSet.pair a b) (ZFSet.pair_mem_prod.2 ⟨ha, hb⟩)
  have hc := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.mul_function.1 mul)).2
  obtain ⟨y, left, _⟩ := (run.diagram.stage i).stage.action_code.function.2
    (ZFSet.pair b x) (ZFSet.pair_mem_prod.2 ⟨hb, hx⟩)
  have hy := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.action_code.function.1 left)).2
  obtain ⟨z, right, _⟩ := (run.diagram.stage i).stage.action_code.function.2
    (ZFSet.pair a y) (ZFSet.pair_mem_prod.2 ⟨ha, hy⟩)
  have hz := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.action_code.function.1 right)).2
  have ek := run.limitMul_unique product ((run.limitMul_at i ha hb hc).2 mul)
  have eq := run.limitAct_unique first ((run.limitAct_at i hb hx hy).2 left)
  rw [eq] at second
  have er := run.limitAct_unique second ((run.limitAct_at i ha hy hz).2 right)
  rw [ek, er]
  exact (run.limitAct_at i hc hx hz).2
    ((run.diagram.stage i).stage.action_code.mul a ha b hb c hc x hx y hy z hz mul left right)

theorem limitAction_one (i₀ : I) (p : ZFSet.{u}) (hp : p ∈ run.limitPoints) :
    ZFSet.pair (ZFSet.pair (run.limitIdentity i₀) p) p ∈ run.limitAction := by
  obtain ⟨i, x, hx, rfl⟩ := run.pointPresentation.limitPoint_coverage hp
  rw [run.limitIdentity_eq i₀ i]
  exact (run.limitAction_at i (run.diagram.stage i).stage.group_code.identity_mem hx hx).2
    ((run.diagram.stage i).stage.action_code.one x hx)

theorem limitAction_code (i₀ : I) :
    PosetActionCode run.limitActors run.limitPoints run.limitMultiplication
      (run.limitIdentity i₀) run.limitOrder run.limitAction where
  function := run.limitAction_function
  one := run.limitAction_one i₀
  mul g _ h _ k _ p _ q _ r _ product first second :=
    (run.limitAction_entry k p r).2 (run.limitAct_mul
      ((run.limitMultiplication_entry g h k).1 product)
      ((run.limitAction_entry h p q).1 first) ((run.limitAction_entry g q r).1 second))
  monotone g _ p _ q _ r _ s _ first second lower :=
    (run.limitOrder_entry r s).2 (run.limitAct_monotone
      ((run.limitAction_entry g p r).1 first) ((run.limitAction_entry g q s).1 second)
      ((run.limitOrder_entry p q).1 lower))

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixPriorFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitPriorFields_values (i : I) (j : Fin 5) {s : ZFSet.{u}}
    (time : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) :
    run.limitPriorFields.value j s = (run.diagram.stage i).history.fieldValue j s :=
  run.limitPriorFields.value_eq_of_entry j ((run.serialFieldUnion_at i j time _).2 rfl)

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitChronologyCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem related_birth_iff {i j : I} {x y : ZFSet.{u}}
    (related : run.pointSystem.Related i x j y) (t : ZFSet.{u}) :
    ZFSet.pair x t ∈ (run.diagram.stage i).birth ↔
      ZFSet.pair y t ∈ (run.diagram.stage j).birth := by
  obtain ⟨k, first, second, z, xz, yz⟩ := related
  exact ((run.diagram.transition first).birth x z t xz).symm.trans
    ((run.diagram.transition second).birth y z t yz)

theorem limitPoint_birth_iff {i j : I} {x y : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier)
    (hy : y ∈ (run.diagram.stage j).stage.carrier)
    (equal : run.pointPresentation.limitPoint i x = run.pointPresentation.limitPoint j y)
    (t : ZFSet.{u}) :
    ZFSet.pair x t ∈ (run.diagram.stage i).birth ↔
      ZFSet.pair y t ∈ (run.diagram.stage j).birth :=
  run.related_birth_iff ((run.pointPresentation.limitPoint_eq_iff_related hx hy).1 equal) t

theorem related_height_iff {i j : I} {x y : ZFSet.{u}}
    (related : run.pointSystem.Related i x j y) (t : ZFSet.{u}) :
    ZFSet.pair x t ∈ (run.diagram.stage i).stage.height ↔
      ZFSet.pair y t ∈ (run.diagram.stage j).stage.height := by
  obtain ⟨k, first, second, z, xz, yz⟩ := related
  exact ((run.diagram.transition first).map.height x z t xz).symm.trans
    ((run.diagram.transition second).map.height y z t yz)

theorem limitPoint_height_iff {i j : I} {x y : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier)
    (hy : y ∈ (run.diagram.stage j).stage.carrier)
    (equal : run.pointPresentation.limitPoint i x = run.pointPresentation.limitPoint j y)
    (t : ZFSet.{u}) :
    ZFSet.pair x t ∈ (run.diagram.stage i).stage.height ↔
      ZFSet.pair y t ∈ (run.diagram.stage j).stage.height :=
  run.related_height_iff ((run.pointPresentation.limitPoint_eq_iff_related hx hy).1 equal) t





theorem limitValueGraph_entry (value : I → ZFSet.{u}) {F V : ZFSet.{u}}
    (lookup : ∀ i f, ZFSet.pair (run.key i) f ∈ F ↔ f = value i)
    (bound : ∀ i x t, ZFSet.pair x t ∈ value i → t ∈ V) (q t : ZFSet.{u}) :
    ZFSet.pair q t ∈ run.limitValueGraph F V ↔
      ∃ i x, x ∈ (run.diagram.stage i).stage.carrier ∧
        q = run.pointPresentation.limitPoint i x ∧ ZFSet.pair x t ∈ value i := by
  rw [limitValueGraph, pair_mem_indexedValueLift]
  constructor
  · rintro ⟨_, _, k, hk, f, e, x, _, family, inclusion, image, entry⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hk
    obtain rfl := (lookup i f).1 family
    obtain rfl := (run.limitPointInclusions_entry i e).1 inclusion
    obtain ⟨hx, equal⟩ := (run.pointPresentation.inclusion_entry i x q).1 image
    exact ⟨i, x, hx, equal, entry⟩
  · rintro ⟨i, x, hx, rfl, entry⟩
    exact ⟨run.pointPresentation.limitPoint_mem hx, bound i x t entry,
      run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩, value i, run.limitPointMap i,
      x, run.pointPresentation.carrier_bound i hx, (lookup i _).2 rfl,
      (run.limitPointInclusions_entry i _).2 rfl,
      (run.pointPresentation.inclusion_entry i x _).2 ⟨hx, rfl⟩, entry⟩

theorem limitValueGraph_at (value : I → ZFSet.{u}) {F V : ZFSet.{u}}
    (lookup : ∀ i f, ZFSet.pair (run.key i) f ∈ F ↔ f = value i)
    (bound : ∀ i x t, ZFSet.pair x t ∈ value i → t ∈ V)
    (compatible : ∀ i j x y, x ∈ (run.diagram.stage i).stage.carrier →
      y ∈ (run.diagram.stage j).stage.carrier →
      run.pointPresentation.limitPoint i x = run.pointPresentation.limitPoint j y →
      ∀ t, ZFSet.pair x t ∈ value i ↔ ZFSet.pair y t ∈ value j)
    (i : I) {x : ZFSet.{u}} (hx : x ∈ (run.diagram.stage i).stage.carrier) (t : ZFSet.{u}) :
    ZFSet.pair (run.pointPresentation.limitPoint i x) t ∈ run.limitValueGraph F V ↔
      ZFSet.pair x t ∈ value i := by
  rw [run.limitValueGraph_entry value lookup bound]
  constructor
  · rintro ⟨j, y, hy, equal, entry⟩
    exact (compatible i j x y hx hy equal t).2 entry
  · intro entry
    exact ⟨i, x, hx, rfl, entry⟩





theorem limitPoint_old_birth_coverage (i j : I) {x t : ZFSet.{u}}
    (entry : ZFSet.pair x t ∈ (run.diagram.stage j).birth)
    (before : t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff) :
    ∃ y ∈ (run.diagram.stage i).stage.carrier,
      ZFSet.pair y t ∈ (run.diagram.stage i).birth ∧
      run.pointPresentation.limitPoint i y = run.pointPresentation.limitPoint j x := by
  have hx := (ZFSet.pair_mem_prod.1 ((run.diagram.stage j).birth_function.1 entry)).1
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  obtain ⟨z, xz⟩ := run.pointSystem.map_entry_total jk hx
  have terminal := ((run.diagram.transition jk).birth x z t xz).2 entry
  obtain ⟨y, hy, yz⟩ := run.coverage ik z t terminal before
  exact ⟨y, hy, ((run.diagram.transition ik).birth y z t yz).1 terminal,
    (run.pointPresentation.limitPoint_transition ik yz).trans
      (run.pointPresentation.limitPoint_transition jk xz).symm⟩

def LimitBirthValue (q t : ZFSet.{u}) : Prop :=
  ∃ i x, x ∈ (run.diagram.stage i).stage.carrier ∧
    q = run.pointPresentation.limitPoint i x ∧ ZFSet.pair x t ∈ (run.diagram.stage i).birth

theorem limitBirthValue_at (i : I) {x : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier) (t : ZFSet.{u}) :
    run.LimitBirthValue (run.pointPresentation.limitPoint i x) t ↔
      ZFSet.pair x t ∈ (run.diagram.stage i).birth := by
  constructor
  · rintro ⟨j, y, hy, equal, entry⟩
    exact (run.limitPoint_birth_iff hx hy equal t).2 entry
  · intro entry
    exact ⟨i, x, hx, rfl, entry⟩

theorem limitBirthValue_total {q : ZFSet.{u}} (member : q ∈ run.limitPoints) :
    ∃ t, run.LimitBirthValue q t := by
  obtain ⟨i, x, hx, rfl⟩ := run.pointPresentation.limitPoint_coverage member
  obtain ⟨t, entry, _⟩ := (run.diagram.stage i).birth_function.2 x hx
  exact ⟨t, i, x, hx, rfl, entry⟩

theorem limitBirthValue_unique {q t s : ZFSet.{u}}
    (first : run.LimitBirthValue q t) (second : run.LimitBirthValue q s) : t = s := by
  obtain ⟨i, x, hx, rfl, xt⟩ := first
  have xs := (run.limitBirthValue_at i hx s).1 second
  exact (show FunctionGraphOn (run.diagram.stage i).stage.carrier (run.diagram.stage i).birth from
    ⟨_, (run.diagram.stage i).birth_function⟩).unique xt xs

theorem limitBirthValue_old_fiber (i : I) (q t : ZFSet.{u})
    (before : t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff) :
    run.LimitBirthValue q t ↔ ∃ x ∈ (run.diagram.stage i).stage.carrier,
      ZFSet.pair x t ∈ (run.diagram.stage i).birth ∧ q = run.pointPresentation.limitPoint i x := by
  constructor
  · rintro ⟨j, y, _, rfl, entry⟩
    obtain ⟨x, hx, birth, equal⟩ := run.limitPoint_old_birth_coverage i j entry before
    exact ⟨x, hx, birth, equal.symm⟩
  · rintro ⟨x, hx, birth, rfl⟩
    exact ⟨i, x, hx, rfl, birth⟩





theorem height_value_mem_bound (i : I) {x t : ZFSet.{u}}
    (entry : ZFSet.pair x t ∈ (run.diagram.stage i).stage.height) : t ∈ run.heightValueBound :=
  pair_second_mem_doubleUnion ((run.stageFieldUnion_mem 10 _).2 ⟨i, entry⟩)

theorem limitHeight_entry (q t : ZFSet.{u}) :
    ZFSet.pair q t ∈ run.limitHeight ↔
      ∃ i x, x ∈ (run.diagram.stage i).stage.carrier ∧
        q = run.pointPresentation.limitPoint i x ∧ ZFSet.pair x t ∈ (run.diagram.stage i).stage.height :=
  run.limitValueGraph_entry (fun i => (run.diagram.stage i).stage.height)
    (run.stageFieldFamily_entry 10) (fun i _ _ => run.height_value_mem_bound i) q t

theorem limitHeight_at (i : I) {x : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier) (t : ZFSet.{u}) :
    ZFSet.pair (run.pointPresentation.limitPoint i x) t ∈ run.limitHeight ↔
      ZFSet.pair x t ∈ (run.diagram.stage i).stage.height :=
  run.limitValueGraph_at (fun j => (run.diagram.stage j).stage.height)
    (run.stageFieldFamily_entry 10) (fun j _ _ => run.height_value_mem_bound j)
    (fun _ _ _ _ hx hy equal t => run.limitPoint_height_iff hx hy equal t) i hx t

theorem limitHeight_function : ZFSet.IsFunc run.limitPoints (ZFSet.prod C D) run.limitHeight := by
  refine ⟨?_, ?_⟩
  · intro z hz
    have subset := indexedValueLift_subset run.indices run.carrierUnion run.limitPoints
      run.heightValueBound (run.stageFieldFamily 10) run.limitPointInclusions
    obtain ⟨q, _, t, _, rfl⟩ := ZFSet.mem_prod.1 (subset hz)
    obtain ⟨i, x, hx, rfl, entry⟩ := (run.limitHeight_entry q t).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨run.pointPresentation.limitPoint_mem hx,
      (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.height_code.function.1 entry)).2⟩
  · intro q hq
    obtain ⟨i, x, hx, rfl⟩ := run.pointPresentation.limitPoint_coverage hq
    obtain ⟨t, entry, unique⟩ := (run.diagram.stage i).stage.height_code.function.2 x hx
    refine ⟨t, (run.limitHeight_at i hx t).2 entry, ?_⟩
    intro s hs
    exact unique s ((run.limitHeight_at i hx s).1 hs)

theorem limitPointMap_height (i : I) {x q : ZFSet.{u}}
    (image : ZFSet.pair x q ∈ run.limitPointMap i) (t : ZFSet.{u}) :
    ZFSet.pair q t ∈ run.limitHeight ↔ ZFSet.pair x t ∈ (run.diagram.stage i).stage.height := by
  obtain ⟨hx, rfl⟩ := (run.pointPresentation.inclusion_entry i x q).1 image
  exact run.limitHeight_at i hx t

theorem limitBirth_entry (q t : ZFSet.{u}) :
    ZFSet.pair q t ∈ run.limitBirth ↔ run.LimitBirthValue q t :=
  run.limitValueGraph_entry (fun i => (run.diagram.stage i).birth) run.birthFamily_entry
    (fun i _ _ entry => run.birth_time_mem_cutoffLimit i entry) q t

theorem limitBirth_function : ZFSet.IsFunc run.limitPoints run.cutoffLimit run.limitBirth := by
  refine ⟨indexedValueLift_subset run.indices run.carrierUnion run.limitPoints
    run.cutoffLimit run.birthFamily run.limitPointInclusions, ?_⟩
  intro q hq
  obtain ⟨t, birth⟩ := run.limitBirthValue_total hq
  refine ⟨t, (run.limitBirth_entry q t).2 birth, ?_⟩
  intro s entry
  exact run.limitBirthValue_unique ((run.limitBirth_entry q s).1 entry) birth

theorem limitBirth_at (i : I) {x : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier) (t : ZFSet.{u}) :
    ZFSet.pair (run.pointPresentation.limitPoint i x) t ∈ run.limitBirth ↔
      ZFSet.pair x t ∈ (run.diagram.stage i).birth :=
  (run.limitBirth_entry _ t).trans (run.limitBirthValue_at i hx t)

theorem limitPointMap_birth_iff (i : I) (x q t : ZFSet.{u})
    (entry : ZFSet.pair x q ∈ run.limitPointMap i) :
    ZFSet.pair q t ∈ run.limitBirth ↔ ZFSet.pair x t ∈ (run.diagram.stage i).birth := by
  obtain ⟨hx, rfl⟩ := (run.pointPresentation.inclusion_entry i x q).1 entry
  exact run.limitBirth_at i hx t

theorem limitBirth_old_fiber (i : I) (q t : ZFSet.{u})
    (before : t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff) :
    ZFSet.pair q t ∈ run.limitBirth ↔ ∃ x ∈ (run.diagram.stage i).stage.carrier,
      ZFSet.pair x t ∈ (run.diagram.stage i).birth ∧ ZFSet.pair x q ∈ run.limitPointMap i := by
  rw [run.limitBirth_entry, run.limitBirthValue_old_fiber i q t before]
  constructor
  · rintro ⟨x, hx, birth, equal⟩
    exact ⟨x, hx, birth, (run.pointPresentation.inclusion_entry i x q).2 ⟨hx, equal⟩⟩
  · rintro ⟨x, hx, birth, entry⟩
    exact ⟨x, hx, birth, ((run.pointPresentation.inclusion_entry i x q).1 entry).2⟩





theorem limitHeight_code : StrictLexHeightCode run.limitPoints C D run.limitOrder run.limitHeight rD where
  function := run.limitHeight_function
  strict p hp q hq c a d b lower different first second := by
    obtain ⟨i, x, y, hx, hy, rfl, rfl⟩ := run.pointPresentation.pair_coverage hp hq
    have sourceOrder := (run.limitLE_at i hx hy).1 ((run.limitOrder_entry _ _).1 lower)
    have sourceDifferent : x ≠ y := fun equal => different (congrArg (run.pointPresentation.limitPoint i) equal)
    exact (run.diagram.stage i).stage.height_code.strict x hx y hy c a d b sourceOrder sourceDifferent
      ((run.limitHeight_at i hx _).1 first) ((run.limitHeight_at i hy _).1 second)

noncomputable def limitHeightRange : ZFSet.{u} := functionGraphRange run.limitPoints run.limitHeight





theorem limit_old_meet : OldMeetCode run.limitOrder run.limitMeetGraph run.limitBirth := by
  intro p q v a b c bornQ bornP earlier notLower meet bornV
  have bounds := run.limitMeet_bounds ((run.limitMeetGraph_entry p q v).1 meet)
  obtain ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl⟩ :=
    run.pointPresentation.triple_coverage bounds.1 bounds.2.1 bounds.2.2
  apply (run.diagram.stage i).old_meet x y z a b c
    ((run.limitBirth_at i hy a).1 bornQ) ((run.limitBirth_at i hx b).1 bornP) earlier
  · intro lower
    exact notLower ((run.limitOrder_entry _ _).2 ((run.limitLE_at i hx hy).2 lower))
  · exact (run.limitMeet_at i hx hy hz).1 ((run.limitMeetGraph_entry _ _ _).1 meet)
  · exact (run.limitBirth_at i hz c).1 bornV





theorem limitChronologyFields_values (i : I) (j : Fin 5) {s : ZFSet.{u}}
    (before : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) :
    run.limitChronologyFields.value j s = (run.diagram.stage i).history.fieldValue j s :=
  (run.limitPriorFields.appendTime_value_old pairing unions run.limitTerminalFields run.limitTerminalFields_ground
    j ((run.cutoffLimit_mem s).2 ⟨i, before⟩)).trans (run.limitPriorFields_values i j before)

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixPreservedSeeds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {I : Type v} [Small.{u} I] [Preorder I] [Finite I]

attribute [local instance] OAI.PartitionPilot.Forcing.GroundMainPrefix.instFiniteMainTransitionIndex
noncomputable def ofFinite (key : I → ZFSet.{u}) (injective : Function.Injective key)
    (order : ∀ i j, i ≤ j ↔ key i = key j ∨ key i ∈ key j)
    (ground : ZFSet.range key ∈ M.sets) (ordinal : ordinalSetProperty (ZFSet.range key))
    (diagram : GroundChronologicalMainDiagram M C D rD pairing unions powers separation I)
    (linked : I → GroundLinkedMainStage M K Labels C D rD)
    (same : ∀ i, (linked i).main = diagram.stage i) (coverage : diagram.CoversOldBirths) :
    GroundMainPrefix M K Labels C D rD pairing unions powers separation I where
  key := key
  key_injective := injective
  key_order := order
  indices_ground := ground
  indices_ordinal := ordinal
  diagram := diagram
  linked := linked
  linked_main := same
  coverage := coverage
  stages_ground := familyCodeGraph_finite_ground pairing unions ⟨_, ground⟩ key _
    (fun i => M.transitive ground (ZFSet.mem_range.2 ⟨i, rfl⟩))
    (fun i => (linked i).code_ground pairing)
  transitions_ground := familyCodeGraph_finite_ground pairing unions ⟨_, ground⟩ _ _
    (fun p => M.orderedPair_mem pairing
      (M.transitive ground (ZFSet.mem_range.2 ⟨p.val.2, rfl⟩))
      (M.transitive ground (ZFSet.mem_range.2 ⟨p.val.1, rfl⟩)))
    (fun p => (diagram.transition p.property).map.code_mem pairing)

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (first second : GroundLinkedMainStage M K Labels C D rD)
variable (step : GroundChronologicalMainTransition first.main second.main)
variable (coverage : step.CoversOldBirths)

noncomputable def twoStage :
    GroundMainPrefix M K Labels C D rD pairing unions powers separation (Fin 2) := by
  have empty : (∅ : ZFSet.{u}) ∈ M.sets :=
    M.empty_mem ⟨first.main.cutoff, first.main.cutoff_ground⟩
  have one := M.insert_mem pairing unions empty empty
  have two := M.insert_mem pairing unions one one
  have ground : ZFSet.range (@finiteMainIndexKey.{u} 2) ∈ M.sets := by
    simpa only [finiteMainIndexKey_range, natSetCode_succ, natSetCode_zero] using two
  have ordinal : ordinalSetProperty (ZFSet.range (@finiteMainIndexKey.{u} 2)) := by
    rw [finiteMainIndexKey_range]
    exact ordinalSetProperty_succ (ordinalSetProperty_succ ordinalSetProperty_empty)
  apply ofFinite pairing unions powers separation finiteMainIndexKey
    (finiteMainIndexKey_injective 2) finiteMainIndexKey_order ground ordinal
    (GroundChronologicalMainDiagram.twoStage pairing unions powers separation step)
    (Fin.cases first (fun _ => second))
  · intro i
    cases i using Fin.cases <;> rfl
  · exact GroundChronologicalMainDiagram.twoStage_coversOldBirths
      pairing unions powers separation step coverage

end PartitionPilot.Forcing.GroundMainPrefix



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LinkedProfileTransitionRawCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

def LinkedProfilePreservingTransitionRawCode (M : TransitiveGround.{u})
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth Families : ZFSet.{u})
    (source target : Fin 24 → ZFSet.{u}) : Prop :=
  LinkedMainTransitionRawCode M K Labels C D rD N sourceCode targetCode z points actors
    sourceBirth targetBirth source target ∧
  Families = M.groundPower (source 0) ∧
  OldProfilePreservationCode (source 0) (source 1) (source 2)
    (target 0) (target 1) (target 2) points Families

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_MainPrefixHistoryUnionRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
universe u v

structure MainPrefixGraphFamily (M : TransitiveGround.{u})
    (K Labels C D rD : ZFSet.{u}) (I : Type v) where
  indices : I → ZFSet.{u}
  stages : I → ZFSet.{u}
  transitions : I → ZFSet.{u}
  valid : ∀ i, MainPrefixGraphCode M K Labels C D rD (indices i) (stages i) (transitions i)
  mono : ∀ i j, indices i ⊆ indices j → stages i ⊆ stages j ∧ transitions i ⊆ transitions j

namespace MainPrefixGraphFamily
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {I : Type v} [Small.{u} I]
variable (family : MainPrefixGraphFamily M K Labels C D rD I)

noncomputable def indexUnion : ZFSet.{u} := ⋃₀ ZFSet.range family.indices
noncomputable def stageUnion : ZFSet.{u} := ⋃₀ ZFSet.range family.stages
noncomputable def transitionUnion : ZFSet.{u} := ⋃₀ ZFSet.range family.transitions

noncomputable def code (i : I) : ZFSet.{u} :=
  mainPrefixCode (family.indices i) (family.stages i) (family.transitions i)

noncomputable def unionCode : ZFSet.{u} :=
  mainPrefixCode family.indexUnion family.stageUnion family.transitionUnion

end MainPrefixGraphFamily

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u

structure PreservedMainPrefixHistoryCode (M : TransitiveGround.{u})
    (K Labels C D rD A p : ZFSet.{u}) : Prop where
  function : FunctionGraphOn A p
  values : ∀ i q, ZFSet.pair i q ∈ p →
    ∃ S E, q = mainPrefixCode (insert i i) S E ∧
      MainPrefixGraphCode M K Labels C D rD (insert i i) S E ∧
      MainPrefixProfileGraphCode M K Labels C D rD S E
  compatible : ∀ i j q r, ZFSet.pair i q ∈ p → ZFSet.pair j r ∈ p →
    (i = j ∨ i ∈ j) → MainPrefixExtends q r

namespace PreservedMainPrefixHistoryCode
variable {M : TransitiveGround.{u}} {K Labels C D rD A p : ZFSet.{u}}
variable (history : PreservedMainPrefixHistoryCode M K Labels C D rD A p)

theorem exists_fields (i : SetMembers A) :
    ∃ fields : ZFSet.{u} × ZFSet.{u},
      decodedFamilyValue history.function i = mainPrefixCode (insert (SetMembers.raw i) (SetMembers.raw i))
        fields.1 fields.2 ∧
      MainPrefixGraphCode M K Labels C D rD (insert (SetMembers.raw i) (SetMembers.raw i)) fields.1 fields.2 ∧
      MainPrefixProfileGraphCode M K Labels C D rD fields.1 fields.2 := by
  obtain ⟨S, E, equal, valid, profiles⟩ := history.values _ _
    (decodedFamilyValue_entry history.function i)
  exact ⟨(S, E), equal, valid, profiles⟩

noncomputable def fields (i : SetMembers A) : ZFSet.{u} × ZFSet.{u} :=
  Classical.choose (history.exists_fields i)

theorem fields_spec (i : SetMembers A) :
    decodedFamilyValue history.function i = mainPrefixCode (insert (SetMembers.raw i) (SetMembers.raw i))
      (history.fields i).1 (history.fields i).2 ∧
    MainPrefixGraphCode M K Labels C D rD (insert (SetMembers.raw i) (SetMembers.raw i))
      (history.fields i).1 (history.fields i).2 ∧
    MainPrefixProfileGraphCode M K Labels C D rD (history.fields i).1 (history.fields i).2 :=
  Classical.choose_spec (history.exists_fields i)

noncomputable def graphFamily : MainPrefixGraphFamily M K Labels C D rD (SetMembers A) where
  indices i := insert (SetMembers.raw i) (SetMembers.raw i)
  stages i := (history.fields i).1
  transitions i := (history.fields i).2
  valid i := (history.fields_spec i).2.1
  mono i j subset := by
    have before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j :=
      ZFSet.mem_insert_iff.1 (subset (ZFSet.mem_insert_iff.2 (Or.inl rfl)))
    have extension := history.compatible _ _ _ _
      (decodedFamilyValue_entry history.function i) (decodedFamilyValue_entry history.function j) before
    rw [(history.fields_spec i).1, (history.fields_spec j).1] at extension
    exact (mainPrefixExtends_iff.1 extension).2

end PreservedMainPrefixHistoryCode





end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitSizes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
variable (indices : GroundBelow M run.indices K)
include choice hK standard indices

theorem carrierUnion_below : GroundBelow M run.carrierUnion K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  change GroundBelow M (ZFSet.sUnion (ZFSet.range (fun i => (run.diagram.stage i).stage.carrier))) K
  rw [familyCodeGraph_valueRange_eq run.key _]
  apply GroundBelow.indexed_sUnion pairing unions powers separation choice run.indices_ground
    (M.union_mem unions (M.union_mem unions run.carrierFamily_ground)) run.carrierFamily_ground hK
    conditions.1 conditions.2.2.1 conditions.2.2.2 indices run.carrierFamily_function.to_isFunc
  intro i A entry
  obtain ⟨j, equal⟩ := (mem_familyCodeGraph run.key
    (fun j => (run.diagram.stage j).stage.carrier) _).1 entry
  have value : A = (run.diagram.stage j).stage.carrier := (ZFSet.pair_inj.1 equal).2.symm
  rw [value]
  simpa only [run.linked_main] using (run.linked j).invariant.points_small

theorem actorUnion_below : GroundBelow M run.actorUnion K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  change GroundBelow M (ZFSet.sUnion (ZFSet.range (fun i => (run.diagram.stage i).stage.actors))) K
  rw [familyCodeGraph_valueRange_eq run.key _]
  apply GroundBelow.indexed_sUnion pairing unions powers separation choice run.indices_ground
    (M.union_mem unions (M.union_mem unions run.actorFamily_ground)) run.actorFamily_ground hK
    conditions.1 conditions.2.2.1 conditions.2.2.2 indices run.actorFamily_function.to_isFunc
  intro i A entry
  obtain ⟨j, equal⟩ := (mem_familyCodeGraph run.key
    (fun j => (run.diagram.stage j).stage.actors) _).1 entry
  have value : A = (run.diagram.stage j).stage.actors := (ZFSet.pair_inj.1 equal).2.symm
  rw [value]
  simpa only [run.linked_main] using (run.linked j).invariant.actors_small

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
variable (indices : GroundBelow M run.indices K)
include choice hK standard indices

theorem limitPoints_below : GroundBelow M run.limitPoints K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  exact GroundBelow.indexedCarrierClasses pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.carrierFamily_ground run.limitPointRelation_ground hK
    conditions.1 conditions.2.2.2 indices (run.carrierUnion_below choice hK standard indices)

theorem limitActors_below : GroundBelow M run.limitActors K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  exact GroundBelow.indexedCarrierClasses pairing unions powers separation run.indices_ground
    run.actorUnion_ground run.actorFamily_ground run.limitActorRelation_ground hK
    conditions.1 conditions.2.2.2 indices (run.actorUnion_below choice hK standard indices)

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixTopColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def heightRangeFamily : ZFSet.{u} := familyCodeGraph run.key
  (fun i => functionGraphRange (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.height)

noncomputable def heightRangeValues : ZFSet.{u} := ZFSet.range
  (fun i => functionGraphRange (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.height)

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitCoverageConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitGroup_code (i₀ : I) :
    GroupCode run.limitActors run.limitMultiplication run.limitInverse (run.limitIdentity i₀) where
  mul_function := run.limitMultiplication_function
  inv_function := run.limitInverse_function
  identity_mem := run.limitIdentity_mem i₀
  one_mul g hg := by
    obtain ⟨i, a, ha, rfl⟩ := run.actorPresentation.limitPoint_coverage hg
    rw [run.limitIdentity_eq i₀ i]
    exact (run.limitMultiplication_at i (run.diagram.stage i).stage.group_code.identity_mem ha ha).2
      ((run.diagram.stage i).stage.group_code.one_mul a ha)
  mul_one g hg := by
    obtain ⟨i, a, ha, rfl⟩ := run.actorPresentation.limitPoint_coverage hg
    rw [run.limitIdentity_eq i₀ i]
    exact (run.limitMultiplication_at i ha (run.diagram.stage i).stage.group_code.identity_mem ha).2
      ((run.diagram.stage i).stage.group_code.mul_one a ha)
  inv_mul g hg h hh inverse := by
    obtain ⟨i, a, b, ha, hb, rfl, rfl⟩ := run.actorPresentation.pair_coverage hg hh
    rw [run.limitIdentity_eq i₀ i]
    exact (run.limitMultiplication_at i hb ha (run.diagram.stage i).stage.group_code.identity_mem).2
      ((run.diagram.stage i).stage.group_code.inv_mul a ha b hb ((run.limitInverse_at i ha hb).1 inverse))
  mul_assoc g hg h hh k hk a _ b _ c _ first second third := by
    obtain ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl⟩ := run.actorPresentation.triple_coverage hg hh hk
    obtain ⟨u, xy, _⟩ := (run.diagram.stage i).stage.group_code.mul_function.2
      (ZFSet.pair x y) (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    obtain ⟨v, yz, _⟩ := (run.diagram.stage i).stage.group_code.mul_function.2
      (ZFSet.pair y z) (ZFSet.pair_mem_prod.2 ⟨hy, hz⟩)
    have hu := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.mul_function.1 xy)).2
    have hv := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.mul_function.1 yz)).2
    obtain ⟨w, uz, _⟩ := (run.diagram.stage i).stage.group_code.mul_function.2
      (ZFSet.pair u z) (ZFSet.pair_mem_prod.2 ⟨hu, hz⟩)
    have hw := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.mul_function.1 uz)).2
    have function : FunctionGraphOn (ZFSet.prod run.limitActors run.limitActors) run.limitMultiplication :=
      ⟨_, run.limitMultiplication_function⟩
    have equalA : a = run.actorPresentation.limitPoint i u :=
      function.unique first ((run.limitMultiplication_at i hx hy hu).2 xy)
    have equalB : b = run.actorPresentation.limitPoint i v :=
      function.unique second ((run.limitMultiplication_at i hy hz hv).2 yz)
    subst a
    subst b
    have equalC : c = run.actorPresentation.limitPoint i w :=
      function.unique third ((run.limitMultiplication_at i hu hz hw).2 uz)
    subst c
    exact (run.limitMultiplication_at i hx hv hw).2
      ((run.diagram.stage i).stage.group_code.mul_assoc x hx y hy z hz u hu v hv w hw xy yz uz)

theorem limitActorMap_multiplication_iff (i : I) (a b c g h k : ZFSet.{u})
    (first : ZFSet.pair a g ∈ run.limitActorMap i)
    (second : ZFSet.pair b h ∈ run.limitActorMap i)
    (third : ZFSet.pair c k ∈ run.limitActorMap i) :
    ZFSet.pair (ZFSet.pair g h) k ∈ run.limitMultiplication ↔
      ZFSet.pair (ZFSet.pair a b) c ∈ (run.diagram.stage i).stage.multiplication := by
  obtain ⟨ha, rfl⟩ := (run.actorPresentation.inclusion_entry i a g).1 first
  obtain ⟨hb, rfl⟩ := (run.actorPresentation.inclusion_entry i b h).1 second
  obtain ⟨hc, rfl⟩ := (run.actorPresentation.inclusion_entry i c k).1 third
  exact run.limitMultiplication_at i ha hb hc

theorem limitActorMap_groupEmbedding (i₀ i : I) :
    GroupEmbeddingCode (run.diagram.stage i).stage.actors run.limitActors
      (run.diagram.stage i).stage.multiplication run.limitMultiplication
      (run.diagram.stage i).stage.identity (run.limitIdentity i₀) (run.limitActorMap i) where
  injection := run.limitActorMap_injection i
  one := (run.actorPresentation.inclusion_entry i _ _).2
    ⟨(run.diagram.stage i).stage.group_code.identity_mem, run.limitIdentity_eq i₀ i⟩
  mul a b c g h k product first second third :=
    (run.limitActorMap_multiplication_iff i a b c g h k first second third).2 product

theorem limitActorMap_inverse_iff (i : I) (a b g h : ZFSet.{u})
    (first : ZFSet.pair a g ∈ run.limitActorMap i)
    (second : ZFSet.pair b h ∈ run.limitActorMap i) :
    ZFSet.pair g h ∈ run.limitInverse ↔ ZFSet.pair a b ∈ (run.diagram.stage i).stage.inverse := by
  obtain ⟨ha, rfl⟩ := (run.actorPresentation.inclusion_entry i a g).1 first
  obtain ⟨hb, rfl⟩ := (run.actorPresentation.inclusion_entry i b h).1 second
  exact run.limitInverse_at i ha hb

structure FixedTopStage (i₀ : I) where
  column : ZFSet.{u}
  coordinate : ZFSet.{u}
  column_mem : column ∈ C
  coordinate_mem : coordinate ∈ D
  stage : GroundMainStage M C D rD
  carrier_eq : stage.carrier = fixedTopCarrier run.limitPoints
  order_eq : stage.order = fixedTopOrder run.limitPoints run.limitOrder
  meet_eq : stage.meetGraph = fixedTopMeet run.limitPoints run.limitOrder
  actors_eq : stage.actors = run.limitActors
  multiplication_eq : stage.multiplication = run.limitMultiplication
  inverse_eq : stage.inverse = run.limitInverse
  identity_eq : stage.identity = run.limitIdentity i₀
  action_eq : stage.action = fixedTopAction run.limitActors run.limitPoints run.limitAction
  bottom_eq : stage.bottom = run.limitBottom i₀
  top_eq : stage.top = run.limitPoints
  height_eq : stage.height = fixedTopHeightGraph run.limitPoints run.limitHeight column coordinate
  column_above : ∀ c ∈ heightColumns run.limitPoints C D run.limitHeight, c ∈ column

end GroundMainPrefix

namespace GroundMainPrefix.FixedTopStage
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} (data : run.FixedTopStage i₀)

theorem carrier_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank data.stage.carrier < o := by
  rw [data.carrier_eq]
  exact rank_fixedTopCarrier_lt limit (run.limitPoints_rank_lt limit rank)

theorem actors_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank data.stage.actors < o := by
  rw [data.actors_eq]
  exact run.limitActors_rank_lt limit rank

theorem carrier_below (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) : GroundBelow M data.stage.carrier K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  rw [data.carrier_eq, fixedTopCarrier]
  exact GroundBelow.insert pairing unions powers separation infinite choice
    run.limitPoints_ground run.limitPoints_ground hK conditions.2.1 conditions.1
    conditions.2.2.1 conditions.2.2.2 (run.limitPoints_below choice hK standard indices)

theorem actors_below (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) : GroundBelow M data.stage.actors K := by
  rw [data.actors_eq]
  exact run.limitActors_below choice hK standard indices

theorem invariant_inputs (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) (rank : ZFSet.rank run.code < ZFSet.rank K) :
    GroundBelow M data.stage.carrier K ∧ GroundBelow M data.stage.actors K ∧
      GroundBelow M Labels K ∧ ZFSet.rank data.stage.carrier < ZFSet.rank K ∧
      ZFSet.rank data.stage.actors < ZFSet.rank K ∧ ZFSet.rank Labels < ZFSet.rank K ∧
      run.cutoffLimit ∈ K ∧ ZFSet.rank C < ZFSet.rank K ∧ ZFSet.rank D < ZFSet.rank K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  exact ⟨data.carrier_below infinite choice hK standard indices, data.actors_below choice hK standard indices,
    (run.linked i₀).invariant.labels_small, data.carrier_rank_lt limit rank, data.actors_rank_lt limit rank,
    (run.linked i₀).invariant.labels_rank, run.cutoffLimit_mem_inaccessible hK standard indices,
    (run.linked i₀).invariant.columns_rank, (run.linked i₀).invariant.coordinates_rank⟩

end GroundMainPrefix.FixedTopStage

namespace GroundMainPrefix.FixedTopStage
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} (data : run.FixedTopStage i₀)

noncomputable def transition (i : I) : GroundMainTransition (run.diagram.stage i).stage data.stage where
  points := run.limitPointMap i
  actors := run.limitActorMap i
  points_ground := run.limitPointMap_ground i
  actors_ground := run.limitActorMap_ground i
  point_embedding := by
    rw [data.carrier_eq, data.order_eq, data.meet_eq]
    have original := run.limitPointMap_meetEmbedding i
    refine ⟨original.injection.retarget (fixedTopCarrier_subset run.limitPoints), ?_, ?_⟩
    · intro x y p q lower first second
      exact fixedTopOrder_subset _ _ (original.monotone x y p q lower first second)
    · intro x y z p q v meet first second third
      exact fixedTopMeet_subset run.limitMeet_code (original.map_meet x y z p q v meet first second third)
  order_iff := by
    intro x y p q first second
    have hq := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 second)).2
    rw [data.order_eq, fixedTopOrder_old_iff hq]
    exact run.limitPointMap_order_iff i x y p q first second
  group_embedding := by
    rw [data.actors_eq, data.multiplication_eq, data.identity_eq]
    exact run.limitActorMap_groupEmbedding i₀ i
  equivariant := by
    intro a g x y p q actor first second action
    have hp := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 first)).2
    rw [data.action_eq]
    exact (fixedTopAction_old_iff hp).2 (run.limitMaps_equivariant i a g x y p q actor first second action)
  bottom := by
    rw [data.bottom_eq]
    exact run.limitPointMap_bottom i₀ i
  height := by
    intro x p value entry
    have hp := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 entry)).2
    rw [data.height_eq, fixedTopHeightGraph_old_iff hp]
    exact run.limitPointMap_height i entry value
  agreement := by
    intro g h g' h' v v' first second point agree
    have hv := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 point)).2
    rw [data.carrier_eq, data.order_eq, data.action_eq]
    exact (run.limitMaps_agreement i g h g' h' v v' first second point agree).fixedTop
      run.limitOrder_code (run.limitAction_code i₀) hv

end GroundMainPrefix.FixedTopStage

section
open SetFormula
universe u v

namespace GroundMainPrefix.FixedTopStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} (data : run.FixedTopStage i₀)

theorem transition_comp {i j : I} (before : i ≤ j) :
    (run.diagram.transition before).map.comp pairing unions powers separation
      (data.transition j) = data.transition i := by
  apply GroundMainTransition.ext
  · change relationCompose _ _ data.stage.carrier _ (run.limitPointMap j) = run.limitPointMap i
    rw [data.carrier_eq, relationCompose_enlargeCodomain
      (run.limitPointMap_injection j).function.1 (fixedTopCarrier_subset run.limitPoints)]
    exact run.limitPointMap_comp before
  · change relationCompose _ _ data.stage.actors _ (run.limitActorMap j) = run.limitActorMap i
    rw [data.actors_eq]
    exact run.limitActorMap_comp before

end GroundMainPrefix.FixedTopStage

end

namespace GroundMainPrefix.FixedTopStage
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} (data : run.FixedTopStage i₀)

noncomputable def chronologyValues : Fin 5 → ZFSet.{u} :=
  Fin.cases data.stage.carrier (Fin.cases data.stage.order
    (Fin.cases data.stage.meetGraph
      (Fin.cases (fixedTopBirth run.limitPoints run.limitBirth run.cutoffLimit)
        (fun _ => data.stage.height))))

structure RankedChronology (level : GroundMainCandidateLevel M K) where
  serial : GroundSerializedChronology M (insert run.cutoffLimit run.cutoffLimit) C D rD
  code_ground : serial.code ∈ M.sets
  code_rank : ZFSet.rank serial.code < ZFSet.rank K
  code_member : serial.code ∈ level.validChronologies C D rD
  graphs : ∀ j, serial.fields.graph j =
    terminalChronologyGraph run.cutoffLimit (run.limitChronologyFields.graph j) (data.chronologyValues j)
  terminal : ∀ j, serial.fields.value j run.cutoffLimit = data.chronologyValues j
  old_values : ∀ j s, s ∈ run.cutoffLimit →
    serial.fields.value j s = run.limitChronologyFields.value j s

namespace RankedChronology
variable {data} {level : GroundMainCandidateLevel M K} (chronology : data.RankedChronology level)

noncomputable def main : GroundChronologicalMainStage M C D rD where
  stage := data.stage
  cutoff := run.cutoffLimit
  cutoff_ground := run.cutoffLimit_ground
  cutoff_ordinal := run.cutoffLimit_ordinal
  history := chronology.serial.toHistory
  carrier_eq := chronology.terminal 0
  order_eq := chronology.terminal 1
  meet_eq := chronology.terminal 2
  height_eq := chronology.terminal 4

theorem main_birth : chronology.main.birth = fixedTopBirth run.limitPoints run.limitBirth run.cutoffLimit :=
  chronology.terminal 3

theorem agreement (j : Fin 5) (s : ZFSet.{u}) :
    chronology.serial.fields.value j s = chronology.main.history.fieldValue j s := by
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) j

theorem history_values (i : I) (j : Fin 5) {s : ZFSet.{u}}
    (before : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) :
    chronology.main.history.fieldValue j s = (run.diagram.stage i).history.fieldValue j s := by
  rw [← chronology.agreement, chronology.old_values j s ((run.cutoffLimit_mem s).2 ⟨i, before⟩)]
  exact run.limitChronologyFields_values i j before

end RankedChronology

end GroundMainPrefix.FixedTopStage

namespace GroundMainPrefix.FixedTopStage.RankedChronology
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} {data : run.FixedTopStage i₀} {level : GroundMainCandidateLevel M K}
variable (chronology : data.RankedChronology level)

noncomputable def transition (i : I) :
    GroundChronologicalMainTransition (run.diagram.stage i) chronology.main where
  map := data.transition i
  cutoff_le := Or.inr (run.cutoff_mem_cutoffLimit i)
  birth := by
    intro x y t entry
    have hy := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 entry)).2
    rw [chronology.main_birth, fixedTopBirth_old_iff hy]
    exact run.limitPointMap_birth_iff i x y t entry
  history_prefix := by
    intro s before
    exact ⟨chronology.history_values i 0 before, chronology.history_values i 1 before,
      chronology.history_values i 2 before, chronology.history_values i 3 before,
      chronology.history_values i 4 before⟩

end GroundMainPrefix.FixedTopStage.RankedChronology

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}

namespace FixedTopStage.RankedChronology
variable {i₀ : I} {data : run.FixedTopStage i₀} {level : GroundMainCandidateLevel M K}
variable (chronology : data.RankedChronology level)

theorem invariant (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) (rank : ZFSet.rank run.code < ZFSet.rank K) :
    chronology.main.Invariant K Labels := by
  have bounds := data.invariant_inputs infinite choice hK standard indices rank
  exact ⟨bounds.1, bounds.2.1, bounds.2.2.1, bounds.2.2.2.1, bounds.2.2.2.2.1,
    bounds.2.2.2.2.2.1, bounds.2.2.2.2.2.2.1, bounds.2.2.2.2.2.2.2.1,
    bounds.2.2.2.2.2.2.2.2⟩

noncomputable def linked (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) (rank : ZFSet.rank run.code < ZFSet.rank K) :
    GroundLinkedMainStage M K Labels C D rD :=
  ⟨chronology.main, chronology.serial, fun j s _ => chronology.agreement j s,
    chronology.invariant infinite choice hK standard indices rank, chronology.code_rank⟩

noncomputable def cone : run.diagram.Cone chronology.main where
  leg := chronology.transition
  coherent := by
    intro i j before
    apply GroundChronologicalMainTransition.ext
    change (run.diagram.transition before).map.comp pairing unions powers separation
      (data.transition j) = data.transition i
    exact data.transition_comp before

end FixedTopStage.RankedChronology

end GroundMainPrefix

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainFinalChronology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def finalGeometry (i₀ : I) : GroundMainFinalGeometry M C D rD where
  carrier := run.limitPoints
  order := run.limitOrder
  meetGraph := run.limitMeetGraph
  actors := run.limitActors
  multiplication := run.limitMultiplication
  inverse := run.limitInverse
  identity := run.limitIdentity i₀
  action := run.limitAction
  bottom := run.limitBottom i₀
  height := run.limitHeight
  birth := run.limitBirth
  times := run.cutoffLimit
  carrier_ground := run.limitPoints_ground
  order_ground := run.limitOrder_ground
  meet_ground := run.limitMeetGraph_ground
  actors_ground := run.limitActors_ground
  multiplication_ground := run.limitMultiplication_ground
  inverse_ground := run.limitInverse_ground
  action_ground := run.limitAction_ground
  height_ground := run.limitHeight_ground
  birth_ground := run.limitBirth_ground
  times_ground := run.cutoffLimit_ground
  columns_ground := (run.diagram.stage i₀).stage.columns_ground
  coordinates_ground := (run.diagram.stage i₀).stage.coordinates_ground
  coordinate_order_ground := (run.diagram.stage i₀).stage.coordinate_order_ground
  meet := run.limitMeet_code
  group_code := run.limitGroup_code i₀
  action_code := run.limitAction_code i₀
  bottom_mem := run.limitBottom_mem i₀
  least := run.limitBottom_least i₀
  height_code := run.limitHeight_code
  birth_function := run.limitBirth_function
  times_ordinal := run.cutoffLimit_ordinal
  old_meet := run.limit_old_meet

end PartitionPilot.Forcing.GroundMainPrefix



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalRowTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]

namespace GroundMainPrefix
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def finalInclusions (i₀ : I) : GroundMainFinalInclusions run (run.finalGeometry i₀) where
  pointMap := run.limitPointMap
  actorMap := run.limitActorMap
  pointFamily := run.limitPointInclusions
  actorFamily := run.limitActorInclusions
  pointMap_ground := run.limitPointMap_ground
  actorMap_ground := run.limitActorMap_ground
  pointFamily_ground := run.limitPointInclusions_ground
  actorFamily_ground := run.limitActorInclusions_ground
  pointFamily_function := run.limitPointInclusions_function
  actorFamily_function := run.limitActorInclusions_function
  pointFamily_entry := run.limitPointInclusions_entry
  actorFamily_entry := run.limitActorInclusions_entry
  point_embedding := run.limitPointMap_meetEmbedding
  order_iff := run.limitPointMap_order_iff
  actor_embedding := run.limitActorMap_groupEmbedding i₀
  inverse_iff := run.limitActorMap_inverse_iff
  action_iff := run.limitMaps_action_iff
  bottom := run.limitPointMap_bottom i₀
  height := fun i _ _ image t => run.limitPointMap_height i image t
  birth := run.limitPointMap_birth_iff
  old_fiber := run.limitBirth_old_fiber
  point_comp := run.limitPointMap_comp
  actor_comp := run.limitActorMap_comp
  point_coverage := by
    intro p hp
    obtain ⟨i, x, hx, rfl⟩ := run.pointPresentation.limitPoint_coverage hp
    exact ⟨i, x, hx, (run.pointPresentation.inclusion_entry i x _).2 ⟨hx, rfl⟩⟩
  actor_coverage := by
    intro g hg
    obtain ⟨i, a, ha, rfl⟩ := run.actorPresentation.limitPoint_coverage hg
    exact ⟨i, a, ha, (run.actorPresentation.inclusion_entry i a _).2 ⟨ha, rfl⟩⟩
  agreement := run.limitMaps_agreement

end GroundMainPrefix

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainPrefixInsertionFamilyTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def finalInsertionCaps (j : I) (caps : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose Labels (run.diagram.stage j).stage.carrier run.limitPoints caps (run.limitPointMap j)

noncomputable def finalInsertionActors (j : I) (actors : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose Labels (run.diagram.stage j).stage.actors run.limitActors actors (run.limitActorMap j)

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixFinalInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def pointStageCover : ZFSet.{u} :=
  indexedImageCover run.indices run.carrierUnion run.limitPoints run.limitPointInclusions

end GroundMainPrefix

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalFulfillmentConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]

structure FinalFulfillment
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (level : GroundMainCandidateLevel M K) (i₀ : I) where
  chronology : run.FinalChronology level
  countable_localization : ∀ X ∈ M.sets, X ⊆ (run.finalGeometry i₀).carrier →
    M.groundEmbeddable X ZFSet.omega →
    (∃ j, ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
      ZFSet.pair y x ∈ (run.finalInclusions i₀).pointMap j) ∧
    ∃ b ∈ (run.finalGeometry i₀).carrier,
      ∀ x ∈ X, ZFSet.pair x b ∈ (run.finalGeometry i₀).order
  growth : ∀ x ∈ (run.finalGeometry i₀).carrier, ∃ y ∈ (run.finalGeometry i₀).carrier,
    ZFSet.pair x y ∈ (run.finalGeometry i₀).order ∧
      ¬ ZFSet.pair y x ∈ (run.finalGeometry i₀).order
  directed : ∀ x ∈ (run.finalGeometry i₀).carrier, ∀ y ∈ (run.finalGeometry i₀).carrier,
    ∃ z ∈ (run.finalGeometry i₀).carrier, ZFSet.pair x z ∈ (run.finalGeometry i₀).order ∧
      ZFSet.pair y z ∈ (run.finalGeometry i₀).order
  separates : ∀ W ∈ (run.finalGeometry i₀).carrier, ∀ d ∈ (run.finalGeometry i₀).carrier,
    ∀ x ∈ (run.finalGeometry i₀).carrier,
    ZFSet.pair W d ∈ (run.finalGeometry i₀).order →
    ZFSet.pair W x ∈ (run.finalGeometry i₀).order →
    ∃ k ∈ (run.finalGeometry i₀).actors,
      (∀ z ∈ (run.finalGeometry i₀).carrier, ZFSet.pair z W ∈ (run.finalGeometry i₀).order →
        ZFSet.pair (ZFSet.pair k z) z ∈ (run.finalGeometry i₀).action) ∧
      ∃ y ∈ (run.finalGeometry i₀).carrier,
        ZFSet.pair (ZFSet.pair k d) y ∈ (run.finalGeometry i₀).action ∧
        ZFSet.pair (ZFSet.pair y x) W ∈ (run.finalGeometry i₀).meetGraph
  rectangles : ∀ c b d g h X,
    ExternalRectangleCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).actors
      (run.finalGeometry i₀).order (run.finalGeometry i₀).meetGraph (run.finalGeometry i₀).action
      c b d g h → X ∈ (run.finalGeometry i₀).carrier →
    (∀ y ∈ (run.finalGeometry i₀).carrier,
      ZFSet.pair (ZFSet.pair g d) y ∈ (run.finalGeometry i₀).action →
      ZFSet.pair y X ∈ (run.finalGeometry i₀).order) →
    (∀ y ∈ (run.finalGeometry i₀).carrier,
      ZFSet.pair (ZFSet.pair h d) y ∈ (run.finalGeometry i₀).action →
      ZFSet.pair y X ∈ (run.finalGeometry i₀).order) →
    ∃ k ∈ (run.finalGeometry i₀).actors, ∃ l ∈ (run.finalGeometry i₀).actors,
      RectangleAtBoundCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
        (run.finalGeometry i₀).meetGraph (run.finalGeometry i₀).action c b d g h X k l

end PartitionPilot.Forcing.GroundMainPrefix



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalSupportConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]

structure FinalSupportFulfillment
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (level : GroundMainCandidateLevel M K) (i₀ : I) extends run.FinalFulfillment level i₀ where
  insertion : ∀ c ∈ (run.finalGeometry i₀).carrier, ∀ e ∈ (run.finalGeometry i₀).carrier,
    ∀ d ∈ (run.finalGeometry i₀).carrier, ∀ F ∈ M.sets,
    MeetFilterCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
      (run.finalGeometry i₀).meetGraph F →
    ZFSet.pair c e ∈ (run.finalGeometry i₀).order →
    ZFSet.pair e c ∉ (run.finalGeometry i₀).order →
    ZFSet.pair c d ∈ (run.finalGeometry i₀).order →
    (∀ x ∈ F, ZFSet.pair e x ∈ (run.finalGeometry i₀).order) →
    ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
      FinalInsertionFamiliesCode Labels (run.finalGeometry i₀).carrier (run.finalGeometry i₀).actors
        (run.finalGeometry i₀).order (run.finalGeometry i₀).meetGraph (run.finalGeometry i₀).action
        c e d F caps actors

end PartitionPilot.Forcing.GroundMainPrefix

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

namespace TransitiveGround
variable (M : TransitiveGround.{u}) (a : PosetAction G P) (s : Presentation P)
variable (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem refinementStageSystem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (nodeOrder : b.conditionOrder ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    {level T T2 : ZFSet.{u}} (hLevel : level ∈ M.sets) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (valid1 : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
    (closed1 : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
    (closed2 : ∀ g (τ : Name s), τ.val ∈ T2 → (a.act s g τ).val ∈ T2)
    (children1 : ∀ τ : Name s, τ.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) τ)
    (children2 : ∀ τ : Name s, τ.val ∈ T2 →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) τ) :
    RefinementStageSystem M a s t b d base directed level T T2 := by
  have first := M.niceNameSystem a s t pairing unions powers separation collection carrier order
    maps hT valid1 closed1 b d base directed group nodes supports children1
  have second := M.niceNameSystem a s t pairing unions powers separation collection carrier order
    maps hT2 valid2 closed2 b d base directed group nodes supports children2
  have indices := M.niceRefinementIndexSystem a s b d pairing unions powers separation collection
    hLevel hT hT2 carrier order nodes nodeOrder first second
  exact ⟨valid1,valid2,children1,children2,first,second,indices,
    ⟨maps,nodeMaps,closed1,closed2,indices.family_ground⟩⟩

end TransitiveGround
end PartitionPilot.Forcing

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

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_rawRefinementIndexActionGraph :
    GroundDefinableFunction M (fun env : Fin 5 → ZFSet.{u} =>
      M.rawRefinementIndexActionGraph (env 0) (env 1) (env 2) (env 3) (env 4)) := by
  let v := GroundSetTerm.var M (n := 5)
  let bound := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 1,v 1]
  let term := GroundSetTerm.app (M.definable_separation separation refinementIndexActionEntryFormula)
    ![bound,v 0,v 1,v 2,v 3,v 4]
  apply term.definition.congr
  intro env
  change ZFSet.sep (fun z => Realize M.sets refinementIndexActionEntryFormula (extend z _)) _ = _
  have args : (fun j : Fin 5 => (![bound,v 0,v 1,v 2,v 3,v 4] j.succ).eval env) = ![env 0,env 1,env 2,env 3,env 4] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))) j
  rw [args]
  rfl

noncomputable def definable_rawTermActionGraph :
    GroundDefinableFunction M (fun env : Fin 4 → ZFSet.{u} =>
      M.rawTermActionGraph (env 0) (env 1) (env 2) (env 3)) := by
  let v := GroundSetTerm.var M (n := 4)
  let bound := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 1,v 1]
  let term := GroundSetTerm.app (M.definable_separation separation termActionEntryFormula)
    ![bound,v 0,v 1,v 2,v 3]
  apply term.definition.congr
  intro env
  change ZFSet.sep (fun z => Realize M.sets termActionEntryFormula (extend z _)) _ = _
  have args : (fun j : Fin 4 => (![bound,v 0,v 1,v 2,v 3] j.succ).eval env) = ![env 0,env 1,env 2,env 3] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) j
  rw [args]
  rfl

end

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

noncomputable def definable_rawRefinementAssignmentActionGraph
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 6 → ZFSet.{u} =>
      M.rawRefinementAssignmentActionGraph (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) := by
  let v := GroundSetTerm.var M (n := 6)
  let index := GroundSetTerm.app (M.definable_rawRefinementIndexActionGraph pairing unions powers separation)
    ![v 0,v 1,v 3,v 4,v 5]
  let term := GroundSetTerm.app (M.definable_rawTermActionGraph pairing unions powers separation)
    ![v 0,v 2,v 3,v 4]
  let terms := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 2,v 2]
  let termPair := GroundSetTerm.app (M.definable_relationProduct pairing unions powers separation)
    ![v 2,v 2,v 2,v 2,term,term]
  exact (GroundSetTerm.app (M.definable_relationProduct pairing unions powers separation)
    ![v 1,terms,v 1,terms,index,termPair]).definition

noncomputable def definable_rawStageRefinementAssignmentActionGraph
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 13 → ZFSet.{u} =>
      M.rawStageRefinementAssignmentActionGraph (env 0) (env 1) (env 2) (env 3) (env 4)
        (env 5) (env 6) (env 7) (env 8) (env 9) (env 10) (env 11) (env 12)) := by
  let v := GroundSetTerm.var M (n := 13)
  let maps := GroundSetTerm.app (M.definable_rawActionMapFamily pairing unions powers separation collection)
    ![v 5,v 4,v 1]
  let nodeMaps := GroundSetTerm.app (M.definable_rawActionMapFamily pairing unions powers separation collection)
    ![v 5,v 8,v 6]
  let first := GroundSetTerm.app (M.definable_rawNiceNameCandidateGraph pairing unions powers separation collection)
    ![v 6,v 10,v 1,v 5,v 9,maps]
  let second := GroundSetTerm.app (M.definable_rawNiceNameCandidateGraph pairing unions powers separation collection)
    ![v 6,v 11,v 1,v 5,v 9,maps]
  let family := GroundSetTerm.app (M.definable_familySetCode pairing unions powers separation) ![v 10,v 3]
  let indices := GroundSetTerm.app (M.definable_refinementIndices pairing unions powers separation)
    ![v 12,v 6,v 7,first,second,v 10,v 11,family,v 1,v 2,v 3]
  exact (GroundSetTerm.app (M.definable_rawRefinementAssignmentActionGraph pairing unions powers separation)
    ![v 0,indices,v 10,v 1,maps,nodeMaps]).definition

end

open SetRealization SetFormula
universe u

end PartitionPilot.Forcing.TransitiveGround

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


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u})

noncomputable def structuralRefinementHistory
    (G nodes nodeOrder basis T T2 stages history : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun x : {x : SetMembers history //
      ∃ f : Fin 5 → ZFSet.{u}, SetMembers.raw x = nonemptyTupleCode 4 f ∧ f 0 ∈ stages} =>
    let f := Classical.choose x.property
    ZFSet.pair (f 0) (M.rawRefinementFormulaDataCode (f 1) (f 2) (f 3) (f 4)
      G nodes nodeOrder basis T T2 (f 0)))

theorem mem_structuralRefinementHistory
    (G nodes nodeOrder basis T T2 stages history z : ZFSet.{u}) :
    z ∈ M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history ↔
      ∃ level ∈ stages, ∃ P order top action,
        ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
        z = ZFSet.pair level (M.rawRefinementFormulaDataCode P order top action
          G nodes nodeOrder basis T T2 level) := by
  rw [structuralRefinementHistory, ZFSet.mem_range]
  constructor
  · rintro ⟨x, equal⟩
    let f := Classical.choose x.property
    have shape := Classical.choose_spec x.property
    refine ⟨f 0, shape.2, f 1, f 2, f 3, f 4, ?_, equal.symm⟩
    have tuple : nonemptyTupleCode 4 f = ZFSet.pair (f 0)
        (forcingStageCode (f 1) (f 2) (f 3) (f 4)) := rfl
    exact tuple ▸ shape.1 ▸ SetMembers.raw_mem x.val
  · rintro ⟨level, hl, P, order, top, action, entry, rfl⟩
    let f : Fin 5 → ZFSet.{u} := ![level, P, order, top, action]
    let x : {x : SetMembers history // ∃ f : Fin 5 → ZFSet.{u},
        SetMembers.raw x = nonemptyTupleCode 4 f ∧ f 0 ∈ stages} :=
      ⟨SetMembers.ofMem _ entry, f, SetMembers.raw_ofMem _ entry, hl⟩
    refine ⟨x, ?_⟩
    have same : Classical.choose x.property = f := nonemptyTupleCode_injective 4
      ((Classical.choose_spec x.property).1.symm.trans (SetMembers.raw_ofMem _ entry))
    dsimp only
    rw [same]
    rfl

theorem pair_mem_structuralRefinementHistory
    (G nodes nodeOrder basis T T2 stages history level output : ZFSet.{u}) :
    ZFSet.pair level output ∈ M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history ↔
      level ∈ stages ∧ ∃ P order top action,
        ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
        output = M.rawRefinementFormulaDataCode P order top action G nodes nodeOrder basis T T2 level := by
  rw [M.mem_structuralRefinementHistory]
  constructor
  · rintro ⟨l, hl, P, order, top, action, entry, equal⟩
    obtain ⟨rfl, value⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hl, P, order, top, action, entry, value⟩
  · rintro ⟨hl, P, order, top, action, entry, rfl⟩
    exact ⟨level, hl, P, order, top, action, entry, rfl⟩

theorem structuralRefinementHistory_entry
    (G nodes nodeOrder basis T T2 stages history level P order top action output : ZFSet.{u})
    (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history) :
    ZFSet.pair level output ∈ M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history ↔
      output = M.rawRefinementFormulaDataCode P order top action G nodes nodeOrder basis T T2 level := by
  rw [M.pair_mem_structuralRefinementHistory]
  constructor
  · rintro ⟨_, P', order', top', action', entry, value⟩
    have same := function.unique entry stored
    obtain ⟨rfl, rfl, rfl, rfl⟩ := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 same
    exact value
  · intro value
    exact ⟨function.pair_source stored, P, order, top, action, stored, value⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder basis T T2 : ZFSet.{u})

 theorem structuralRefinementHistory_domain_restrict {stages earlier history : ZFSet.{u}}
    (subset : earlier ⊆ stages) :
    M.structuralRefinementHistory G nodes nodeOrder basis T T2 earlier history =
      graphRestriction earlier (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨level, hl, P, order, top, action, stored, rfl⟩ := (M.mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _).1 member
    exact pair_mem_graphRestriction.2 ⟨(M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).2
      ⟨subset hl, P, order, top, action, stored, rfl⟩, hl⟩
  · intro member
    obtain ⟨level, hl, output, rfl, entry⟩ := mem_graphRestriction.1 member
    obtain ⟨_, P, order, top, action, stored, value⟩ := (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).1 entry
    exact (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).2
      ⟨hl, P, order, top, action, stored, value⟩

theorem structuralRefinementHistory_history_restrict (stages history : ZFSet.{u}) :
    M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages (graphRestriction stages history) =
      M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history := by
  apply ZFSet.ext
  intro z
  rw [M.mem_structuralRefinementHistory, M.mem_structuralRefinementHistory]
  constructor
  · rintro ⟨level, hl, P, order, top, action, stored, value⟩
    exact ⟨level, hl, P, order, top, action, (pair_mem_graphRestriction.1 stored).1, value⟩
  · rintro ⟨level, hl, P, order, top, action, stored, value⟩
    exact ⟨level, hl, P, order, top, action, pair_mem_graphRestriction.2 ⟨stored, hl⟩, value⟩

theorem structuralRefinementHistory_function {stages history : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (shape : ∀ level ∈ stages, ∃ P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history) :
    FunctionGraphOn stages (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) := by
  let H := M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history
  refine ⟨⋃₀ ⋃₀ H, ?_, ?_⟩
  · intro z hz
    obtain ⟨level, hl, P, order, top, action, _, equal⟩ := (M.mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _).1 hz
    rw [equal] at hz ⊢
    exact ZFSet.pair_mem_prod.2 ⟨hl, pair_second_mem_doubleUnion hz⟩
  · intro level hl
    obtain ⟨P, order, top, action, stored⟩ := shape level hl
    have exactEntry := M.structuralRefinementHistory_entry G nodes nodeOrder basis T T2 stages history
      level P order top action
    refine ⟨_, (exactEntry _ function stored).2 rfl, ?_⟩
    intro y hy
    exact (exactEntry y function stored).1 hy

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
universe u

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem refinementDataHistoryIndices_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {stages history : ZFSet.{u}} (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) :
    refinementDataHistoryIndices stages history ∈ M.sets :=
  M.refinementHistoryIndices_mem unions separation hStages
    (M.refinementDataHistoryField_mem pairing unions powers separation hStages hHistory 0)

end TransitiveGround




end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

 theorem rawRefinementFormulaData_level
    (P order top action G nodes nodeOrder basis T T2 level : ZFSet.{u}) :
    RefinementIndexLevelCode (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) level := by
  intro z hz
  obtain ⟨fields, equal, bound⟩ := M.refinementIndices_fields _ _ _ _ _ _ _ _ _ _ _ hz
  exact ⟨fields, equal, ZFSet.mem_singleton.1 (bound 0)⟩

variable (G nodes nodeOrder basis T T2 stages history : ZFSet.{u})

theorem structuralRefinementHistory_decoded {level output : ZFSet.{u}}
    (entry : ZFSet.pair level output ∈ M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) :
    ∃ data : Fin 15 → ZFSet.{u}, output = refinementFormulaDataCode data := by
  obtain ⟨_, P, order, top, action, _, equal⟩ := (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).1 entry
  exact ⟨_, equal⟩

theorem structuralRefinementHistory_fields {level : ZFSet.{u}} (data : Fin 15 → ZFSet.{u})
    (entry : ZFSet.pair level (refinementFormulaDataCode data) ∈
      M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) :
    level ∈ stages ∧ ∃ P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
      data = M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level := by
  obtain ⟨hl, P, order, top, action, stored, equal⟩ := (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).1 entry
  exact ⟨hl, P, order, top, action, stored, refinementFormulaDataCode_injective equal⟩

theorem structuralRefinementHistory_structural_fields {level : ZFSet.{u}} (data : Fin 15 → ZFSet.{u})
    (entry : ZFSet.pair level (refinementFormulaDataCode data) ∈
      M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) :
    data 6 = T ∧ RefinementIndexLevelCode (data 0) level ∧
      ∃ action, ZFSet.pair level (forcingStageCode (data 7) (data 8) (data 9) action) ∈ history := by
  obtain ⟨_, P, order, top, action, stored, rfl⟩ :=
    M.structuralRefinementHistory_fields G nodes nodeOrder basis T T2 stages history data entry
  exact ⟨rfl, M.rawRefinementFormulaData_level _ _ _ _ _ _ _ _ _ _ _, action, stored⟩

theorem structuralRefinementHistory_dataHistory
    (function : FunctionGraphOn stages history)
    (shape : ∀ level ∈ stages, ∃ P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history) :
    RefinementDataHistory stages (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) T where
  function := M.structuralRefinementHistory_function G nodes nodeOrder basis T T2 function shape
  decoded := fun _ _ entry => M.structuralRefinementHistory_decoded G nodes nodeOrder basis T T2 stages history entry
  terms := fun _ data entry =>
    (M.structuralRefinementHistory_structural_fields G nodes nodeOrder basis T T2 stages history data entry).1
  literal := fun _ data entry =>
    (M.structuralRefinementHistory_structural_fields G nodes nodeOrder basis T T2 stages history data entry).2.1

end PartitionPilot.Forcing.TransitiveGround



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
include pairing unions powers separation collection group nodes supports hHistory hT witnesses

theorem structuralHistory_rawTests_union :
    ∀ level (data : Fin 15 → ZFSet.{u}), ZFSet.pair level (refinementFormulaDataCode data) ∈
      M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 stages history →
      ∀ (family lower : Nat → ZFSet.{u}) q,
        (∀ n m, n ≤ m → family n ⊆ family m) →
        (∀ n, ZFSet.pair q (lower n) ∈ data 8) →
        (∀ n, stageOneRawTests M data (family n) (lower n)) →
        stageOneRawTests M data (stageOneAssignmentUnion family) q := by
  intro level data entry family lower q increasing below tests
  obtain ⟨_, P, order, top, action, stored, rfl⟩ :=
    M.structuralRefinementHistory_fields t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history data entry
  have ground := M.forcingStageCode_fields
    (M.transitive (M.union_mem unions (M.union_mem unions hHistory))
      (pair_second_mem_doubleUnion stored))
  exact (witnesses level P order top action stored).rawTests_union
    pairing unions powers separation collection ground.1 group nodes ground.2.1 supports hT
    family lower q increasing below tests

end PartitionPilot.Forcing.TransitiveGround

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

noncomputable def transitionBody {n}
    (p y upperOrder cutGraph meet omega C E : Fin n) (fields : Fin 15 → Fin n) : SetFormula (n + 8) :=
  let old := suffixIndex n 8
  let v := prefixIndex n 8
  .conj (transitionShape p y upperOrder cutGraph).toFormula
    (.conj (SetFormula.reindex (extend (v 7) (extend (v 1) (fun j => old (fields j))))
      (M.definable_storedPreparationRequests pairing unions powers separation).formula)
      (preparedCertificateFamilyFormula (old (fields 7)) (old (fields 8)) (v 6)
        (old (fields 10)) (old (fields 11)) (old meet) (old (fields 14))
        (old (fields 13)) (old (fields 9)) (old omega) (v 7) (old C) (old E) (v 3) (v 4)))

noncomputable def storedPreparationFormula {n}
    (p y upperOrder cutGraph meet omega C E : Fin n) (fields : Fin 15 → Fin n) : SetFormula n :=
  exBlock 8 (transitionBody M pairing unions powers separation p y upperOrder cutGraph meet omega C E fields)

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def storedPreparationRelation
    (Q upperOrder nodes T levels alpha meet : ZFSet.{u}) (fields : Fin 15 → ZFSet.{u}) : ZFSet.{u} :=
  let W := M.groundRelations T Q
  let C := M.supportedEqualityCertificateBound nodes W
  let E := M.synchronizedEnumerationBound nodes W
  let cut := rowAssignmentCutGraph Q (fields 7) levels alpha
  ZFSet.sep (fun z => ∃ p y, z = ZFSet.pair p y ∧
    M.StoredPreparationCode upperOrder cut meet ZFSet.omega C E fields p y)
    (ZFSet.prod Q (M.preparationWitnessBound nodes T Q))

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

theorem refinementHistoryForcing_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {rows T stages history : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hT : T ∈ M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.refinementHistoryForcing rows T stages history ∈ M.sets :=
  M.forcingHistoryConditions_mem pairing unions powers separation hRows
    (M.refinementDataHistoryIndices_mem pairing unions powers separation hStages hHistory) hT
    hStages hHistory (M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hHistory hT) omega

end TransitiveGround

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

theorem refinementHistoryOrder_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {rows rowOrder T stages history : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hOrder : rowOrder ∈ M.sets) (hT : T ∈ M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.refinementHistoryOrder rows rowOrder T stages history ∈ M.sets :=
  M.rowAssignmentOrder_mem pairing unions powers separation
    (M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hStages hHistory omega)
    hRows (M.groundSmallSubsets_mem powers separation
      (M.stageOneAssignments_mem pairing unions powers separation
        (M.refinementDataHistoryIndices_mem pairing unions powers separation hStages hHistory) hT) omega) hOrder

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

namespace PartitionPilot.Forcing
universe u

theorem TransitiveGround.refinementHistoryOrder_raw (M : TransitiveGround.{u})
    (rows rowOrder T stages history : ZFSet.{u}) :
    M.refinementHistoryOrder rows rowOrder T stages history =
      rawRowAssignmentOrder (M.refinementHistoryForcing rows T stages history) rowOrder :=
  (rawRowAssignmentOrder_eq (M.refinementHistoryForcing_shape rows T stages history)).symm

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundDefinableRefinementHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_refinementDataHistoryIndicesSetFormula {n : Nat}
    (output stages history : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (refinementDataHistoryIndicesSetFormula output stages history) env ↔
      env output = refinementDataHistoryIndices (env stages) (env history) := by
  have ground := M.refinementDataHistoryIndices_mem pairing unions powers separation
    (members stages) (members history)
  apply M.realize_exactSetFormula output _ env (members output)
    (fun _ member => M.transitive ground member)
  intro z hz
  exact (BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members)).trans
    (BoundedFormula.truth_refinementDataHistoryIndicesEntryFormula stages.succ history.succ 0 _)

noncomputable def definable_refinementDataHistoryIndices : GroundDefinableFunction M
    (fun env : Fin 2 → ZFSet.{u} => refinementDataHistoryIndices (env 0) (env 1)) where
  formula := refinementDataHistoryIndicesSetFormula 0 1 2
  closed := fun _ members => M.refinementDataHistoryIndices_mem pairing unions powers separation
    (members 0) (members 1)
  correct := fun env members z hz => M.realize_refinementDataHistoryIndicesSetFormula
    pairing unions powers separation 0 1 2 (extend z env) (Fin.cases hz members)

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_StructuralRefinementHistoryFormulas
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
variable (collection : CollectionSchema M.sets)

noncomputable def definable_structuralRefinementEntry :
    GroundDefinableFunction M (fun env : Fin 11 → ZFSet.{u} =>
      ZFSet.pair (env 0) (M.rawRefinementFormulaDataCode (env 1) (env 2) (env 3) (env 4)
        (env 5) (env 6) (env 7) (env 8) (env 9) (env 10) (env 0))) := by
  let v := GroundSetTerm.var M (n := 11)
  let data := GroundSetTerm.app (M.definable_rawRefinementFormulaDataCode pairing unions powers separation collection)
    ![v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 0]
  let entry := GroundSetTerm.app (M.definable_nonemptyTuple pairing 1) ![v 0, data]
  exact entry.definition

noncomputable def structuralRefinementEntryFormula : SetFormula 9 :=
  let w := prefixIndex 9 5
  let old := suffixIndex 9 5
  exBlock 5 (.conj (BoundedFormula.nonemptyTupleFormula 4 (old 0) w).toFormula
    (.conj (.mem (w 0) (old 2))
      (SetFormula.reindex (extend (old 1)
        ![w 0, w 1, w 2, w 3, w 4, old 3, old 4, old 5, old 6, old 7, old 8])
        (M.definable_structuralRefinementEntry pairing unions powers separation collection).formula)))

theorem realize_structuralRefinementEntryFormula (env : Fin 9 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (M.structuralRefinementEntryFormula pairing unions powers separation collection) env ↔
      ∃ f : Fin 5 → ZFSet.{u}, env 0 = nonemptyTupleCode 4 f ∧ f 0 ∈ env 2 ∧
        env 1 = ZFSet.pair (f 0) (M.rawRefinementFormulaDataCode (f 1) (f 2) (f 3) (f 4)
          (env 3) (env 4) (env 5) (env 6) (env 7) (env 8) (f 0)) := by
  unfold structuralRefinementEntryFormula
  rw [realize_exBlock]
  have meaning (f : Fin 5 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj (BoundedFormula.nonemptyTupleFormula 4 (suffixIndex 9 5 0)
        (prefixIndex 9 5)).toFormula (.conj (.mem (prefixIndex 9 5 0) (suffixIndex 9 5 2))
        (SetFormula.reindex (extend (suffixIndex 9 5 1)
          ![prefixIndex 9 5 0, prefixIndex 9 5 1, prefixIndex 9 5 2, prefixIndex 9 5 3,
            prefixIndex 9 5 4, suffixIndex 9 5 3, suffixIndex 9 5 4, suffixIndex 9 5 5,
            suffixIndex 9 5 6, suffixIndex 9 5 7, suffixIndex 9 5 8])
          (M.definable_structuralRefinementEntry pairing unions powers separation collection).formula)))
          (extendMany 5 f env) ↔
      env 0 = nonemptyTupleCode 4 f ∧ f 0 ∈ env 2 ∧
        env 1 = ZFSet.pair (f 0) (M.rawRefinementFormulaDataCode (f 1) (f 2) (f 3) (f 4)
          (env 3) (env 4) (env 5) (env 6) (env 7) (env 8) (f 0)) := by
    change (Realize M.sets (BoundedFormula.nonemptyTupleFormula 4 _ _).toFormula _ ∧ _ ∧ _) ↔ _
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 5 f env ground members),
      BoundedFormula.truth_nonemptyTupleFormula]
    simp only [extendMany_suffix, extendMany_prefix]
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    rw [realize_reindex, map_extend]
    have args : (fun j : Fin 11 => extendMany 5 f env
      (![prefixIndex 9 5 0, prefixIndex 9 5 1, prefixIndex 9 5 2, prefixIndex 9 5 3,
        prefixIndex 9 5 4, suffixIndex 9 5 3, suffixIndex 9 5 4, suffixIndex 9 5 5,
        suffixIndex 9 5 6, suffixIndex 9 5 7, suffixIndex 9 5 8] j)) =
      ![f 0, f 1, f 2, f 3, f 4, env 3, env 4, env 5, env 6, env 7, env 8] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (fun k => Fin.elim0 k))))))))))) j
    rw [args]
    exact (M.definable_structuralRefinementEntry pairing unions powers separation collection).correct _
      (Fin.cases (ground 0) (Fin.cases (ground 1) (Fin.cases (ground 2) (Fin.cases (ground 3)
        (Fin.cases (ground 4) (Fin.cases (members 3) (Fin.cases (members 4) (Fin.cases (members 5)
          (Fin.cases (members 6) (Fin.cases (members 7) (Fin.cases (members 8) (fun j => Fin.elim0 j))))))))))))
      _ (members 1)
  constructor
  · rintro ⟨f, ground, holds⟩
    exact ⟨f, (meaning f ground).1 holds⟩
  · rintro ⟨f, shape, level, value⟩
    have ground := M.nonemptyTupleCode_field_mem 4 f (shape ▸ members 0)
    exact ⟨f, ground, (meaning f ground).2 ⟨shape, level, value⟩⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStructuralRefinementHistories
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
variable (collection : CollectionSchema M.sets)

theorem imageMeaning (env : Fin 8 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (y : ZFSet.{u}) (hy : y ∈ M.sets) :
    y ∈ M.structuralRefinementHistory (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7) ↔
      ∃ x ∈ env 7, Realize M.sets (M.structuralRefinementEntryFormula pairing unions powers separation collection)
        (extend x (extend y ![env 6, env 0, env 1, env 2, env 3, env 4, env 5])) := by
  rw [M.mem_structuralRefinementHistory]
  have meaning (x : ZFSet.{u}) (hx : x ∈ env 7) :=
    M.realize_structuralRefinementEntryFormula pairing unions powers separation collection
      (extend x (extend y ![env 6, env 0, env 1, env 2, env 3, env 4, env 5]))
      (Fin.cases (M.transitive (members 7) hx) (Fin.cases hy
        (Fin.cases (members 6) (Fin.cases (members 0) (Fin.cases (members 1)
          (Fin.cases (members 2) (Fin.cases (members 3) (Fin.cases (members 4)
            (Fin.cases (members 5) (fun j => Fin.elim0 j))))))))))
  constructor
  · rintro ⟨level, hl, P, order, top, action, entry, equal⟩
    exact ⟨_, entry, (meaning _ entry).2 ⟨![level, P, order, top, action], rfl, hl, equal⟩⟩
  · rintro ⟨x, hx, holds⟩
    obtain ⟨f, shape, level, value⟩ := (meaning x hx).1 holds
    change x = ZFSet.pair (f 0) (forcingStageCode (f 1) (f 2) (f 3) (f 4)) at shape
    exact ⟨f 0, level, f 1, f 2, f 3, f 4, shape ▸ hx, value⟩

include pairing unions powers separation collection in
 theorem structuralRefinementHistory_mem (env : Fin 8 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    M.structuralRefinementHistory (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7) ∈ M.sets := by
  let params : Fin 7 → ZFSet.{u} := ![env 6, env 0, env 1, env 2, env 3, env 4, env 5]
  have paramGround : ∀ j, params j ∈ M.sets := Fin.cases (members 6) (Fin.cases (members 0)
    (Fin.cases (members 1) (Fin.cases (members 2) (Fin.cases (members 3)
      (Fin.cases (members 4) (Fin.cases (members 5) (fun j => Fin.elim0 j)))))))
  apply M.definable_image_mem separation collection
    (M.structuralRefinementEntryFormula pairing unions powers separation collection) params paramGround (members 7)
  · intro y hy
    obtain ⟨level, _, P, order, top, action, entry, rfl⟩ := (M.mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _).1 hy
    have fields := M.nonemptyTupleCode_field_mem 4 (![level, P, order, top, action])
      (M.transitive (members 7) entry)
    exact (M.definable_structuralRefinementEntry pairing unions powers separation collection).closed
      ![level, P, order, top, action, env 0, env 1, env 2, env 3, env 4, env 5]
      (Fin.cases (fields 0) (Fin.cases (fields 1) (Fin.cases (fields 2) (Fin.cases (fields 3)
        (Fin.cases (fields 4) (Fin.cases (members 0) (Fin.cases (members 1) (Fin.cases (members 2)
          (Fin.cases (members 3) (Fin.cases (members 4) (Fin.cases (members 5) (fun j => Fin.elim0 j))))))))))))
  · exact imageMeaning M pairing unions powers separation collection env members
  · intro x hx y hy z hz first second
    have meaning (w : ZFSet.{u}) (hw : w ∈ M.sets) :=
      M.realize_structuralRefinementEntryFormula pairing unions powers separation collection
        (extend x (extend w params))
        (Fin.cases (M.transitive (members 7) hx) (Fin.cases hw paramGround))
    obtain ⟨f, shape, _, value⟩ := (meaning y hy).1 first
    obtain ⟨g, shape', _, value'⟩ := (meaning z hz).1 second
    have same := nonemptyTupleCode_injective 4 (shape.symm.trans shape')
    exact value.trans (same ▸ value'.symm)

noncomputable def structuralRefinementHistoryFormula : SetFormula 9 :=
  exactSetFormula 0 (.ex (.conj (.mem 0 10)
    (SetFormula.reindex ![0, 1, 9, 3, 4, 5, 6, 7, 8]
      (M.structuralRefinementEntryFormula pairing unions powers separation collection))))

noncomputable def definable_structuralRefinementHistory :
    GroundDefinableFunction M (fun env : Fin 8 → ZFSet.{u} =>
      M.structuralRefinementHistory (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7)) where
  formula := M.structuralRefinementHistoryFormula pairing unions powers separation collection
  closed := M.structuralRefinementHistory_mem pairing unions powers separation collection
  correct := fun env members => historyFormula_correct M
    (M.structuralRefinementEntryFormula pairing unions powers separation collection) env members _
    (M.structuralRefinementHistory_mem pairing unions powers separation collection env members)
    (imageMeaning M pairing unions powers separation collection env members)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_StructuralAssignmentActionGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

noncomputable def structuralAssignments (G nodes nodeOrder basis T T2 stages history : ZFSet.{u}) : ZFSet.{u} :=
  stageOneAssignments (refinementDataHistoryIndices stages
    (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history)) T

theorem rawStageRefinementAssignmentActionGraph_bound
    (g G nodes nodeOrder nodeAction basis T T2 stages history level P order top action : ZFSet.{u})
    (hl : level ∈ stages) (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history) :
    M.rawStageRefinementAssignmentActionGraph g P order top action G nodes nodeOrder nodeAction basis T T2 level ⊆
      ZFSet.prod (M.structuralAssignments G nodes nodeOrder basis T T2 stages history)
        (M.structuralAssignments G nodes nodeOrder basis T T2 stages history) := by
  let data := M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level
  have packed : ZFSet.pair level (refinementFormulaDataCode data) ∈
      M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history :=
    (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).2
      ⟨hl, P, order, top, action, stored, rfl⟩
  have includeIndex : data 0 ⊆ refinementDataHistoryIndices stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) := by
    intro i hi
    exact (mem_refinementDataHistoryIndices _ _ _).2 ⟨level, hl, data, packed, hi⟩
  have includeAssignments : stageOneAssignments (data 0) T ⊆
      M.structuralAssignments G nodes nodeOrder basis T T2 stages history := by
    intro x hx
    obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments _ _ _).1 hx
    exact (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨includeIndex hi, hu, hw⟩
  intro z hz
  unfold rawStageRefinementAssignmentActionGraph rawRefinementAssignmentActionGraph relationProduct at hz
  have bound : z ∈ ZFSet.prod (stageOneAssignments (data 0) T) (stageOneAssignments (data 0) T) :=
    (ZFSet.mem_sep.1 hz).1
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 bound
  exact ZFSet.pair_mem_prod.2 ⟨includeAssignments hx, includeAssignments hy⟩

noncomputable def structuralAssignmentActionGraph
    (G nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u}) : ZFSet.{u} :=
  let J := M.structuralAssignments G nodes nodeOrder basis T T2 stages history
  ZFSet.sep (fun z => ∃ g ∈ G, ∃ x y, z = ZFSet.pair (ZFSet.pair g x) y ∧
    ∃ level ∈ stages, ∃ P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
      ZFSet.pair x y ∈ M.rawStageRefinementAssignmentActionGraph g P order top action
        G nodes nodeOrder nodeAction basis T T2 level)
    (ZFSet.prod (ZFSet.prod G J) J)

theorem mem_structuralAssignmentActionGraph
    (G nodes nodeOrder nodeAction basis T T2 stages history z : ZFSet.{u}) :
    z ∈ M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history ↔
      ∃ g ∈ G, ∃ x y, z = ZFSet.pair (ZFSet.pair g x) y ∧
        ∃ level ∈ stages, ∃ P order top action,
          ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
          ZFSet.pair x y ∈ M.rawStageRefinementAssignmentActionGraph g P order top action
            G nodes nodeOrder nodeAction basis T T2 level := by
  rw [structuralAssignmentActionGraph, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨g, hg, x, y, rfl, level, hl, P, order, top, action, stored, edge⟩
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_bound g G nodes nodeOrder nodeAction basis T T2
        stages history level P order top action hl stored edge)
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, bounds.1⟩, bounds.2⟩,
      g, hg, x, y, rfl, level, hl, P, order, top, action, stored, edge⟩

theorem pair_mem_structuralAssignmentActionGraph
    (G nodes nodeOrder nodeAction basis T T2 stages history g x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g x) y ∈
      M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history ↔
      g ∈ G ∧ ∃ level ∈ stages, ∃ P order top action,
        ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
        ZFSet.pair x y ∈ M.rawStageRefinementAssignmentActionGraph g P order top action
          G nodes nodeOrder nodeAction basis T T2 level := by
  rw [M.mem_structuralAssignmentActionGraph]
  constructor
  · rintro ⟨g', hg, x', y', equal, rest⟩
    obtain ⟨first, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
    exact ⟨hg, rest⟩
  · rintro ⟨hg, rest⟩
    exact ⟨g, hg, x, y, rfl, rest⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_StructuralAssignmentActionFormulas
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
variable (collection : CollectionSchema M.sets)

noncomputable def structuralAssignmentEntryFormula : SetFormula 10 :=
  exBlock 10 (.conj witnessBounds.toFormula
    (SetFormula.reindex operationSlots
      (M.definable_rawStageRefinementAssignmentActionGraph pairing unions powers separation collection).formula))

theorem realize_structuralAssignmentEntryFormula (env : Fin 10 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (M.structuralAssignmentEntryFormula pairing unions powers separation collection) env ↔
      env 0 ∈ M.structuralAssignmentActionGraph (env 1) (env 2) (env 3) (env 4)
        (env 5) (env 6) (env 7) (env 8) (env 9) := by
  unfold structuralAssignmentEntryFormula
  rw [realize_exBlock, M.mem_structuralAssignmentActionGraph]
  have meaning (f : Fin 10 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj witnessBounds.toFormula
        (SetFormula.reindex operationSlots
          (M.definable_rawStageRefinementAssignmentActionGraph pairing unions powers separation collection).formula))
          (extendMany 10 f env) ↔
      f 0 ∈ env 1 ∧ env 0 = ZFSet.pair (ZFSet.pair (f 0) (f 1)) (f 2) ∧
        f 3 ∈ env 8 ∧ f 9 ∈ env 9 ∧
        f 9 = ZFSet.pair (f 3) (forcingStageCode (f 4) (f 5) (f 6) (f 7)) ∧
        ZFSet.pair (f 1) (f 2) ∈ f 8 ∧
        f 8 = M.rawStageRefinementAssignmentActionGraph (f 0) (f 4) (f 5) (f 6) (f 7)
          (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7) (f 3) := by
    change (Realize M.sets witnessBounds.toFormula _ ∧ _) ↔ _
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 10 f env ground members)]
    simp only [witnessBounds, BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
      BoundedFormula.truth_nonemptyTupleFormula, BoundedFormula.truth_pairMembershipFormula,
      extendMany_prefix, extendMany_suffix]
    rw [realize_reindex]
    have args : (fun j => extendMany 10 f env (operationSlots j)) =
        extend (f 8) ![f 0,f 4,f 5,f 6,f 7,env 1,env 2,env 3,env 4,env 5,env 6,env 7,f 3] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))))))))) j
    have argGround : ∀ j, (![f 0,f 4,f 5,f 6,f 7,env 1,env 2,env 3,env 4,env 5,env 6,env 7,f 3] : Fin 13 → ZFSet.{u}) j ∈ M.sets :=
      (Fin.cases (ground 0) (Fin.cases (ground 4) (Fin.cases (ground 5) (Fin.cases (ground 6) (Fin.cases (ground 7) (Fin.cases (members 1) (Fin.cases (members 2) (Fin.cases (members 3) (Fin.cases (members 4) (Fin.cases (members 5) (Fin.cases (members 6) (Fin.cases (members 7) (Fin.cases (ground 3) (fun j => Fin.elim0 j))))))))))))))
    rw [args, (M.definable_rawStageRefinementAssignmentActionGraph pairing unions powers separation collection).correct _ argGround _ (ground 8)]
    change ((_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ∧ _) ↔ _
    tauto
  constructor
  · rintro ⟨f, ground, holds⟩
    obtain ⟨hg, equal, hl, source, shape, edge, graph⟩ := (meaning f ground).1 holds
    exact ⟨f 0, hg, f 1, f 2, equal, f 3, hl, f 4, f 5, f 6, f 7, shape ▸ source, graph ▸ edge⟩
  · rintro ⟨g, hg, x, y, equal, level, hl, P, order, top, action, stored, edge⟩
    let source := ZFSet.pair level (forcingStageCode P order top action)
    let graph := M.rawStageRefinementAssignmentActionGraph g P order top action
      (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7) level
    have hSource := M.transitive (members 9) stored
    have fields := M.nonemptyTupleCode_field_mem 4 ![level,P,order,top,action] hSource
    have hOuter : ZFSet.pair (ZFSet.pair g x) y ∈ M.sets := equal ▸ members 0
    have outer := M.nonemptyTupleCode_field_mem 1 ![ZFSet.pair g x,y] hOuter
    have inner := M.nonemptyTupleCode_field_mem 1 ![g,x] (outer 0)
    have hGraph : graph ∈ M.sets :=
      (M.definable_rawStageRefinementAssignmentActionGraph pairing unions powers separation collection).closed
        ![g,P,order,top,action,env 1,env 2,env 3,env 4,env 5,env 6,env 7,level]
        (Fin.cases (inner 0) (Fin.cases (fields 1) (Fin.cases (fields 2) (Fin.cases (fields 3)
          (Fin.cases (fields 4) (Fin.cases (members 1) (Fin.cases (members 2) (Fin.cases (members 3)
            (Fin.cases (members 4) (Fin.cases (members 5) (Fin.cases (members 6)
              (Fin.cases (members 7) (Fin.cases (fields 0) (fun j => Fin.elim0 j))))))))))))))
    let f : Fin 10 → ZFSet.{u} := ![g,x,y,level,P,order,top,action,graph,source]
    have ground : ∀ j, f j ∈ M.sets :=
      Fin.cases (inner 0) (Fin.cases (inner 1) (Fin.cases (outer 1) (Fin.cases (fields 0)
        (Fin.cases (fields 1) (Fin.cases (fields 2) (Fin.cases (fields 3)
          (Fin.cases (fields 4) (Fin.cases hGraph (Fin.cases hSource (fun j => Fin.elim0 j))))))))))
    exact ⟨f, ground, (meaning f ground).2 ⟨hg, equal, hl, stored, rfl, edge, rfl⟩⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundStructuralForcingActionGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def structuralForcingCarrier
    (rows G nodes nodeOrder basis T T2 stages history : ZFSet.{u}) : ZFSet.{u} :=
  M.refinementHistoryForcing rows T stages
    (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

include pairing unions powers separation collection in
theorem structuralForcingCarrier_mem (env : Fin 9 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.structuralForcingCarrier (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7) (env 8) ∈ M.sets :=
  M.refinementHistoryForcing_mem pairing unions powers separation (members 0) (members 5) (members 7)
    ((M.definable_structuralRefinementHistory pairing unions powers separation collection).closed
      (fun j => env j.succ) (fun j => members j.succ)) omega

noncomputable def structuralForcingCarrierFormula {n : Nat}
    (output rows G nodes nodeOrder basis T T2 stages history N : Fin n) : SetFormula n :=
  .ex (.conj
    (reindex (extend 0 ![G.succ, nodes.succ, nodeOrder.succ, basis.succ, T.succ, T2.succ, stages.succ, history.succ])
      (M.definable_structuralRefinementHistory pairing unions powers separation collection).formula)
    (refinementHistoryForcingOutputFormula output.succ rows.succ T.succ stages.succ 0 N.succ))

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

noncomputable def definable_structuralAssignments :
    GroundDefinableFunction M (fun env : Fin 8 → ZFSet.{u} =>
      M.structuralAssignments (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7)) := by
  let v := GroundSetTerm.var M (n := 8)
  let packed := GroundSetTerm.app (M.definable_structuralRefinementHistory pairing unions powers separation collection)
    ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7]
  let indices := GroundSetTerm.app (M.definable_refinementDataHistoryIndices pairing unions powers separation) ![v 6,packed]
  let product (x y : GroundSetTerm M 8) := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![x,y]
  exact (product indices (product (v 4) (v 4))).definition

noncomputable def definable_structuralAssignmentActionGraph :
    GroundDefinableFunction M (fun env : Fin 9 → ZFSet.{u} =>
      M.structuralAssignmentActionGraph (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7) (env 8)) := by
  let v := GroundSetTerm.var M (n := 9)
  let J := GroundSetTerm.app (M.definable_structuralAssignments pairing unions powers separation collection)
    ![v 0,v 1,v 2,v 4,v 5,v 6,v 7,v 8]
  let product (x y : GroundSetTerm M 9) := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![x,y]
  let bound := product (product (v 0) J) J
  let term := GroundSetTerm.app (M.definable_separation separation
    (M.structuralAssignmentEntryFormula pairing unions powers separation collection))
    ![bound,v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8]
  have equal (env : Fin 9 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
      term.eval env = M.structuralAssignmentActionGraph (env 0) (env 1) (env 2) (env 3)
        (env 4) (env 5) (env 6) (env 7) (env 8) := by
    have args : (fun j : Fin 9 => (![bound,v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8] j.succ).eval env) = env := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))))) j
    change ZFSet.sep (fun z => Realize M.sets
      (M.structuralAssignmentEntryFormula pairing unions powers separation collection) (extend z _)) (bound.eval env) = _
    rw [args]
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, holds⟩
      exact (M.realize_structuralAssignmentEntryFormula pairing unions powers separation collection
        (extend z env) (Fin.cases (M.transitive (bound.ground env members) hz) members)).1 holds
    · intro member
      have raw := member
      unfold structuralAssignmentActionGraph at raw
      have hz : z ∈ bound.eval env := (ZFSet.mem_sep.1 raw).1
      exact ⟨hz, (M.realize_structuralAssignmentEntryFormula pairing unions powers separation collection
        (extend z env) (Fin.cases (M.transitive (bound.ground env members) hz) members)).2 member⟩
  exact { formula := term.definition.formula
          closed := fun env members => equal env members ▸ term.ground env members
          correct := fun env members z hz => (term.correct env members z hz).trans
            (congrArg (fun x => z = x) (equal env members)).to_iff }

include pairing unions powers separation collection in
theorem structuralAssignmentActionGraph_mem {G nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u}}
    (hG : G ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets) (hna : nodeAction ∈ M.sets)
    (hb : basis ∈ M.sets) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (hs : stages ∈ M.sets) (hh : history ∈ M.sets) :
    M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history ∈ M.sets :=
  (M.definable_structuralAssignmentActionGraph pairing unions powers separation collection).closed
    ![G,nodes,nodeOrder,nodeAction,basis,T,T2,stages,history]
    (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hna (Fin.cases hb (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j))))))))))

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem structuralForcingActionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {rows rowAction G nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hRowAction : rowAction ∈ M.sets)
    (hG : G ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets)
    (hna : nodeAction ∈ M.sets) (hb : basis ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    rawRowAssignmentActionGraph G
      (M.structuralForcingCarrier rows G nodes nodeOrder basis T T2 stages history) rows
      (M.structuralForcingCarrier rows G nodes nodeOrder basis T T2 stages history).sUnion.sUnion
      (M.structuralAssignments G nodes nodeOrder basis T T2 stages history) rowAction
      (M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history) ∈ M.sets := by
  have hQ := M.structuralForcingCarrier_mem pairing unions powers separation collection
    ![rows,G,nodes,nodeOrder,basis,T,T2,stages,history]
    (Fin.cases hRows (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))) omega
  have hJ := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![G,nodes,nodeOrder,basis,T,T2,stages,history]
    (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb (Fin.cases hT
      (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hF := M.structuralAssignmentActionGraph_mem pairing unions powers separation collection
    hG hn hno hna hb hT hT2 hs hh
  exact M.rawRowAssignmentActionGraph_mem pairing unions powers separation collection
    hG hQ hRows (M.union_mem unions (M.union_mem unions hQ)) hJ hRowAction hF

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRecursiveRowNameActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {R : Type u} (c : Presentation R)
variable {T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M c.carrier T stages history)
variable (ordinal : ordinalSetProperty stages) (carrier : c.carrier ∈ M.sets)
local notation "Q" => M.refinementHistoryForcing c.carrier T stages history
local notation "pres" => SetMembers.presentation Q

noncomputable def refinementHistoryRowInclusion (p : R) : SetMembers Q :=
  SetMembers.ofMem (ZFSet.pair (c.encode p) ∅)
    (run.empty_assignments ordinal carrier (c.encode_mem p))

local notation "incl" => M.refinementHistoryRowInclusion c run ordinal carrier

theorem refinementHistoryRowInclusion_encode (p : R) :
    (pres).encode (incl p) = c.pairEmpty.encode p :=
  SetMembers.raw_ofMem _ _

noncomputable def refinementHistoryRowNameLift (tau : Name c.pairEmpty) : Name (pres) :=
  Name.rename (pres) incl tau

local notation "liftName" => M.refinementHistoryRowNameLift c run ordinal carrier
include run ordinal carrier

theorem refinementHistoryRowNameLift_val (tau : Name c.pairEmpty) :
    (liftName tau).val = tau.val :=
  Name.rename_val_of_encode (pres) incl
    (M.refinementHistoryRowInclusion_encode c run ordinal carrier) tau

theorem refinementHistoryRowNameFamily_valid (X : ZFSet.{u})
    (valid : ∀ z ∈ X, IsName c.pairEmpty z) :
    ∀ z ∈ X, IsName (pres) z := by
  intro z hz
  have lifted := (liftName ⟨z, valid z hz⟩).property
  exact (congrArg (IsName (pres))
    (M.refinementHistoryRowNameLift_val c run ordinal carrier ⟨z, valid z hz⟩)).mp lifted

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {R : Type u} (c : Presentation R)
variable {T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M c.carrier T stages history)
variable (ordinal : ordinalSetProperty stages) (carrier : c.carrier ∈ M.sets)
local notation "Q" => M.refinementHistoryForcing c.carrier T stages history
local notation "pres" => SetMembers.presentation Q
local notation "incl" => M.refinementHistoryRowInclusion c run ordinal carrier
local notation "liftName" => M.refinementHistoryRowNameLift c run ordinal carrier
variable {G : Type v} [Group G] [PartialOrder R]
variable [PartialOrder (SetMembers (M.refinementHistoryForcing c.carrier T stages history))]
variable (a : PosetAction G R)
variable (e : PosetAction G (SetMembers (M.refinementHistoryForcing c.carrier T stages history)))
variable (image : G → ZFSet.{u} → ZFSet.{u})
variable (coordinates : ∀ (g : G)
  (q : SetMembers (M.refinementHistoryForcing c.carrier T stages history)) (row : R) (A : ZFSet.{u}),
  SetMembers.raw q = ZFSet.pair (c.encode row) A →
  SetMembers.raw (e.iso g q) = ZFSet.pair (c.encode (a.iso g row)) (image g A))
variable (emptyImage : ∀ g, image g ∅ = ∅)
include run ordinal carrier coordinates emptyImage

theorem refinementHistoryRowInclusion_equivariant (g : G) (p : R) :
    e.iso g (incl p) = incl (a.iso g p) := by
  apply SetMembers.raw_injective Q
  have encoded := M.refinementHistoryRowInclusion_encode c run ordinal carrier p
  change SetMembers.raw (incl p) = ZFSet.pair (c.encode p) ∅ at encoded
  rw [coordinates g (incl p) p ∅ encoded, emptyImage]
  exact (M.refinementHistoryRowInclusion_encode c run ordinal carrier (a.iso g p)).symm

theorem refinementHistoryRowNameLift_act (g : G) (tau : Name c.pairEmpty) :
    e.act (pres) g (liftName tau) = liftName (a.act c.pairEmpty g tau) :=
  a.act_rename_of_equivariant e c.pairEmpty (pres) incl
    (fun g p => (M.refinementHistoryRowInclusion_equivariant c run ordinal carrier
      a e image coordinates emptyImage g p).symm) g tau

theorem refinementHistoryRowNameLift_hs (F : NormalSubgroupFamily G) (tau : Name c.pairEmpty)
    (hs : HereditarilySymmetric a c.pairEmpty F tau) :
    HereditarilySymmetric e (pres) F (liftName tau) :=
  hs.rename e (pres) incl
    (fun g p => (M.refinementHistoryRowInclusion_equivariant c run ordinal carrier
      a e image coordinates emptyImage g p).symm)

theorem refinementHistoryRowNameFamily_transport (F : NormalSubgroupFamily G) (X : ZFSet.{u})
    (valid : ∀ z ∈ X, IsName c.pairEmpty z)
    (closed : ∀ g (tau : Name c.pairEmpty), tau.val ∈ X → (a.act c.pairEmpty g tau).val ∈ X)
    (symmetric : ∀ tau : Name c.pairEmpty, tau.val ∈ X → HereditarilySymmetric a c.pairEmpty F tau) :
    (∀ z ∈ X, IsName (pres) z) ∧
      (∀ g (tau : Name (pres)), tau.val ∈ X → (e.act (pres) g tau).val ∈ X) ∧
      (∀ tau : Name (pres), tau.val ∈ X → HereditarilySymmetric e (pres) F tau) := by
  refine ⟨M.refinementHistoryRowNameFamily_valid c run ordinal carrier X valid, ?_, ?_⟩
  · intro g tau member
    let sigma : Name c.pairEmpty := ⟨tau.val, valid tau.val member⟩
    have same : liftName sigma = tau := Subtype.ext
      (M.refinementHistoryRowNameLift_val c run ordinal carrier sigma)
    rw [← same, M.refinementHistoryRowNameLift_act c run ordinal carrier a e image coordinates emptyImage,
      M.refinementHistoryRowNameLift_val c run ordinal carrier]
    exact closed g sigma member
  · intro tau member
    let sigma : Name c.pairEmpty := ⟨tau.val, valid tau.val member⟩
    have same : liftName sigma = tau := Subtype.ext
      (M.refinementHistoryRowNameLift_val c run ordinal carrier sigma)
    rw [← same]
    exact M.refinementHistoryRowNameLift_hs c run ordinal carrier a e image coordinates emptyImage
      F sigma (symmetric sigma member)

end PartitionPilot.Forcing.TransitiveGround

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
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {rows rowOrder : ZFSet.{u}}
variable (order : PartialOrderCode rows rowOrder) (T stages history : ZFSet.{u})

theorem refinementHistoryDecodedOrder_eq :
    letI := M.refinementHistoryPartialOrder order T stages history
    (SetMembers.presentation (M.refinementHistoryForcing rows T stages history)).conditionOrder =
      M.refinementHistoryOrder rows rowOrder T stages history :=
  (M.refinementHistoryOrder_partialOrder order T stages history).conditionOrder_eq

theorem refinementHistoryDecodedTop_eq
    (run : RecursiveRefinementDataHistory M rows T stages history)
    (ordinal : ordinalSetProperty stages) (hRows : rows ∈ M.sets)
    (top : ZFSet.{u}) (topMem : top ∈ rows)
    (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder) :
    letI := M.refinementHistoryPartialOrder order T stages history
    letI := M.refinementHistoryOrderTop order T stages history run ordinal hRows top topMem topRows
    (SetMembers.presentation (M.refinementHistoryForcing rows T stages history)).encode ⊤ = ZFSet.pair top ∅ :=
  SetMembers.raw_ofMem _ _

end TransitiveGround

end

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]

theorem recursiveRefinementStageSystem
    (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
    (b : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 stages history : ZFSet.{u})
    (run : RecursiveRefinementDataHistory M c.carrier T stages history)
    (ordinal : ordinalSetProperty stages)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : c.carrier ∈ M.sets) (order : c.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (nodeOrder : b.conditionOrder ∈ M.sets)
    (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets)
    (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
    (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
      HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
    (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
      HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
    (top : ZFSet.{u}) (topMem : top ∈ c.carrier)
    (topRows : ∀ row ∈ c.carrier, ZFSet.pair row top ∈ c.conditionOrder) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages history
      run ordinal carrier top topMem topRows
    ∀ (e : PosetAction G (SetMembers (M.refinementHistoryForcing c.carrier T stages history)))
      (image : G → ZFSet.{u} → ZFSet.{u}),
      (∀ g (q : SetMembers (M.refinementHistoryForcing c.carrier T stages history)) row A,
        SetMembers.raw q = ZFSet.pair (c.encode row) A →
        SetMembers.raw (e.iso g q) = ZFSet.pair (c.encode (a.iso g row)) (image g A)) →
      (∀ g, image g ∅ = ∅) →
      e.actionGraph (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history)) t ∈ M.sets →
      RefinementStageSystem M e
        (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history))
        t b d base directed stages T T2 := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages history
    run ordinal carrier top topMem topRows
  intro e image coordinates emptyImage actionGround
  have nextCarrier : (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history)).carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hStages hHistory omega
  have nextOrder : (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history)).conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier order hT hStages hHistory omega
  have maps := M.conditionMapFamily_mem_of_actionGraph e
    (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history)) t
    pairing unions powers separation collection nextCarrier group actionGround
  obtain ⟨nextValid1, nextClosed1, nextHS1⟩ :=
    M.refinementHistoryRowNameFamily_transport c run ordinal carrier a e image coordinates emptyImage
      (d.principalSupportFamily base directed) T valid1 closed1 symmetric1
  obtain ⟨nextValid2, nextClosed2, nextHS2⟩ :=
    M.refinementHistoryRowNameFamily_transport c run ordinal carrier a e image coordinates emptyImage
      (d.principalSupportFamily base directed) T2 valid2 closed2 symmetric2
  exact M.refinementStageSystem e
    (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history)) t b d base directed
    pairing unions powers separation collection nextCarrier nextOrder group nodes nodeOrder maps nodeMaps supports
    hStages hT hT2 nextValid1 nextValid2 nextClosed1 nextClosed2 nextHS1 nextHS2

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {R : Type u}
variable (c : Presentation R) (T stages history : ZFSet.{u})
local notation "Q" => M.refinementHistoryForcing c.carrier T stages history
local notation "upper" => SetMembers.presentation Q

theorem rowCarrier_shape : Q ⊆ ZFSet.prod c.carrier (Q).sUnion.sUnion := by
  intro z hz
  obtain ⟨row, hrow, A, _, code⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages history hz)
  rw [code] at hz ⊢
  exact ZFSet.pair_mem_prod.2 ⟨hrow, pair_second_mem_doubleUnion hz⟩

noncomputable def refinementHistoryRowFunction : SetMembers Q → R :=
  (upper).decodeFunction c (rowAssignmentRows Q c.carrier (Q).sUnion.sUnion)
    (rowAssignmentRows_function (M.rowCarrier_shape c T stages history))

theorem refinementHistoryRowFunction_code (p : SetMembers Q) (row : R) (A : ZFSet.{u})
    (code : SetMembers.raw p = ZFSet.pair (c.encode row) A) :
    M.refinementHistoryRowFunction c T stages history p = row := by
  have entry := (upper).decodeFunction_mem c (rowAssignmentRows Q c.carrier (Q).sUnion.sUnion)
    (rowAssignmentRows_function (M.rowCarrier_shape c T stages history)) p
  change ZFSet.pair (SetMembers.raw p)
    (c.encode (M.refinementHistoryRowFunction c T stages history p)) ∈ _ at entry
  rw [code] at entry
  apply c.injective
  exact ((rowAssignmentRows_entry Q c.carrier (Q).sUnion.sUnion (c.encode row) A _).1 entry).2.2.2

theorem refinementHistoryRowFunction_coordinates (p : SetMembers Q) :
    ∃ A, SetMembers.raw p =
      ZFSet.pair (c.encode (M.refinementHistoryRowFunction c T stages history p)) A := by
  obtain ⟨row, hrow, A, _, code⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages history (SetMembers.raw_mem p))
  obtain ⟨r, rfl⟩ := (c.mem_carrier row).1 hrow
  exact ⟨A, (M.refinementHistoryRowFunction_code c T stages history p r A code).symm ▸ code⟩

variable [PartialOrder R]

noncomputable def refinementHistoryRowRestriction :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    SetMembers Q →o R := by
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  refine { toFun := M.refinementHistoryRowFunction c T stages history, monotone' := ?_ }
  intro p q below
  obtain ⟨A, pCode⟩ := M.refinementHistoryRowFunction_coordinates c T stages history p
  obtain ⟨B, qCode⟩ := M.refinementHistoryRowFunction_coordinates c T stages history q
  change ZFSet.pair (SetMembers.raw p) (SetMembers.raw q) ∈ _ at below
  rw [pCode, qCode] at below
  exact (c.pair_mem_conditionOrder _ _).1
    ((M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages history _ _ _ _).1 below).2.2.1

variable (run : RecursiveRefinementOrderHistory M c.carrier c.conditionOrder T stages history)
variable (ordinal : ordinalSetProperty stages) (carrier : c.carrier ∈ M.sets)
local notation "incl" => M.refinementHistoryRowInclusion c run.carriers ordinal carrier

noncomputable def refinementHistoryRowEmbedding :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    R ↪o SetMembers Q := by
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  have incRaw : ∀ p : R, SetMembers.raw (incl p) = ZFSet.pair (c.encode p) ∅ :=
    M.refinementHistoryRowInclusion_encode c run.carriers ordinal carrier
  refine { toFun := incl, inj' := ?_, map_rel_iff' := ?_ }
  · intro p q equal
    apply c.injective
    have raw := congrArg SetMembers.raw equal
    rw [incRaw p, incRaw q] at raw
    exact (ZFSet.pair_injective raw).1
  · intro p q
    change ZFSet.pair (SetMembers.raw (incl p)) (SetMembers.raw (incl q)) ∈ _ ↔ p ≤ q
    rw [incRaw p, incRaw q, M.pair_mem_refinementHistoryOrder]
    have hp := SetMembers.raw_mem (incl p)
    have hq := SetMembers.raw_mem (incl q)
    rw [incRaw p] at hp
    rw [incRaw q] at hq
    constructor
    · intro below
      exact (c.pair_mem_conditionOrder _ _).1 below.2.2.1
    · intro below
      exact ⟨hp, hq, (c.pair_mem_conditionOrder _ _).2 below, fun _ hz => hz⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RecursiveStructuralRefinementHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder basis T T2 rows rowOrder stages history : ZFSet.{u})

 theorem structuralRefinementHistory_recursiveOrder
    (ordinal : ordinalSetProperty stages) (function : FunctionGraphOn stages history)
    (shape : ∀ level ∈ stages, ∃ P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history)
    (equations : ∀ level P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      P = M.refinementHistoryForcing rows T level
        (M.structuralRefinementHistory G nodes nodeOrder basis T T2 level (graphRestriction level history)) ∧
      order = M.refinementHistoryOrder rows rowOrder T level
        (M.structuralRefinementHistory G nodes nodeOrder basis T T2 level (graphRestriction level history))) :
    RecursiveRefinementOrderHistory M rows rowOrder T stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) := by
  have prefixes {level : ZFSet.{u}} (hl : level ∈ stages) :
      M.structuralRefinementHistory G nodes nodeOrder basis T T2 level (graphRestriction level history) =
      graphRestriction level (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) := by
    rw [M.structuralRefinementHistory_history_restrict,
      M.structuralRefinementHistory_domain_restrict G nodes nodeOrder basis T T2 (ordinal.1 level hl)]
  refine ⟨⟨M.structuralRefinementHistory_dataHistory G nodes nodeOrder basis T T2 stages history function shape, ?_⟩, ?_⟩
  · intro level data entry
    obtain ⟨hl, P, order, top, action, stored, rfl⟩ :=
      M.structuralRefinementHistory_fields G nodes nodeOrder basis T T2 stages history data entry
    exact (equations level P order top action stored).1.trans
      (congrArg (M.refinementHistoryForcing rows T level) (prefixes hl))
  · intro level data entry
    obtain ⟨hl, P, order, top, action, stored, rfl⟩ :=
      M.structuralRefinementHistory_fields G nodes nodeOrder basis T T2 stages history data entry
    exact (equations level P order top action stored).2.trans
      (congrArg (M.refinementHistoryOrder rows rowOrder T level) (prefixes hl))

theorem structuralRefinementHistory_recursiveOrder_of_trace
    {step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
    (ordinal : ordinalSetProperty stages) (trace : OrdinalRecursionTrace step stages history)
    (correct : ∀ level prior stage, step level prior stage → ∃ top action,
      stage = forcingStageCode
        (M.refinementHistoryForcing rows T level
          (M.structuralRefinementHistory G nodes nodeOrder basis T T2 level prior))
        (M.refinementHistoryOrder rows rowOrder T level
          (M.structuralRefinementHistory G nodes nodeOrder basis T T2 level prior)) top action) :
    RecursiveRefinementOrderHistory M rows rowOrder T stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) := by
  apply M.structuralRefinementHistory_recursiveOrder G nodes nodeOrder basis T T2 rows rowOrder stages history ordinal trace.1
  · intro level hl
    obtain ⟨stage, stored⟩ := trace.1.total hl
    obtain ⟨top, action, equal⟩ := correct level _ stage (trace.2 level hl stage stored)
    exact ⟨_, _, top, action, equal ▸ stored⟩
  · intro level P order top action stored
    obtain ⟨top', action', equal⟩ := correct level _ _
      (trace.2 level (trace.1.pair_source stored) _ stored)
    have fields := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 equal
    exact ⟨fields.1, fields.2.1⟩

end PartitionPilot.Forcing.TransitiveGround

end

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

noncomputable def structuralForcingStageFromCarrier
    (Q rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u}) : ZFSet.{u} :=
  rawFlatForcingStage Q rows rowOrder rowTop rowAction G
    (M.structuralAssignments G nodes nodeOrder basis T T2 stages history)
    (M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history)

noncomputable def definable_structuralForcingStageFromCarrier
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 14 → ZFSet.{u} =>
      M.structuralForcingStageFromCarrier (env 0) (env 1) (env 2) (env 3) (env 4)
        (env 5) (env 6) (env 7) (env 8) (env 9) (env 10) (env 11) (env 12) (env 13)) := by
  let v := GroundSetTerm.var M (n := 14)
  let assignments := GroundSetTerm.app (M.definable_structuralAssignments pairing unions powers separation collection)
    ![v 5, v 6, v 7, v 9, v 10, v 11, v 12, v 13]
  let action := GroundSetTerm.app (M.definable_structuralAssignmentActionGraph pairing unions powers separation collection)
    ![v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13]
  exact (GroundSetTerm.app (M.definable_rawFlatForcingStage pairing unions powers separation collection)
    ![v 0, v 1, v 2, v 3, v 4, v 5, assignments, action]).definition





noncomputable def structuralForcingStage
    (rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u}) : ZFSet.{u} :=
  M.structuralForcingStageFromCarrier
    (M.structuralForcingCarrier rows G nodes nodeOrder basis T T2 stages history)
    rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 stages history

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G L : Type u}
variable [Group G] [PartialOrder L]
variable (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
variable (rows rowOrder rowTop rowAction T T2 : ZFSet.{u})
local notation "step" => fun level prior output =>
  output = M.structuralForcingStage rows rowOrder rowTop rowAction t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior

theorem structuralTrace_prefix_ground
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    {stages history : ZFSet.{u}} (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages) (trace : OrdinalRecursionTrace step stages history)
    {level P order top action : ZFSet.{u}}
    (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history) :
    level ∈ M.sets ∧ ordinalSetProperty level ∧ graphRestriction level history ∈ M.sets ∧
      OrdinalRecursionTrace step level (graphRestriction level history) ∧
      P ∈ M.sets ∧ order ∈ M.sets ∧ top ∈ M.sets ∧ action ∈ M.sets := by
  have member := trace.1.pair_source stored
  have hLevel := M.transitive hStages member
  have levelOrdinal := ordinalSetProperty_member ordinal member
  have codeGround := M.transitive (M.union_mem unions (M.union_mem unions hHistory))
    (pair_second_mem_doubleUnion stored)
  exact ⟨hLevel, levelOrdinal, M.graphRestriction_mem unions separation hLevel hHistory,
    trace.restrict levelOrdinal (ordinal.1 level member), M.forcingStageCode_fields codeGround⟩

theorem structuralTrace_stageWitnesses
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (current : ∀ level prior, level ∈ M.sets → prior ∈ M.sets → ordinalSetProperty level →
      OrdinalRecursionTrace step level prior →
      (∀ earlier P order top action, ZFSet.pair earlier (forcingStageCode P order top action) ∈ prior →
        RawRefinementStageWitness M t b d base directed T T2 earlier P order top action) →
      ∀ P order top action,
        forcingStageCode P order top action =
          M.structuralForcingStage rows rowOrder rowTop rowAction t.carrier b.carrier b.conditionOrder
            (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior →
        RawRefinementStageWitness M t b d base directed T T2 level P order top action)
    {stages history : ZFSet.{u}} (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages) (trace : OrdinalRecursionTrace step stages history) :
    ∀ level P order top action, ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      RawRefinementStageWitness M t b d base directed T T2 level P order top action := by
  intro level
  induction level using ZFSet.inductionOn with
  | h level ih =>
    intro P order top action stored
    obtain ⟨hLevel, levelOrdinal, hPrefix, prefixTrace, _fields⟩ :=
      M.structuralTrace_prefix_ground t b d rows rowOrder rowTop rowAction T T2
        unions separation hStages hHistory ordinal trace stored
    apply current level (graphRestriction level history) hLevel hPrefix levelOrdinal prefixTrace
    · intro earlier P' order' top' action' entry
      have prefixEntry := pair_mem_graphRestriction.1 entry
      exact ih earlier prefixEntry.2 P' order' top' action' prefixEntry.1
    · exact trace.2 level (trace.1.pair_source stored) _ stored

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})

theorem structuralForcingStage_eq (stages history : ZFSet.{u}) :
    M.structuralForcingStage rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 stages history =
    forcingStageCode
      (M.refinementHistoryForcing rows T stages
        (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history))
      (M.refinementHistoryOrder rows rowOrder T stages
        (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history))
      (ZFSet.pair rowTop ∅)
      (rawRowAssignmentActionGraph G
        (M.structuralForcingCarrier rows G nodes nodeOrder basis T T2 stages history)
        rows (⋃₀ ⋃₀ (M.structuralForcingCarrier rows G nodes nodeOrder basis T T2 stages history))
        (M.structuralAssignments G nodes nodeOrder basis T T2 stages history) rowAction
        (M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history)) := by
  unfold structuralForcingStage structuralForcingStageFromCarrier rawFlatForcingStage structuralForcingCarrier
  rw [M.refinementHistoryOrder_raw]

theorem structuralForcingTrace_recursiveOrder {stages history : ZFSet.{u}}
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace
      (fun level prior stage => stage = M.structuralForcingStage rows rowOrder rowTop rowAction
        G nodes nodeOrder nodeAction basis T T2 level prior) stages history) :
    RecursiveRefinementOrderHistory M rows rowOrder T stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) := by
  apply M.structuralRefinementHistory_recursiveOrder_of_trace G nodes nodeOrder basis T T2
    rows rowOrder stages history ordinal trace
  intro level prior stage equal
  exact ⟨_, _, equal.trans (M.structuralForcingStage_eq rows rowOrder rowTop rowAction G nodes
    nodeOrder nodeAction basis T T2 level prior)⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_StructuralPreparationSourceImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

theorem rawStageRefinementAssignmentActionGraph_branch_bound
    (g P order top action G nodes nodeOrder nodeAction basis T T2 level : ZFSet.{u}) :
    M.rawStageRefinementAssignmentActionGraph g P order top action G nodes nodeOrder nodeAction basis T T2 level ⊆
      ZFSet.prod
        (stageOneAssignments (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T)
        (stageOneAssignments (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T) := by
  intro z member
  unfold rawStageRefinementAssignmentActionGraph rawRefinementAssignmentActionGraph relationProduct at member
  exact (ZFSet.mem_sep.1 member).1

variable (G nodes nodeOrder basis T T2 : ZFSet.{u})

theorem mem_structuralAssignments (stages history x : ZFSet.{u}) :
    x ∈ M.structuralAssignments G nodes nodeOrder basis T T2 stages history ↔
      ∃ level ∈ stages, ∃ P order top action,
        ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
        x ∈ stageOneAssignments
          (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T := by
  rw [structuralAssignments, mem_stageOneAssignments]
  constructor
  · rintro ⟨i, hi, u, hu, w, hw, rfl⟩
    obtain ⟨level, hl, data, entry, member⟩ := (mem_refinementDataHistoryIndices _ _ _).1 hi
    obtain ⟨_, P, order, top, action, stored, rfl⟩ :=
      M.structuralRefinementHistory_fields G nodes nodeOrder basis T T2 stages history data entry
    exact ⟨level, hl, P, order, top, action, stored,
      (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨member, hu, hw⟩⟩
  · rintro ⟨level, hl, P, order, top, action, stored, member⟩
    obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments _ _ _).1 member
    refine ⟨i, ?_, u, hu, w, hw, rfl⟩
    exact (mem_refinementDataHistoryIndices _ _ _).2
      ⟨level, hl, M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level,
        (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).2
          ⟨hl, P, order, top, action, stored, rfl⟩, hi⟩

theorem structuralAssignment_branch_unique {stages history level other P order top action
    P' order' top' action' x : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history)
    (stored' : ZFSet.pair other (forcingStageCode P' order' top' action') ∈ history)
    (member : x ∈ stageOneAssignments
      (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T)
    (member' : x ∈ stageOneAssignments
      (M.rawRefinementFormulaData P' order' top' action' G nodes nodeOrder basis T T2 other 0) T) :
    level = other ∧ P = P' ∧ order = order' ∧ top = top' ∧ action = action' := by
  obtain ⟨i, hi, u, _hu, w, _hw, rfl⟩ := (mem_stageOneAssignments _ _ _).1 member
  have hi' := ((stageOneAssignment_mem_assignments _ _ _ _ _).1 member').1
  obtain ⟨v, eqv, hv⟩ := M.rawRefinementFormulaData_level P order top action G nodes nodeOrder basis T T2 level i hi
  obtain ⟨v', eqv', hv'⟩ := M.rawRefinementFormulaData_level P' order' top' action' G nodes nodeOrder basis T T2 other i hi'
  have fields := nonemptyTupleCode_injective 5 (eqv.symm.trans eqv')
  have equal : level = other := hv.symm.trans ((congrFun fields 0).trans hv')
  rw [← equal] at stored'
  exact ⟨equal, (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 (function.unique stored stored')⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u})
local notation "J" => M.structuralAssignments G nodes nodeOrder basis T T2 stages history
local notation "graph" => M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history

noncomputable def structuralAssignmentImage (g A : ZFSet.{u}) : ZFSet.{u} :=
  relationImage A J (rawActionSection g graph J)

theorem structuralAssignmentImage_subset (g A : ZFSet.{u}) :
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A ⊆ J :=
  fun y hy => ((mem_relationImage A J (rawActionSection g graph J) y).1 hy).1

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder basis T T2 : ZFSet.{u})

theorem structuralAssignmentLevels_entry (stages history x level : ZFSet.{u}) :
    ZFSet.pair x level ∈ refinementDataHistoryLevels stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) T ↔
      level ∈ stages ∧ ∃ P order top action,
        ZFSet.pair level (forcingStageCode P order top action) ∈ history ∧
        x ∈ stageOneAssignments
          (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T := by
  rw [pair_mem_refinementDataHistoryLevels]
  constructor
  · rintro ⟨i, hi, u, hu, w, hw, rfl, hl, fields, eqFields, levelEq⟩
    obtain ⟨other, _ho, data, entry, member⟩ := (mem_refinementDataHistoryIndices _ _ _).1 hi
    obtain ⟨_, P, order, top, action, stored, rfl⟩ :=
      M.structuralRefinementHistory_fields G nodes nodeOrder basis T T2 stages history data entry
    obtain ⟨v, eqv, hv⟩ :=
      M.rawRefinementFormulaData_level P order top action G nodes nodeOrder basis T T2 other i member
    have tupleEq := nonemptyTupleCode_injective 5 (eqFields.symm.trans eqv)
    have same : level = other := levelEq.trans ((congrFun tupleEq 0).trans hv)
    cases same
    exact ⟨hl, P, order, top, action, stored,
      (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨member, hu, hw⟩⟩
  · rintro ⟨hl, P, order, top, action, stored, member⟩
    obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments _ _ _).1 member
    obtain ⟨v, eqv, hv⟩ :=
      M.rawRefinementFormulaData_level P order top action G nodes nodeOrder basis T T2 level i hi
    refine ⟨i, ?_, u, hu, w, hw, rfl, hl, v, eqv, hv.symm⟩
    exact (mem_refinementDataHistoryIndices _ _ _).2
      ⟨level, hl, M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level,
        (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).2
          ⟨hl, P, order, top, action, stored, rfl⟩, hi⟩

theorem structuralAssignments_cut_eq {stages earlier : ZFSet.{u}}
    (subset : earlier ⊆ stages) (history A : ZFSet.{u}) :
    assignmentCut (refinementDataHistoryLevels stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) T) earlier A =
        ZFSet.sep (fun x => x ∈ M.structuralAssignments G nodes nodeOrder basis T T2 earlier history) A := by
  apply ZFSet.ext
  intro x
  rw [mem_assignmentCut, ZFSet.mem_sep, M.mem_structuralAssignments]
  constructor
  · rintro ⟨member, level, hl, edge⟩
    obtain ⟨_, P, order, top, action, stored, branch⟩ :=
      (M.structuralAssignmentLevels_entry G nodes nodeOrder basis T T2 stages history x level).1 edge
    exact ⟨member, level, hl, P, order, top, action, stored, branch⟩
  · rintro ⟨member, level, hl, P, order, top, action, stored, branch⟩
    exact ⟨member, level, hl,
      (M.structuralAssignmentLevels_entry G nodes nodeOrder basis T T2 stages history x level).2
        ⟨subset hl, P, order, top, action, stored, branch⟩⟩

theorem structuralAssignments_history_restrict (stages history : ZFSet.{u}) :
    M.structuralAssignments G nodes nodeOrder basis T T2 stages (graphRestriction stages history) =
      M.structuralAssignments G nodes nodeOrder basis T T2 stages history := by
  apply ZFSet.ext
  intro x
  rw [M.mem_structuralAssignments, M.mem_structuralAssignments]
  constructor
  · rintro ⟨level, hl, P, order, top, action, stored, member⟩
    exact ⟨level, hl, P, order, top, action, (pair_mem_graphRestriction.1 stored).1, member⟩
  · rintro ⟨level, hl, P, order, top, action, stored, member⟩
    exact ⟨level, hl, P, order, top, action, pair_mem_graphRestriction.2 ⟨stored, hl⟩, member⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable {G nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u}}
variable (hG : G ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets)
variable (hna : nodeAction ∈ M.sets) (hb : basis ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
local notation "J" => M.structuralAssignments G nodes nodeOrder basis T T2 stages history
local notation "graph" => M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history

include pairing unions powers separation collection hG hn hno hna hb hT hT2 hs hh in
theorem structuralAssignmentSection_mem {g : ZFSet.{u}} (hg : g ∈ M.sets) :
    rawActionSection g graph J ∈ M.sets := by
  have hJ := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![G,nodes,nodeOrder,basis,T,T2,stages,history]
    (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb (Fin.cases hT
      (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hF := M.structuralAssignmentActionGraph_mem pairing unions powers separation collection
    hG hn hno hna hb hT hT2 hs hh
  exact (M.definable_rawActionSection pairing unions powers separation).closed ![g,graph,J]
    (Fin.cases hg (Fin.cases hF (Fin.cases hJ (fun j => Fin.elim0 j))))

include pairing unions powers separation collection hG hn hno hna hb hT hT2 hs hh in
theorem structuralAssignmentImage_small (omega : ZFSet.omega ∈ M.sets)
    {g A : ZFSet.{u}} (hg : g ∈ M.sets)
    (injection : InjectionCode J J (rawActionSection g graph J))
    (member : A ∈ M.groundSmallSubsets J ZFSet.omega) :
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A ∈
      M.groundSmallSubsets J ZFSet.omega := by
  obtain ⟨hA, subset, small⟩ := (M.mem_groundSmallSubsets J ZFSet.omega A).1 member
  have hJ := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![G,nodes,nodeOrder,basis,T,T2,stages,history]
    (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb (Fin.cases hT
      (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hF := M.structuralAssignmentSection_mem pairing unions powers separation collection
    hG hn hno hna hb hT hT2 hs hh hg
  exact (M.mem_groundSmallSubsets J ZFSet.omega _).2
    ⟨M.relationImage_mem separation hA hJ hF,
      M.structuralAssignmentImage_subset G nodes nodeOrder nodeAction basis T T2 stages history g A,
      M.groundEmbeddable_image pairing unions powers separation hA hJ omega hF injection subset small⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})

theorem structuralAssignmentActionGraph_history_restrict (stages history : ZFSet.{u}) :
    M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages (graphRestriction stages history) =
      M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history := by
  apply ZFSet.ext
  intro z
  rw [M.mem_structuralAssignmentActionGraph, M.mem_structuralAssignmentActionGraph]
  constructor
  · rintro ⟨g, hg, x, y, equal, level, hl, P, order, top, action, stored, edge⟩
    exact ⟨g, hg, x, y, equal, level, hl, P, order, top, action,
      (pair_mem_graphRestriction.1 stored).1, edge⟩
  · rintro ⟨g, hg, x, y, equal, level, hl, P, order, top, action, stored, edge⟩
    exact ⟨g, hg, x, y, equal, level, hl, P, order, top, action,
      pair_mem_graphRestriction.2 ⟨stored, hl⟩, edge⟩

theorem structuralAssignmentActionGraph_prefix_entry {stages earlier history : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (subset : earlier ⊆ stages) (g x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g x) y ∈
      M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 earlier history ↔
      ZFSet.pair (ZFSet.pair g x) y ∈
        M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history ∧
      x ∈ M.structuralAssignments G nodes nodeOrder basis T T2 earlier history := by
  constructor
  · intro edge
    obtain ⟨hg, level, hl, P, order, top, action, stored, branch⟩ :=
      (M.pair_mem_structuralAssignmentActionGraph _ _ _ _ _ _ _ _ _ _ _ _).1 edge
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_branch_bound g P order top action
        G nodes nodeOrder nodeAction basis T T2 level branch)
    exact ⟨(M.pair_mem_structuralAssignmentActionGraph _ _ _ _ _ _ _ _ _ _ _ _).2
      ⟨hg, level, subset hl, P, order, top, action, stored, branch⟩,
      (M.mem_structuralAssignments G nodes nodeOrder basis T T2 earlier history x).2
        ⟨level, hl, P, order, top, action, stored, bounds.1⟩⟩
  · rintro ⟨edge, source⟩
    obtain ⟨hg, level, _hl, P, order, top, action, stored, branch⟩ :=
      (M.pair_mem_structuralAssignmentActionGraph _ _ _ _ _ _ _ _ _ _ _ _).1 edge
    obtain ⟨other, ho, P', order', top', action', stored', member⟩ :=
      (M.mem_structuralAssignments G nodes nodeOrder basis T T2 earlier history x).1 source
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_branch_bound g P order top action
        G nodes nodeOrder nodeAction basis T T2 level branch)
    obtain ⟨same, _⟩ := M.structuralAssignment_branch_unique G nodes nodeOrder basis T T2
      function stored stored' bounds.1 member
    exact (M.pair_mem_structuralAssignmentActionGraph _ _ _ _ _ _ _ _ _ _ _ _).2
      ⟨hg, level, same.symm ▸ ho, P, order, top, action, stored, branch⟩

theorem structuralAssignmentSection_entry (stages history g x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ rawActionSection g
      (M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history)
      (M.structuralAssignments G nodes nodeOrder basis T T2 stages history) ↔
      ZFSet.pair (ZFSet.pair g x) y ∈
        M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history := by
  rw [pair_mem_rawActionSection]
  constructor
  · exact fun member => member.2.2
  · intro edge
    obtain ⟨_hg, level, hl, P, order, top, action, stored, branch⟩ :=
      (M.pair_mem_structuralAssignmentActionGraph _ _ _ _ _ _ _ _ _ _ _ _).1 edge
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_bound g G nodes nodeOrder nodeAction basis T T2
        stages history level P order top action hl stored branch)
    exact ⟨bounds.1, bounds.2, edge⟩

theorem structuralAssignmentActionGraph_earlier_iff {stages history g x y : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (earlier : ZFSet.{u})
    (edge : ZFSet.pair (ZFSet.pair g x) y ∈
      M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history) :
    x ∈ M.structuralAssignments G nodes nodeOrder basis T T2 earlier history ↔
      y ∈ M.structuralAssignments G nodes nodeOrder basis T T2 earlier history := by
  obtain ⟨_hg, level, _hl, P, order, top, action, stored, branch⟩ :=
    (M.pair_mem_structuralAssignmentActionGraph _ _ _ _ _ _ _ _ _ _ _ _).1 edge
  have bounds := ZFSet.pair_mem_prod.1
    (M.rawStageRefinementAssignmentActionGraph_branch_bound g P order top action
      G nodes nodeOrder nodeAction basis T T2 level branch)
  constructor
  · intro member
    obtain ⟨other, ho, P', order', top', action', stored', source⟩ :=
      (M.mem_structuralAssignments G nodes nodeOrder basis T T2 earlier history x).1 member
    have same := (M.structuralAssignment_branch_unique G nodes nodeOrder basis T T2
      function stored stored' bounds.1 source).1
    exact (M.mem_structuralAssignments G nodes nodeOrder basis T T2 earlier history y).2
      ⟨level, same.symm ▸ ho, P, order, top, action, stored, bounds.2⟩
  · intro member
    obtain ⟨other, ho, P', order', top', action', stored', target⟩ :=
      (M.mem_structuralAssignments G nodes nodeOrder basis T T2 earlier history y).1 member
    have same := (M.structuralAssignment_branch_unique G nodes nodeOrder basis T T2
      function stored stored' bounds.2 target).1
    exact (M.mem_structuralAssignments G nodes nodeOrder basis T T2 earlier history x).2
      ⟨level, same.symm ▸ ho, P, order, top, action, stored, bounds.1⟩





theorem structuralAssignmentImage_entry (stages history g A y : ZFSet.{u}) :
    y ∈ M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A ↔
      ∃ x ∈ A, ZFSet.pair (ZFSet.pair g x) y ∈
        M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history := by
  rw [structuralAssignmentImage, mem_relationImage]
  constructor
  · rintro ⟨_, x, hx, edge⟩
    exact ⟨x, hx, (M.structuralAssignmentSection_entry G nodes nodeOrder nodeAction basis T T2 stages history g x y).1 edge⟩
  · rintro ⟨x, hx, edge⟩
    have sectionEdge := (M.structuralAssignmentSection_entry G nodes nodeOrder nodeAction basis T T2 stages history g x y).2 edge
    exact ⟨((pair_mem_rawActionSection _ _ _ _ _).1 sectionEdge).2.1, x, hx, sectionEdge⟩

theorem structuralAssignmentImage_history_restrict (stages history g A : ZFSet.{u}) :
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages (graphRestriction stages history) g A =
      M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A := by
  unfold structuralAssignmentImage
  rw [M.structuralAssignments_history_restrict, M.structuralAssignmentActionGraph_history_restrict]

theorem structuralAssignmentImage_cut {stages earlier history : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (subset : earlier ⊆ stages) (g A : ZFSet.{u}) :
    assignmentCut (refinementDataHistoryLevels stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) T) earlier
      (M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A) =
      M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 earlier history g
        (assignmentCut (refinementDataHistoryLevels stages
          (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) T) earlier A) := by
  rw [M.structuralAssignments_cut_eq G nodes nodeOrder basis T T2 subset,
    M.structuralAssignments_cut_eq G nodes nodeOrder basis T T2 subset]
  apply ZFSet.ext
  intro y
  rw [ZFSet.mem_sep, M.structuralAssignmentImage_entry, M.structuralAssignmentImage_entry]
  constructor
  · rintro ⟨⟨x, hx, edge⟩, target⟩
    have source := (M.structuralAssignmentActionGraph_earlier_iff G nodes nodeOrder nodeAction basis T T2
      function earlier edge).2 target
    exact ⟨x, ZFSet.mem_sep.2 ⟨hx, source⟩,
      (M.structuralAssignmentActionGraph_prefix_entry G nodes nodeOrder nodeAction basis T T2 function subset g x y).2
        ⟨edge, source⟩⟩
  · rintro ⟨x, hx, edge⟩
    obtain ⟨member, source⟩ := ZFSet.mem_sep.1 hx
    have whole := (M.structuralAssignmentActionGraph_prefix_entry G nodes nodeOrder nodeAction basis T T2
      function subset g x y).1 edge |>.1
    exact ⟨⟨x, member, whole⟩,
      (M.structuralAssignmentActionGraph_earlier_iff G nodes nodeOrder nodeAction basis T T2
        function earlier whole).1 source⟩

theorem structuralAssignmentImage_prefix_cut {stages earlier history : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (subset : earlier ⊆ stages) (g A : ZFSet.{u}) :
    assignmentCut (refinementDataHistoryLevels stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) T) earlier
      (M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A) =
      M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 earlier (graphRestriction earlier history) g
        (assignmentCut (refinementDataHistoryLevels stages
          (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) T) earlier A) := by
  rw [M.structuralAssignmentImage_history_restrict]
  exact M.structuralAssignmentImage_cut G nodes nodeOrder nodeAction basis T T2 function subset g A

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})
variable {stages history level P order top action g : ZFSet.{u}}
variable (function : FunctionGraphOn stages history) (actor : g ∈ G)
variable (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history)
local notation "d" => M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level
local notation "J" => stageOneAssignments (d 0) T
local notation "branch" => M.rawStageRefinementAssignmentActionGraph g P order top action
  G nodes nodeOrder nodeAction basis T T2 level
local notation "image" => M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g

include function actor stored in
theorem structuralAssignmentImage_target_branch_iff {A y : ZFSet.{u}} (target : y ∈ J) :
    y ∈ image A ↔ y ∈ relationImage A J branch := by
  rw [M.structuralAssignmentImage_entry, mem_relationImage]
  constructor
  · rintro ⟨x, hx, edge⟩
    obtain ⟨_hg, other, _ho, P', order', top', action', stored', entry⟩ :=
      (M.pair_mem_structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2
        stages history g x y).1 edge
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_branch_bound g P' order' top' action'
        G nodes nodeOrder nodeAction basis T T2 other entry)
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :=
      M.structuralAssignment_branch_unique G nodes nodeOrder basis T T2
        function stored stored' target bounds.2
    exact ⟨target, x, hx, entry⟩
  · rintro ⟨_, x, hx, entry⟩
    exact ⟨x, hx, (M.pair_mem_structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2
      stages history g x y).2
        ⟨actor, level, function.pair_source stored, P, order, top, action, stored, entry⟩⟩

include function actor stored in
theorem structuralAssignmentImage_rawTests_branch_iff (A lower : ZFSet.{u}) :
    stageOneRawTests M d (image A) lower ↔
      stageOneRawTests M d (relationImage A J branch) lower := by
  apply stageOneRawTests_congr
  intro i hi u hu w hw
  change u ∈ T at hu
  change w ∈ T at hw
  exact M.structuralAssignmentImage_target_branch_iff G nodes nodeOrder nodeAction basis T T2
    function actor stored ((stageOneAssignment_mem_assignments (d 0) T i u w).2 ⟨hi, hu, hw⟩)

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_StructuralAssignmentActionLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {H : Type u} [Group H]

theorem structuralAssignment_relationLaws (t : Presentation H)
    (nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u})
    (function : FunctionGraphOn stages history)
    (branches : ∀ level ∈ stages, ∀ P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      RelationActionLaws H
        (stageOneAssignments (M.rawRefinementFormulaData P order top action
          t.carrier nodes nodeOrder basis T T2 level 0) T)
        (fun g => M.rawStageRefinementAssignmentActionGraph (t.encode g) P order top action
          t.carrier nodes nodeOrder nodeAction basis T T2 level)) :
    RelationActionLaws H
      (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)
      (fun g => rawActionSection (t.encode g)
        (M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history)
        (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)) := by
  let ι := {v : Fin 5 → ZFSet.{u} // v 0 ∈ stages ∧
    ZFSet.pair (v 0) (forcingStageCode (v 1) (v 2) (v 3) (v 4)) ∈ history}
  let X (i : ι) := stageOneAssignments (M.rawRefinementFormulaData (i.val 1) (i.val 2)
    (i.val 3) (i.val 4) t.carrier nodes nodeOrder basis T T2 (i.val 0) 0) T
  let branch (i : ι) (g : H) := M.rawStageRefinementAssignmentActionGraph (t.encode g)
    (i.val 1) (i.val 2) (i.val 3) (i.val 4)
    t.carrier nodes nodeOrder nodeAction basis T T2 (i.val 0)
  let J := M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history
  let graph := M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history
  have cover (x : ZFSet.{u}) : x ∈ J ↔ ∃ i : ι, x ∈ X i := by
    rw [M.mem_structuralAssignments]
    constructor
    · rintro ⟨level, hl, P, order, top, action, stored, member⟩
      exact ⟨⟨![level, P, order, top, action], hl, stored⟩, member⟩
    · rintro ⟨i, member⟩
      exact ⟨i.val 0, i.property.1, i.val 1, i.val 2, i.val 3, i.val 4, i.property.2, member⟩
  apply RelationActionLaws.of_disjoint_family X branch J (fun g => rawActionSection (t.encode g) graph J) cover
  · intro g z
    constructor
    · intro member
      obtain ⟨x, _hx, y, _hy, rfl, edge⟩ :=
        (BoundedFormula.truth_actionSectionEntryFormula 0 1 2 3 _).1
          ((mem_rawActionSection (t.encode g) graph J z).1 member)
      obtain ⟨_hg, level, hl, P, order, top, action, stored, entry⟩ :=
        (M.pair_mem_structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history (t.encode g) x y).1 edge
      exact ⟨⟨![level, P, order, top, action], hl, stored⟩, entry⟩
    · rintro ⟨i, member⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1
        (M.rawStageRefinementAssignmentActionGraph_branch_bound (t.encode g)
          (i.val 1) (i.val 2) (i.val 3) (i.val 4) t.carrier nodes nodeOrder nodeAction basis T T2 (i.val 0) member)
      exact (pair_mem_rawActionSection _ _ _ _ _).2
        ⟨(cover x).2 ⟨i, hx⟩, (cover y).2 ⟨i, hy⟩,
          (M.pair_mem_structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history (t.encode g) x y).2
            ⟨t.encode_mem g, i.val 0, i.property.1, i.val 1, i.val 2, i.val 3, i.val 4, i.property.2, member⟩⟩
  · intro i j x hi hj
    have equal := M.structuralAssignment_branch_unique t.carrier nodes nodeOrder basis T T2
      function i.property.2 j.property.2 hi hj
    apply Subtype.ext
    exact funext (Fin.cases equal.1 (Fin.cases equal.2.1 (Fin.cases equal.2.2.1
      (Fin.cases equal.2.2.2.1 (Fin.cases equal.2.2.2.2 (fun k => Fin.elim0 k))))))
  · intro i
    exact branches (i.val 0) i.property.1 (i.val 1) (i.val 2) (i.val 3) (i.val 4) i.property.2

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_StructuralForcingStageWitnessStep
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

theorem structuralForcingCarrier_shape
    (rows G nodes nodeOrder basis T T2 stages history : ZFSet.{u}) :
    M.structuralForcingCarrier rows G nodes nodeOrder basis T T2 stages history ⊆
      ZFSet.prod rows (ZFSet.powerset
        (M.structuralAssignments G nodes nodeOrder basis T T2 stages history)) := by
  intro z member
  have candidate := (M.mem_refinementHistoryForcing rows T stages
    (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) z).1 member |>.1
  obtain ⟨row, hrow, A, _hA, subset, _small, rfl⟩ := (M.mem_stageOneCandidateBound _ _ _ _).1 candidate
  exact ZFSet.pair_mem_prod.2 ⟨hrow, ZFSet.mem_powerset.2 subset⟩

theorem structuralForcingCarrier_action_candidate
    {G R : Type u} [Group G] [PartialOrder R]
    (a : PosetAction G R) (c : Presentation R) (t : Presentation G)
    (nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (hG : t.carrier ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets)
    (hna : nodeAction ∈ M.sets) (hb : basis ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets)
    (laws : RelationActionLaws G
      (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)
      (fun g => rawActionSection (t.encode g)
        (M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history)
        (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)))
    (g : G) (row : R) (A : ZFSet.{u})
    (member : ZFSet.pair (c.encode row) A ∈
      M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history) :
    ZFSet.pair (c.encode (a.iso g row))
      (M.structuralAssignmentImage t.carrier nodes nodeOrder nodeAction basis T T2 stages history (t.encode g) A) ∈
      M.stageOneCandidateBound c.carrier
        (refinementDataHistoryIndices stages
          (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)) T := by
  have candidate := (M.mem_refinementHistoryForcing c.carrier T stages
    (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
      (ZFSet.pair (c.encode row) A)).1 member |>.1
  have small := (ZFSet.pair_mem_prod.1 candidate).2
  exact ZFSet.pair_mem_prod.2 ⟨c.encode_mem (a.iso g row),
    M.structuralAssignmentImage_small pairing unions powers separation collection
      hG hn hno hna hb hT hT2 hs hh omega (M.transitive hG (t.encode_mem g))
      (laws.injection g) small⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {G R : Type u} [Group G] [PartialOrder R]
variable (a : PosetAction G R) (c : Presentation R) (t : Presentation G)
variable (nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u})
variable (laws : RelationActionLaws G
  (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)
  (fun g => rawActionSection (t.encode g)
    (M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history)
    (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)))
variable (preserves : ∀ g : G, ∀ r : R, ∀ A,
  ZFSet.pair (c.encode r) A ∈ M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history →
  ZFSet.pair (c.encode (a.iso g r))
    (M.structuralAssignmentImage t.carrier nodes nodeOrder nodeAction basis T T2 stages history (t.encode g) A) ∈
    M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history)

noncomputable def structuralForcingAction :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
    PosetAction G (SetMembers (M.refinementHistoryForcing c.carrier T stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history))) := by
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages
    (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
  let Q := M.refinementHistoryForcing c.carrier T stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
  have code : PosetActionCode t.carrier Q ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
      (SetMembers.presentation Q).conditionOrder
      (rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
        (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history) (a.actionGraph c t)
        (M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history)) := by
    rw [M.refinementHistoryDecodedOrder_eq, M.refinementHistoryOrder_raw]
    exact presentedRowAssignmentGraph_code a c t Q _ _
      (M.structuralForcingCarrier_shape c.carrier t.carrier nodes nodeOrder basis T T2 stages history) laws preserves
  exact code.toPresentedPosetAction t (SetMembers.presentation Q)

theorem structuralForcingAction_graph :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
    (M.structuralForcingAction a c t nodes nodeOrder nodeAction basis T T2 stages history laws preserves).actionGraph
      (SetMembers.presentation (M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history)) t =
      rawRowAssignmentActionGraph t.carrier
        (M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history) c.carrier
        (⋃₀ ⋃₀ (M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history))
        (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history) (a.actionGraph c t)
        (M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages
    (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
  unfold structuralForcingAction
  exact PosetActionCode.toPresentedPosetAction_graph _ _ _

theorem structuralForcingAction_coordinates :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
    ∀ g (p : SetMembers (M.refinementHistoryForcing c.carrier T stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history))) r A,
      SetMembers.raw p = ZFSet.pair (c.encode r) A →
      SetMembers.raw ((M.structuralForcingAction a c t nodes nodeOrder nodeAction basis T T2 stages history laws preserves).iso g p) =
        ZFSet.pair (c.encode (a.iso g r))
          (M.structuralAssignmentImage t.carrier nodes nodeOrder nodeAction basis T T2 stages history (t.encode g) A) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages
    (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
  intro g p r A equal
  let Q := M.refinementHistoryForcing c.carrier T stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
  let act := M.structuralForcingAction a c t nodes nodeOrder nodeAction basis T T2 stages history laws preserves
  have edge := (act.triple_mem_actionGraph (SetMembers.presentation Q) t g p (act.iso g p)).2 rfl
  have graph := M.structuralForcingAction_graph a c t nodes nodeOrder nodeAction basis T T2 stages history laws preserves
  change act.actionGraph (SetMembers.presentation Q) t = _ at graph
  rw [graph] at edge
  change ZFSet.pair (ZFSet.pair (t.encode g) (SetMembers.raw p)) (SetMembers.raw (act.iso g p)) ∈ _ at edge
  obtain ⟨q, D, _, target⟩ := exists_presentedRowAssignmentCoordinates c
    (M.structuralForcingCarrier_shape c.carrier t.carrier nodes nodeOrder basis T T2 stages history) (SetMembers.raw_mem (act.iso g p))
  rw [equal, target] at edge
  obtain ⟨_, _, row, data⟩ := (presentedRowAssignmentGraph_entry a c t Q _ _ g r q A D).1 edge
  rw [target, row, data]
  rfl

omit [Group G] in
theorem structuralAssignmentImage_empty (g : ZFSet.{u}) :
    M.structuralAssignmentImage t.carrier nodes nodeOrder nodeAction basis T T2 stages history g ∅ = ∅ := by
  apply ZFSet.ext
  intro y
  constructor
  · intro member
    obtain ⟨_, x, hx, _⟩ := (mem_relationImage _ _ _ y).1 member
    exact False.elim (ZFSet.notMem_empty x hx)
  · intro member
    exact False.elim (ZFSet.notMem_empty y member)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {G R : Type u} [Group G] [PartialOrder R]
variable (a : PosetAction G R) (c : Presentation R) (t : Presentation G)
variable (rowTop nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})

theorem structuralTrace_cutAction {stages history level P order top action : ZFSet.{u}}
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun beta prior stage =>
      stage = M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier nodes nodeOrder nodeAction basis T T2 beta prior) stages history)
    (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history)
    (function : ZFSet.IsFunc (ZFSet.prod t.carrier P) P action)
    (g : G) (r : R) (A : ZFSet.{u})
    (lower : ZFSet.pair (c.encode r)
      (assignmentCut (refinementDataHistoryLevels stages
        (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history) T) level A) ∈ P) :
    let levels := refinementDataHistoryLevels stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history) T
    let moved := M.structuralAssignmentImage t.carrier nodes nodeOrder nodeAction basis T T2 stages history (t.encode g) A
    let nextLower := ZFSet.pair (c.encode (a.iso g r)) (assignmentCut levels level moved)
    nextLower ∈ P ∧
      ZFSet.pair (ZFSet.pair (t.encode g) (ZFSet.pair (c.encode r) (assignmentCut levels level A))) nextLower ∈ action := by
  dsimp only
  have hl := trace.1.pair_source stored
  have code := (trace.2 level hl _ stored).trans
    (M.structuralForcingStage_eq c.carrier c.conditionOrder rowTop (a.actionGraph c t)
      t.carrier nodes nodeOrder nodeAction basis T T2 level (graphRestriction level history))
  obtain ⟨carrierEq, _orderEq, _topEq, actionEq⟩ := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 code
  rw [carrierEq, actionEq] at function
  have lowerMember := carrierEq ▸ lower
  have result := presentedRowAssignmentGraph_totalValue a c t
    (M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 level (graphRestriction level history))
    (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 level (graphRestriction level history))
    (M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 level (graphRestriction level history))
    (M.refinementHistoryForcing_shape c.carrier T level
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 level (graphRestriction level history)))
    function g r _ lowerMember
  rw [carrierEq, actionEq]
  rw [M.structuralAssignmentImage_prefix_cut t.carrier nodes nodeOrder nodeAction basis T T2
    trace.1 (ordinal.1 level hl)]
  exact result

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R : Type u} [Group G] [PartialOrder R]
variable (a : PosetAction G R) (c : Presentation R) (t : Presentation G)
variable (rowTop nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})

theorem structuralForcingCarrier_action_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (hG : t.carrier ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets)
    (hna : nodeAction ∈ M.sets) (hb : basis ∈ M.sets) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun beta prior stage =>
      stage = M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier nodes nodeOrder nodeAction basis T T2 beta prior) stages history)
    (laws : RelationActionLaws G
      (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)
      (fun g => rawActionSection (t.encode g)
        (M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history)
        (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)))
    (functions : ∀ level P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history →
        ZFSet.IsFunc (ZFSet.prod t.carrier P) P action)
    (symmetry : ∀ level P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      ∀ (g : G) (A p q : ZFSet.{u}), ZFSet.pair (ZFSet.pair (t.encode g) p) q ∈ action →
        (stageOneRawTests M (M.rawRefinementFormulaData P order top action t.carrier nodes nodeOrder basis T T2 level)
          (relationImage A
            (stageOneAssignments (M.rawRefinementFormulaData P order top action t.carrier nodes nodeOrder basis T T2 level 0) T)
            (M.rawStageRefinementAssignmentActionGraph (t.encode g) P order top action t.carrier
              nodes nodeOrder nodeAction basis T T2 level)) q ↔
        stageOneRawTests M (M.rawRefinementFormulaData P order top action t.carrier nodes nodeOrder basis T T2 level) A p))
    (g : G) (row : R) (A : ZFSet.{u})
    (member : ZFSet.pair (c.encode row) A ∈
      M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history) :
    ZFSet.pair (c.encode (a.iso g row))
      (M.structuralAssignmentImage t.carrier nodes nodeOrder nodeAction basis T T2 stages history (t.encode g) A) ∈
      M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history := by
  have candidate := M.structuralForcingCarrier_action_candidate a c t nodes nodeOrder nodeAction basis T T2
    stages history pairing unions powers separation collection hG hn hno hna hb hT hT2 hs hh omega laws g row A member
  have previous := (M.mem_refinementHistoryForcing c.carrier T stages
    (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history) _).1 member |>.2
  apply (M.mem_refinementHistoryForcing c.carrier T stages
    (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history) _).2
  refine ⟨candidate, ?_⟩
  intro level hl
  obtain ⟨packet, entry, valid⟩ := previous level hl
  obtain ⟨data, rfl⟩ := M.structuralRefinementHistory_decoded t.carrier nodes nodeOrder basis T T2 stages history entry
  obtain ⟨_, P, order, top, action, stored, rfl⟩ :=
    M.structuralRefinementHistory_fields t.carrier nodes nodeOrder basis T T2 stages history data entry
  refine ⟨_, entry, ?_⟩
  rw [packedSuccessorConditionCode_code_iff, stageTwoConditionCode_pair_iff] at valid ⊢
  obtain ⟨lower, tests⟩ := valid
  have moved := M.structuralTrace_cutAction a c t rowTop nodes nodeOrder nodeAction basis T T2
    ordinal trace stored (functions level P order top action stored) g row A lower
  refine ⟨moved.1, ?_⟩
  apply (M.structuralAssignmentImage_rawTests_branch_iff t.carrier nodes nodeOrder nodeAction basis T T2
    trace.1 (t.encode_mem g) stored A _).2
  exact (symmetry level P order top action stored g A _ _ moved.2).2 tests

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

theorem structuralForcingStage_witness_step
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (earlier : ∀ level P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      RawRefinementStageWitness M t b d base directed T T2 level P order top action)
    (P order top action : ZFSet.{u})
    (output : forcingStageCode P order top action =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history) :
    RawRefinementStageWitness M t b d base directed T T2 stages P order top action := by
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  have hPacked : packed ∈ M.sets :=
    M.structuralRefinementHistory_mem pairing unions powers separation collection
      ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
      (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
        (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  have fields : ∀ level P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      ∀ j, (![level, P, order, top, action] : Fin 5 → ZFSet.{u}) j ∈ M.sets := by
    intro level P order top action stored
    exact M.nonemptyTupleCode_field_mem 4 ![level, P, order, top, action] (M.transitive hh stored)
  have laws := M.structuralAssignment_relationLaws t b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history trace.1 (by
      intro level _hl P order top action stored
      have ground := fields level P order top action stored
      exact (earlier level P order top action stored).relationLaws pairing unions powers separation collection
        (ground 1) group nodes (ground 2) supports (ground 0) hT)
  have preserves := M.structuralForcingCarrier_action_mem a c t rowTop b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2
    pairing unions powers separation collection group nodes nodeOrder nodeAction supports hT hT2 hs hh omega
    ordinal trace laws (fun level P order top action stored =>
      (earlier level P order top action stored).action_function) (by
      intro level P order top action stored g A p q edge
      have ground := fields level P order top action stored
      exact (earlier level P order top action stored).rawTests_actionGraph_iff
        pairing unions powers separation collection (ground 1) group nodes (ground 2) supports (ground 0) hT g A p q edge)
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed run.carriers ordinal carrier rowTop topMem topRows
  let e := M.structuralForcingAction a c t b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history laws preserves
  have graph := M.structuralForcingAction_graph a c t b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history laws preserves
  have actionGround : e.actionGraph (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages packed)) t ∈ M.sets := by
    change e.actionGraph (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages packed)) t = _ at graph
    rw [graph]
    exact M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier rowAction group nodes nodeOrder nodeAction supports hT hT2 hs hh omega
  have system := M.recursiveRefinementStageSystem c a t b d base directed T T2 stages packed run.carriers ordinal
    pairing unions powers separation collection carrier rowOrderGround group nodes nodeOrder nodeMaps supports hT hT2 hs hPacked omega
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 rowTop topMem topRows e
    (fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A)
    (M.structuralForcingAction_coordinates a c t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history laws preserves)
    (fun g => M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g)) actionGround
  have equal := output.trans (M.structuralForcingStage_eq c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history)
  obtain ⟨rfl, rfl, rfl, rfl⟩ := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 equal
  exact ⟨M.refinementHistoryOrder_partialOrder c.conditionOrder_code T stages packed,
    run.carriers.empty_assignments ordinal carrier topMem,
    run.carriers.greatest ordinal carrier topMem topRows, e, graph, system⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundRecursiveRefinementInternalClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {R : Type u} [PartialOrder R]
variable (c : Presentation R) (T stages history : ZFSet.{u})
variable (run : RecursiveRefinementOrderHistory M c.carrier c.conditionOrder T stages history)
variable (ordinal : ordinalSetProperty stages)
variable (unionTests : ∀ beta (d : Fin 15 → ZFSet.{u}),
  ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
  ∀ (family lower : Nat → ZFSet.{u}) q,
    (∀ n m, n ≤ m → family n ⊆ family m) →
    (∀ n, ZFSet.pair q (lower n) ∈ d 8) →
    (∀ n, stageOneRawTests M d (family n) (lower n)) →
    stageOneRawTests M d (stageOneAssignmentUnion family) q)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (carrier : c.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
variable (rowClosed : InternallyCountablyClosed M c)
local notation "Q" => M.refinementHistoryForcing c.carrier T stages history
local notation "J" => stageOneAssignments (refinementDataHistoryIndices stages history) T
local notation "B" => M.groundSmallSubsets J ZFSet.omega
local notation "shape" => M.refinementHistoryForcing_shape c.carrier T stages history
local notation "row" => flatCarrierRow c Q B shape
local notation "data" => flatCarrierData c Q B shape
include run ordinal unionTests pairing unions powers separation infinite choice carrier hT hStages hHistory rowClosed

theorem refinementHistory_lower_bound :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    ∀ seq : Nat → SetMembers Q, groundSequenceGraph seq ∈ M.sets → Antitone seq →
      ∃ q : R, (∀ n, q ≤ row (seq n)) ∧ ∃ p : SetMembers Q,
        SetMembers.raw p = ZFSet.pair (c.encode q)
          (stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n)))) ∧ ∀ n, p ≤ seq n := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  intro seq whole decreasing
  have omega := M.omega_mem separation infinite
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hStages hHistory omega
  have hJ := M.stageOneAssignments_mem pairing unions powers separation
    (M.refinementDataHistoryIndices_mem pairing unions powers separation hStages hHistory) hT
  have hB := M.groundSmallSubsets_mem powers separation hJ omega
  obtain ⟨rowGround, dataGround⟩ := M.flatCarrierSequence_projections_ground c Q B shape
    pairing unions powers separation hQ carrier hB omega seq whole
  have comparisons {n m : Nat} (less : n ≤ m) :
      row (seq m) ≤ row (seq n) ∧ SetMembers.raw (data (seq n)) ⊆ SetMembers.raw (data (seq m)) := by
    have below := decreasing less
    change ZFSet.pair (SetMembers.raw (seq m)) (SetMembers.raw (seq n)) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages history at below
    rw [flatCarrier_coordinates c Q B shape (seq m), flatCarrier_coordinates c Q B shape (seq n)] at below
    have checked := (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages history _ _ _ _).1 below
    exact ⟨(c.pair_mem_conditionOrder _ _).1 checked.2.2.1, checked.2.2.2⟩
  obtain ⟨q, belowRows⟩ := rowClosed (fun n => row (seq n)) rowGround (fun _ _ less => (comparisons less).1)
  have small := M.groundSmallSubset_union_mem pairing unions powers separation infinite choice hJ
    (fun n => data (seq n)) dataGround
  have candidate : ZFSet.pair (c.encode q)
      (stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n)))) ∈
      M.stageOneCandidateBound c.carrier (refinementDataHistoryIndices stages history) T :=
    ZFSet.pair_mem_prod.2 ⟨c.encode_mem q, small⟩
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hHistory hT
  have members (n : Nat) : ZFSet.pair (c.encode (row (seq n))) (SetMembers.raw (data (seq n))) ∈ Q := by
    rw [← flatCarrier_coordinates c Q B shape (seq n)]
    exact SetMembers.raw_mem (seq n)
  obtain ⟨member, below⟩ := run.union_lower_bound_of_candidates ordinal unionTests
    (fun n => SetMembers.raw (data (seq n))) (fun n => c.encode (row (seq n))) (c.encode q)
    members (fun _ _ less => (comparisons less).2)
    (fun n => (c.pair_mem_conditionOrder _ _).2 (belowRows n)) candidate (by
      intro gamma hgamma
      exact M.refinementDataHistoryCandidate_cut separation run.carriers.data (ordinal.1 gamma hgamma)
        hLevels (M.transitive hStages hgamma) omega candidate)
  let p : SetMembers Q := SetMembers.ofMem _ member
  have code : SetMembers.raw p = ZFSet.pair (c.encode q)
      (stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n)))) := SetMembers.raw_ofMem _ _
  refine ⟨q, belowRows, p, code, ?_⟩
  intro n
  change ZFSet.pair (SetMembers.raw p) (SetMembers.raw (seq n)) ∈
    M.refinementHistoryOrder c.carrier c.conditionOrder T stages history
  rw [code, flatCarrier_coordinates c Q B shape (seq n)]
  exact below n

theorem refinementHistory_internally_closed :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    InternallyCountablyClosed M (SetMembers.presentation Q) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  intro seq whole decreasing
  obtain ⟨_, _, p, _, below⟩ := M.refinementHistory_lower_bound c T stages history run ordinal unionTests
    pairing unions powers separation infinite choice carrier hT hStages hHistory rowClosed seq whole decreasing
  exact ⟨p, below⟩

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

theorem structuralForcingTrace_witnesses
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history) :
    ∀ level P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      RawRefinementStageWitness M t b d base directed T T2 level P order top action := by
  apply M.structuralTrace_stageWitnesses t b d c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    T T2 base directed unions separation ?_ hs hh ordinal trace
  intro level prior hl hp ord run earlier P order top action output
  exact structuralForcingStage_witness_step M c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hl hp ord run earlier P order top action output

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

theorem semanticStructuralCurrent_witness
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (P order top action : ZFSet.{u})
    (output : forcingStageCode P order top action =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history) :
    RawRefinementStageWitness M t b d base directed T T2 stages P order top action :=
  structuralForcingStage_witness_step M c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
    (structuralForcingTrace_witnesses M c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace) P order top action output

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAugmentedClassRequests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

noncomputable def fixedIndexOldFineClassImage
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
    (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (idx A : ZFSet.{u}) : ZFSet.{u} :=
  let I := M.niceRefinementIndices a s b d level T T2 valid
  let bound := M.groundRelations T s.carrier
  let graph := M.niceAssignmentClassGraphs a s b d level T T2 valid (assignmentOnIndices I T A) 1
  relationImage (fixedIndexAssignmentPairs idx T A) bound
    (fixedIndexAssignmentClassGraph idx T A bound graph)

noncomputable def fixedIndexAugmentedRequests
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
    (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (idx A : ZFSet.{u})
    (Rc u : Name s) : ZFSet.{u} :=
  insert (Name.refinementClass T valid Rc u).val
    (M.fixedIndexOldFineClassImage a s b d level T T2 valid idx A)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticFairPreparationRecordedLimits
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

noncomputable def fairPreparationEventGraph
    (Q stages U E0 orbit : ZFSet.{u}) : ZFSet.{u} :=
  let histories := M.groundRelations ZFSet.omega E0
  let events := insert ∅ (ZFSet.prod stages U)
  let tail := ZFSet.prod histories events
  let middle := ZFSet.prod Q tail
  let bound := ZFSet.prod ZFSet.omega middle
  relationCompose ZFSet.omega tail events
    (relationCompose ZFSet.omega middle tail
      (relationCompose ZFSet.omega bound middle orbit (productSecond ZFSet.omega middle))
      (productSecond Q tail))
    (productSecond histories events)

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPreparedWitnessSelections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def preparedWitnessSelections (rows T stages packed nodes p A : ZFSet.{u}) : ZFSet.{u} :=
  let Q := M.refinementHistoryForcing rows T stages packed
  M.retainedPreparationSelections A (ZFSet.prod stages (M.preparationWitnessBound nodes T Q))
    (M.varyingPreparationRelation stages packed Q (ZFSet.prod Q Q) nodes T) p
    (refinementDataHistoryLevels stages packed T)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSharedConditionalNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation collection carrier order

theorem sharedConditionName_mem {n : Nat} (phi : SetFormula n)
    (env : Assignment (M.nameDomain s) n) (i : Fin n)
    {J : ZFSet.{u}} (hJ : J ∈ M.sets) (valid : ∀ z ∈ J, IsName s z) :
    (Name.sharedConditionName (M.nameDomain s) phi env i J valid).val ∈ M.sets := by
  have family := M.familySet_mem s ⊤ pairing unions powers separation hJ
    (M.transitive carrier (s.encode_mem ⊤)) valid
  exact M.ordinarySeparationName_mem s pairing unions powers separation collection carrier order
    (sharedConditionFormula phi i) env ⟨Name.familySet ⊤ J valid, family⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPreparedSelectionProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
open scoped ZFSet
universe u
variable (M : TransitiveGround.{u})

noncomputable def preparedSelectionProfiles (A stages Q nodes T selections : ZFSet.{u}) : ZFSet.{u} :=
  let W := M.groundRelations T Q
  let K := M.groundRelations W (M.supportedEqualityCertificateBound nodes W)
  let E := M.groundRelations W (M.synchronizedEnumerationBound nodes W)
  let L := ZFSet.prod stages (M.preparationWitnessBound nodes T Q)
  let witnesses := relationImage A L selections
  let certificates := relationImage witnesses K (preparedWitnessCertificateGraph stages Q K E)
  ⋃₀ relationImage certificates (M.groundPower (M.groundPower nodes))
    (M.certificateProfileImageFamily nodes W)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundSharedRefinementValidity
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
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (J : Fin 3 → ZFSet.{u}) (hJ : ∀ i, J i ∈ M.sets)
variable (valid : ∀ i, ∀ z ∈ J i, IsName s z)
variable (env : Assignment (M.nameDomain s) 4)

noncomputable def refinementConditionAssignment : Assignment (M.nameDomain s) 4 :=
  let names : Fin 3 → (M.nameDomain s).names := fun i =>
    ⟨Name.refinementConditionNames (M.nameDomain s) env J valid i,
      M.sharedConditionName_mem s pairing unions powers separation collection carrier order
        BoundedFormula.refinementValidityFormula.toFormula env i.castSucc (hJ i) (valid i)⟩
  ![names 0, names 1, names 2, env 3]

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end


