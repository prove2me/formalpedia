-- Prove2me | Definitions.Def_OAIQ253P004
-- name    : OAIQ253P004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:53:05.583219+00:00
-- url     : https://prove2.me/theorems/4087c7bb-a370-4689-ba7e-0943130607a0
-- title:
--   Definitions bundle OAIQ253P004 of the split of OpenAI, The Partition Principle does not imply Choice
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 471 declarations of OpenAI's Lean: 154 definitions, 26 inductive types or structures and 291 theorems. The definitions and types are `OAI.PartitionPilot.Forcing.GroundBoundedExternalBirthData`, `OAI.PartitionPilot.Forcing.GroundBoundedExternalHeightData`, `OAI.PartitionPilot.Forcing.GroundChronologicalCompression`, `OAI.PartitionPilot.Forcing.GroundChronologicalExternal`, `OAI.PartitionPilot.Forcing.GroundChronologicalExternal.toMainStage`, `OAI.PartitionPilot.Forcing.GroundChronologicalHistory.fieldValue`, `OAI.PartitionPilot.Forcing.GroundChronologicalHistory.of_inclusion`, `OAI.PartitionPilot.Forcing.GroundChronologicalHistory.replaceTerminalFixedTop`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainDiagram`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainDiagram.Cone`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainDiagram.Cone.append`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainDiagram.Cone.appendStage`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainDiagram.Cone.appendTransition`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainDiagram.CoversOldBirths`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainDiagram.actorSystem`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainDiagram.coneOfLast`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainDiagram.pointSystem`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainDiagram.reindex`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainDiagram.twoStage`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainDiagram.twoStageStage`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainDiagram.twoStageTransition`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainStage`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainStage.Invariant`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainStage.birth`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainStage.externalTransition`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainTransition`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainTransition.CoversOldBirths`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainTransition.PreservesOldProfiles`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainTransition.comp`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainTransition.identity`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainTransition.ofFieldLaws`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainTransition.retargetEq`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainTransition.retargetLinked`, `OAI.PartitionPilot.Forcing.GroundChronologyFields.appendTime`, `OAI.PartitionPilot.Forcing.GroundChronologyFields.attainedBound`, `OAI.PartitionPilot.Forcing.GroundChronologyFields.normalizeBound`, `OAI.PartitionPilot.Forcing.GroundChronologyFields.replaceTerminal`, `OAI.PartitionPilot.Forcing.GroundChronologyFields.toHistory`, `OAI.PartitionPilot.Forcing.GroundChronologyFields.value`, `OAI.PartitionPilot.Forcing.GroundCompressionCompletion.boundedCapImages` and 140 more.
--
--   **Sources.** They come from these modules of lean/OAI/SetTheory, in whole or in part: `PartitionPrinciple_Definability_CodedInjectiveCones`, `PartitionPrinciple_Definability_CompressionExternalStepRealization`, `PartitionPrinciple_Definability_CountableSetFormulas`, `PartitionPrinciple_Definability_DepthSlotCodes`, `PartitionPrinciple_Definability_ExternalColumnCodes`, `PartitionPrinciple_Definability_ExternalFamilySlotCodes`, `PartitionPrinciple_Definability_ExternalGroupOperationGraphs`, `PartitionPrinciple_Definability_ExternalTileCoordinateRealization`, `PartitionPrinciple_Definability_ExternalTileSlotSupportRealization`, `PartitionPrinciple_Definability_ExternalWordRewriteFormulas`, `PartitionPrinciple_Definability_ExternalWordRewriteRealization`, `PartitionPrinciple_Definability_FiniteWordMapCodes`, `PartitionPrinciple_Definability_FixedTopCodes`, `PartitionPrinciple_Definability_GroundBoundedExternalBirths`, `PartitionPrinciple_Definability_GroundExternalRequestSetRecognition`, `PartitionPrinciple_Definability_GroundFlatCopyGraphs`, `PartitionPrinciple_Definability_GroundFlatCopyPresentation`, `PartitionPrinciple_Definability_GroundPartialFunctionSpaces`, `PartitionPrinciple_Definability_GroundRefinementPairClassGraphs`, `PartitionPrinciple_Definability_LinkedMainInvariantCodes`, `PartitionPrinciple_Definability_NatUnionCodes`, `PartitionPrinciple_Definability_NonemptyTupleFields`, `PartitionPrinciple_Definability_TaggedSumPresentations`, `PartitionPrinciple_Forcing_GroundChronologicalTransitionTransport`, `PartitionPrinciple_Forcing_GroundExternalOldAction`, `PartitionPrinciple_Forcing_GroundExternalStarSupports`, `PartitionPrinciple_Forcing_GroundFixedTopStep`, `PartitionPrinciple_Forcing_GroundFixedTopTerminal`, `PartitionPrinciple_Forcing_GroundInaccessibleConditions`, `PartitionPrinciple_Forcing_GroundProductActions`, `PartitionPrinciple_Forcing_SmallCodedMeetActions`, `PartitionPrinciple_Geometry_CompressionExternalTileOverlaps`, `PartitionPrinciple_Geometry_ExternalOwnerCoordinateLaws`, `PartitionPrinciple_Geometry_ExternalTileVertexPresentation`, `PartitionPrinciple_Geometry_FiniteWordOperations`, `PartitionPrinciple_Geometry_GroundBatchEmbeddingRecognition`, `PartitionPrinciple_Geometry_GroundCompressionFiniteFieldGraphs`, `PartitionPrinciple_Geometry_GroundCompressionOrigins`, `PartitionPrinciple_Geometry_GroundCompressionStarIncidence`, `PartitionPrinciple_Geometry_GroundDefinableSelections`, `PartitionPrinciple_Geometry_GroundExternalAlphabetInversion`, `PartitionPrinciple_Geometry_GroundExternalGenerators`, `PartitionPrinciple_Geometry_GroundExternalGroupEmbeddings`, `PartitionPrinciple_Geometry_GroundExternalLocalHeightSelection`, `PartitionPrinciple_Geometry_GroundExternalMainTransition`, `PartitionPrinciple_Geometry_GroundExternalProfilePreservation`, `PartitionPrinciple_Geometry_GroundExternalRequestOverlaps`, `PartitionPrinciple_Geometry_GroundExternalRewriteSteps`, `PartitionPrinciple_Geometry_GroundExternalSlotCopies`, `PartitionPrinciple_Geometry_GroundExternalStarOverlaps`, `PartitionPrinciple_Geometry_GroundFiniteAccounting`, `PartitionPrinciple_Geometry_GroundFiniteWordLaws`, `PartitionPrinciple_Geometry_GroundFixedTopOrders`, `PartitionPrinciple_Geometry_GroundHeightPushforward`, `PartitionPrinciple_Geometry_GroundIndexedClassInclusions`, `PartitionPrinciple_Geometry_GroundInitialExternalGroup`, `PartitionPrinciple_Geometry_GroundLinkedTransitionRetarget`, `PartitionPrinciple_Geometry_GroundMainDiagramAppend`, `PartitionPrinciple_Geometry_GroundMainTaskCapFulfillment`, `PartitionPrinciple_Geometry_GroundMainTransitionLaws`, `PartitionPrinciple_Geometry_GroundMainTransitionValidity`, `PartitionPrinciple_Geometry_GroundPreparationFamilyImages`, `PartitionPrinciple_Geometry_GroundTileStarIncidence`, `PartitionPrinciple_Geometry_InitialCompressionAccounting`, `PartitionPrinciple_Geometry_RectangleFulfillmentAtBound`, `PartitionPrinciple_Geometry_TileStarIncomingCodes`, `PartitionPrinciple_Models_GroundExternalWordQuotient`, `PartitionPrinciple_Transfinite_CodedMainPrefixSystems`, `PartitionPrinciple_Transfinite_CompressionPrefixCoinitiality`, `PartitionPrinciple_Transfinite_ExternalChronologyStageLaws`, `PartitionPrinciple_Transfinite_GroundBatchBirths`, `PartitionPrinciple_Transfinite_GroundChronologicalCompressionCoinitiality`, `PartitionPrinciple_Transfinite_GroundChronologyFieldAppend`, `PartitionPrinciple_Transfinite_GroundCompressionBirthData`, `PartitionPrinciple_Transfinite_GroundCompressionPrefixGraphs`, `PartitionPrinciple_Transfinite_GroundExternalBirthLayers`, `PartitionPrinciple_Transfinite_GroundInitialCompressionHistory`, `PartitionPrinciple_Transfinite_GroundInitialExternalChronology`, `PartitionPrinciple_Transfinite_GroundInvariantSuccessors`, `PartitionPrinciple_Transfinite_GroundLinkedMainStageCodeLaws`, `PartitionPrinciple_Transfinite_GroundMainPrefixPreservedSeeds`, `PartitionPrinciple_Transfinite_GroundMainStageInvariant`, `PartitionPrinciple_Transfinite_GroundMainSuccessorProfilePreservation`, `PartitionPrinciple_Transfinite_GroundSerializedChronologyTimeEquality`, `PartitionPrinciple_Transfinite_GroundStandardInaccessible`, `PartitionPrinciple_Transfinite_GroundTwoStageMainDiagram`, `PartitionPrinciple_Transfinite_RecursiveStateFieldEnvironments`, `PartitionPrinciple_Transfinite_SerializedChronologyCodes`, `PartitionPrinciple_Transfinite_SmallTileHeightInputs`.
--
--   **Imports.** It imports the published bundle `Def_PartitionPrinciple`; the bundles `OAIQ253P002` and `OAIQ253P003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ253P006`, `OAIQ253P007` and `OAIQ253P008`; the statement `OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialExternalBoundedGeometry`.
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
import Definitions.Def_OAIQ253P002
import Definitions.Def_OAIQ253P003

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CountableSetFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



namespace SetFormula

universe u

theorem realize_reindex (U : Set ZFSet.{u}) {n m : Nat} (f : Fin n → Fin m)
    (φ : SetFormula n) (env : Fin m → ZFSet.{u}) :
    Realize U (reindex f φ) env ↔ Realize U φ (fun i => env (f i)) := by
  induction φ generalizing m with
  | equal i j => rfl
  | mem i j => rfl
  | neg φ ih => exact not_congr (ih f env)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ f env) (ihψ f env)
  | all φ ih =>
    change (∀ x ∈ U, Realize U (reindex (liftIndex f) φ) (extend x env)) ↔ _
    apply forall_congr'
    intro x
    apply forall_congr'
    intro _
    rw [ih, extend_liftIndex]

end SetFormula



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NatUnionCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

open scoped ZFSet

universe u

theorem graphRestriction_eq_sep {A B C f : ZFSet.{u}} (h : ZFSet.IsFunc A B f) :
    graphRestriction C f = ZFSet.sep (fun z => z ∈ ZFSet.prod C B) f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact ZFSet.mem_sep.2 ⟨entry, ZFSet.pair_mem_prod.2
      ⟨hx, (ZFSet.pair_mem_prod.1 (h.1 entry)).2⟩⟩
  · intro hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).2
    exact pair_mem_graphRestriction.2 ⟨(ZFSet.mem_sep.1 hz).1, hx⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPartialFunctionSpaces
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

open SetFormula
universe u

namespace GroundDefinableFunction

def reindex {M : TransitiveGround.{u}} {n k : Nat}
    {f : (Fin k → ZFSet.{u}) → ZFSet.{u}} (defined : GroundDefinableFunction M f)
    (slots : Fin k → Fin n) : GroundDefinableFunction M (fun env => f (fun j => env (slots j))) where
  formula := SetFormula.reindex (liftIndex slots) defined.formula
  closed := fun env members => defined.closed _ (fun j => members (slots j))
  correct := by
    intro env members z hz
    rw [realize_reindex, extend_liftIndex]
    exact defined.correct _ (fun j => members (slots j)) z hz

def compFormula {n k : Nat} (outer : SetFormula (k + 1))
    (inner : Fin k → SetFormula (n + 1)) : SetFormula (n + 1) :=
  exBlock k (.conj
    (conjBlock k (fun j => SetFormula.reindex
      (extend (prefixIndex (n + 1) k j) (fun i => suffixIndex (n + 1) k i.succ)) (inner j)))
    (SetFormula.reindex (extend (suffixIndex (n + 1) k 0) (prefixIndex (n + 1) k)) outer))

def comp {M : TransitiveGround.{u}} {n k : Nat}
    {f : (Fin k → ZFSet.{u}) → ZFSet.{u}}
    {g : Fin k → (Fin n → ZFSet.{u}) → ZFSet.{u}}
    (outer : GroundDefinableFunction M f) (inner : ∀ j, GroundDefinableFunction M (g j)) :
    GroundDefinableFunction M (fun env => f (fun j => g j env)) where
  formula := compFormula outer.formula (fun j => (inner j).formula)
  closed := fun env members => outer.closed _ (fun j => (inner j).closed env members)
  correct := by
    intro env members z hz
    rw [compFormula, realize_exBlock]
    constructor
    · rintro ⟨fields, fieldMembers, clauses, result⟩
      have each := (realize_conjBlock M.sets _ _ _).1 clauses
      have values : fields = fun j => g j env := by
        funext j
        have meaning := (realize_reindex M.sets _ _ _).1 (each j)
        rw [map_extend] at meaning
        simp only [extendMany_prefix, extendMany_suffix] at meaning
        exact ((inner j).correct env members (fields j) (fieldMembers j)).1 meaning
      have meaning := (realize_reindex M.sets _ _ _).1 result
      rw [map_extend] at meaning
      simp only [extendMany_prefix, extendMany_suffix] at meaning
      have output := (outer.correct fields fieldMembers z hz).1 meaning
      exact values ▸ output
    · intro equal
      let fields : Fin k → ZFSet.{u} := fun j => g j env
      have fieldMembers : ∀ j, fields j ∈ M.sets := fun j => (inner j).closed env members
      refine ⟨fields, fieldMembers, ?_, ?_⟩
      · apply (realize_conjBlock M.sets _ _ _).2
        intro j
        rw [realize_reindex, map_extend]
        simp only [extendMany_prefix, extendMany_suffix]
        exact ((inner j).correct env members (fields j) (fieldMembers j)).2 rfl
      · rw [realize_reindex, map_extend]
        simp only [extendMany_prefix, extendMany_suffix]
        exact (outer.correct fields fieldMembers z hz).2 equal

end GroundDefinableFunction

end PartitionPilot.Forcing


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NonemptyTupleFields
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

theorem graphRestriction_mem
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    {A f : ZFSet.{u}} (hA : A ∈ M.sets) (hf : f ∈ M.sets) :
    graphRestriction A f ∈ M.sets :=
  M.injection_restriction_mem separation hA (M.union_mem unions (M.union_mem unions hf)) hf

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundFlatCopyGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem functionGraphRange_mem
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    {A f : ZFSet.{u}} (hA : A ∈ M.sets) (hf : f ∈ M.sets) :
    functionGraphRange A f ∈ M.sets :=
  M.relationImage_mem separation hA (M.union_mem unions (M.union_mem unions hf)) hf

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

include pairing unions powers separation in
theorem flatCopyOrderGraph_mem {E U Q classifier r : ZFSet.{u}}
    (hE : E ∈ M.sets) (hU : U ∈ M.sets) (hQ : Q ∈ M.sets)
    (hClassifier : classifier ∈ M.sets) (hr : r ∈ M.sets) :
    flatCopyOrderGraph E U Q classifier r ∈ M.sets := by
  let params := extend E (extend U (extend Q (extend classifier (extend r Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.flatCopyOrderEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hE (Fin.cases hU (Fin.cases hQ (Fin.cases hClassifier (Fin.cases hr (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hQ hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.flatCopyOrderEntryFormula 0 1 2 3 4 5) (extend z params)) (ZFSet.prod Q Q) =
      flatCopyOrderGraph E U Q classifier r := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_flatCopyOrderEntryFormula]
    exact ⟨And.right, fun h => ⟨(ZFSet.mem_sep.1 h).1, h⟩⟩
  exact equal ▸ selected

include pairing unions powers separation in
theorem flatCopyActionGraph_mem {E U Q classifier m : ZFSet.{u}}
    (hE : E ∈ M.sets) (hU : U ∈ M.sets) (hQ : Q ∈ M.sets)
    (hClassifier : classifier ∈ M.sets) (hm : m ∈ M.sets) :
    flatCopyActionGraph E U Q classifier m ∈ M.sets := by
  let params := extend E (extend U (extend Q (extend classifier (extend m Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.flatCopyActionEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hE (Fin.cases hU (Fin.cases hQ (Fin.cases hClassifier (Fin.cases hm (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hE hQ) hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.flatCopyActionEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod (ZFSet.prod E Q) Q) = flatCopyActionGraph E U Q classifier m := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_flatCopyActionEntryFormula]
    exact ⟨And.right, fun h => ⟨(ZFSet.mem_sep.1 h).1, h⟩⟩
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedInjectiveCones
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



section
universe u

theorem relationCompose_identity_left {A B r : ZFSet.{u}} (bound : r ⊆ ZFSet.prod A B) :
    relationCompose A A B (identityFunctionGraph A) r = r := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, _, a, _, y, _, rfl, identity, image⟩ := (mem_relationCompose _ _ _ _ _ z).1 entry
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph A x a).1 identity
    exact image
  · intro entry
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (bound entry)
    exact (pair_mem_relationCompose _ _ _ _ _ x y).2
      ⟨hx, hy, x, hx, (pair_mem_identityFunctionGraph A x x).2 ⟨rfl, hx⟩, entry⟩

theorem relationCompose_identity_right {A B r : ZFSet.{u}} (bound : r ⊆ ZFSet.prod A B) :
    relationCompose A B B r (identityFunctionGraph B) = r := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, _, a, _, y, _, rfl, image, identity⟩ := (mem_relationCompose _ _ _ _ _ z).1 entry
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph B a y).1 identity
    exact image
  · intro entry
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (bound entry)
    exact (pair_mem_relationCompose _ _ _ _ _ x y).2
      ⟨hx, hy, y, hy, entry, (pair_mem_identityFunctionGraph B y y).2 ⟨rfl, hy⟩⟩

end



end PartitionPilot.Forcing

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

namespace PartitionPilot.Forcing.SetFormula

universe u

def binaryApplication {k n : Nat} (φ : SetFormula (k + 2)) (params : Fin k → Fin n)
    (x y : Fin n) : SetFormula n := reindex (extend x (extend y params)) φ

theorem realize_binaryApplication (U : Set ZFSet.{u}) {k n : Nat} (φ : SetFormula (k + 2))
    (params : Fin k → Fin n) (x y : Fin n) (env : Fin n → ZFSet.{u}) :
    Realize U (binaryApplication φ params x y) env ↔
      Realize U φ (extend (env x) (extend (env y) (fun i => env (params i)))) := by
  rw [binaryApplication, realize_reindex, map_extend, map_extend]

end PartitionPilot.Forcing.SetFormula

end


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

section

namespace PartitionPilot.Forcing.SetFormula

def partialCollectionFormula {n : Nat} (φ : SetFormula (n + 2)) : SetFormula (n + 2) :=
  imp (ex (binaryApplication φ (fun j => j.succ.succ.succ) 1 0)) φ

def relationImageFormula {n : Nat} (φ : SetFormula (n + 2)) : SetFormula (n + 2) :=
  ex (.conj (.mem 0 2) (binaryApplication φ (fun j => j.succ.succ.succ) 0 1))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_partialCollectionFormula {n : Nat} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (x y : ZFSet.{u}) :
    Realize M.sets (partialCollectionFormula φ) (extend x (extend y params)) ↔
      ((∃ z ∈ M.sets, Realize M.sets φ (extend x (extend z params))) →
        Realize M.sets φ (extend x (extend y params))) := by
  simp only [partialCollectionFormula, realize_imp, realize_ex, realize_binaryApplication]
  rfl

theorem realize_relationImageFormula {n : Nat} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (A y : ZFSet.{u}) (hA : A ∈ M.sets) :
    Realize M.sets (relationImageFormula φ) (extend y (extend A params)) ↔
      ∃ x ∈ A, Realize M.sets φ (extend x (extend y params)) := by
  rw [relationImageFormula, realize_ex]
  constructor
  · rintro ⟨x, _, member, rel⟩
    exact ⟨x, member, (realize_binaryApplication M.sets φ _ _ _ _).1 rel⟩
  · rintro ⟨x, hx, rel⟩
    exact ⟨x, M.transitive hA hx, hx, (realize_binaryApplication M.sets φ _ _ _ _).2 rel⟩

theorem partialCollection_witness (collection : CollectionSchema M.sets)
    {n : Nat} (φ : SetFormula (n + 2)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A : ZFSet.{u}} (hA : A ∈ M.sets) :
    ∃ W ∈ M.sets, ∀ x ∈ A,
      (∃ y ∈ M.sets, Realize M.sets φ (extend x (extend y params))) →
      ∃ y ∈ W, Realize M.sets φ (extend x (extend y params)) := by
  classical
  have witnesses : ∀ x ∈ A, ∃ y ∈ M.sets,
      Realize M.sets (partialCollectionFormula φ) (extend x (extend y params)) := by
    intro x _
    by_cases possible : ∃ y ∈ M.sets, Realize M.sets φ (extend x (extend y params))
    · obtain ⟨y, hy, rel⟩ := possible
      exact ⟨y, hy, (M.realize_partialCollectionFormula φ params x y).2 (fun _ => rel)⟩
    · exact ⟨A, hA, (M.realize_partialCollectionFormula φ params x A).2 (fun h => False.elim (possible h))⟩
  obtain ⟨W, hW, bounds⟩ := M.collection_witness collection (partialCollectionFormula φ) params members hA witnesses
  refine ⟨W, hW, ?_⟩
  intro x hx possible
  obtain ⟨y, hy, rel⟩ := bounds x hx
  exact ⟨y, hy, (M.realize_partialCollectionFormula φ params x y).1 rel possible⟩

theorem definable_image_mem (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {n : Nat} (φ : SetFormula (n + 2)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A C : ZFSet.{u}} (hA : A ∈ M.sets)
    (ground : ∀ y ∈ C, y ∈ M.sets)
    (correct : ∀ y ∈ M.sets, y ∈ C ↔ ∃ x ∈ A, Realize M.sets φ (extend x (extend y params)))
    (functional : ∀ x ∈ A, ∀ y ∈ M.sets, ∀ z ∈ M.sets,
      Realize M.sets φ (extend x (extend y params)) →
      Realize M.sets φ (extend x (extend z params)) → y = z) : C ∈ M.sets := by
  obtain ⟨W, hW, bounds⟩ := M.partialCollection_witness collection φ params members hA
  have bound : C ⊆ W := by
    intro y hy
    have hyM := ground y hy
    obtain ⟨x, hx, rel⟩ := (correct y hyM).1 hy
    obtain ⟨z, hz, relz⟩ := bounds x hx ⟨y, hyM, rel⟩
    exact (functional x hx y hyM z (M.transitive hW hz) rel relz).symm ▸ hz
  have selected := M.separation_mem separation (relationImageFormula φ) (extend A params)
    (Fin.cases hA members) hW
  have eq : ZFSet.sep (fun y => Realize M.sets (relationImageFormula φ) (extend y (extend A params))) W = C := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep, M.realize_relationImageFormula φ params A y hA]
    constructor
    · rintro ⟨hy, rel⟩
      exact (correct y (M.transitive hW hy)).2 rel
    · intro hy
      exact ⟨bound hy, (correct y (ground y hy)).1 hy⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaggedSumPresentations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

theorem externalSignCode_injective : Function.Injective (externalSignCode : Bool → ZFSet.{u}) := by
  intro a b eq
  cases a <;> cases b <;> simp only [externalSignCode, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
    natSetCode_injective.eq_iff] at eq ⊢
  · exact False.elim (Nat.zero_ne_one eq)
  · exact False.elim (Nat.zero_ne_one eq.symm)

theorem mem_natTwo_iff_externalSignCode (x : ZFSet.{u}) :
    x ∈ natSetCode 2 ↔ ∃ b : Bool, x = externalSignCode b := by
  constructor
  · intro hx
    obtain ⟨n, hn, rfl⟩ := (mem_natSetCode x 2).1 hx
    have cases : n = 0 ∨ n = 1 := by omega
    rcases cases with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  · rintro ⟨b, rfl⟩
    cases b <;> exact (natSetCode_mem_iff _ 2).2 (by decide)

theorem externalActorSymbol_injective : Function.Injective (externalActorSymbol : ZFSet.{u} → ZFSet.{u}) :=
  fun _ _ eq => (ZFSet.pair_inj.1 eq).2

theorem externalLetterSymbol_inj {s t : ZFSet.{u}} {b c : Bool} :
    externalLetterSymbol s b = externalLetterSymbol t c ↔ s = t ∧ b = c := by
  constructor
  · intro eq
    have parts := ZFSet.pair_inj.1 (ZFSet.pair_inj.1 eq).2
    exact ⟨parts.1, externalSignCode_injective parts.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem externalActorSymbol_ne_letterSymbol (g s : ZFSet.{u}) (b : Bool) :
    externalActorSymbol g ≠ externalLetterSymbol s b := by
  intro eq
  have tags : (0 : Nat) = 1 := natSetCode_injective (ZFSet.pair_inj.1 eq).1
  exact Nat.zero_ne_one tags

theorem mem_externalGeneratorAlphabet (G S z : ZFSet.{u}) :
    z ∈ externalGeneratorAlphabet G S ↔
      (∃ g ∈ G, z = externalActorSymbol g) ∨
        ∃ s ∈ S, ∃ b : Bool, z = externalLetterSymbol s b := by
  rw [externalGeneratorAlphabet, ZFSet.mem_union]
  constructor
  · rintro (old | signed)
    · obtain ⟨tag, htag, g, hg, eq⟩ := ZFSet.mem_prod.1 old
      have tagEq := ZFSet.mem_singleton.1 htag
      subst tag
      exact Or.inl ⟨g, hg, eq⟩
    · obtain ⟨tag, htag, p, hp, eq⟩ := ZFSet.mem_prod.1 signed
      have tagEq := ZFSet.mem_singleton.1 htag
      subst tag
      obtain ⟨s, hs, sign, hsign, rfl⟩ := ZFSet.mem_prod.1 hp
      obtain ⟨b, rfl⟩ := (mem_natTwo_iff_externalSignCode sign).1 hsign
      exact Or.inr ⟨s, hs, b, eq⟩
  · rintro (⟨g, hg, rfl⟩ | ⟨s, hs, b, rfl⟩)
    · exact Or.inl (ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hg⟩)
    · exact Or.inr (ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl,
        ZFSet.pair_mem_prod.2 ⟨hs, (mem_natTwo_iff_externalSignCode _).2 ⟨b, rfl⟩⟩⟩)

theorem externalActorSymbol_mem (G S g : ZFSet.{u}) :
    externalActorSymbol g ∈ externalGeneratorAlphabet G S ↔ g ∈ G := by
  rw [mem_externalGeneratorAlphabet]
  constructor
  · rintro (⟨h, hh, eq⟩ | ⟨s, _, b, eq⟩)
    · exact externalActorSymbol_injective eq ▸ hh
    · exact False.elim (externalActorSymbol_ne_letterSymbol g s b eq)
  · intro hg
    exact Or.inl ⟨g, hg, rfl⟩

theorem externalLetterSymbol_mem (G S s : ZFSet.{u}) (b : Bool) :
    externalLetterSymbol s b ∈ externalGeneratorAlphabet G S ↔ s ∈ S := by
  rw [mem_externalGeneratorAlphabet]
  constructor
  · rintro (⟨g, _, eq⟩ | ⟨t, ht, c, eq⟩)
    · exact False.elim (externalActorSymbol_ne_letterSymbol g s b eq.symm)
    · exact (externalLetterSymbol_inj.1 eq).1 ▸ ht
  · intro hs
    exact Or.inr ⟨s, hs, b, rfl⟩

def externalAlphabetEncode {J L : Type u} (s : Presentation J) (t : Presentation L) :
    J ⊕ (L × Bool) → ZFSet.{u}
  | .inl g => externalActorSymbol (s.encode g)
  | .inr p => externalLetterSymbol (t.encode p.1) p.2

theorem externalAlphabetEncode_injective {J L : Type u} (s : Presentation J) (t : Presentation L) :
    Function.Injective (externalAlphabetEncode s t) := by
  intro x y eq
  cases x with
  | inl g =>
    cases y with
    | inl h => exact congrArg Sum.inl (s.injective (externalActorSymbol_injective eq))
    | inr p => exact False.elim (externalActorSymbol_ne_letterSymbol _ _ _ eq)
  | inr p =>
    cases y with
    | inl g => exact False.elim (externalActorSymbol_ne_letterSymbol _ _ _ eq.symm)
    | inr q =>
      have parts := externalLetterSymbol_inj.1 eq
      exact congrArg Sum.inr (Prod.ext (t.injective parts.1) parts.2)

def externalGeneratorAlphabetPresentation {J L : Type u} (s : Presentation J) (t : Presentation L) :
    Presentation (J ⊕ (L × Bool)) where
  carrier := externalGeneratorAlphabet s.carrier t.carrier
  encode := externalAlphabetEncode s t
  injective := externalAlphabetEncode_injective s t
  mem_carrier z := by
    rw [mem_externalGeneratorAlphabet]
    constructor
    · rintro (⟨g, hg, eq⟩ | ⟨l, hl, b, eq⟩)
      · obtain ⟨j, rfl⟩ := (s.mem_carrier g).1 hg
        exact ⟨.inl j, eq.symm⟩
      · obtain ⟨l, rfl⟩ := (t.mem_carrier l).1 hl
        exact ⟨.inr (l, b), eq.symm⟩
    · rintro ⟨x, rfl⟩
      cases x with
      | inl g => exact Or.inl ⟨s.encode g, s.encode_mem g, rfl⟩
      | inr p => exact Or.inr ⟨t.encode p.1, t.encode_mem p.1, p.2, rfl⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalGeneratorAlphabet_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G S : ZFSet.{u}} (hG : G ∈ M.sets) (hS : S ∈ M.sets) :
    externalGeneratorAlphabet G S ∈ M.sets := by
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨G, hG⟩
  have hOne : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  have hTwo : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions hOne hOne
  have hTagZero : ({natSetCode 0} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hZero hZero
  have hTagOne : ({natSetCode 1} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hOne hOne
  exact M.binary_union_mem pairing unions
    (M.prod_mem pairing unions powers separation hTagZero hG)
    (M.prod_mem pairing unions powers separation hTagOne
      (M.prod_mem pairing unions powers separation hS hTwo))

end TransitiveGround






namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem finiteWords_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) : M.finiteWords A ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  have space := M.groundRelations_mem pairing unions powers separation hOmega hA
  let params := extend ZFSet.omega (extend A Fin.elim0)
  have selected := M.separation_mem separation
    (BoundedFormula.finiteWordFormula 1 2 0).toFormula params
    (Fin.cases hOmega (Fin.cases hA (fun j => Fin.elim0 j))) space
  have correct (f : ZFSet.{u}) (hf : f ∈ M.sets) :
      Realize M.sets (BoundedFormula.finiteWordFormula 1 2 0).toFormula (extend f params) ↔
        ∃ n ∈ ZFSet.omega, ZFSet.IsFunc n A f :=
    (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hf (Fin.cases hOmega (Fin.cases hA (fun j => Fin.elim0 j))))).trans
        (BoundedFormula.truth_finiteWordFormula 1 2 0 _)
  have eq : ZFSet.sep (fun f => Realize M.sets
      (BoundedFormula.finiteWordFormula 1 2 0).toFormula (extend f params))
        (M.groundRelations ZFSet.omega A) = M.finiteWords A := by
    apply ZFSet.ext
    intro f
    rw [ZFSet.mem_sep, finiteWords, ZFSet.mem_sep]
    exact and_congr_right (fun hf => correct f (M.transitive space hf))
  exact eq ▸ selected

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



section
open SetFormula SetRealization
universe u
namespace GroundDefinableFunction
variable {M : TransitiveGround.{u}} {n : Nat}
variable {f : (Fin (n + 1) → ZFSet.{u}) → ZFSet.{u}}

def graphPairFormula (formula : SetFormula ((n + 1) + 1)) : SetFormula (n + 2) :=
  .ex (.conj (SetFormula.reindex (extend 0 (extend 1 (fun j : Fin n => j.succ.succ.succ))) formula)
    (orderedPairFormula 2 1 0))

theorem realize_graphPairFormula (defined : GroundDefinableFunction M f)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (params : Fin n → ZFSet.{u}) (members : ∀ j, params j ∈ M.sets)
    {x z : ZFSet.{u}} (hx : x ∈ M.sets) (hz : z ∈ M.sets) :
    Realize M.sets (graphPairFormula defined.formula) (extend x (extend z params)) ↔
      z = ZFSet.pair x (f (extend x params)) := by
  rw [graphPairFormula, realize_ex]
  constructor
  · rintro ⟨y, hy, formula, pair⟩
    rw [realize_reindex, map_extend, map_extend] at formula
    have value := (defined.correct (extend x params) (Fin.cases hx members) y hy).1 formula
    have output := (M.realize_orderedPairFormula pairing 2 1 0 _ hz hx hy).1 pair
    exact value ▸ output
  · intro equal
    have hy := defined.closed (extend x params) (Fin.cases hx members)
    refine ⟨f (extend x params), hy, ?_,
      (M.realize_orderedPairFormula pairing 2 1 0 _ hz hx hy).2 equal⟩
    rw [realize_reindex, map_extend, map_extend]
    exact (defined.correct (extend x params) (Fin.cases hx members) _ hy).2 rfl

theorem graph_mem (defined : GroundDefinableFunction M f)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (params : Fin n → ZFSet.{u}) (members : ∀ j, params j ∈ M.sets)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) : defined.graph params A ∈ M.sets := by
  apply M.definable_image_mem separation collection (graphPairFormula defined.formula) params members hA
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := (defined.mem_graph params A z).1 hz
    exact M.orderedPair_mem pairing (M.transitive hA hx)
      (defined.closed (extend x params) (Fin.cases (M.transitive hA hx) members))
  · intro z hz
    rw [mem_graph]
    exact exists_congr (fun x => and_congr_right (fun hx =>
      (defined.realize_graphPairFormula pairing params members (M.transitive hA hx) hz).symm))
  · intro x hx y hy z hz first second
    exact ((defined.realize_graphPairFormula pairing params members (M.transitive hA hx) hy).1 first).trans
      ((defined.realize_graphPairFormula pairing params members (M.transitive hA hx) hz).1 second).symm

end GroundDefinableFunction
end




section
open SetFormula
universe u
namespace GroundDefinableFunction

def graphCodeFormula {n : Nat} (formula : SetFormula (n + 2)) : SetFormula (n + 2) :=
  exactSetFormula 0 (.ex (.conj (.mem 0 3)
    (SetFormula.reindex (extend 0 (extend 1 (fun j : Fin n => j.succ.succ.succ.succ)))
      (graphPairFormula formula))))

variable {M : TransitiveGround.{u}} {n : Nat}
variable {f : (Fin (n + 1) → ZFSet.{u}) → ZFSet.{u}}

noncomputable def definable_graph (defined : GroundDefinableFunction M f)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin (n + 1) → ZFSet.{u} =>
      defined.graph (fun j => env j.succ) (env 0)) where
  formula := graphCodeFormula defined.formula
  closed := fun env members => defined.graph_mem pairing separation collection
    (fun j => env j.succ) (fun j => members j.succ) (members 0)
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
    · intro w hw
      exact M.transitive (defined.graph_mem pairing separation collection
        (fun j => env j.succ) (fun j => members j.succ) (members 0)) hw
    · intro w hw
      rw [realize_ex]
      change (∃ x ∈ M.sets, x ∈ env 0 ∧ Realize M.sets
        (SetFormula.reindex (extend 0 (extend 1 (fun j : Fin n => j.succ.succ.succ.succ)))
          (graphPairFormula defined.formula)) (extend x (extend w (extend z env)))) ↔ _
      rw [defined.mem_graph]
      constructor
      · rintro ⟨x, hx, member, formula⟩
        rw [realize_reindex, map_extend, map_extend] at formula
        exact ⟨x, member, (defined.realize_graphPairFormula pairing (fun j => env j.succ)
          (fun j => members j.succ) hx hw).1 formula⟩
      · rintro ⟨x, member, equal⟩
        have hx := M.transitive (members 0) member
        refine ⟨x, hx, member, ?_⟩
        rw [realize_reindex, map_extend, map_extend]
        exact (defined.realize_graphPairFormula pairing (fun j => env j.succ)
          (fun j => members j.succ) hx hw).2 equal

end GroundDefinableFunction
end



open SetRealization SetFormula
universe u


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_DepthSlotCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetRealization
universe u

noncomputable def depthSlotGraph : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ j ∈ natSetCode 3, ∃ k ∈ ZFSet.omega,
    ∃ t ∈ ZFSet.omega, z = ZFSet.pair (ZFSet.pair n j) k ∧
      ZFSet.pair (ZFSet.pair (natSetCode 3) n) t ∈ natMulGraph ∧
      ZFSet.pair (ZFSet.pair t j) k ∈ natAddGraph)
    (ZFSet.prod (ZFSet.prod ZFSet.omega (natSetCode 3)) ZFSet.omega)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FiniteWordMapCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization
universe u
variable {B : Type u} (s : Presentation B)

theorem exists_finiteWordGraph {n : Nat} {f : ZFSet.{u}}
    (function : ZFSet.IsFunc (natSetCode n) s.carrier f) :
    ∃ xs : List B, xs.length = n ∧ finiteWordGraph s xs = f := by
  classical
  have values (i : Fin n) : ∃ b : B, ZFSet.pair (natSetCode i.val) (s.encode b) ∈ f := by
    obtain ⟨y, entry, _⟩ := function.2 (natSetCode i.val) ((natSetCode_mem_iff i.val n).2 i.isLt)
    obtain ⟨b, eq⟩ := (s.mem_carrier y).1 (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    exact ⟨b, eq.symm ▸ entry⟩
  let value : Fin n → B := fun i => Classical.choose (values i)
  have entry (i : Fin n) : ZFSet.pair (natSetCode i.val) (s.encode (value i)) ∈ f :=
    Classical.choose_spec (values i)
  let xs := List.ofFn value
  have length : xs.length = n := List.length_ofFn
  refine ⟨xs, length, ?_⟩
  have graphFunction : FunctionGraphOn (natSetCode n) (finiteWordGraph s xs) := by
    rw [← length]
    exact ⟨s.carrier, finiteWordGraph_function s xs⟩
  apply graphFunction.eq_of_agree ⟨s.carrier, function⟩
  intro x y z xy xz
  obtain ⟨i, eq⟩ := (mem_finiteWordGraph s xs _).1 xy
  obtain ⟨first, second⟩ := ZFSet.pair_inj.1 eq
  have hi : i.val < n := length ▸ i.isLt
  have getValue : xs.get i = value ⟨i.val, hi⟩ := by
    simp only [xs, List.get_eq_getElem, List.getElem_ofFn]
  have original : ZFSet.pair x y ∈ f := by
    rw [first, second, getValue]
    exact entry ⟨i.val, hi⟩
  exact (show FunctionGraphOn (natSetCode n) f from ⟨s.carrier, function⟩).unique original xz

theorem finiteWordGraph_injective : Function.Injective (finiteWordGraph s) := by
  intro xs ys eq
  have other : ZFSet.IsFunc (natSetCode ys.length) s.carrier (finiteWordGraph s xs) :=
    eq.symm ▸ finiteWordGraph_function s ys
  have length := finiteWord_domain_unique (finiteWordGraph_function s xs) other
  apply List.ext_get length
  intro k hx hy
  apply s.injective
  have first := (pair_mem_finiteWordGraph s xs k _).2 ⟨hx, rfl⟩
  have second := (pair_mem_finiteWordGraph s ys k _).2 ⟨hy, rfl⟩
  rw [eq] at first
  exact (show FunctionGraphOn (natSetCode ys.length) (finiteWordGraph s ys) from
    ⟨s.carrier, finiteWordGraph_function s ys⟩).unique first second

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (hB : s.carrier ∈ M.sets)

include pairing unions separation infinite hB

theorem finiteWords_exact_lists (f : ZFSet.{u}) :
    f ∈ M.finiteWords s.carrier ↔ ∃ xs : List B, finiteWordGraph s xs = f := by
  constructor
  · intro hf
    obtain ⟨_, n, function⟩ := (M.mem_finiteWords s.carrier f).1 hf
    obtain ⟨xs, _, eq⟩ := exists_finiteWordGraph s function
    exact ⟨xs, eq⟩
  · rintro ⟨xs, rfl⟩
    exact finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB xs

noncomputable def finiteWordPresentation : Presentation (List B) where
  carrier := M.finiteWords s.carrier
  encode := finiteWordGraph s
  injective := finiteWordGraph_injective s
  mem_carrier := finiteWords_exact_lists s M pairing unions separation infinite hB

end TransitiveGround

end

open SetRealization SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_FiniteWordOperations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem finiteWordGraph_append_code {B : Type u} (s : Presentation B) (xs ys : List B) :
    FiniteWordAppendCode s.carrier ZFSet.omega natAddGraph
      (finiteWordGraph s xs) (finiteWordGraph s ys) (finiteWordGraph s (xs ++ ys)) := by
  refine ⟨natSetCode xs.length, natSetCode_mem_omega _, natSetCode ys.length, natSetCode_mem_omega _,
    natSetCode (xs.length + ys.length), natSetCode_mem_omega _, finiteWordGraph_function s xs,
    finiteWordGraph_function s ys, ?_, (pair_mem_natAddGraph _ _ _).2 rfl, ?_⟩
  · simpa only [List.length_append] using finiteWordGraph_function s (xs ++ ys)
  · intro i hi a _
    obtain ⟨k, _, rfl⟩ := (mem_natSetCode i (xs.length + ys.length)).1 hi
    rw [finiteWordGraph_append_entry]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨j, equal, entry⟩
      have hj := (ZFSet.pair_mem_prod.1 ((finiteWordGraph_function s ys).1 entry)).1
      exact ⟨natSetCode j, hj, (pair_mem_natAddGraph _ _ _).2 equal, entry⟩
    · rintro ⟨j, hj, sum, entry⟩
      obtain ⟨l, _, rfl⟩ := (mem_natSetCode j ys.length).1 hj
      exact ⟨l, (pair_mem_natAddGraph _ _ _).1 sum, entry⟩

theorem finiteWordAppendCode_iff {B : Type u} (s : Presentation B) (xs ys : List B) (h : ZFSet.{u}) :
    FiniteWordAppendCode s.carrier ZFSet.omega natAddGraph
      (finiteWordGraph s xs) (finiteWordGraph s ys) h ↔ h = finiteWordGraph s (xs ++ ys) :=
  ⟨fun code => code.unique (finiteWordGraph_append_code s xs ys),
    fun equal => equal.symm ▸ finiteWordGraph_append_code s xs ys⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalAlphabetInversion
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

open SetRealization
universe u

noncomputable def externalSymbolInverseGraph (G S inv : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ externalGeneratorAlphabet G S,
    ∃ y ∈ externalGeneratorAlphabet G S, z = ZFSet.pair x y ∧
      ExternalSymbolInverseEntry G S inv x y)
    (ZFSet.prod (externalGeneratorAlphabet G S) (externalGeneratorAlphabet G S))

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFiniteWordLaws
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

noncomputable def finiteWordReverseGraph (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ f ∈ M.finiteWords A, ∃ h ∈ M.finiteWords A,
    z = ZFSet.pair f h ∧ FiniteWordReverseCode A ZFSet.omega natAddGraph f h)
    (ZFSet.prod (M.finiteWords A) (M.finiteWords A))

theorem pair_mem_finiteWordAppendGraph (A f g h : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair f g) h ∈ M.finiteWordAppendGraph A ↔
      f ∈ M.finiteWords A ∧ g ∈ M.finiteWords A ∧ h ∈ M.finiteWords A ∧
        FiniteWordAppendCode A ZFSet.omega natAddGraph f g h := by
  rw [finiteWordAppendGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, f', hf, g', hg, h', hh, eq, code⟩
    obtain ⟨fg, rfl⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 fg
    exact ⟨hf, hg, hh, code⟩
  · rintro ⟨hf, hg, hh, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hf, hg⟩, hh⟩,
      f, hf, g, hg, h, hh, rfl, code⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

theorem finiteWordAppendGraph_eq_graph {B : Type u} (s : Presentation B)
    (hB : s.carrier ∈ M.sets) :
    M.finiteWordAppendGraph s.carrier =
      ((finiteWordPresentation s M pairing unions separation infinite hB).product
        (finiteWordPresentation s M pairing unions separation infinite hB)).graph
          (finiteWordPresentation s M pairing unions separation infinite hB)
            (fun p => p.1 ++ p.2) := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  change z ∈ M.finiteWordAppendGraph s.carrier ↔
    ∃ p : List B × List B, ZFSet.pair
      (ZFSet.pair (finiteWordGraph s p.1) (finiteWordGraph s p.2))
        (finiteWordGraph s (p.1 ++ p.2)) = z
  constructor
  · intro hz
    obtain ⟨fg, hfg, h, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    obtain ⟨f, hf, g, hg, rfl⟩ := ZFSet.mem_prod.1 hfg
    obtain ⟨xs, rfl⟩ := (finiteWords_exact_lists s M pairing unions separation infinite hB f).1 hf
    obtain ⟨ys, rfl⟩ := (finiteWords_exact_lists s M pairing unions separation infinite hB g).1 hg
    have code := ((M.pair_mem_finiteWordAppendGraph _ _ _ _).1 hz).2.2.2
    have eq := (finiteWordAppendCode_iff s xs ys h).1 code
    subst h
    exact ⟨(xs, ys), rfl⟩
  · rintro ⟨⟨xs, ys⟩, rfl⟩
    exact (M.pair_mem_finiteWordAppendGraph _ _ _ _).2
      ⟨finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB xs,
        finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB ys,
        finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB (xs ++ ys),
        finiteWordGraph_append_code s xs ys⟩

end TransitiveGround






namespace TransitiveGround

variable (M : TransitiveGround.{u})

noncomputable def externalInverseWordGraph (G S inv : ZFSet.{u}) : ZFSet.{u} :=
  let alphabet := externalGeneratorAlphabet G S
  let words := M.finiteWords alphabet
  relationCompose words words words
    (M.finiteWordMapGraph alphabet alphabet (externalSymbolInverseGraph G S inv))
    (M.finiteWordReverseGraph alphabet)

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FixedTopCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

theorem fixedTop_old_glb {P r μ x y z : ZFSet.{u}} (old : MeetOrderCode P r μ)
    (entry : ZFSet.pair (ZFSet.pair x y) z ∈ μ) :
    GreatestLowerBoundCode (fixedTopCarrier P) (fixedTopOrder P r) x y z := by
  obtain ⟨hx, hy, hz, glb⟩ := old.pair_iff.1 entry
  refine ⟨(fixedTopOrder_old_iff hx).2 glb.1, (fixedTopOrder_old_iff hy).2 glb.2.1, ?_⟩
  intro w _ wx wy
  have hw := fixedTopOrder_no_new_below old.order hx wx
  exact (fixedTopOrder_old_iff hz).2 (glb.2.2 w hw
    ((fixedTopOrder_old_iff hx).1 wx) ((fixedTopOrder_old_iff hy).1 wy))

theorem fixedTopMeet_code {P r μ : ZFSet.{u}} (old : MeetOrderCode P r μ) :
    MeetOrderCode (fixedTopCarrier P) (fixedTopOrder P r) (fixedTopMeet P r) := by
  apply canonicalMeetGraph_code (fixedTopOrder_code old.order)
  intro x hx y hy
  rcases (mem_fixedTopCarrier P x).1 hx with rfl | oldx
  · exact ⟨y, hy, fixedTopOrder_greatest hy, (fixedTopOrder_code old.order).refl y hy,
      fun _ _ _ wy => wy⟩
  · rcases (mem_fixedTopCarrier P y).1 hy with rfl | oldy
    · exact ⟨x, hx, (fixedTopOrder_code old.order).refl x hx, fixedTopOrder_greatest hx,
        fun _ _ wx _ => wx⟩
    · obtain ⟨z, entry, _⟩ := old.operation.2 (ZFSet.pair x y) (ZFSet.pair_mem_prod.2 ⟨oldx, oldy⟩)
      exact ⟨z, fixedTopCarrier_old (ZFSet.pair_mem_prod.1 (old.operation.1 entry)).2,
        fixedTop_old_glb old entry⟩

theorem fixedTopMeet_old_iff {P r μ x y z : ZFSet.{u}}
    (old : MeetOrderCode P r μ) (hx : x ∈ P) (hy : y ∈ P) :
    ZFSet.pair (ZFSet.pair x y) z ∈ fixedTopMeet P r ↔ ZFSet.pair (ZFSet.pair x y) z ∈ μ := by
  constructor
  · intro entry
    obtain ⟨_, _, _, glb⟩ := (fixedTopMeet_code old).pair_iff.1 entry
    have hz := fixedTopOrder_no_new_below old.order hx glb.1
    refine old.pair_iff.2 ⟨hx, hy, hz, (fixedTopOrder_old_iff hx).1 glb.1,
      (fixedTopOrder_old_iff hy).1 glb.2.1, ?_⟩
    intro w hw wx wy
    exact (fixedTopOrder_old_iff hz).1 (glb.2.2 w (fixedTopCarrier_old hw)
      ((fixedTopOrder_old_iff hx).2 wx) ((fixedTopOrder_old_iff hy).2 wy))
  · intro entry
    have hz := (ZFSet.pair_mem_prod.1 (old.operation.1 entry)).2
    exact (fixedTopMeet_code old).pair_iff.2
      ⟨fixedTopCarrier_old hx, fixedTopCarrier_old hy, fixedTopCarrier_old hz, fixedTop_old_glb old entry⟩

theorem fixedTopMeet_top_left {P r μ x z : ZFSet.{u}}
    (old : MeetOrderCode P r μ) (hx : x ∈ fixedTopCarrier P) :
    ZFSet.pair (ZFSet.pair P x) z ∈ fixedTopMeet P r ↔ z = x := by
  have code := fixedTopMeet_code old
  have entry : ZFSet.pair (ZFSet.pair P x) x ∈ fixedTopMeet P r :=
    code.pair_iff.2 ⟨fixedTopCarrier_top P, hx, hx, fixedTopOrder_greatest hx,
      code.order.refl x hx, fun _ _ _ wx => wx⟩
  constructor
  · intro other
    obtain ⟨v, _, unique⟩ := code.operation.2 (ZFSet.pair P x)
      (ZFSet.pair_mem_prod.2 ⟨fixedTopCarrier_top P, hx⟩)
    exact (unique z other).trans (unique x entry).symm
  · intro equal
    exact equal.symm ▸ entry

theorem fixedTopMeet_subset {P r μ : ZFSet.{u}} (old : MeetOrderCode P r μ) :
    μ ⊆ fixedTopMeet P r := by
  intro z hz
  obtain ⟨xy, hxy, v, _, rfl⟩ := ZFSet.mem_prod.1 (old.operation.1 hz)
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
  exact (fixedTopMeet_old_iff old hx hy).2 hz

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundInaccessibleConditions
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

def GroundInaccessibleConditions (M : TransitiveGround.{u}) (K : ZFSet.{u}) : Prop :=
  ordinalSetProperty K ∧ ZFSet.omega ∈ K ∧ GroundRegular M K ∧ GroundStrongLimit M K

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_SmallCodedMeetActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

open SetRealization
universe u

namespace MeetOrderCode

variable {P r μ : ZFSet.{u}} (code : MeetOrderCode P r μ)

theorem toSmallMeetOrder_meet_eq_iff (x y z : SetMembers P) :
    code.toSmallMeetOrder.meet x y = z ↔
      ZFSet.pair (ZFSet.pair (SetMembers.raw x) (SetMembers.raw y)) (SetMembers.raw z) ∈ μ :=
  code.smallMeet_eq_iff x y z

end MeetOrderCode

namespace PosetActionCode

variable {G P m inv one r μ A : ZFSet.{u}} (action : PosetActionCode G P m one r A)

noncomputable def toOrderAction (group : GroupCode G m inv one) (meet : MeetOrderCode P r μ) :
    letI := group.toGroup
    Compression.RecursiveMaps.CosetGeometry.OrderAction (SetMembers G) meet.toSmallMeetOrder := by
  letI := group.toGroup
  exact {
    iso := action.toSmallMeetIso group meet
    one := action.act_one group
    mul := action.act_mul group }

theorem toOrderAction_eq_iff (group : GroupCode G m inv one) (meet : MeetOrderCode P r μ)
    (g : SetMembers G) (x y : SetMembers P) :
    letI := group.toGroup
    ((action.toOrderAction group meet).iso g).toFun x = y ↔
      ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw x)) (SetMembers.raw y) ∈ A :=
  action.act_eq_iff g x y

end PosetActionCode

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalWordRewriteFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem finiteWordGraph_singleton {B : Type u} (s : Presentation B) (a : B) :
    finiteWordGraph s [a] = wordSingleton (s.encode a) := by
  apply ZFSet.ext
  intro z
  rw [mem_finiteWordGraph, wordSingleton, ZFSet.mem_singleton]
  constructor
  · rintro ⟨i, eq⟩
    have hi : i.val < 1 := i.isLt
    have equal : i = ⟨0, by simp⟩ := Fin.ext (by change i.val = 0; omega)
    subst i
    exact eq
  · intro eq
    exact ⟨⟨0, by simp⟩, eq⟩

theorem finiteWordGraph_double {B : Type u} (s : Presentation B) (a b : B) :
    finiteWordGraph s [a, b] = wordDouble (s.encode a) (s.encode b) := by
  apply ZFSet.ext
  intro z
  rw [mem_finiteWordGraph, wordDouble, ZFSet.mem_pair]
  constructor
  · rintro ⟨i, eq⟩
    have hi : i.val < 2 := i.isLt
    have cases : i = ⟨0, by simp⟩ ∨ i = ⟨1, by simp⟩ := by
      have values : i.val = 0 ∨ i.val = 1 := by omega
      exact values.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
    rcases cases with rfl | rfl
    · exact Or.inl eq
    · exact Or.inr eq
  · rintro (eq | eq)
    · exact ⟨⟨0, by simp⟩, eq⟩
    · exact ⟨⟨1, by simp⟩, eq⟩

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalRewriteSteps
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

theorem pair_mem_externalWordStepGraph (W append G S m one f g : ZFSet.{u}) :
    ZFSet.pair f g ∈ externalWordStepGraph W append G S m one ↔
      f ∈ W ∧ g ∈ W ∧ ExternalWordStepCode W append G S m one f g := by
  rw [externalWordStepGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, f', hf, g', hg, equal, step⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hf, hg, step⟩
  · rintro ⟨hf, hg, step⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hf, hg⟩, f, hf, g, hg, rfl, step⟩

theorem externalWordStepGraph_symmetric {W append G S m one f g : ZFSet.{u}}
    (entry : ZFSet.pair f g ∈ externalWordStepGraph W append G S m one) :
    ZFSet.pair g f ∈ externalWordStepGraph W append G S m one := by
  obtain ⟨hf, hg, step⟩ := (pair_mem_externalWordStepGraph _ _ _ _ _ _ _ _).1 entry
  exact (pair_mem_externalWordStepGraph _ _ _ _ _ _ _ _).2 ⟨hg, hf, step.symm⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalWordRewriteRealization
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
variable {J L : Type u} [Group J] (s : Presentation J) (t : Presentation L)

theorem externalWordAtomicCode_iff (xs ys : List (J ⊕ (L × Bool))) :
    ExternalWordAtomicCode s.carrier t.carrier
      ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) ys) ↔
      ExternalWordRewrite.Atomic xs ys := by
  let a := externalGeneratorAlphabetPresentation s t
  have oldOne (g : J) : finiteWordGraph a [.inl g] = wordSingleton (externalActorSymbol (s.encode g)) :=
    finiteWordGraph_singleton a _
  have oldTwo (g h : J) : finiteWordGraph a [.inl g, .inl h] =
      wordDouble (externalActorSymbol (s.encode g)) (externalActorSymbol (s.encode h)) :=
    finiteWordGraph_double a _ _
  have signedTwo (l : L) (b c : Bool) : finiteWordGraph a [.inr (l, b), .inr (l, c)] =
      wordDouble (externalLetterSymbol (t.encode l) b) (externalLetterSymbol (t.encode l) c) :=
    finiteWordGraph_double a _ _
  constructor
  · intro atomic
    rcases atomic with ⟨_, left, right⟩ | ⟨g, hg, h, hh, k, hk, product, left, right⟩ |
      ⟨l, hl, left, right⟩
    · have xsEq := finiteWordGraph_injective a (left.trans (oldOne 1).symm)
      have ysEq := finiteWordGraph_injective a (right.trans (finiteWordGraph_nil a).symm)
      subst xs ys
      exact .old_one
    · obtain ⟨g, rfl⟩ := (s.mem_carrier g).1 hg
      obtain ⟨h, rfl⟩ := (s.mem_carrier h).1 hh
      obtain ⟨k, rfl⟩ := (s.mem_carrier k).1 hk
      have productEq := ((s.product s).pair_mem_graph s (fun p => p.1 * p.2) (g, h) k).1 product
      have xsEq := finiteWordGraph_injective a (left.trans (oldTwo g h).symm)
      have ysEq := finiteWordGraph_injective a (right.trans (oldOne k).symm)
      subst xs ys k
      exact .old_mul g h
    · obtain ⟨l, rfl⟩ := (t.mem_carrier l).1 hl
      have ysEq := finiteWordGraph_injective a (right.trans (finiteWordGraph_nil a).symm)
      subst ys
      rcases left with left | left
      · have xsEq := finiteWordGraph_injective a (left.trans (signedTwo l false true).symm)
        subst xs
        exact .cancel l false
      · have xsEq := finiteWordGraph_injective a (left.trans (signedTwo l true false).symm)
        subst xs
        exact .cancel l true
  · intro atomic
    cases atomic with
    | old_one => exact Or.inl ⟨s.encode_mem 1, oldOne 1, finiteWordGraph_nil a⟩
    | old_mul g h =>
      exact Or.inr (Or.inl ⟨s.encode g, s.encode_mem g, s.encode h, s.encode_mem h,
        s.encode (g * h), s.encode_mem (g * h),
        ((s.product s).pair_mem_graph s (fun p => p.1 * p.2) (g, h) (g * h)).2 rfl,
        oldTwo g h, oldOne (g * h)⟩)
    | cancel l b =>
      refine Or.inr (Or.inr ⟨t.encode l, t.encode_mem l, ?_, finiteWordGraph_nil a⟩)
      cases b
      · exact Or.inl (signedTwo l false true)
      · exact Or.inr (signedTwo l true false)

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hAlphabet : (externalGeneratorAlphabetPresentation s t).carrier ∈ M.sets)

include pairing unions separation infinite hAlphabet

theorem externalWordStepCode_iff (xs ys : List (J ⊕ (L × Bool))) :
    ExternalWordStepCode (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier))
      (M.finiteWordAppendGraph (externalGeneratorAlphabet s.carrier t.carrier))
      s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) ys) ↔
      ExternalWordRewrite.Step xs ys := by
  let a := externalGeneratorAlphabetPresentation s t
  have word (v : List (J ⊕ (L × Bool))) :=
    finiteWordGraph_mem_finiteWords a M pairing unions separation infinite hAlphabet v
  have decode (v : ZFSet.{u}) := finiteWords_exact_lists a M pairing unions separation infinite hAlphabet v
  have append (v w : List (J ⊕ (L × Bool))) :
      ZFSet.pair (ZFSet.pair (finiteWordGraph a v) (finiteWordGraph a w))
        (finiteWordGraph a (v ++ w)) ∈ M.finiteWordAppendGraph a.carrier :=
    (M.pair_mem_finiteWordAppendGraph _ _ _ _).2
      ⟨word v, word w, word (v ++ w), finiteWordGraph_append_code a v w⟩
  have appendEq (v w z : List (J ⊕ (L × Bool)))
      (entry : ZFSet.pair (ZFSet.pair (finiteWordGraph a v) (finiteWordGraph a w))
        (finiteWordGraph a z) ∈ M.finiteWordAppendGraph a.carrier) : z = v ++ w :=
    finiteWordGraph_injective a ((finiteWordAppendCode_iff a v w _).1
      ((M.pair_mem_finiteWordAppendGraph _ _ _ _).1 entry).2.2.2)
  constructor
  · rintro ⟨pre, hp, post, hq, l, hl, r, hr, pl, _, pr, _, atomic, left, right, direction⟩
    obtain ⟨pre, rfl⟩ := (decode pre).1 hp
    obtain ⟨post, rfl⟩ := (decode post).1 hq
    obtain ⟨l, rfl⟩ := (decode l).1 hl
    obtain ⟨r, rfl⟩ := (decode r).1 hr
    have leftEq := (finiteWordAppendCode_iff a pre l pl).1
      ((M.pair_mem_finiteWordAppendGraph _ _ _ _).1 left).2.2.2
    have rightEq := (finiteWordAppendCode_iff a pre r pr).1
      ((M.pair_mem_finiteWordAppendGraph _ _ _ _).1 right).2.2.2
    subst pl pr
    refine ⟨pre, post, l, r, (externalWordAtomicCode_iff s t l r).1 atomic, ?_⟩
    rcases direction with ⟨first, second⟩ | ⟨first, second⟩
    · exact Or.inl ⟨appendEq _ _ _ first, appendEq _ _ _ second⟩
    · exact Or.inr ⟨appendEq _ _ _ first, appendEq _ _ _ second⟩
  · rintro ⟨pre, post, l, r, atomic, direction⟩
    refine ⟨finiteWordGraph a pre, word pre, finiteWordGraph a post, word post,
      finiteWordGraph a l, word l, finiteWordGraph a r, word r,
      finiteWordGraph a (pre ++ l), word (pre ++ l),
      finiteWordGraph a (pre ++ r), word (pre ++ r),
      (externalWordAtomicCode_iff s t l r).2 atomic, append pre l, append pre r, ?_⟩
    rcases direction with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨append (pre ++ l) post, append (pre ++ r) post⟩
    · exact Or.inr ⟨append (pre ++ l) post, append (pre ++ r) post⟩

theorem pair_mem_externalWordSteps (xs ys : List (J ⊕ (L × Bool))) :
    ZFSet.pair (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) ys) ∈
        M.externalWordSteps s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1) ↔
      ExternalWordRewrite.Step xs ys := by
  rw [externalWordSteps, pair_mem_externalWordStepGraph,
    M.externalWordStepCode_iff s t pairing unions separation infinite hAlphabet xs ys]
  exact ⟨fun h => h.2.2, fun h => ⟨
    finiteWordGraph_mem_finiteWords _ M pairing unions separation infinite hAlphabet xs,
    finiteWordGraph_mem_finiteWords _ M pairing unions separation infinite hAlphabet ys, h⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

end

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

universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem equivalenceClassifier_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A E : ZFSet.{u}} (hA : A ∈ M.sets) (hE : E ∈ M.sets) :
    equivalenceClassifier A E ∈ M.sets := by
  have hQ := M.equivalenceClasses_mem powers separation hA hE
  let params := extend A (extend E (extend (equivalenceClasses A E) Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.equivalenceClassifierEntryFormula 0 1 2 3) params
    (Fin.cases hA (Fin.cases hE (Fin.cases hQ (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hA hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.equivalenceClassifierEntryFormula 0 1 2 3) (extend z params))
      (ZFSet.prod A (equivalenceClasses A E)) = equivalenceClassifier A E := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_equivalenceClassifierEntryFormula,
      mem_equivalenceClassifier]
    constructor
    · rintro ⟨_, y, hy, C, _, equal, rfl⟩
      exact ⟨y, hy, equal⟩
    · rintro ⟨y, hy, rfl⟩
      have hyQ := Forcing.equivalenceClass_mem (E := E) hy
      exact ⟨ZFSet.pair_mem_prod.2 ⟨hy, hyQ⟩, y, hy,
        equivalenceClass A E y, hyQ, rfl, rfl⟩
  exact equal ▸ selected

theorem equivalenceClasses_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A E : ZFSet.{u}} (hA : A ∈ M.sets) (hE : E ∈ M.sets)
    (equivalence : EquivalenceRelationCode A E) :
    equivalenceClasses A E ∈ M.sets ∧ equivalenceClassifier A E ∈ M.sets ∧
      ZFSet.IsFunc A (equivalenceClasses A E) (equivalenceClassifier A E) ∧
      (∀ C ∈ equivalenceClasses A E, ∃ y ∈ A,
        ZFSet.pair y C ∈ equivalenceClassifier A E) ∧
      (∀ x y C D, ZFSet.pair x C ∈ equivalenceClassifier A E →
        ZFSet.pair y D ∈ equivalenceClassifier A E → (C = D ↔ ZFSet.pair x y ∈ E)) :=
  ⟨M.equivalenceClasses_mem powers separation hA hE,
    M.equivalenceClassifier_mem pairing unions powers separation hA hE,
    equivalenceClassifier_function A E, fun _ hC => equivalenceClassifier_onto hC,
    fun _ _ _ _ first second => equivalence.classifier_kernel first second⟩

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_TileStarIncomingCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem finiteWordGraph_chain_path {B : Type u} (s : Presentation B)
    (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    (x : B) (xs : List B) (chain : List.IsChain r (x :: xs)) :
    FiniteRelationPathCode ZFSet.omega s.carrier R (s.encode x)
      (s.encode ((x :: xs).getLast (List.cons_ne_nil _ _)))
      (finiteWordGraph s (x :: xs)) := by
  refine ⟨natSetCode xs.length, natSetCode_mem_omega _, natSetCode (xs.length + 1),
    natSetCode_mem_omega _, rfl, finiteWordGraph_chain_trace s r edges x xs chain, ?_⟩
  apply (pair_mem_finiteWordGraph s (x :: xs) xs.length _).2
  refine ⟨by simp, ?_⟩
  simp only [List.get_eq_getElem, List.getLast_eq_getElem, List.length_cons, Nat.add_sub_cancel]

theorem reflTransGen_iff_finiteWordGraph_path {B : Type u} (s : Presentation B)
    (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y) (x y : B) :
    Relation.ReflTransGen r x y ↔ ∃ xs : List B,
      FiniteRelationPathCode ZFSet.omega s.carrier R (s.encode x) (s.encode y)
        (finiteWordGraph s xs) := by
  constructor
  · intro path
    obtain ⟨xs, chain, last⟩ := List.exists_isChain_cons_of_relationReflTransGen path
    exact ⟨x :: xs, last ▸ finiteWordGraph_chain_path s r edges x xs chain⟩
  · rintro ⟨xs, code⟩
    exact code.reflTransGen s r edges





end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem pair_mem_finitePathClosure_iff (A R x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ M.finitePathClosure A R ↔
      x ∈ A ∧ y ∈ A ∧ ∃ t ∈ M.finiteWords A, FiniteRelationPathCode ZFSet.omega A R x y t := by
  rw [finitePathClosure, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a, ha, b, hb, t, ht, eq, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨ha, hb, t, ht, code⟩
  · rintro ⟨hx, hy, t, ht, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, t, ht, rfl, code⟩

theorem finitePathClosure_subset (A R : ZFSet.{u}) :
    M.finitePathClosure A R ⊆ ZFSet.prod A A :=
  fun _ h => (ZFSet.mem_sep.1 h).1

theorem finitePathClosure_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A R : ZFSet.{u}} (hA : A ∈ M.sets) (hR : R ∈ M.sets) :
    M.finitePathClosure A R ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  have hPaths := M.finiteWords_mem pairing unions powers separation infinite hA
  have hZero := M.empty_mem ⟨A, hA⟩
  let params := extend A (extend R (extend ZFSet.omega (extend (M.finiteWords A)
    (extend ∅ Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.finitePathClosureEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hA (Fin.cases hR (Fin.cases hOmega (Fin.cases hPaths
      (Fin.cases hZero (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hA hA)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.finitePathClosureEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod A A) = M.finitePathClosure A R := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, finitePathClosure, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_finitePathClosureEntryFormula _ _ _ _ _ _ _ rfl)
  exact equal ▸ selected

theorem pair_mem_finitePathClosure
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {B : Type u} (s : Presentation B) (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    (hB : s.carrier ∈ M.sets) (x y : B) :
    ZFSet.pair (s.encode x) (s.encode y) ∈ M.finitePathClosure s.carrier R ↔
      Relation.ReflTransGen r x y := by
  rw [M.pair_mem_finitePathClosure_iff]
  constructor
  · rintro ⟨_, _, t, _, code⟩
    exact code.reflTransGen s r edges
  · intro path
    obtain ⟨xs, code⟩ := (reflTransGen_iff_finiteWordGraph_path s r edges x y).1 path
    exact ⟨s.encode_mem x, s.encode_mem y, finiteWordGraph s xs,
      finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB xs, code⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})
  (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
  (unions : Realize M.sets SetFormula.union Fin.elim0)
  (separation : SeparationSchema M.sets)
  (infinite : Realize M.sets infinity Fin.elim0)
  {B : Type u} (s : Presentation B) (r : B → B → Prop) {R : ZFSet.{u}}
  (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
  (hB : s.carrier ∈ M.sets)

include pairing unions separation infinite edges hB in
theorem finitePathClosure_equivalence (symmetric : ∀ ⦃left right⦄, r left right → r right left) :
    EquivalenceRelationCode s.carrier (M.finitePathClosure s.carrier R) := by
  let : Std.Symm r := ⟨fun _ _ related => symmetric related⟩
  have exactPath := M.pair_mem_finitePathClosure pairing unions separation infinite s r edges hB
  refine ⟨M.finitePathClosure_subset s.carrier R, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    exact (exactPath a a).2 .refl
  · intro x y xy
    obtain ⟨hx, hy, _⟩ := (M.pair_mem_finitePathClosure_iff s.carrier R x y).1 xy
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (s.mem_carrier y).1 hy
    exact (exactPath b a).2 (symm ((exactPath a b).1 xy))
  · intro x y z xy yz
    obtain ⟨hx, hy, _⟩ := (M.pair_mem_finitePathClosure_iff s.carrier R x y).1 xy
    have hz := ((M.pair_mem_finitePathClosure_iff s.carrier R y z).1 yz).2.1
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨c, rfl⟩ := (s.mem_carrier z).1 hz
    exact (exactPath a c).2 (((exactPath a b).1 xy).trans ((exactPath b c).1 yz))

include pairing unions separation infinite edges hB in
theorem finitePathQuotient_spec
    (powers : Realize M.sets powerSet Fin.elim0) (hR : R ∈ M.sets)
    (symmetric : ∀ ⦃left right⦄, r left right → r right left) :
    let E := M.finitePathClosure s.carrier R
    E ∈ M.sets ∧ EquivalenceRelationCode s.carrier E ∧
      equivalenceClasses s.carrier E ∈ M.sets ∧ equivalenceClassifier s.carrier E ∈ M.sets ∧
      ZFSet.IsFunc s.carrier (equivalenceClasses s.carrier E) (equivalenceClassifier s.carrier E) ∧
      (∀ C ∈ equivalenceClasses s.carrier E, ∃ x ∈ s.carrier,
        ZFSet.pair x C ∈ equivalenceClassifier s.carrier E) ∧
      (∀ x y C D, ZFSet.pair x C ∈ equivalenceClassifier s.carrier E →
        ZFSet.pair y D ∈ equivalenceClassifier s.carrier E → (C = D ↔ ZFSet.pair x y ∈ E)) := by
  dsimp only
  have ground := M.finitePathClosure_mem pairing unions powers separation infinite hB hR
  have equivalence := M.finitePathClosure_equivalence pairing unions separation infinite s r edges hB symmetric
  exact ⟨ground, equivalence,
    M.equivalenceClasses_spec pairing unions powers separation hB ground equivalence⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundFlatCopyPresentation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open Compression.RecursiveMaps Attachment CosetGeometry
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : TileRequests.Family P R) (a : OrderAction J P)
variable (s : Presentation (External J f.Letters)) (t : Presentation A) {steps : ZFSet.{u}}
variable (edges : ∀ x y, ZFSet.pair ((s.product t).encode x) ((s.product t).encode y) ∈ steps ↔ f.FlatStep a x y)
variable (hE : s.carrier ∈ M.sets) (hU : t.carrier ∈ M.sets)

include pairing unions powers separation infinite edges hE hU in
theorem flatCopyEquivalence_code :
    EquivalenceRelationCode (ZFSet.prod s.carrier t.carrier)
      (M.finitePathClosure (ZFSet.prod s.carrier t.carrier) steps) :=
  M.finitePathClosure_equivalence pairing unions separation infinite (s.product t) (f.FlatStep a)
    edges (M.prod_mem pairing unions powers separation hE hU) (fun _ _ h => h.symm)

include pairing unions powers separation infinite edges hE hU in
theorem pair_mem_flatCopyEquivalence (x y : f.FlatLabel (J := J)) :
    ZFSet.pair ((s.product t).encode x) ((s.product t).encode y) ∈
      M.finitePathClosure (ZFSet.prod s.carrier t.carrier) steps ↔ f.FlatPath a x y :=
  M.pair_mem_finitePathClosure pairing unions separation infinite (s.product t) (f.FlatStep a)
    edges (M.prod_mem pairing unions powers separation hE hU) x y

noncomputable def flatCopyPresentation : Presentation (f.Node a) :=
  ((s.product t).quotientPresentation (f.flatSetoid a)
    (M.flatCopyEquivalence_code pairing unions powers separation infinite f a s t edges hE hU)
    (M.pair_mem_flatCopyEquivalence pairing unions powers separation infinite f a s t edges hE hU)).reindex
    (f.flatQuotientEquiv a).symm

theorem flatCopyPresentation_encode_copy (w : External J f.Letters) (x : A) :
    (M.flatCopyPresentation pairing unions powers separation infinite f a s t edges hE hU).encode
      ((f.copy a w).toFun x) =
      equivalenceClass (ZFSet.prod s.carrier t.carrier)
        (M.finitePathClosure (ZFSet.prod s.carrier t.carrier) steps)
        (ZFSet.pair (s.encode w) (t.encode x)) := by
  change (s.product t).quotientEncode (f.flatSetoid a)
    (M.flatCopyEquivalence_code pairing unions powers separation infinite f a s t edges hE hU)
    (M.pair_mem_flatCopyEquivalence pairing unions powers separation infinite f a s t edges hE hU)
    ((f.flatQuotientEquiv a).symm ((f.copy a w).toFun x)) = _
  rw [← f.flatQuotientEquiv_class a w x, Equiv.symm_apply_apply]
  rfl

theorem flatCopyClassifier_eq_graph :
    equivalenceClassifier (ZFSet.prod s.carrier t.carrier)
      (M.finitePathClosure (ZFSet.prod s.carrier t.carrier) steps) =
    (s.product t).graph (M.flatCopyPresentation pairing unions powers separation infinite f a s t edges hE hU)
      (fun x => (f.copy a x.1).toFun x.2) := by
  apply ZFSet.ext
  intro z
  rw [mem_equivalenceClassifier, Presentation.mem_graph]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨⟨w, x⟩, rfl⟩ := ((s.product t).mem_carrier y).1 hy
    exact ⟨(w, x), by rw [M.flatCopyPresentation_encode_copy]; rfl⟩
  · rintro ⟨⟨w, x⟩, rfl⟩
    refine ⟨ZFSet.pair (s.encode w) (t.encode x), (s.product t).encode_mem (w, x), ?_⟩
    rw [M.flatCopyPresentation_encode_copy]
    rfl

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundExternalWordQuotient
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

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

include pairing unions powers separation infinite

theorem externalWordEquivalence_code {G S m one : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) :
    EquivalenceRelationCode (M.finiteWords (externalGeneratorAlphabet G S))
      (M.externalWordEquivalence G S m one) := by
  let W := M.finiteWords (externalGeneratorAlphabet G S)
  let p := SetMembers.presentation W
  have hW : W ∈ M.sets := M.finiteWords_mem pairing unions powers separation infinite
    (M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS)
  exact M.finitePathClosure_equivalence pairing unions separation infinite p
    (fun x y => ZFSet.pair (p.encode x) (p.encode y) ∈ M.externalWordSteps G S m one)
    (fun _ _ => Iff.rfl) hW (fun _ _ entry => externalWordStepGraph_symmetric entry)

variable {J L : Type u} [Group J] (s : Presentation J) (t : Presentation L)
variable (hG : s.carrier ∈ M.sets) (hS : t.carrier ∈ M.sets)

include pairing unions powers separation infinite hG hS in
theorem pair_mem_externalWordEquivalence (xs ys : List (J ⊕ (L × Bool))) :
    ZFSet.pair (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) ys) ∈
        M.externalWordEquivalence s.carrier t.carrier
          ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1) ↔
      ExternalWordRewrite.Path xs ys := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  let a := externalGeneratorAlphabetPresentation s t
  let w := finiteWordPresentation a M pairing unions separation infinite hAlphabet
  exact M.pair_mem_finitePathClosure pairing unions separation infinite w ExternalWordRewrite.Step
    (M.pair_mem_externalWordSteps s t pairing unions separation infinite hAlphabet)
    (M.finiteWords_mem pairing unions powers separation infinite hAlphabet) xs ys

include pairing unions powers separation infinite hG hS in
theorem pair_mem_externalWordEquivalence_congruence (xs ys : List (J ⊕ (L × Bool))) :
    ZFSet.pair (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs)
      (finiteWordGraph (externalGeneratorAlphabetPresentation s t) ys) ∈
        M.externalWordEquivalence s.carrier t.carrier
          ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1) ↔
      ExternalWordRewrite.congruence J L xs ys :=
  (M.pair_mem_externalWordEquivalence pairing unions powers separation infinite s t hG hS xs ys).trans
    (ExternalWordRewrite.path_iff_conGen xs ys)

noncomputable def externalWordQuotientPresentation : Presentation (ExternalWordRewrite.WordQuotient J L) :=
  let a := externalGeneratorAlphabetPresentation s t
  let hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  let w := finiteWordPresentation a M pairing unions separation infinite hAlphabet
  w.quotientPresentation (ExternalWordRewrite.congruence J L).toSetoid
    (M.externalWordEquivalence_code pairing unions powers separation infinite hG hS)
    (M.pair_mem_externalWordEquivalence_congruence pairing unions powers separation infinite s t hG hS)

theorem externalWordQuotientPresentation_encode_mk (xs : List (J ⊕ (L × Bool))) :
    (M.externalWordQuotientPresentation pairing unions powers separation infinite s t hG hS).encode
      (ExternalWordRewrite.quotientMap J L xs) =
        equivalenceClass (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier))
          (M.externalWordEquivalence s.carrier t.carrier
            ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1))
          (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs) := rfl

theorem externalWordClassifier_eq_graph :
    equivalenceClassifier (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier))
      (M.externalWordEquivalence s.carrier t.carrier
        ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)) =
      (finiteWordPresentation (externalGeneratorAlphabetPresentation s t) M pairing unions separation infinite
        (M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS)).graph
        (M.externalWordQuotientPresentation pairing unions powers separation infinite s t hG hS)
        (ExternalWordRewrite.quotientMap J L) := by
  exact (finiteWordPresentation (externalGeneratorAlphabetPresentation s t) M
    pairing unions separation infinite
    (M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS)).quotientClassifier_eq_graph
      (ExternalWordRewrite.congruence J L).toSetoid
      (M.externalWordEquivalence_code pairing unions powers separation infinite hG hS)
      (M.pair_mem_externalWordEquivalence_congruence pairing unions powers separation infinite s t hG hS)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalGroupOperationGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open Compression.RecursiveMaps.CosetGeometry
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable {J L : Type u} [Group J] (s : Presentation J) (t : Presentation L)
variable (hG : s.carrier ∈ M.sets) (hS : t.carrier ∈ M.sets)

noncomputable def externalGroupPresentation : Presentation (External J L) :=
  (M.externalWordQuotientPresentation pairing unions powers separation infinite s t hG hS).reindex
    (ExternalWordRewrite.quotientEquiv J L).symm.toEquiv

theorem externalGroupPresentation_encode_evalWord (xs : List (J ⊕ (L × Bool))) :
    (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS).encode
      (ExternalWordRewrite.evalWord J L xs) =
        equivalenceClass (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier))
          (M.externalWordEquivalence s.carrier t.carrier
            ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1))
          (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs) := by
  change (M.externalWordQuotientPresentation pairing unions powers separation infinite s t hG hS).encode
    (ExternalWordRewrite.fromExternal J L (ExternalWordRewrite.evalWord J L xs)) = _
  rw [ExternalWordRewrite.fromExternal_evalWord]
  exact M.externalWordQuotientPresentation_encode_mk pairing unions powers separation infinite s t hG hS xs

theorem externalGroupClassifier_eq_graph :
    equivalenceClassifier (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier))
      (M.externalWordEquivalence s.carrier t.carrier
        ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)) =
      (finiteWordPresentation (externalGeneratorAlphabetPresentation s t) M pairing unions separation infinite
        (M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS)).graph
        (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS)
        (ExternalWordRewrite.evalWord J L) := by
  let words := finiteWordPresentation (externalGeneratorAlphabetPresentation s t) M
    pairing unions separation infinite
    (M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS)
  let quotient := M.externalWordQuotientPresentation pairing unions powers separation infinite s t hG hS
  refine (M.externalWordClassifier_eq_graph pairing unions powers separation infinite s t hG hS).trans ?_
  refine Eq.trans ?_ (quotient.graph_reindex
    (ExternalWordRewrite.quotientEquiv J L).symm.toEquiv words (ExternalWordRewrite.evalWord J L)).symm
  exact congrArg (words.graph quotient)
    (funext fun xs => (ExternalWordRewrite.fromExternal_evalWord J L xs).symm)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open Compression.RecursiveMaps.CosetGeometry
universe u
variable (M : TransitiveGround.{u})

noncomputable def externalGroupInverse (G S m inv one : ZFSet.{u}) : ZFSet.{u} :=
  quotientUnaryGraph (M.finiteWords (externalGeneratorAlphabet G S))
    (M.externalGroupCarrier G S m one) (M.externalGroupProjection G S m one)
    (M.externalInverseWordGraph G S inv)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

variable {J L : Type u} [Group J] (s : Presentation J) (t : Presentation L)
variable (hG : s.carrier ∈ M.sets) (hS : t.carrier ∈ M.sets)

theorem externalGroupMultiplication_eq_graph :
    let q := M.externalGroupPresentation pairing unions powers separation infinite s t hG hS
    M.externalGroupMultiplication s.carrier t.carrier
      ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1) =
      (q.product q).graph q (fun p => p.1 * p.2) := by
  dsimp only
  unfold externalGroupMultiplication externalGroupProjection
  rw [M.externalGroupClassifier_eq_graph pairing unions powers separation infinite s t hG hS]
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have append := M.finiteWordAppendGraph_eq_graph pairing unions separation infinite
    (externalGeneratorAlphabetPresentation s t) hAlphabet
  change M.finiteWordAppendGraph (externalGeneratorAlphabet s.carrier t.carrier) = _ at append
  rw [append]
  exact quotientBinaryGraph_eq_graph
    (finiteWordPresentation (externalGeneratorAlphabetPresentation s t) M pairing unions separation infinite hAlphabet)
    (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS)
    (ExternalWordRewrite.evalWord J L) List.append
    (fun x y => x * y) (ExternalWordRewrite.evalWord_surjective J L)
    (fun x y => (ExternalWordRewrite.evalWord J L).map_mul x y)

theorem externalGroupIdentity_eq_encode :
    M.externalGroupIdentity s.carrier t.carrier
      ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1) =
      (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS).encode 1 := by
  have unit : ExternalWordRewrite.evalWord J L [] = 1 := (ExternalWordRewrite.evalWord J L).map_one
  have encoded := M.externalGroupPresentation_encode_evalWord pairing unions powers separation infinite
    s t hG hS []
  rw [unit, finiteWordGraph_nil] at encoded
  exact encoded.symm

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalGenerators
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

theorem pair_mem_externalActorSymbolGraph (G S g a : ZFSet.{u}) :
    ZFSet.pair g a ∈ externalActorSymbolGraph G S ↔ g ∈ G ∧ a = externalActorSymbol g := by
  constructor
  · intro h
    obtain ⟨_, g', hg, a', _, eq, value⟩ := ZFSet.mem_sep.1 h
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hg, value⟩
  · rintro ⟨hg, rfl⟩
    have ha := (externalActorSymbol_mem G S g).2 hg
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, ha⟩, g, hg, _, ha, rfl, rfl⟩

theorem pair_mem_externalGeneratorSymbolGraph (G S s a : ZFSet.{u}) :
    ZFSet.pair s a ∈ externalGeneratorSymbolGraph G S ↔ s ∈ S ∧ a = externalLetterSymbol s true := by
  constructor
  · intro h
    obtain ⟨_, s', hs, a', _, eq, value⟩ := ZFSet.mem_sep.1 h
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hs, value⟩
  · rintro ⟨hs, rfl⟩
    have ha := (externalLetterSymbol_mem G S s true).2 hs
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hs, ha⟩, s, hs, _, ha, rfl, rfl⟩

theorem externalActorSymbolGraph_eq_graph {J L : Type u} (s : Presentation J) (t : Presentation L) :
    externalActorSymbolGraph s.carrier t.carrier = s.graph
      (externalGeneratorAlphabetPresentation s t) Sum.inl := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  constructor
  · intro hz
    obtain ⟨g, hg, a, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    have value := ((pair_mem_externalActorSymbolGraph _ _ g a).1 hz).2
    obtain ⟨g, rfl⟩ := (s.mem_carrier g).1 hg
    exact ⟨g, congrArg (ZFSet.pair (s.encode g)) value.symm⟩
  · rintro ⟨g, rfl⟩
    exact (pair_mem_externalActorSymbolGraph _ _ _ _).2 ⟨s.encode_mem g, rfl⟩

theorem externalGeneratorSymbolGraph_eq_graph {J L : Type u}
    (s : Presentation J) (t : Presentation L) :
    externalGeneratorSymbolGraph s.carrier t.carrier = t.graph
      (externalGeneratorAlphabetPresentation s t) (fun a => Sum.inr (a, true)) := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  constructor
  · intro hz
    obtain ⟨l, hl, a, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    have value := ((pair_mem_externalGeneratorSymbolGraph _ _ l a).1 hz).2
    obtain ⟨l, rfl⟩ := (t.mem_carrier l).1 hl
    exact ⟨l, congrArg (ZFSet.pair (t.encode l)) value.symm⟩
  · rintro ⟨l, rfl⟩
    exact (pair_mem_externalGeneratorSymbolGraph _ _ _ _).2 ⟨t.encode_mem l, rfl⟩

end PartitionPilot.Forcing

section

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

theorem pair_mem_singletonWordGraph (A W x w : ZFSet.{u}) :
    ZFSet.pair x w ∈ singletonWordGraph A W ↔ x ∈ A ∧ w ∈ W ∧ w = wordSingleton x := by
  constructor
  · intro h
    obtain ⟨_, y, hy, v, hv, eq, value⟩ := ZFSet.mem_sep.1 h
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hy, hv, value⟩
  · rintro ⟨hx, hw, value⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hx, hw⟩, x, hx, w, hw, rfl, value⟩

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem singletonWordGraph_eq_graph
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {B : Type u} (s : Presentation B) (hA : s.carrier ∈ M.sets) :
    singletonWordGraph s.carrier (M.finiteWords s.carrier) =
      s.graph (finiteWordPresentation s M pairing unions separation infinite hA) (fun x => [x]) := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  constructor
  · intro hz
    obtain ⟨x, hx, w, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    have value := ((pair_mem_singletonWordGraph _ _ x w).1 hz).2.2
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    exact ⟨x, congrArg (ZFSet.pair (s.encode x)) ((finiteWordGraph_singleton s x).trans value.symm)⟩
  · rintro ⟨x, rfl⟩
    exact (pair_mem_singletonWordGraph _ _ _ _).2 ⟨s.encode_mem x,
      finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hA [x],
      finiteWordGraph_singleton s x⟩

end TransitiveGround

end PartitionPilot.Forcing

end

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

structure GroundExternalGroupData (M : TransitiveGround.{u}) (G S m inv one : ZFSet.{u}) : Prop where
  carrier_mem : M.externalGroupCarrier G S m one ∈ M.sets
  multiplication_mem : M.externalGroupMultiplication G S m one ∈ M.sets
  inverse_mem : M.externalGroupInverse G S m inv one ∈ M.sets
  identity_mem : M.externalGroupIdentity G S m one ∈ M.sets
  projection_mem : M.externalGroupProjection G S m one ∈ M.sets
  group_code : GroupCode (M.externalGroupCarrier G S m one)
    (M.externalGroupMultiplication G S m one) (M.externalGroupInverse G S m inv one)
    (M.externalGroupIdentity G S m one)

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
open Compression.RecursiveMaps.CosetGeometry
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

variable {J L : Type u} [Group J] (s : Presentation J) (t : Presentation L)
variable (hG : s.carrier ∈ M.sets) (hS : t.carrier ∈ M.sets)

theorem externalSymbolClasses_eq_graph :
    M.externalSymbolClasses s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2))
      (s.encode 1) = (externalGeneratorAlphabetPresentation s t).graph
        (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS)
        (ExternalWordRewrite.symbolValue J L) := by
  let a := externalGeneratorAlphabetPresentation s t
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  let w := finiteWordPresentation a M pairing unions separation infinite hAlphabet
  let q := M.externalGroupPresentation pairing unions powers separation infinite s t hG hS
  unfold externalSymbolClasses externalGroupProjection
  dsimp only
  have singleton := M.singletonWordGraph_eq_graph pairing unions separation infinite a hAlphabet
  change singletonWordGraph (externalGeneratorAlphabet s.carrier t.carrier)
    (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier)) = _ at singleton
  rw [singleton, M.externalGroupClassifier_eq_graph pairing unions powers separation infinite s t hG hS]
  have composed := a.relationCompose_graph w q (fun x => [x]) (ExternalWordRewrite.evalWord J L)
  have single : (fun x : J ⊕ (L × Bool) => ExternalWordRewrite.evalWord J L [x]) =
      ExternalWordRewrite.symbolValue J L := by
    rfl
  rw [single] at composed
  exact composed

theorem externalOldInclusion_eq_graph :
    M.externalOldInclusion s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2))
      (s.encode 1) = s.graph
        (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS) (old J L) := by
  unfold externalOldInclusion
  rw [externalActorSymbolGraph_eq_graph,
    M.externalSymbolClasses_eq_graph pairing unions powers separation infinite s t hG hS]
  exact s.relationCompose_graph (externalGeneratorAlphabetPresentation s t)
    (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS)
    Sum.inl (ExternalWordRewrite.symbolValue J L)

theorem externalChildGenerators_eq_graph :
    M.externalChildGenerators s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2))
      (s.encode 1) = t.graph
        (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS) (generator J L) := by
  unfold externalChildGenerators
  rw [externalGeneratorSymbolGraph_eq_graph,
    M.externalSymbolClasses_eq_graph pairing unions powers separation infinite s t hG hS]
  exact t.relationCompose_graph (externalGeneratorAlphabetPresentation s t)
    (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS)
    (fun x => Sum.inr (x, true)) (ExternalWordRewrite.symbolValue J L)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalGroupEmbeddings
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

namespace GroupEmbeddingCode

theorem identity {G m inv one : ZFSet.{u}} (group : GroupCode G m inv one) :
    GroupEmbeddingCode G G m m one one (identityFunctionGraph G) := by
  refine ⟨identityFunctionGraph_injection G,
    (pair_mem_identityFunctionGraph G one one).2 ⟨rfl, group.identity_mem⟩, ?_⟩
  intro a b c a' b' c' product first second third
  obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph G a a').1 first
  obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph G b b').1 second
  obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph G c c').1 third
  exact product

end GroupEmbeddingCode
end PartitionPilot.Forcing

namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {G H : Type u} [Group G] [Group H]

theorem groupEmbeddingCode (s : Presentation G) (t : Presentation H)
    (f : G →* H) (injective : Function.Injective f) :
    GroupEmbeddingCode s.carrier t.carrier
      ((s.product s).graph s (fun p => p.1 * p.2))
      ((t.product t).graph t (fun p => p.1 * p.2)) (s.encode 1) (t.encode 1) (s.graph t f) := by
  refine ⟨s.graph_injection t f injective, (s.pair_mem_graph t f 1 1).2 f.map_one, ?_⟩
  intro a b c a' b' c' product first second third
  obtain ⟨a, aa⟩ := (s.mem_graph t f _).1 first
  obtain ⟨b, bb⟩ := (s.mem_graph t f _).1 second
  obtain ⟨c, cc⟩ := (s.mem_graph t f _).1 third
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 aa
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 bb
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 cc
  have mul := ((s.product s).pair_mem_graph s _ (a, b) c).1 product
  exact ((t.product t).pair_mem_graph t _ (f a, f b) (f c)).2 (by rw [← mul, f.map_mul])

end PartitionPilot.SetRealization.Presentation



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open Compression.RecursiveMaps.CosetGeometry
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

include pairing unions powers separation infinite in
theorem externalOldInclusion_groupEmbedding_of_presentation
    {J L : Type u} [Group J] (s : Presentation J) (t : Presentation L)
    (hG : s.carrier ∈ M.sets) (hS : t.carrier ∈ M.sets) :
    let m := (s.product s).graph s (fun p => p.1 * p.2)
    GroupEmbeddingCode s.carrier (M.externalGroupCarrier s.carrier t.carrier m (s.encode 1))
      m (M.externalGroupMultiplication s.carrier t.carrier m (s.encode 1))
      (s.encode 1) (M.externalGroupIdentity s.carrier t.carrier m (s.encode 1))
      (M.externalOldInclusion s.carrier t.carrier m (s.encode 1)) := by
  dsimp only
  rw [M.externalOldInclusion_eq_graph pairing unions powers separation infinite s t hG hS,
    M.externalGroupMultiplication_eq_graph pairing unions powers separation infinite s t hG hS,
    M.externalGroupIdentity_eq_encode pairing unions powers separation infinite s t hG hS]
  exact s.groupEmbeddingCode
    (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS)
    (old J L) (old_injective J L)

include pairing unions powers separation infinite in
theorem externalOldInclusion_groupEmbedding {G S m inv one : ZFSet.{u}}
    (group : GroupCode G m inv one) (hG : G ∈ M.sets) (hS : S ∈ M.sets) :
    GroupEmbeddingCode G (M.externalGroupCarrier G S m one)
      m (M.externalGroupMultiplication G S m one) one (M.externalGroupIdentity G S m one)
      (M.externalOldInclusion G S m one) := by
  let := group.toGroup
  have code := M.externalOldInclusion_groupEmbedding_of_presentation pairing unions powers separation infinite
    (SetMembers.presentation G) (SetMembers.presentation S) hG hS
  dsimp only at code
  rw [group.multiplication_graph_eq, group.identity_code_eq] at code
  exact code

end PartitionPilot.Forcing.TransitiveGround

end

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
universe u

namespace GroundCofinalRegular
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}

theorem regular (cofinalRegular : GroundCofinalRegular M K) (ordinal : ordinalSetProperty K) :
    GroundRegular M K := by
  classical
  intro α hα f hf function
  have missing : ∃ δ ∈ K, ¬ ∃ x ∈ α, ∃ y ∈ K,
      ZFSet.pair x y ∈ f ∧ (δ = y ∨ δ ∈ y) := by
    by_contra noMissing
    apply cofinalRegular α hα f hf
    refine ⟨function, ?_⟩
    intro β hβ
    by_contra gap
    exact noMissing ⟨β, hβ, gap⟩
  obtain ⟨δ, hδ, gap⟩ := missing
  refine ⟨δ, hδ, ?_⟩
  intro x y entry
  obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.1 (function.1 entry)
  rcases ordinalSetProperty_mem_compare ordinal hδ hy with above | equal | below
  · exact False.elim (gap ⟨x, hx, y, hy, entry, Or.inr above⟩)
  · exact False.elim (gap ⟨x, hx, y, hy, entry, Or.inl equal⟩)
  · exact below

end GroundCofinalRegular

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem exists_groundCardinalRepresentative {α : ZFSet.{u}}
    (hα : α ∈ M.sets) (ordinal : ordinalSetProperty α) :
    ∃ κ ∈ M.sets, GroundCardinal M κ ∧ (κ = α ∨ κ ∈ α) ∧
      ∃ f ∈ M.sets, InjectionCode α κ f ∧
        identityFunctionGraph κ ∈ M.sets ∧ InjectionCode κ α (identityFunctionGraph κ) := by
  classical
  let candidates : Set ZFSet.{u} := {κ | (κ = α ∨ κ ∈ α) ∧ M.groundEmbeddable α κ}
  have present : candidates.Nonempty := ⟨α, Or.inl rfl, identityFunctionGraph α,
    M.identityFunctionGraph_mem pairing unions powers separation hα,
    identityFunctionGraph_injection α⟩
  obtain ⟨κ, member, minimal⟩ := ZFSet.mem_wf.has_min candidates present
  have bound : κ = α ∨ κ ∈ α := member.1
  have hκ : κ ∈ M.sets := bound.elim (fun equal => equal ▸ hα) (M.transitive hα)
  have ordκ : ordinalSetProperty κ := bound.elim (fun equal => equal ▸ ordinal)
    (ordinalSetProperty_member ordinal)
  have subset : κ ⊆ α := bound.elim (fun equal => equal ▸ (fun _ hx => hx))
    (fun smaller x hx => ordinal.1 κ smaller x hx)
  obtain ⟨f, hf, forward⟩ := member.2
  have cardinal : GroundCardinal M κ := by
    refine ⟨ordκ, fun β hβ smaller => ?_⟩
    obtain ⟨g, hg, injection⟩ := smaller
    have hβM := M.transitive hκ hβ
    have candidate : β ∈ candidates := ⟨Or.inr (subset hβ),
      relationCompose α κ β f g,
      M.relationCompose_mem pairing unions powers separation hα hκ hβM hf hg,
      forward.compose injection⟩
    exact minimal β candidate hβ
  exact ⟨κ, hκ, cardinal, bound, f, hf, forward,
    M.identityFunctionGraph_mem pairing unions powers separation hκ,
    (identityFunctionGraph_injection κ).retarget subset⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCardinalStrongLimit
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}

theorem to_groundStrongLimit (strong : GroundCardinalStrongLimit M K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) : GroundStrongLimit M K := by
  intro α hα
  have hαM := M.transitive hK hα
  obtain ⟨κ, hκM, cardinal, bound, f, hf, injection, _, _⟩ :=
    M.exists_groundCardinalRepresentative pairing unions powers separation hαM
      (ordinalSetProperty_member ordinal hα)
  have hκ : κ ∈ K := bound.elim (fun equal => equal ▸ hα) (ordinal.1 α hα κ)
  exact (strong κ hκ cardinal).of_embeddable pairing unions powers separation
    (M.groundPower_mem powers hαM) (M.groundPower_mem powers hκM) hK
    (M.groundEmbeddable_power pairing unions powers separation hαM hκM ⟨f, hf, injection⟩)

end GroundCardinalStrongLimit

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundHeightPushforward
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {A B : Type u} (s : Presentation A) (t : Presentation B)
variable {P : MeetOrder A} {Q : MeetOrder B} (embedding : MeetEmbedding P Q)
variable {r μ v ν : ZFSet.{u}}
variable (source : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ r ↔ P.le x y)
variable (target : ∀ x y, ZFSet.pair (t.encode x) (t.encode y) ∈ v ↔ Q.le x y)
variable (sourceMeet : ∀ x y z, ZFSet.pair (ZFSet.pair (s.encode x) (s.encode y)) (s.encode z) ∈ μ ↔ P.meet x y = z)
variable (targetMeet : ∀ x y z, ZFSet.pair (ZFSet.pair (t.encode x) (t.encode y)) (t.encode z) ∈ ν ↔ Q.meet x y = z)

include source target sourceMeet targetMeet in
theorem meetEmbeddingCode : MeetEmbeddingCode s.carrier t.carrier r v μ ν (s.graph t embedding.toFun) := by
  have injective : Function.Injective embedding.toFun := by
    intro x y equal
    apply P.antisymm
    · apply (embedding.le_iff x y).1
      rw [equal]
      exact Q.refl _
    · apply (embedding.le_iff y x).1
      rw [equal]
      exact Q.refl _
  refine ⟨s.graph_injection t _ injective, ?_, ?_⟩
  · intro x y a b lower first second
    have hx := (ZFSet.pair_mem_prod.1 ((s.graph_isFunc t embedding.toFun).1 first)).1
    have hy := (ZFSet.pair_mem_prod.1 ((s.graph_isFunc t embedding.toFun).1 second)).1
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    have ha := (ZFSet.pair_mem_prod.1 ((s.graph_isFunc t embedding.toFun).1 first)).2
    have hb := (ZFSet.pair_mem_prod.1 ((s.graph_isFunc t embedding.toFun).1 second)).2
    obtain ⟨a, rfl⟩ := (t.mem_carrier a).1 ha
    obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 hb
    have ea := (s.pair_mem_graph t embedding.toFun x a).1 first
    have eb := (s.pair_mem_graph t embedding.toFun y b).1 second
    apply (target a b).2
    rw [← ea, ← eb]
    exact (embedding.le_iff x y).2 ((source x y).1 lower)
  · intro x y z a b c meet first second third
    have graph := s.graph_isFunc t embedding.toFun
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 (ZFSet.pair_mem_prod.1 (graph.1 first)).1
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 (ZFSet.pair_mem_prod.1 (graph.1 second)).1
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 (ZFSet.pair_mem_prod.1 (graph.1 third)).1
    obtain ⟨a, rfl⟩ := (t.mem_carrier a).1 (ZFSet.pair_mem_prod.1 (graph.1 first)).2
    obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 (ZFSet.pair_mem_prod.1 (graph.1 second)).2
    obtain ⟨c, rfl⟩ := (t.mem_carrier c).1 (ZFSet.pair_mem_prod.1 (graph.1 third)).2
    have ea := (s.pair_mem_graph t embedding.toFun x a).1 first
    have eb := (s.pair_mem_graph t embedding.toFun y b).1 second
    have ec := (s.pair_mem_graph t embedding.toFun z c).1 third
    apply (targetMeet a b c).2
    rw [← ea, ← eb, ← ec, ← (sourceMeet x y z).1 meet]
    exact (embedding.map_meet x y).symm

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open Compression.RecursiveMaps Attachment CosetGeometry
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : TileRequests.Family P R) (a : OrderAction J P)
variable (s : Presentation (External J f.Letters)) (t : Presentation A) {steps : ZFSet.{u}}
variable (edges : ∀ x y, ZFSet.pair ((s.product t).encode x) ((s.product t).encode y) ∈ steps ↔ f.FlatStep a x y)
variable (hE : s.carrier ∈ M.sets) (hU : t.carrier ∈ M.sets)

theorem flatCopyClassifier_entry_iff (w : External J f.Letters) (x : A) (z : f.Node a) :
    ZFSet.pair (ZFSet.pair (s.encode w) (t.encode x))
      ((M.flatCopyPresentation pairing unions powers separation infinite f a s t edges hE hU).encode z) ∈
      equivalenceClassifier (ZFSet.prod s.carrier t.carrier)
        (M.finitePathClosure (ZFSet.prod s.carrier t.carrier) steps) ↔ (f.copy a w).toFun x = z := by
  rw [M.flatCopyClassifier_eq_graph pairing unions powers separation infinite f a s t edges hE hU]
  exact (s.product t).pair_mem_graph _ _ (w, x) z

end PartitionPilot.Forcing.TransitiveGround

section

namespace PartitionPilot.SetRealization.Presentation
open Forcing Compression.RecursiveMaps
universe u
variable {A B : Type u} (s : Presentation A) (t : Presentation B)
variable {P : MeetOrder A} {Q : MeetOrder B} (embedding : IdealEmbedding P Q)
variable {r μ v ν : ZFSet.{u}}
variable (source : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ r ↔ P.le x y)
variable (target : ∀ x y, ZFSet.pair (t.encode x) (t.encode y) ∈ v ↔ Q.le x y)
variable (sourceMeet : ∀ x y z, ZFSet.pair (ZFSet.pair (s.encode x) (s.encode y)) (s.encode z) ∈ μ ↔ P.meet x y = z)
variable (targetMeet : ∀ x y z, ZFSet.pair (ZFSet.pair (t.encode x) (t.encode y)) (t.encode z) ∈ ν ↔ Q.meet x y = z)

include source target sourceMeet targetMeet in
theorem idealEmbeddingCode : IdealEmbeddingCode s.carrier t.carrier r v μ ν (s.graph t embedding.toFun) := by
  have function := s.graph_isFunc t embedding.toFun
  refine ⟨s.meetEmbeddingCode t embedding.toMeetEmbedding source target sourceMeet targetMeet, ?_, ?_⟩
  · intro x y x' y' first second lower
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 (ZFSet.pair_mem_prod.1 (function.1 first)).1
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 (ZFSet.pair_mem_prod.1 (function.1 second)).1
    obtain ⟨x', rfl⟩ := (t.mem_carrier x').1 (ZFSet.pair_mem_prod.1 (function.1 first)).2
    obtain ⟨y', rfl⟩ := (t.mem_carrier y').1 (ZFSet.pair_mem_prod.1 (function.1 second)).2
    have firstEq := (s.pair_mem_graph t embedding.toFun x x').1 first
    have secondEq := (s.pair_mem_graph t embedding.toFun y y').1 second
    apply (source x y).2
    apply (embedding.le_iff x y).1
    rw [firstEq, secondEq]
    exact (target x' y').1 lower
  · intro x x' z image hz lower
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 (ZFSet.pair_mem_prod.1 (function.1 image)).1
    obtain ⟨x', rfl⟩ := (t.mem_carrier x').1 (ZFSet.pair_mem_prod.1 (function.1 image)).2
    obtain ⟨z, rfl⟩ := (t.mem_carrier z).1 hz
    have imageEq := (s.pair_mem_graph t embedding.toFun x x').1 image
    have below : Q.le z (embedding.toFun x) := imageEq.symm ▸ (target z x').1 lower
    obtain ⟨y, rfl⟩ := embedding.ideal x z below
    exact ⟨s.encode y, s.encode_mem y, (source y x).2 ((embedding.le_iff y x).1 below),
      (s.pair_mem_graph t embedding.toFun y _).2 rfl⟩

end PartitionPilot.SetRealization.Presentation

end

namespace PartitionPilot.Forcing
open SetFormula SetRealization
open Compression.RecursiveMaps Attachment CosetGeometry
universe u

namespace TransitiveGround

theorem flatCopyEmbeddingGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U Q classifier w : ZFSet.{u}}
    (hU : U ∈ M.sets) (hQ : Q ∈ M.sets) (hClassifier : classifier ∈ M.sets) (hw : w ∈ M.sets) :
    flatCopyEmbeddingGraph U Q classifier w ∈ M.sets := by
  let params := extend U (extend Q (extend classifier (extend w Fin.elim0)))
  have selected := M.bounded_separation_mem separation (BoundedFormula.flatCopyEmbeddingEntryFormula 0 1 2 3 4)
    params (Fin.cases hU (Fin.cases hQ (Fin.cases hClassifier (Fin.cases hw (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation hU hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.flatCopyEmbeddingEntryFormula 0 1 2 3 4)
      (extend z params)) (ZFSet.prod U Q) = flatCopyEmbeddingGraph U Q classifier w := by
    apply ZFSet.ext
    intro z
    rw [flatCopyEmbeddingGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_flatCopyEmbeddingEntryFormula 0 1 2 3 4 _)
  exact equal ▸ selected

end TransitiveGround

variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : TileRequests.Family P R) (a : OrderAction J P)
variable (s : Presentation (External J f.Letters)) (t : Presentation A) (q : Presentation (f.Node a))
variable {classifier r μ : ZFSet.{u}}
variable (classed : ∀ w x z, ZFSet.pair (ZFSet.pair (s.encode w) (t.encode x)) (q.encode z) ∈ classifier ↔
  (f.copy a w).toFun x = z)

include classed in
theorem flatCopyEmbeddingGraph_code
    (related : ∀ x y, ZFSet.pair (t.encode x) (t.encode y) ∈ r ↔ P.le x y)
    (sourceMeet : ∀ x y z, ZFSet.pair (ZFSet.pair (t.encode x) (t.encode y)) (t.encode z) ∈ μ ↔ P.meet x y = z)
    (w : External J f.Letters) :
    let order := flatCopyOrderGraph s.carrier t.carrier q.carrier classifier r
    MeetEmbeddingCode t.carrier q.carrier r order μ (canonicalMeetGraph q.carrier order)
      (flatCopyEmbeddingGraph t.carrier q.carrier classifier (s.encode w)) := by
  dsimp only
  rw [flatCopyEmbeddingGraph_eq_graph f a s t q classed w]
  have order := flatCopy_order_iff f a s t q classed related
  exact t.meetEmbeddingCode q (f.copy a w).toMeetEmbedding related order sourceMeet
    (q.canonicalMeetGraph_iff (f.gluedOrder a) order)

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

namespace GroundDefinableFunction
open SetFormula
universe u

def withAux {M : TransitiveGround.{u}} {n}
    {a f : (Fin n → ZFSet.{u}) → ZFSet.{u}}
    (aux : GroundDefinableFunction M a) (body : SetFormula (n + 2))
    (closed : ∀ env, (∀ i, env i ∈ M.sets) → f env ∈ M.sets)
    (correct : ∀ env, (∀ i, env i ∈ M.sets) → ∀ z ∈ M.sets,
      Realize M.sets body (extend (a env) (extend z env)) ↔ z = f env) :
    GroundDefinableFunction M f where
  formula := ex (.conj
    (SetFormula.reindex (extend 0 (fun i => i.succ.succ)) aux.formula) body)
  closed := closed
  correct := by
    intro env members z hz
    simp only [realize_ex, Realize]
    constructor
    · rintro ⟨value, hvalue, specified, result⟩
      have equal : value = a env := by
        apply (aux.correct env members value hvalue).1
        have meaning := (realize_reindex M.sets _ aux.formula _).1 specified
        rw [map_extend] at meaning
        exact meaning
      subst value
      exact (correct env members z hz).1 result
    · intro equal
      refine ⟨a env, aux.closed env members, ?_, (correct env members z hz).2 equal⟩
      rw [realize_reindex, map_extend]
      exact (aux.correct env members (a env) (aux.closed env members)).2 rfl

def withAuxFamily {M : TransitiveGround.{u}} {n k}
    {a : Fin k → (Fin n → ZFSet.{u}) → ZFSet.{u}}
    {f : (Fin n → ZFSet.{u}) → ZFSet.{u}}
    (aux : ∀ j, GroundDefinableFunction M (a j)) (body : SetFormula (n + 1 + k))
    (closed : ∀ env, (∀ i, env i ∈ M.sets) → f env ∈ M.sets)
    (correct : ∀ env, (∀ i, env i ∈ M.sets) → ∀ z ∈ M.sets,
      Realize M.sets body (extendMany k (fun j => a j env) (extend z env)) ↔ z = f env) :
    GroundDefinableFunction M f where
  formula := exBlock k (.conj
    (conjBlock k (fun j => SetFormula.reindex
      (extend (prefixIndex (n + 1) k j) (fun i => suffixIndex (n + 1) k i.succ)) (aux j).formula)) body)
  closed := closed
  correct := by
    intro env members z hz
    rw [realize_exBlock]
    constructor
    · rintro ⟨fields, fieldMembers, clauses, result⟩
      have each := (realize_conjBlock M.sets _ _ _).1 clauses
      have values : fields = fun j => a j env := by
        funext j
        have meaning := (realize_reindex M.sets _ _ _).1 (each j)
        rw [map_extend] at meaning
        simp only [extendMany_prefix, extendMany_suffix] at meaning
        exact ((aux j).correct env members (fields j) (fieldMembers j)).1 meaning
      exact (correct env members z hz).1 (values ▸ result)
    · intro equal
      let fields : Fin k → ZFSet.{u} := fun j => a j env
      have fieldMembers : ∀ j, fields j ∈ M.sets := fun j => (aux j).closed env members
      refine ⟨fields, fieldMembers, ?_, (correct env members z hz).2 equal⟩
      apply (realize_conjBlock M.sets _ _ _).2
      intro j
      rw [realize_reindex, map_extend]
      simp only [extendMany_prefix, extendMany_suffix]
      exact ((aux j).correct env members (fields j) (fieldMembers j)).2 rfl

end GroundDefinableFunction

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInvariantSuccessors
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

universe u






structure RecursiveCompressionInvariant
    {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
    (seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)
    {D rD μD J Qs rs μs As Es Fs Ss Maps A : ZFSet.{u}}
    {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
    (_h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A) : Prop where
  originalSubset : P0 ⊆ D
  originalOrder : ∀ x ∈ P0, ∀ y ∈ P0, ZFSet.pair x y ∈ rD ↔ ZFSet.pair x y ∈ r0
  originalMeet : ∀ x ∈ P0, ∀ y ∈ P0, ∀ z,
    ZFSet.pair (ZFSet.pair x y) z ∈ μD ↔ ZFSet.pair (ZFSet.pair x y) z ∈ μ0
  originalAction : ∀ g x, x ∈ P0 → ∀ y,
    ZFSet.pair (ZFSet.pair g x) y ∈ A ↔ ZFSet.pair (ZFSet.pair g x) y ∈ A0
  top : ∀ x ∈ D, ZFSet.pair x τ ∈ rD
  agreement : ∀ g ∈ G, ∀ k ∈ G, ∀ v ∈ P0,
    ActionAgreementBelow P0 r0 A0 g k v →
      ActionAgreementBelow d.batchCarrier d.batchOrder A g k v
  negative : ∀ i S a F cap base v w,
    ZFSet.pair i S ∈ Maps → ZFSet.pair i a ∈ Sources → ZFSet.pair i F ∈ Filters →
    ZFSet.pair τ cap ∈ S → ZFSet.pair a base ∈ S → v ∈ P0 → v ∉ F →
    ZFSet.pair (ZFSet.pair cap v) w ∈ d.batchMeetGraph → ZFSet.pair w base ∈ d.batchOrder

namespace RecursiveCompressionInvariant

variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable {D rD μD J Qs rs μs As Es Fs Ss Maps A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (state : RecursiveCompressionInvariant seed h) (s : CodedRecursiveTaskAction h T)

include state s in
theorem compatible : RecursiveRepresentativeCompatibility h T := by
  intro δ i j a g k x y z transport source firstRep secondRep hx below first second
  have hδ := (s.taskAction.entry_shape transport).1
  have hg := (ZFSet.pair_mem_prod.1 (h.representatives.1 firstRep)).2
  have hk := (ZFSet.pair_mem_prod.1 (h.representatives.1 secondRep)).2
  have ha := (ZFSet.pair_mem_prod.1 (seed.sources.1 source)).2
  obtain ⟨product, productEntry, _⟩ := h.group.mul_function.2 (ZFSet.pair δ g)
    (ZFSet.pair_mem_prod.2 ⟨hδ, hg⟩)
  have hp := (ZFSet.pair_mem_prod.1 (h.group.mul_function.1 productEntry)).2
  have agree := state.agreement product hp k hk a ha
    (seed.productAgreement δ i j g k product a transport source firstRep secondRep productEntry)
  have hy := (ZFSet.pair_mem_prod.1 (h.action.function.1 first)).2
  obtain ⟨w, acted, _⟩ := h.action.function.2 (ZFSet.pair δ y)
    (ZFSet.pair_mem_prod.2 ⟨hδ, hy⟩)
  have composed := h.action.mul δ hδ g hg product hp x hx y hy w
    (ZFSet.pair_mem_prod.1 (h.action.function.1 acted)).2 productEntry first acted
  have equal := agree.entry_eq h.action hk hx below composed second
  exact equal ▸ acted

end RecursiveCompressionInvariant

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.RecursiveCompressionInvariant

universe u
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable {D rD μD J Qs rs μs As Es Fs Ss Maps A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (state : RecursiveCompressionInvariant seed h) (s : CodedRecursiveTaskAction h T)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

include state s in
theorem nextAgreement {g k v : ZFSet.{u}} (hg : g ∈ G) (hk : k ∈ G) (hv : v ∈ P0)
    (agree : ActionAgreementBelow P0 r0 A0 g k v) :
    ActionAgreementBelow next.batchCarrier next.batchOrder (h.nextActionGraph T) g k v := by
  let positive : ZFSet.{u} → Prop := fun i => ∃ F, ZFSet.pair i F ∈ Filters ∧ v ∈ F
  apply s.nextAction_agreement M next ⟨g, hg⟩ ⟨k, hk⟩
    ⟨τ, state.originalSubset seed.top_mem⟩ state.top ⟨v, state.originalSubset hv⟩ positive
  · intro i S a cap base w mapEntry source capEntry baseEntry notPositive meet
    let index : {i : ZFSet.{u} // i ∈ I} := ⟨i, h.maps.pair_source mapEntry⟩
    exact state.negative i S a (seed.filters.value index) cap base v w
      mapEntry source (seed.filters.value_entry index) capEntry baseEntry hv
      (fun member => notPositive ⟨seed.filters.value index, seed.filters.value_entry index, member⟩) meet
  · exact state.agreement g hg k hk v hv agree
  · intro i j k pos first second
    obtain ⟨F, entry, member⟩ := pos
    exact seed.positiveAgreement _ _ v i j k F agree entry member first second

include state in
theorem nextNegative
    (entries : ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔
      i ∈ I ∧ f = h.liftSection M next i)
    {i S a F cap base v w : ZFSet.{u}}
    (mapEntry : ZFSet.pair i S ∈ h.groundLiftFamily M next)
    (source : ZFSet.pair i a ∈ Sources) (filter : ZFSet.pair i F ∈ Filters)
    (capEntry : ZFSet.pair τ cap ∈ S) (baseEntry : ZFSet.pair a base ∈ S)
    (hv : v ∈ P0) (negative : v ∉ F)
    (meet : ZFSet.pair (ZFSet.pair cap v) w ∈ next.batchMeetGraph) :
    ZFSet.pair w base ∈ next.batchOrder := by
  obtain ⟨hi, rfl⟩ := (entries i S).1 mapEntry
  let index : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have oldMap := h.maps.value_entry index
  have ha := (ZFSet.pair_mem_prod.1 (h.sources.1 source)).2
  have oldCap := (h.liftSection_old_iff M next oldMap (state.originalSubset seed.top_mem)).1 capEntry
  have oldBase := (h.liftSection_old_iff M next oldMap ha).1 baseEntry
  have embedding := h.valid i (h.maps.value index) oldMap
  exact h.negative_cap_persists M next
    (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 oldCap)).2
    (d.original_carrier_subset state.originalSubset hv)
    (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 oldBase)).2
    (fun z entry => state.negative i (h.maps.value index) a F cap base v z
      oldMap source filter oldCap oldBase hv negative entry) meet

include state s in
theorem nextInvariant
    (entries : ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔
      i ∈ I ∧ f = h.liftSection M next i)
    (nextInputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
      G m inv one (h.nextActionGraph T)) : RecursiveCompressionInvariant seed nextInputs where
  originalSubset := d.original_carrier_subset state.originalSubset
  originalOrder := fun _ hx _ hy => d.original_order_iff state.originalSubset state.originalOrder hx hy
  originalMeet := fun _ hx _ hy _ => d.original_meet_iff state.originalSubset state.originalMeet hx hy
  originalAction := fun _ _ hx _ => h.nextAction_original_iff state.originalSubset state.originalAction hx
  top := d.coding.greatest_preserved (state.originalSubset seed.top_mem) state.top
  agreement := fun _ hg _ hk _ hv agree => state.nextAgreement s M next hg hk hv agree
  negative := fun _ _ _ _ _ _ _ _ mapEntry source filter capEntry baseEntry hv negative meet =>
    state.nextNegative M next entries mapEntry source filter capEntry baseEntry hv negative meet

end PartitionPilot.Forcing.RecursiveCompressionInvariant



namespace PartitionPilot.Forcing
open SetFormula
universe u

structure RecursiveGroundFields (M : TransitiveGround.{u})
    {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
    {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
    (_h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A) : Prop where
  carrier : D ∈ M.sets
  order : rD ∈ M.sets
  meet : μD ∈ M.sets
  indices : J ∈ M.sets
  spaces : Qs ∈ M.sets
  relations : rs ∈ M.sets
  meets : μs ∈ M.sets
  anchors : As ∈ M.sets
  embeddings : Es ∈ M.sets
  filters : Fs ∈ M.sets
  separators : Ss ∈ M.sets
  maps : Maps ∈ M.sets
  action : A ∈ M.sets

namespace RecursiveGroundFields
variable {M : TransitiveGround.{u}}
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (ground : RecursiveGroundFields M h)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include ground pairing unions powers separation

theorem current_codes : d.batchCarrier ∈ M.sets ∧ d.batchOrder ∈ M.sets ∧
    d.batchMeetGraph ∈ M.sets := by
  obtain ⟨hL, hrL, hμL, _, _, _⟩ := M.batchAttachment_ground_codes
    pairing unions powers separation d ground.carrier ground.order ground.indices
      ground.spaces ground.relations ground.meets ground.anchors ground.embeddings ground.filters
  exact ⟨hL, hrL, hμL⟩

theorem next_fields
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) :
    h.nextIndices ∈ M.sets ∧
    pairSecondField I J h.nextIndices Qs ∈ M.sets ∧
    pairSecondField I J h.nextIndices rs ∈ M.sets ∧
    pairSecondField I J h.nextIndices μs ∈ M.sets ∧
    pairSecondField I J h.nextIndices As ∈ M.sets ∧
    M.groundPairCompositions h.nextIndices I J (familyPointBound Qs) D d.batchCarrier Es Maps ∈ M.sets ∧
    M.groundPairPushFilters h.nextIndices I J d.batchCarrier d.batchOrder Maps Fs ∈ M.sets ∧
    recursiveSeparatorFamily h.nextIndices I J D d.batchCarrier Maps Ss ∈ M.sets := by
  obtain ⟨hL, hrL, _⟩ := ground.current_codes pairing unions powers separation
  have hK := h.nextIndices_mem M pairing unions powers separation
    hI ground.indices ground.carrier ground.filters hSources
  have fields {F : ZFSet.{u}} (hF : F ∈ M.sets) : pairSecondField I J h.nextIndices F ∈ M.sets :=
    M.pairFieldGraph_mem pairing unions powers separation false hI ground.indices hK
      (M.union_mem unions (M.union_mem unions hF)) hF
  have subset := recursiveAttachmentIndices_subset I J D Fs.sUnion.sUnion Sources Fs
  exact ⟨hK, fields ground.spaces, fields ground.relations, fields ground.meets,
    fields ground.anchors,
    (M.groundPairCompositions_spec pairing unions powers separation hK hI ground.indices
      (M.familyPointBound_mem unions ground.spaces) ground.carrier hL ground.embeddings
      ground.maps d.embeddings h.maps subset).1,
    (M.groundPairPushFilters_spec pairing unions powers separation hK hI ground.indices
      hL hrL ground.maps ground.filters h.maps d.filters subset).1,
    M.recursiveSeparatorFamily_mem pairing unions powers separation hK hI ground.indices
      ground.carrier hL ground.maps ground.separators⟩

theorem next_codes (next : h.NextInputs M)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) :
    next.batchCarrier ∈ M.sets ∧ next.batchOrder ∈ M.sets ∧ next.batchMeetGraph ∈ M.sets := by
  obtain ⟨hL, hrL, _⟩ := ground.current_codes pairing unions powers separation
  obtain ⟨hK, hQs, hrs, hμs, hAs, hEs, hFs, _⟩ :=
    ground.next_fields pairing unions powers separation hI hSources
  obtain ⟨hC, hrC, hμC, _, _, _⟩ := M.batchAttachment_ground_codes
    pairing unions powers separation next hL hrL hK hQs hrs hμs hAs hEs hFs
  exact ⟨hC, hrC, hμC⟩

theorem next (next : h.NextInputs M)
    (inputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
      G m inv one (h.nextActionGraph T))
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) : RecursiveGroundFields M inputs := by
  obtain ⟨hL, hrL, hμL⟩ := ground.current_codes pairing unions powers separation
  obtain ⟨hK, hQs, hrs, hμs, hAs, hEs, hFs, hSs⟩ :=
    ground.next_fields pairing unions powers separation hI hSources
  obtain ⟨hC, _, _⟩ := ground.next_codes pairing unions powers separation next hI hSources
  have maps := (h.groundLiftFamily_spec M pairing unions powers separation next
    hI ground.indices ground.carrier hL hC ground.spaces ground.relations ground.anchors
      ground.maps hSources ground.filters hReps hG ground.action).2.1
  have action := h.nextActionGraph_mem M pairing unions powers separation
    hI ground.indices ground.carrier hL ground.spaces ground.relations ground.anchors
      ground.filters hSources hG ground.action hT
  exact ⟨hL, hrL, hμL, hK, hQs, hrs, hμs, hAs, hEs, hFs, hSs, maps, action⟩

end RecursiveGroundFields

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.RecursiveCompressionInvariant
open SetFormula
universe u
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable {D rD μD J Qs rs μs As Es Fs Ss Maps A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (state : RecursiveCompressionInvariant seed h) (s : CodedRecursiveTaskAction h T)
variable (M : TransitiveGround.{u})
include state s

theorem exists_groundNext
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (ground : RecursiveGroundFields M h)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    ∃ next : h.NextInputs M,
      ∃ nextInputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
        G m inv one (h.nextActionGraph T),
        CodedRecursiveTaskAction nextInputs T ∧ RecursiveCompressionInvariant seed nextInputs ∧
        RecursiveGroundFields M nextInputs := by
  obtain ⟨next, _, _, _, _, _, _, _, _, _, entries, nextInputs, nextTask⟩ :=
    s.exists_groundSuccessor M pairing unions powers separation (state.compatible s)
      hI ground.indices ground.carrier ground.order ground.spaces ground.relations ground.meets
      ground.anchors ground.embeddings ground.filters ground.separators ground.maps
      hSources hReps hG ground.action hT
  exact ⟨next, nextInputs, nextTask, state.nextInvariant s M next entries nextInputs,
    ground.next pairing unions powers separation next nextInputs hI hSources hReps hG hT⟩

end PartitionPilot.Forcing.RecursiveCompressionInvariant

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RecursiveStateFieldEnvironments
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
universe u

namespace RecursiveStateCoherence
variable {I : ZFSet.{u}} {first middle last : RecursiveStateData.{u}}

theorem refl (maps : FunctionGraphOn I first.Maps) : RecursiveStateCoherence I first first where
  carrier := fun _ hx => hx
  order := fun _ _ _ _ => Iff.rfl
  meet := fun _ _ _ _ _ => Iff.rfl
  currentCarrier := fun _ hx => hx
  currentOrder := fun _ _ _ _ => Iff.rfl
  currentMeet := fun _ _ _ _ _ => Iff.rfl
  action := fun _ _ _ _ => Iff.rfl
  maps := by
    intro _ _ S S' firstEntry secondEntry _ _ _
    exact maps.unique firstEntry secondEntry ▸ Iff.rfl

theorem trans (left : RecursiveStateCoherence I first middle)
    (right : RecursiveStateCoherence I middle last) (middleMaps : FunctionGraphOn I middle.Maps) :
    RecursiveStateCoherence I first last where
  carrier := fun _ hx => right.carrier (left.carrier hx)
  order := fun _ hx _ hy => (right.order _ (left.carrier hx) _ (left.carrier hy)).trans (left.order _ hx _ hy)
  meet := fun _ hx _ hy _ => (right.meet _ (left.carrier hx) _ (left.carrier hy) _).trans (left.meet _ hx _ hy _)
  currentCarrier := fun _ hx => right.currentCarrier (left.currentCarrier hx)
  currentOrder := fun _ hx _ hy =>
    (right.currentOrder _ (left.currentCarrier hx) _ (left.currentCarrier hy)).trans (left.currentOrder _ hx _ hy)
  currentMeet := fun _ hx _ hy _ =>
    (right.currentMeet _ (left.currentCarrier hx) _ (left.currentCarrier hy) _).trans (left.currentMeet _ hx _ hy _)
  action := fun _ _ hx _ => (right.action _ _ (left.currentCarrier hx) _).trans (left.action _ _ hx _)
  maps := by
    intro i hi S S' oldEntry newEntry x hx y
    obtain ⟨B, middleEntry⟩ := middleMaps.total hi
    exact (right.maps i hi B S' middleEntry newEntry x (left.carrier hx) y).trans
      (left.maps i hi S B oldEntry middleEntry x hx y)

end RecursiveStateCoherence

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_InitialCompressionAccounting
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

structure GroundCompressionState (M : TransitiveGround.{u})
    {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
    (seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters) where
  data : RecursiveStateData.{u}
  batch : AttachmentBatchInputs data.D data.rD data.μD data.J
    data.Qs data.rs data.μs data.As data.Es data.Fs data.Ss
  inputs : CodedRecursiveMapInputs batch I data.Maps Sources Reps G m inv one data.A
  task : CodedRecursiveTaskAction inputs T
  invariant : RecursiveCompressionInvariant seed inputs
  ground : RecursiveGroundFields M inputs

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem inputs_toState : state.inputs.toState = state.data := by
  cases state with
  | mk data batch inputs task invariant ground => cases data; rfl

theorem exists_successor
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    ∃ result : GroundCompressionState M seed,
      result.data = state.data.successor M I Sources Reps G T := by
  obtain ⟨next, inputs, task, invariant, ground⟩ := state.invariant.exists_groundNext state.task M
    pairing unions powers separation state.ground hI hSources hReps hG hT
  let result : GroundCompressionState M seed :=
    ⟨inputs.toState, next, inputs, task, invariant, ground⟩
  refine ⟨result, ?_⟩
  change inputs.toState = state.data.successor M I Sources Reps G T
  exact (state.inputs.toState_successor M next inputs).trans
    (congrArg (fun data => data.successor M I Sources Reps G T) state.inputs_toState)

end GroundCompressionState

end

end PartitionPilot.Forcing

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

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace RecursiveStateData

theorem iterate_zero (initial : RecursiveStateData.{u}) (M : TransitiveGround.{u})
    (I Sources Reps G T : ZFSet.{u}) : initial.iterate M I Sources Reps G T 0 = initial := rfl

theorem iterate_succ (initial : RecursiveStateData.{u}) (M : TransitiveGround.{u})
    (I Sources Reps G T : ZFSet.{u}) (n : Nat) :
    initial.iterate M I Sources Reps G T (n + 1) =
      (initial.iterate M I Sources Reps G T n).successor M I Sources Reps G T := rfl

end RecursiveStateData

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)

noncomputable def next : GroundCompressionState M seed :=
  Classical.choose (state.exists_successor pairing unions powers separation hI hSources hReps hG hT)

theorem next_data :
    (state.next pairing unions powers separation hI hSources hReps hG hT).data =
      state.data.successor M I Sources Reps G T :=
  Classical.choose_spec (state.exists_successor pairing unions powers separation hI hSources hReps hG hT)

noncomputable def iterate : Nat → GroundCompressionState M seed
  | 0 => state
  | n + 1 => (iterate n).next pairing unions powers separation hI hSources hReps hG hT

theorem iterate_data (n : Nat) :
    (state.iterate pairing unions powers separation hI hSources hReps hG hT n).data =
      state.data.iterate M I Sources Reps G T n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((state.iterate pairing unions powers separation hI hSources hReps hG hT n).next
      pairing unions powers separation hI hSources hReps hG hT).data = _
    rw [next_data, ih, RecursiveStateData.iterate_succ]

include pairing unions powers separation hI hSources hReps hG hT in
theorem canonical_iterate_valid (n : Nat) :
    ∃ current : GroundCompressionState M seed,
      current.data = state.data.iterate M I Sources Reps G T n :=
  ⟨state.iterate pairing unions powers separation hI hSources hReps hG hT n,
    state.iterate_data pairing unions powers separation hI hSources hReps hG hT n⟩

end GroundCompressionState
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
universe u

theorem pairSecondField_constant {I J K : ZFSet.{u}} (value : ZFSet.{u})
    (subset : K ⊆ ZFSet.prod I J) :
    pairSecondField I J K (constantFamilyGraph J value) = constantFamilyGraph K value := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    unfold pairSecondField pairFieldGraph at entry
    obtain ⟨k, hk, x, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 entry).1
    obtain ⟨i, hi, j, hj, rfl⟩ := ZFSet.mem_prod.1 (subset hk)
    have old := ((pairSecondField_entry_iff hi hj).1 entry).2
    exact (pair_mem_constantFamilyGraph K value _ x).2
      ⟨hk, ((pair_mem_constantFamilyGraph J value j x).1 old).2⟩
  · intro entry
    change z ∈ ZFSet.prod K {value} at entry
    obtain ⟨k, hk, x, _, rfl⟩ := ZFSet.mem_prod.1 entry
    have equal := ((pair_mem_constantFamilyGraph K value k x).1 entry).2
    obtain ⟨i, hi, j, hj, rfl⟩ := ZFSet.mem_prod.1 (subset hk)
    exact (pairSecondField_entry_iff hi hj).2
      ⟨hk, (pair_mem_constantFamilyGraph J value j x).2 ⟨hj, equal⟩⟩

namespace RecursiveTemplateConstancy
variable {P r μ : ZFSet.{u}} {state : RecursiveStateData.{u}}
variable (constant : RecursiveTemplateConstancy P r μ state)
include constant

theorem successor (M : TransitiveGround.{u}) (I Sources Reps G T : ZFSet.{u}) :
    RecursiveTemplateConstancy P r μ (state.successor M I Sources Reps G T) := by
  let K := recursiveAttachmentIndices I state.J state.D (⋃₀ ⋃₀ state.Fs) Sources state.Fs
  have subset : K ⊆ ZFSet.prod I state.J := recursiveAttachmentIndices_subset _ _ _ _ _ _
  constructor
  · change pairSecondField I state.J K state.Qs = constantFamilyGraph K P
    rw [constant.spaces]
    exact pairSecondField_constant P subset
  · change pairSecondField I state.J K state.rs = constantFamilyGraph K r
    rw [constant.relations]
    exact pairSecondField_constant r subset
  · change pairSecondField I state.J K state.μs = constantFamilyGraph K μ
    rw [constant.meets]
    exact pairSecondField_constant μ subset

theorem iterate (M : TransitiveGround.{u}) (I Sources Reps G T : ZFSet.{u}) (n : Nat) :
    RecursiveTemplateConstancy P r μ (state.iterate M I Sources Reps G T n) := by
  induction n with
  | zero => exact constant
  | succ n ih => exact ih.successor M I Sources Reps G T

end RecursiveTemplateConstancy

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFiniteAccounting
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem successor_coherent : RecursiveStateCoherence I state.data
    (state.data.successor M I Sources Reps G T) := by
  obtain ⟨next, _, _, _, _, _, _, _, _, _, entries, inputs, _⟩ :=
    state.task.exists_groundSuccessor M pairing unions powers separation
      (state.invariant.compatible state.task) hI state.ground.indices state.ground.carrier
      state.ground.order state.ground.spaces state.ground.relations state.ground.meets
      state.ground.anchors state.ground.embeddings state.ground.filters state.ground.separators
      state.ground.maps hSources hReps hG state.ground.action hT
  have result := state.inputs.next_coherent M next entries inputs
  rw [state.inputs.toState_successor M next inputs, state.inputs_toState] at result
  exact result

theorem canonical_iterate_coherent {n k : Nat} (before : n ≤ k) :
    RecursiveStateCoherence I (state.data.iterate M I Sources Reps G T n)
      (state.data.iterate M I Sources Reps G T k) := by
  induction k, before using Nat.le_induction with
  | base =>
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT n
    rw [← equal]
    exact RecursiveStateCoherence.refl current.inputs.maps
  | succ k _ ih =>
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT k
    have step := current.successor_coherent pairing unions powers separation hI hSources hReps hG hT
    rw [equal, ← RecursiveStateData.iterate_succ] at step
    apply ih.trans step
    rw [← equal]
    exact current.inputs.maps

end PartitionPilot.Forcing.GroundCompressionState



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RectangleFulfillmentAtBound
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

theorem mem_externalRectangles (P G r μ A t : ZFSet.{u}) :
    t ∈ externalRectangles P G r μ A ↔ ∃ c b d g h,
      t = externalRectangleCode c b d g h ∧ ExternalRectangleCode P G r μ A c b d g h := by
  rw [externalRectangles, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, c, _, b, _, d, _, g, _, h, _, eq, code⟩
    exact ⟨c, b, d, g, h, eq, code⟩
  · rintro ⟨c, b, d, g, h, rfl, code⟩
    exact ⟨(externalRectangleCode_mem_bound P G c b d g h).2
      ⟨code.1, code.2.1, code.2.2.1, code.2.2.2.1, code.2.2.2.2.1⟩,
      c, code.1, b, code.2.1, d, code.2.2.1, g, code.2.2.2.1, h, code.2.2.2.2.1, rfl, code⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionOrigins
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem canonical_iterate_codes (n : Nat) :
    let data := state.data.iterate M I Sources Reps G T n
    MeetOrderCode data.D data.rD data.μD ∧
      MeetOrderCode data.currentCarrier data.currentOrder data.currentMeet ∧
      PosetActionCode G data.currentCarrier m one data.currentOrder data.A ∧
      FunctionGraphOn I data.Maps ∧
      ∀ i S, ZFSet.pair i S ∈ data.Maps →
        MeetEmbeddingCode data.D data.currentCarrier data.rD data.currentOrder data.μD data.currentMeet S := by
  obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
    hI hSources hReps hG hT n
  rw [← equal]
  exact ⟨current.batch.oldOrder, current.batch.batch_meetOrder, current.inputs.action,
    current.inputs.maps, current.inputs.valid⟩

theorem canonical_iterate_graphs_mono {n k : Nat} (before : n ≤ k) :
    let first := state.data.iterate M I Sources Reps G T n
    let last := state.data.iterate M I Sources Reps G T k
    first.D ⊆ last.D ∧ first.rD ⊆ last.rD ∧ first.μD ⊆ last.μD ∧
      first.currentCarrier ⊆ last.currentCarrier ∧ first.currentOrder ⊆ last.currentOrder ∧
      first.currentMeet ⊆ last.currentMeet ∧ first.A ⊆ last.A ∧
      ∀ i S S', ZFSet.pair i S ∈ first.Maps → ZFSet.pair i S' ∈ last.Maps → S ⊆ S' := by
  let first := state.data.iterate M I Sources Reps G T n
  let last := state.data.iterate M I Sources Reps G T k
  have coherent := state.canonical_iterate_coherent pairing unions powers separation
    hI hSources hReps hG hT before
  obtain ⟨old, current, action, maps, valid⟩ := state.canonical_iterate_codes
    pairing unions powers separation hI hSources hReps hG hT n
  have pair_subset {X Y f g : ZFSet.{u}} (shape : f ⊆ ZFSet.prod X Y)
      (transfer : ∀ x ∈ X, ∀ y ∈ Y, ZFSet.pair x y ∈ f → ZFSet.pair x y ∈ g) : f ⊆ g := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
    exact transfer x hx y hy hz
  refine ⟨coherent.carrier, ?_, ?_, coherent.currentCarrier, ?_, ?_, ?_, ?_⟩
  · exact pair_subset old.order.relation
      (fun x hx y hy entry => (coherent.order x hx y hy).2 entry)
  · apply pair_subset old.operation.1
    intro xy hxy z _ entry
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    exact (coherent.meet x hx y hy z).2 entry
  · exact pair_subset current.order.relation
      (fun x hx y hy entry => (coherent.currentOrder x hx y hy).2 entry)
  · apply pair_subset current.operation.1
    intro xy hxy z _ entry
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    exact (coherent.currentMeet x hx y hy z).2 entry
  · apply pair_subset action.function.1
    intro gx hgx y _ entry
    obtain ⟨g, _, x, hx, rfl⟩ := ZFSet.mem_prod.1 hgx
    exact (coherent.action g x hx y).2 entry
  · intro i S S' oldEntry newEntry
    apply pair_subset (valid i S oldEntry).injection.function.1
    intro x hx y _ entry
    exact (coherent.maps i (maps.pair_source oldEntry) S S' oldEntry newEntry x hx y).2 entry

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing
universe u





structure GroundCompressionOrigin (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}) where
  seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters
  state : GroundCompressionState M seed
  initial_data : state.data = initial

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundExternalRequestSetRecognition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

theorem pair_mem_externalRequestCarrier (I P Rectangles t x : ZFSet.{u}) :
    ZFSet.pair t x ∈ externalRequestCarrier I P Rectangles ↔
      (t = natSetCode 0 ∧ x ∈ I) ∨ (t = natSetCode 1 ∧ x ∈ P) ∨
        (t = natSetCode 2 ∧ x ∈ Rectangles) := by
  simp only [externalRequestCarrier, ZFSet.mem_union, ZFSet.pair_mem_prod,
    ZFSet.mem_singleton, or_assoc]

theorem compression_mem_externalRequestCarrier (I P Rectangles i : ZFSet.{u}) :
    ZFSet.pair (natSetCode 0) i ∈ externalRequestCarrier I P Rectangles ↔ i ∈ I := by
  rw [pair_mem_externalRequestCarrier]
  simp only [natSetCode_injective.eq_iff]
  simp

theorem separation_mem_externalRequestCarrier (I P Rectangles x : ZFSet.{u}) :
    ZFSet.pair (natSetCode 1) x ∈ externalRequestCarrier I P Rectangles ↔ x ∈ P := by
  rw [pair_mem_externalRequestCarrier]
  simp only [natSetCode_injective.eq_iff]
  simp

theorem rectangle_mem_externalRequestCarrier (I P Rectangles z : ZFSet.{u}) :
    ZFSet.pair (natSetCode 2) z ∈ externalRequestCarrier I P Rectangles ↔ z ∈ Rectangles := by
  rw [pair_mem_externalRequestCarrier]
  simp only [natSetCode_injective.eq_iff]
  simp

theorem pair_mem_externalChildLetters (I P Rectangles request child : ZFSet.{u}) :
    ZFSet.pair request child ∈ externalChildLetters I P Rectangles ↔
      (request ∈ externalRequestCarrier I P Rectangles ∧ child = natSetCode 0) ∨
        (request ∈ ZFSet.prod {natSetCode 2} Rectangles ∧ child = natSetCode 1) := by
  simp only [externalChildLetters, ZFSet.mem_union, ZFSet.pair_mem_prod, ZFSet.mem_singleton]

theorem compression_child_iff (I P Rectangles i child : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (natSetCode 0) i) child ∈ externalChildLetters I P Rectangles ↔
      i ∈ I ∧ child = natSetCode 0 := by
  rw [pair_mem_externalChildLetters, compression_mem_externalRequestCarrier]
  simp only [ZFSet.pair_mem_prod, ZFSet.mem_singleton, natSetCode_injective.eq_iff]
  simp

theorem separation_child_iff (I P Rectangles x child : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (natSetCode 1) x) child ∈ externalChildLetters I P Rectangles ↔
      x ∈ P ∧ child = natSetCode 0 := by
  rw [pair_mem_externalChildLetters, separation_mem_externalRequestCarrier]
  simp only [ZFSet.pair_mem_prod, ZFSet.mem_singleton, natSetCode_injective.eq_iff]
  simp

theorem rectangle_child_iff (I P Rectangles z child : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (natSetCode 2) z) child ∈ externalChildLetters I P Rectangles ↔
      z ∈ Rectangles ∧ (child = natSetCode 0 ∨ child = natSetCode 1) := by
  rw [pair_mem_externalChildLetters, rectangle_mem_externalRequestCarrier]
  simp only [ZFSet.pair_mem_prod, ZFSet.mem_singleton, true_and]
  exact and_or_left.symm

theorem externalRequestCarrier_subset (I P Rectangles : ZFSet.{u}) :
    externalRequestCarrier I P Rectangles ⊆
      ZFSet.prod externalRequestTags (externalRequestPayloadBound I P Rectangles) := by
  intro z hz
  rcases ZFSet.mem_union.1 hz with old | rectangle
  · rcases ZFSet.mem_union.1 old with compression | separation
    · obtain ⟨t, ht, x, hx, rfl⟩ := ZFSet.mem_prod.1 compression
      rw [ZFSet.mem_singleton] at ht
      subst t
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert _ _,
        ZFSet.mem_union.2 (Or.inl (ZFSet.mem_union.2 (Or.inl hx)))⟩
    · obtain ⟨t, ht, x, hx, rfl⟩ := ZFSet.mem_prod.1 separation
      rw [ZFSet.mem_singleton] at ht
      subst t
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert_of_mem _ (ZFSet.mem_insert _ _),
        ZFSet.mem_union.2 (Or.inl (ZFSet.mem_union.2 (Or.inr hx)))⟩
  · obtain ⟨t, ht, x, hx, rfl⟩ := ZFSet.mem_prod.1 rectangle
    rw [ZFSet.mem_singleton] at ht
    subst t
    exact ZFSet.pair_mem_prod.2
      ⟨ZFSet.mem_insert_of_mem _ (ZFSet.mem_insert_of_mem _ (ZFSet.mem_singleton.2 rfl)),
        ZFSet.mem_union.2 (Or.inr hx)⟩

noncomputable def externalRequestKinds (I P Rectangles : ZFSet.{u}) : ZFSet.{u} :=
  graphRestriction (externalRequestCarrier I P Rectangles)
    (productFirst externalRequestTags (externalRequestPayloadBound I P Rectangles))

noncomputable def externalRequestPayloads (I P Rectangles : ZFSet.{u}) : ZFSet.{u} :=
  graphRestriction (externalRequestCarrier I P Rectangles)
    (productSecond externalRequestTags (externalRequestPayloadBound I P Rectangles))

theorem triple_mem_externalTileVertices (Requests Rectangles U q i x : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair q i) x ∈ externalTileVertices Requests Rectangles U ↔
      ((q ∈ Requests ∧ (i = natSetCode 0 ∨ i = natSetCode 1)) ∨
        (q ∈ ZFSet.prod {natSetCode 2} Rectangles ∧ i = natSetCode 2)) ∧ x ∈ U := by
  simp only [externalTileVertices, ZFSet.mem_union, ZFSet.pair_mem_prod,
    ZFSet.mem_pair, ZFSet.mem_singleton]
  tauto

end

section
open SetRealization
universe u

theorem externalRequestIndexCode_injective (I P R : ZFSet.{u}) :
    Function.Injective (@externalRequestIndexCode I P R) := by
  intro x y equal
  rcases x with i | (x | r) <;> rcases y with j | (y | s) <;>
    simp only [externalRequestIndexCode, ZFSet.pair_inj, natSetCode_injective.eq_iff] at equal
  all_goals simp_all
  all_goals exact SetMembers.raw_injective _ equal

noncomputable def externalRequestPresentation (I P R : ZFSet.{u}) :
    Presentation (ExternalRequestIndex I P R) where
  carrier := externalRequestCarrier I P R
  encode := externalRequestIndexCode
  injective := externalRequestIndexCode_injective I P R
  mem_carrier z := by
    constructor
    · intro hz
      obtain ⟨tag, _, value, _, equal⟩ := ZFSet.mem_prod.1 (externalRequestCarrier_subset I P R hz)
      rw [equal] at hz
      rcases (pair_mem_externalRequestCarrier I P R tag value).1 hz with
        ⟨rfl, hi⟩ | ⟨rfl, hx⟩ | ⟨rfl, hr⟩
      · exact ⟨.inl (SetMembers.ofMem value hi), by
          simpa only [externalRequestIndexCode, SetMembers.raw_ofMem] using equal.symm⟩
      · exact ⟨.inr (.inl (SetMembers.ofMem value hx)), by
          simpa only [externalRequestIndexCode, SetMembers.raw_ofMem] using equal.symm⟩
      · exact ⟨.inr (.inr (SetMembers.ofMem value hr)), by
          simpa only [externalRequestIndexCode, SetMembers.raw_ofMem] using equal.symm⟩
    · rintro ⟨index, rfl⟩
      rcases index with i | (x | r)
      · exact (compression_mem_externalRequestCarrier I P R _).2 (SetMembers.raw_mem i)
      · exact (separation_mem_externalRequestCarrier I P R _).2 (SetMembers.raw_mem x)
      · exact (rectangle_mem_externalRequestCarrier I P R _).2 (SetMembers.raw_mem r)

noncomputable def externalRequestChildCode {I P R : ZFSet.{u}} :
    (r : ExternalRequestIndex I P R) → ExternalRequestChild r → ZFSet.{u}
  | .inl _, _ => natSetCode 0
  | .inr (.inl _), _ => natSetCode 0
  | .inr (.inr _), child => externalSignCode child.down

theorem externalRequestChildCode_injective {I P R : ZFSet.{u}}
    (r : ExternalRequestIndex I P R) : Function.Injective (externalRequestChildCode r) := by
  rcases r with i | (x | r)
  · intro a b _
    exact ULift.ext _ _ (Subsingleton.elim a.down b.down)
  · intro a b _
    exact ULift.ext _ _ (Subsingleton.elim a.down b.down)
  · intro a b equal
    exact ULift.ext _ _ (externalSignCode_injective equal)

theorem externalRequestChildCode_range {I P R : ZFSet.{u}}
    (r : ExternalRequestIndex I P R) (c : ZFSet.{u}) :
    ZFSet.pair (externalRequestIndexCode r) c ∈ externalChildLetters I P R ↔
      ∃ child : ExternalRequestChild r, externalRequestChildCode r child = c := by
  rcases r with i | (x | r)
  · rw [externalRequestIndexCode, compression_child_iff]
    exact ⟨fun h => ⟨⟨()⟩, h.2.symm⟩,
      fun ⟨_, equal⟩ => ⟨SetMembers.raw_mem i, equal.symm⟩⟩
  · rw [externalRequestIndexCode, separation_child_iff]
    exact ⟨fun h => ⟨⟨()⟩, h.2.symm⟩,
      fun ⟨_, equal⟩ => ⟨SetMembers.raw_mem x, equal.symm⟩⟩
  · rw [externalRequestIndexCode, rectangle_child_iff]
    constructor
    · rintro ⟨_, equal | equal⟩
      · exact ⟨⟨false⟩, equal.symm⟩
      · exact ⟨⟨true⟩, equal.symm⟩
    · rintro ⟨⟨b⟩, equal⟩
      refine ⟨SetMembers.raw_mem r, ?_⟩
      cases b
      · exact Or.inl equal.symm
      · exact Or.inr equal.symm

noncomputable def externalRequestLetterCode {I P R : ZFSet.{u}}
    (letter : Sigma (@ExternalRequestChild I P R)) : ZFSet.{u} :=
  ZFSet.pair (externalRequestIndexCode letter.1) (externalRequestChildCode letter.1 letter.2)

theorem externalRequestLetterCode_injective (I P R : ZFSet.{u}) :
    Function.Injective (@externalRequestLetterCode I P R) := by
  rintro ⟨r, a⟩ ⟨s, b⟩ equal
  have parts := ZFSet.pair_inj.1 equal
  have same := externalRequestIndexCode_injective I P R parts.1
  cases same
  have child := externalRequestChildCode_injective r parts.2
  cases child
  rfl

noncomputable def externalRequestLetterPresentation (I P R : ZFSet.{u}) :
    Presentation (Sigma (@ExternalRequestChild I P R)) where
  carrier := externalChildLetters I P R
  encode := externalRequestLetterCode
  injective := externalRequestLetterCode_injective I P R
  mem_carrier z := by
    constructor
    · intro hz
      have shape : ∃ request ∈ externalRequestCarrier I P R, ∃ child,
          z = ZFSet.pair request child := by
        rcases ZFSet.mem_union.1 hz with zero | one
        · obtain ⟨request, member, child, _, equal⟩ := ZFSet.mem_prod.1 zero
          exact ⟨request, member, child, equal⟩
        · obtain ⟨request, member, child, _, equal⟩ := ZFSet.mem_prod.1 one
          exact ⟨request, ZFSet.mem_union.2 (Or.inr member), child, equal⟩
      obtain ⟨request, member, child, rfl⟩ := shape
      obtain ⟨r, rfl⟩ := ((externalRequestPresentation I P R).mem_carrier request).1 member
      obtain ⟨c, equal⟩ := (externalRequestChildCode_range r child).1 hz
      exact ⟨⟨r, c⟩, congrArg (ZFSet.pair (externalRequestIndexCode r)) equal⟩
    · rintro ⟨⟨r, c⟩, rfl⟩
      exact (externalRequestChildCode_range r _).2 ⟨c, rfl⟩

end

open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalRequestOverlaps
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

theorem pair_mem_externalRequestOverlapGraph (Requests P G Rectangles Maps U r A a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ externalRequestOverlapGraph Requests P G Rectangles Maps U r A ↔
      a ∈ externalTileVertices Requests Rectangles U ∧ b ∈ externalTileVertices Requests Rectangles U ∧
        ∃ q ∈ Requests, ∃ i ∈ externalRequestTags, ∃ x ∈ U, ∃ j ∈ externalRequestTags, ∃ y ∈ U,
          a = ZFSet.pair (ZFSet.pair q i) x ∧ b = ZFSet.pair (ZFSet.pair q j) y ∧
            ExternalRequestOverlapCode P G Rectangles Maps (ZFSet.sUnion (ZFSet.sUnion Maps)) r A
              (natSetCode 0) (natSetCode 1) (natSetCode 2) q i x j y := by
  rw [externalRequestOverlapGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a', ha, b', hb, q, hq, i, hi, x, hx, j, hj, y, hy, equal, left, right, overlap⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, q, hq, i, hi, x, hx, j, hj, y, hy, left, right, overlap⟩
  · rintro ⟨ha, hb, q, hq, i, hi, x, hx, j, hj, y, hy, left, right, overlap⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ha, hb⟩, a, ha, b, hb, q, hq, i, hi, x, hx, j, hj, y, hy,
      rfl, left, right, overlap⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalTileVertices_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Requests Rectangles U : ZFSet.{u}} (hRequests : Requests ∈ M.sets)
    (hRectangles : Rectangles ∈ M.sets) (hU : U ∈ M.sets) :
    externalTileVertices Requests Rectangles U ∈ M.sets := by
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨U, hU⟩
  have hFirst : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  have hSecond : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions hFirst hFirst
  have single : ({natSetCode 2} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hSecond hSecond
  exact M.binary_union_mem pairing unions
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hRequests (M.unorderedPair_mem pairing hZero hFirst)) hU)
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation
        (M.prod_mem pairing unions powers separation single hRectangles) single) hU)

theorem externalRequestOverlapGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Requests P G Rectangles Maps U r A : ZFSet.{u}}
    (hRequests : Requests ∈ M.sets) (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hRectangles : Rectangles ∈ M.sets) (hMaps : Maps ∈ M.sets) (hU : U ∈ M.sets)
    (hr : r ∈ M.sets) (hA : A ∈ M.sets) :
    externalRequestOverlapGraph Requests P G Rectangles Maps U r A ∈ M.sets := by
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨U, hU⟩
  have hFirst : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  have hSecond : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions hFirst hFirst
  have single : ({natSetCode 2} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hSecond hSecond
  have hTags : externalRequestTags ∈ M.sets :=
    M.insert_mem pairing unions hZero (M.insert_mem pairing unions hFirst single)
  have hV := M.externalTileVertices_mem pairing unions powers separation hRequests hRectangles hU
  have hF := M.union_mem unions (M.union_mem unions hMaps)
  let params := extend (externalTileVertices Requests Rectangles U) (extend Requests
    (extend externalRequestTags (extend U (extend P (extend G (extend Rectangles
      (extend Maps (extend (ZFSet.sUnion (ZFSet.sUnion Maps)) (extend r (extend A (extend (natSetCode 0)
        (extend (natSetCode 1) (extend (natSetCode 2) Fin.elim0)))))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalRequestOverlapEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14) params
    (Fin.cases hV (Fin.cases hRequests (Fin.cases hTags (Fin.cases hU (Fin.cases hP (Fin.cases hG
      (Fin.cases hRectangles (Fin.cases hMaps (Fin.cases hF (Fin.cases hr (Fin.cases hA
        (Fin.cases hZero (Fin.cases hFirst (Fin.cases hSecond (fun i => Fin.elim0 i)))))))))))))))
    (M.prod_mem pairing unions powers separation hV hV)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalRequestOverlapEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14)
      (extend z params)) (ZFSet.prod (externalTileVertices Requests Rectangles U)
        (externalTileVertices Requests Rectangles U)) = externalRequestOverlapGraph Requests P G Rectangles Maps U r A := by
    apply ZFSet.ext
    intro z
    rw [externalRequestOverlapGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalRequestOverlapEntryFormula
      0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundBatchBirths
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

theorem fixedTopBirth_oldMeet {P T r μ birth s : ZFSet.{u}}
    (meet : MeetOrderCode P r μ) (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ s) (oldMeet : OldMeetCode r μ birth) :
    OldMeetCode (fixedTopOrder P r) (fixedTopMeet P r) (fixedTopBirth P birth s) := by
  intro x y z a b c ya xb ab notLower xy zc
  rcases (pair_mem_fixedTopBirth P birth s x b).1 xb with ⟨newx, newb⟩ | oldx
  · subst x b
    rcases (pair_mem_fixedTopBirth P birth s y a).1 ya with ⟨newy, newa⟩ | oldy
    · subst y a
      exact False.elim (ZFSet.mem_irrefl s ab)
    · have hy := (ZFSet.pair_mem_prod.1 (born.1 oldy)).1
      have equal := (fixedTopMeet_top_left meet (fixedTopCarrier_old hy)).1 xy
      subst z
      have oldc := (fixedTopBirth_old_iff hy).1 zc
      exact earlier y c oldc
  · have hx := (ZFSet.pair_mem_prod.1 (born.1 oldx)).1
    rcases (pair_mem_fixedTopBirth P birth s y a).1 ya with ⟨newy, newa⟩ | oldy
    · subst y a
      exact False.elim (ZFSet.mem_asymm (earlier x b oldx) ab)
    · have hy := (ZFSet.pair_mem_prod.1 (born.1 oldy)).1
      have oldxy := (fixedTopMeet_old_iff meet hx hy).1 xy
      have hz := (ZFSet.pair_mem_prod.1 (meet.operation.1 oldxy)).2
      exact oldMeet x y z a b c oldy oldx ab
        (fun lower => notLower ((fixedTopOrder_old_iff hy).2 lower)) oldxy
        ((fixedTopBirth_old_iff hz).1 zc)

end

namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

def fixedTopBirth_incoming_layer
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {P r birth s : ZFSet.{u}} (hP : P ∈ M.sets)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ s) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (fixedTopCarrier P)
      (fixedTopOrder P r) (fixedTopMeet P r) (fixedTopBirth P birth s) s :=
  .countablePoints {P} (M.fixedTopBirth_singleton_small pairing hP).1
    (M.fixedTopBirth_singleton_small pairing hP).2
    (fun _ _ entry => ZFSet.mem_singleton.2 ((fixedTopBirth_new_time_iff earlier).1 entry))

noncomputable def fixedTopBirth_earlier_layer
    (separation : SeparationSchema M.sets)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {P T r μ birth s t : ZFSet.{u}}
    (hP : P ∈ M.sets) (meet : MeetOrderCode P r μ) (born : ZFSet.IsFunc P T birth)
    (before : t ∈ s)
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet P r μ birth t) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (fixedTopCarrier P)
      (fixedTopOrder P r) (fixedTopMeet P r) (fixedTopBirth P birth s) t := by
  apply layer.of_literal_extension separation hP (fixedTopCarrier_subset P)
    (fixedTopOrder_subset P r) (fixedTopMeet_subset meet) (fixedTopBirth_subset P birth s)
  intro x _ entry
  have old := (fixedTopBirth_earlier_iff before).1 entry
  exact ⟨(ZFSet.pair_mem_prod.1 (born.1 old)).1, old⟩

noncomputable def fixedTopBirth_layers
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {P T r μ birth s : ZFSet.{u}}
    (hP : P ∈ M.sets) (meet : MeetOrderCode P r μ) (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ s)
    (layers : ∀ t ∈ s, CodedGrowthLayer M Space sourceOrder sourceMeet P r μ birth t)
    (t : ZFSet.{u}) (bounded : t = s ∨ t ∈ s) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (fixedTopCarrier P)
      (fixedTopOrder P r) (fixedTopMeet P r) (fixedTopBirth P birth s) t := by
  classical
  by_cases equal : t = s
  · subst t
    exact M.fixedTopBirth_incoming_layer pairing hP earlier
  · have before := bounded.resolve_left equal
    exact M.fixedTopBirth_earlier_layer separation hP meet born before (layers t before)

end TransitiveGround

open SetRealization SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCompressionBirthData
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
universe u

namespace NatBirthExtensionCode
variable {P stamp : Nat → ZFSet.{u}} {old birth U T : ZFSet.{u}}

variable (code : NatBirthExtensionCode P stamp old birth)
include code

theorem restriction_zero (mono : ∀ n m, n ≤ m → P n ⊆ P m)
    (born : ZFSet.IsFunc (P 0) T old) : graphRestriction (P 0) birth = old := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, t, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact (code.old_entry_iff mono hx).1 entry
  · intro hz
    obtain ⟨x, hx, t, _, rfl⟩ := ZFSet.mem_prod.1 (born.1 hz)
    exact pair_mem_graphRestriction.2 ⟨(code.old_entry_iff mono hx).2 hz, hx⟩

theorem restriction_function (carrier : NatUnionCode P U)
    (mono : ∀ n m, n ≤ m → P n ⊆ P m)
    (born : ZFSet.IsFunc (P 0) T old) (stamps : ∀ n, stamp n ∈ T) (n : Nat) :
    ZFSet.IsFunc (P n) T (graphRestriction (P n) birth) := by
  have full := code.function carrier mono born stamps
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, t, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hx, (ZFSet.pair_mem_prod.1 (full.1 entry)).2⟩
  · intro x hx
    obtain ⟨t, entry, unique⟩ := full.2 x (carrier.subset n hx)
    exact ⟨t, pair_mem_graphRestriction.2 ⟨entry, hx⟩,
      fun s hs => unique s (pair_mem_graphRestriction.1 hs).1⟩

end NatBirthExtensionCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.NatBirthExtensionCode
universe u
variable {P stamp : Nat → ZFSet.{u}} {old birth T : ZFSet.{u}}
variable (code : NatBirthExtensionCode P stamp old birth)
variable (mono : ∀ n m, n ≤ m → P n ⊆ P m)
variable (born : ZFSet.IsFunc (P 0) T old)
include code

omit code in
include mono in
theorem restriction_mono {n m : Nat} (before : n ≤ m) :
    graphRestriction (P n) birth ⊆ graphRestriction (P m) birth := by
  intro z hz
  obtain ⟨x, hx, t, rfl, entry⟩ := mem_graphRestriction.1 hz
  exact pair_mem_graphRestriction.2 ⟨entry, mono n m before hx⟩

include mono born in
theorem restriction_step (n : Nat) {N : ZFSet.{u}}
    (next : P (n + 1) = taggedExtension (P n) N) :
    graphRestriction (P (n + 1)) birth = taggedBirth (P n) N (graphRestriction (P n) birth) (stamp n) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, t, rfl, entry⟩ := mem_graphRestriction.1 hz
    apply (pair_mem_taggedBirth _ _ _ _ _ _).2
    by_cases oldPoint : x ∈ P n
    · exact Or.inl (pair_mem_graphRestriction.2 ⟨entry, oldPoint⟩)
    · have fresh : x ∈ ZFSet.prod {P n} N := by
        rw [next] at hx
        exact (ZFSet.mem_union.1 hx).resolve_left oldPoint
      rcases (code.entries x t).1 entry with original | ⟨m, hm, notM, equal⟩
      · exact False.elim (oldPoint (mono 0 n (Nat.zero_le n)
          (ZFSet.pair_mem_prod.1 (born.1 original)).1))
      · have same := first_appearance_unique mono hm notM hx oldPoint
        exact Or.inr ⟨fresh, same ▸ equal⟩
  · intro hz
    rcases ZFSet.mem_union.1 hz with original | fresh
    · obtain ⟨x, hx, t, rfl, entry⟩ := mem_graphRestriction.1 original
      exact pair_mem_graphRestriction.2 ⟨entry, mono n (n + 1) (Nat.le_succ n) hx⟩
    · obtain ⟨x, hx, t, ht, rfl⟩ := ZFSet.mem_prod.1 fresh
      obtain rfl := ZFSet.mem_singleton.1 ht
      have current : x ∈ P (n + 1) := by
        rw [next]
        exact ZFSet.mem_union.2 (Or.inr hx)
      have outside : x ∉ P n := fun h => taggedExtension_disjoint (P n) N x h hx
      exact pair_mem_graphRestriction.2
        ⟨(code.entries x (stamp n)).2 (Or.inr ⟨n, current, outside, rfl⟩), current⟩

include mono in
theorem restriction_bound
    (oldBound : ∀ n x t, ZFSet.pair x t ∈ old → t ∈ stamp n)
    (stampBefore : ∀ n m, n < m → stamp n ∈ stamp m)
    (n : Nat) {x t : ZFSet.{u}} (entry : ZFSet.pair x t ∈ graphRestriction (P n) birth) :
    t ∈ stamp n := by
  obtain ⟨entry, hx⟩ := pair_mem_graphRestriction.1 entry
  rcases (code.entries x t).1 entry with original | ⟨m, _, notM, rfl⟩
  · exact oldBound n x t original
  · exact stampBefore m n (lt_of_not_ge (fun h => notM (mono n m h hx)))

include mono born in
theorem earlier_fiber
    (stampMono : ∀ n m, n ≤ m → stamp n ⊆ stamp m)
    (n : Nat) {x t : ZFSet.{u}} (before : t ∈ stamp n)
    (entry : ZFSet.pair x t ∈ birth) :
    x ∈ P n ∧ ZFSet.pair x t ∈ graphRestriction (P n) birth := by
  have hx : x ∈ P n := by
    rcases (code.entries x t).1 entry with original | ⟨m, hm, _, rfl⟩
    · exact mono 0 n (Nat.zero_le n) (ZFSet.pair_mem_prod.1 (born.1 original)).1
    · have smaller : m < n := lt_of_not_ge
        (fun h => ZFSet.mem_irrefl (stamp m) (stampMono n m h before))
      exact mono (m + 1) n (Nat.succ_le_of_lt smaller) hm
  exact ⟨hx, pair_mem_graphRestriction.2 ⟨entry, hx⟩⟩

end PartitionPilot.Forcing.NatBirthExtensionCode



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable {base stamps limit old birth : ZFSet.{u}}
variable (code : NatBirthExtensionCode (fun n => (state.data.iterate M I Sources Reps G T n).D)
    (compressionStamp base) old birth)
variable (born : ZFSet.IsFunc state.data.D limit old)
variable (times : CompressionStampCode base stamps limit)
include pairing unions powers separation hI hSources hReps hG hT code

include data born times in
theorem canonical_birth_function (n : Nat) :
    ZFSet.IsFunc (state.data.iterate M I Sources Reps G T n).D limit
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) :=
  code.restriction_function (data.fieldUnion 0)
    (fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation
      hI hSources hReps hG hT h).1) born times.stamp_mem_limit n

include born in
theorem canonical_birth_step (n : Nat) :
    graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D birth =
      taggedBirth (state.data.iterate M I Sources Reps G T n).D
        (state.data.iterate M I Sources Reps G T n).fresh
        (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth)
        (compressionStamp base n) :=
  code.restriction_step
    (fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation
      hI hSources hReps hG hT h).1) born n rfl

theorem canonical_birth_before_stamp
    (oldBound : ∀ x t, ZFSet.pair x t ∈ old → t ∈ base ∨ t = base)
    (n : Nat) {x t : ZFSet.{u}}
    (entry : ZFSet.pair x t ∈ graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) :
    t ∈ compressionStamp base n :=
  code.restriction_bound
    (fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation
      hI hSources hReps hG hT h).1)
    (fun n x t h => compressionStamp_old_mem (oldBound x t h) n)
    (fun n k h => (compressionStamp_mem_iff base n k).2 h) n entry

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable {base stamps limit old birth : ZFSet.{u}}
variable (code : NatBirthExtensionCode (fun n => (state.data.iterate M I Sources Reps G T n).D)
    (compressionStamp base) old birth)
variable (born : ZFSet.IsFunc state.data.D limit old)
variable {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
include pairing unions powers separation hI hSources hReps hG hT code born

noncomputable def canonical_birth_layer_to_union (n : Nat) {t : ZFSet.{u}}
    (before : t ∈ compressionStamp base n)
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet
      (state.data.iterate M I Sources Reps G T n).D
      (state.data.iterate M I Sources Reps G T n).rD
      (state.data.iterate M I Sources Reps G T n).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) t) :
    CodedGrowthLayer M Space sourceOrder sourceMeet
      (data.fields 0) (data.fields 1) (data.fields 2) birth t := by
  have mono := fun n k h => (state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT (n := n) (k := k) h).1
  have ground : (state.data.iterate M I Sources Reps G T n).D ∈ M.sets := by
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT n
    rw [← equal]
    exact current.ground.carrier
  exact layer.of_literal_extension separation ground
    ((data.fieldUnion 0).subset n) ((data.fieldUnion 1).subset n)
    ((data.fieldUnion 2).subset n)
    (graphRestriction_subset (state.data.iterate M I Sources Reps G T n).D birth)
    (fun _ _ entry => code.earlier_fiber mono born
      (fun _ _ h => compressionStamp_subset base h) n before entry)

noncomputable def prior_birth_layer_to_union {t : ZFSet.{u}} (priorTime : t ∈ base ∨ t = base)
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet
      state.data.D state.data.rD state.data.μD old t) :
    CodedGrowthLayer M Space sourceOrder sourceMeet
      (data.fields 0) (data.fields 1) (data.fields 2) birth t := by
  have mono := fun n k h => (state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT (n := n) (k := k) h).1
  have zero := code.restriction_zero mono born
  apply state.canonical_birth_layer_to_union data pairing unions powers separation
    hI hSources hReps hG hT code born 0 (compressionStamp_old_mem priorTime 0)
  rw [zero]
  simpa only [RecursiveStateData.iterate_zero] using layer

end PartitionPilot.Forcing.GroundCompressionState



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_SmallTileHeightInputs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression Compression.RecursiveMaps
universe u

namespace MeetEmbeddingCode
variable {P Q rP rQ μP μQ f : ZFSet.{u}}
variable (embedding : MeetEmbeddingCode P Q rP rQ μP μQ f)

noncomputable def smallValue (x : SetMembers P) : SetMembers Q :=
  (SetMembers.presentation P).decodeFunction (SetMembers.presentation Q) f
    embedding.injection.function x

theorem smallValue_entry (x : SetMembers P) :
    ZFSet.pair (SetMembers.raw x) (SetMembers.raw (embedding.smallValue x)) ∈ f :=
  (SetMembers.presentation P).decodeFunction_mem (SetMembers.presentation Q) f
    embedding.injection.function x

theorem smallValue_eq_iff (x : SetMembers P) (y : SetMembers Q) :
    embedding.smallValue x = y ↔ ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ f :=
  (SetMembers.presentation P).decodeFunction_iff (SetMembers.presentation Q) f
    embedding.injection.function x y

noncomputable def toSmallMeetEmbedding (source : MeetOrderCode P rP μP)
    (target : MeetOrderCode Q rQ μQ) :
    MeetEmbedding source.toSmallMeetOrder target.toSmallMeetOrder where
  toFun := embedding.smallValue
  le_iff x y := embedding.order_iff source target
    (embedding.smallValue_entry x) (embedding.smallValue_entry y)
  map_meet x y := by
    symm
    apply (target.smallMeet_eq_iff _ _ _).2
    exact embedding.map_meet _ _ _ _ _ _ (source.smallMeet_entry x y)
      (embedding.smallValue_entry x) (embedding.smallValue_entry y)
      (embedding.smallValue_entry (source.smallMeet x y))

end MeetEmbeddingCode

noncomputable def smallCompressionTileIso {P r μ f : ZFSet.{u}}
    (meet : MeetOrderCode P r μ) (embedding : MeetEmbeddingCode P P r r μ μ f)
    (K : SetMembers P)
    (range : ∀ z, (∃ x ∈ P, ZFSet.pair x z ∈ f) ↔
      z ∈ P ∧ ZFSet.pair z (SetMembers.raw K) ∈ r) :
    MeetIso meet.toSmallMeetOrder (Attachment.idealOrder meet.toSmallMeetOrder K) := by
  apply isoOntoIdeal meet.toSmallMeetOrder (embedding.toSmallMeetEmbedding meet meet) K
  · intro x
    exact ((range _).1 ⟨SetMembers.raw x, SetMembers.raw_mem x, embedding.smallValue_entry x⟩).2
  · intro z hz
    obtain ⟨x, hx, entry⟩ := (range (SetMembers.raw z)).2 ⟨SetMembers.raw_mem z, hz⟩
    refine ⟨SetMembers.ofMem x hx, (embedding.smallValue_eq_iff _ z).2 ?_⟩
    simpa only [SetMembers.raw_ofMem] using entry

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_CompressionExternalTileOverlaps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization Compression Compression.RecursiveMaps
universe u

theorem externalRectangleParameters_exists {P G r μ A : ZFSet.{u}}
    (z : SetMembers (externalRectangles P G r μ A)) :
    ∃ v : ZFSet.{u} × ZFSet.{u} × ZFSet.{u} × ZFSet.{u} × ZFSet.{u},
    SetMembers.raw z = externalRectangleCode v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 ∧
      ExternalRectangleCode P G r μ A v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 := by
  obtain ⟨c, b, d, g, h, equal, code⟩ :=
    (mem_externalRectangles P G r μ A _).1 (SetMembers.raw_mem z)
  exact ⟨(c, b, d, g, h), equal, code⟩

noncomputable def externalRectangleParameters {P G r μ A : ZFSet.{u}}
    (z : SetMembers (externalRectangles P G r μ A)) :
    ZFSet.{u} × ZFSet.{u} × ZFSet.{u} × ZFSet.{u} × ZFSet.{u} :=
  Classical.choose (externalRectangleParameters_exists z)

theorem externalRectangleParameters_spec {P G r μ A : ZFSet.{u}}
    (z : SetMembers (externalRectangles P G r μ A)) :
    let v := externalRectangleParameters z
    SetMembers.raw z = externalRectangleCode v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 ∧
      ExternalRectangleCode P G r μ A v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 :=
  Classical.choose_spec (externalRectangleParameters_exists z)

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalMap (i : SetMembers I) : ZFSet.{u} :=
  completion.algebra.function.value ⟨SetMembers.raw i, SetMembers.raw_mem i⟩

theorem externalMap_entry (i : SetMembers I) :
    ZFSet.pair (SetMembers.raw i) (completion.externalMap i) ∈ completion.algebra.maps :=
  completion.algebra.function.value_entry ⟨SetMembers.raw i, SetMembers.raw_mem i⟩

noncomputable def externalCap (i : SetMembers I) : SetMembers (completion.algebra.union.fields 0) :=
  (SetMembers.presentation I).decodeFunction (SetMembers.presentation (completion.algebra.union.fields 0))
    (completion.algebra.caps τ) completion.caps_function i

theorem externalCap_entry (i : SetMembers I) :
    ZFSet.pair (SetMembers.raw i) (SetMembers.raw (completion.externalCap i)) ∈ completion.algebra.caps τ :=
  (SetMembers.presentation I).decodeFunction_mem (SetMembers.presentation (completion.algebra.union.fields 0))
    (completion.algebra.caps τ) completion.caps_function i

noncomputable def externalCopy (i : SetMembers I) :
    MeetIso completion.algebra.union.meet.toSmallMeetOrder
      (Attachment.idealOrder completion.algebra.union.meet.toSmallMeetOrder (completion.externalCap i)) :=
  smallCompressionTileIso completion.algebra.union.meet
    (completion.algebra.embedding _ _ (completion.externalMap_entry i)) (completion.externalCap i)
    (fun x => completion.range _ _ _ x (completion.externalMap_entry i) (completion.externalCap_entry i))

variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))

noncomputable def externalRectangle
    (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) :
    ActionRectangle completion.algebra.union.meet.toSmallMeetOrder
      (completion.algebra.union.action.toSmallMeetIso group completion.algebra.union.meet) :=
  (((externalRectangleParameters_spec z).2).lift_compression compression oldAction).toSmallActionRectangle
    group completion.algebra.union.action completion.algebra.union.meet

noncomputable def externalRequest :
    ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0) →
      TileRequests.Request completion.algebra.union.meet.toSmallMeetOrder
  | .inl i => .compression (completion.externalCap i) (completion.externalCopy i)
  | .inr (.inl x) => .separation (SetMembers.ofMem (SetMembers.raw x)
      (compression.subset (SetMembers.raw_mem x)))
  | .inr (.inr z) => .rectangle ((completion.externalRectangle group oldAction compression z).toInput
      (SetMembers.ofMem τ completion.top_mem) (fun x => by
        simpa only [MeetOrderCode.toSmallMeetOrder, SetMembers.raw_ofMem] using
          completion.top _ (SetMembers.raw_mem x)))

noncomputable def externalFamily : TileRequests.Family completion.algebra.union.meet.toSmallMeetOrder
    (ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)) where
  top := SetMembers.ofMem τ completion.top_mem
  greatest x := by
    simpa only [MeetOrderCode.toSmallMeetOrder, SetMembers.raw_ofMem] using
      completion.top _ (SetMembers.raw_mem x)
  request := completion.externalRequest group oldAction compression

theorem externalFamily_child (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)) :
    (completion.externalFamily group oldAction compression).Child r = ExternalRequestChild r := by
  rcases r with i | (x | z) <;> rfl

noncomputable def externalFamilyLetterEquiv :
    (completion.externalFamily group oldAction compression).Letters ≃
      Sigma (@ExternalRequestChild I P0 (externalRectangles P0 G r0 μ0 A0)) where
  toFun x := ⟨x.1, cast (completion.externalFamily_child group oldAction compression x.1) x.2⟩
  invFun x := ⟨x.1, cast (completion.externalFamily_child group oldAction compression x.1).symm x.2⟩
  left_inv x := by cases x; simp; rfl
  right_inv x := by cases x; simp

noncomputable def externalFamilyLetterPresentation :
    Presentation (completion.externalFamily group oldAction compression).Letters where
  carrier := externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
  encode x := externalRequestLetterCode (completion.externalFamilyLetterEquiv group oldAction compression x)
  injective := (externalRequestLetterCode_injective _ _ _).comp
    (completion.externalFamilyLetterEquiv group oldAction compression).injective
  mem_carrier z := by
    have member : z ∈ externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0) ↔
        ∃ x : Sigma (@ExternalRequestChild I P0 (externalRectangles P0 G r0 μ0 A0)),
          externalRequestLetterCode x = z :=
      (externalRequestLetterPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).mem_carrier z
    rw [member]
    exact ⟨fun ⟨x, hx⟩ => ⟨(completion.externalFamilyLetterEquiv group oldAction compression).symm x, by
      simpa only [Equiv.apply_symm_apply] using hx⟩, fun ⟨x, hx⟩ =>
      ⟨completion.externalFamilyLetterEquiv group oldAction compression x, hx⟩⟩

theorem externalFamilyLetterPresentation_carrier :
    (completion.externalFamilyLetterPresentation group oldAction compression).carrier =
      externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0) := rfl

end GroundCompressionCompletion

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem compressionProjection_entry_iff (I i j : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (natSetCode 0) i) j ∈ productSecond {natSetCode 0} I ↔
      i ∈ I ∧ j = i := by
  rw [mem_productSecond]
  constructor
  · rintro ⟨t, ht, x, hx, equal⟩
    have sameI := (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 equal).1).2
    exact ⟨sameI.symm ▸ hx, (ZFSet.pair_inj.1 equal).2.trans sameI.symm⟩
  · rintro ⟨hi, equal⟩
    subst j
    exact ⟨natSetCode 0, ZFSet.mem_singleton.2 rfl, i, hi, rfl⟩

theorem externalCompressionField_entry_iff {I V F i y : ZFSet.{u}}
    (function : ZFSet.IsFunc I V F) :
    ZFSet.pair (ZFSet.pair (natSetCode 0) i) y ∈ externalCompressionField I V F ↔
      ZFSet.pair i y ∈ F := by
  rw [externalCompressionField, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, j, _, projection, entry⟩
    have same := (compressionProjection_entry_iff I i j).1 projection
    exact same.2 ▸ entry
  · intro entry
    have bounds := ZFSet.pair_mem_prod.1 (function.1 entry)
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, bounds.1⟩, bounds.2,
      i, bounds.1, (compressionProjection_entry_iff I i i).2 ⟨bounds.1, rfl⟩, entry⟩

theorem externalCompressionField_function {I V F : ZFSet.{u}}
    (function : ZFSet.IsFunc I V F) :
    ZFSet.IsFunc (ZFSet.prod {natSetCode 0} I) V (externalCompressionField I V F) :=
  relationCompose_function_of_subset (productSecond_function {natSetCode 0} I) function (fun _ h => h)

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalCaps : ZFSet.{u} :=
  externalCompressionField I (completion.algebra.union.fields 0) (completion.algebra.caps τ)

theorem external_fields_entries (i f k : ZFSet.{u}) :
    (ZFSet.pair (ZFSet.pair (natSetCode 0) i) f ∈ completion.externalMaps ↔
      ZFSet.pair i f ∈ completion.algebra.maps) ∧
    (ZFSet.pair (ZFSet.pair (natSetCode 0) i) k ∈ completion.externalCaps ↔
      ZFSet.pair i k ∈ completion.algebra.caps τ) :=
  ⟨externalCompressionField_entry_iff completion.algebra.function.to_isFunc,
    externalCompressionField_entry_iff completion.caps_function⟩

end GroundCompressionCompletion

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))

noncomputable def externalFamilyVertexCode
    (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)) :
    Option ((completion.externalFamily group oldAction compression).Child r) → ZFSet.{u}
  | none => natSetCode 0
  | some child => insert
      (externalRequestChildCode r (cast (completion.externalFamily_child group oldAction compression r) child))
      (externalRequestChildCode r (cast (completion.externalFamily_child group oldAction compression r) child))

theorem externalFamilyVertexCode_root
    (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)) :
    completion.externalFamilyVertexCode group oldAction compression r none = natSetCode 0 := rfl

theorem externalFamilyVertexCode_compression (i : SetMembers I) :
    completion.externalFamilyVertexCode group oldAction compression (.inl i) (some ⟨()⟩) = natSetCode 1 := rfl

theorem externalFamilyVertexCode_separation (x : SetMembers P0) :
    completion.externalFamilyVertexCode group oldAction compression (.inr (.inl x)) (some ⟨()⟩) = natSetCode 1 := rfl

theorem externalFamilyVertexCode_rectangle (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) (b : Bool) :
    completion.externalFamilyVertexCode group oldAction compression (.inr (.inr z)) (some ⟨b⟩) =
      natSetCode (if b then 2 else 1) := by cases b <;> rfl

end PartitionPilot.Forcing.GroundCompressionCompletion



namespace PartitionPilot.Forcing
open SetRealization
universe u

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

theorem externalMaps_compression_iff (i : SetMembers I) (f : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) f ∈ completion.externalMaps ↔
      f = completion.externalMap i := by
  rw [(completion.external_fields_entries (SetMembers.raw i) f ∅).1]
  exact ⟨fun entry => (completion.algebra.function.unique entry (completion.externalMap_entry i)),
    fun equal => equal.symm ▸ completion.externalMap_entry i⟩

theorem externalMaps_tag {tag x f : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair tag x) f ∈ completion.externalMaps) : tag = natSetCode 0 := by
  have function := externalCompressionField_function completion.algebra.function.to_isFunc
  have domain := (ZFSet.pair_mem_prod.1 (function.1 entry)).1
  exact ZFSet.mem_singleton.1 (ZFSet.pair_mem_prod.1 domain).1

theorem externalMap_external_bound (i : SetMembers I) : completion.externalMap i ∈ completion.externalMaps.sUnion.sUnion :=
  pair_second_mem_doubleUnion ((completion.externalMaps_compression_iff i _).2 rfl)

theorem externalOverlapForward_compression {P Rectangles r A : ZFSet.{u}}
    (task : SetMembers I) (i x j y : ZFSet.{u}) :
    ExternalRequestOverlapForward P G Rectangles completion.externalMaps completion.externalMaps.sUnion.sUnion r A
      (natSetCode 0) (natSetCode 1) (natSetCode 2)
      (ZFSet.pair (natSetCode 0) (SetMembers.raw task)) i x j y ↔
      i = natSetCode 0 ∧ j = natSetCode 1 ∧ ZFSet.pair y x ∈ completion.externalMap task := by
  simp only [ExternalRequestOverlapForward, ZFSet.pair_inj, natSetCode_injective.eq_iff,
    completion.externalMaps_compression_iff]
  simp
  intro _ _ _
  simpa only [ZFSet.mem_sUnion] using completion.externalMap_external_bound task

theorem externalOverlapForward_separation {P Rectangles r A : ZFSet.{u}}
    (point : SetMembers P) (i x j y : ZFSet.{u}) :
    ExternalRequestOverlapForward P G Rectangles completion.externalMaps completion.externalMaps.sUnion.sUnion r A
      (natSetCode 0) (natSetCode 1) (natSetCode 2)
      (ZFSet.pair (natSetCode 1) (SetMembers.raw point)) i x j y ↔
      i = natSetCode 0 ∧ j = natSetCode 1 ∧ x = y ∧ ZFSet.pair x (SetMembers.raw point) ∈ r := by
  have empty : ∀ f, ZFSet.pair (ZFSet.pair (natSetCode 1) (SetMembers.raw point)) f ∉ completion.externalMaps := by
    intro f entry
    have equal := natSetCode_injective (completion.externalMaps_tag entry)
    exact Nat.noConfusion equal
  simp only [ExternalRequestOverlapForward, ZFSet.pair_inj, natSetCode_injective.eq_iff]
  simp [empty, SetMembers.raw_mem point]

theorem externalOverlapForward_rectangle {P r0 μ0 A0 r A : ZFSet.{u}}
    (z : SetMembers (externalRectangles P G r0 μ0 A0)) (i x j y : ZFSet.{u}) :
    let v := externalRectangleParameters z
    ExternalRequestOverlapForward P G (externalRectangles P G r0 μ0 A0)
      completion.externalMaps completion.externalMaps.sUnion.sUnion r A
      (natSetCode 0) (natSetCode 1) (natSetCode 2)
      (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) i x j y ↔
      (i = natSetCode 0 ∧ j = natSetCode 1 ∧ ZFSet.pair y v.1 ∈ r ∧ ZFSet.pair (ZFSet.pair v.2.2.2.1 y) x ∈ A) ∨
      (i = natSetCode 0 ∧ j = natSetCode 2 ∧ ZFSet.pair y v.1 ∈ r ∧ ZFSet.pair (ZFSet.pair v.2.2.2.2 y) x ∈ A) ∨
      (i = natSetCode 1 ∧ j = natSetCode 2 ∧ x = y ∧ ZFSet.pair x v.2.1 ∈ r) := by
  have empty : ∀ f, ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) f ∉ completion.externalMaps := by
    intro f entry
    have equal := natSetCode_injective (completion.externalMaps_tag entry)
    exact Nat.noConfusion equal
  dsimp only
  rw [ExternalRequestOverlapForward]
  constructor
  · rintro (⟨_, _, f, _, entry, _⟩ | ⟨_, _, w, _, equal, _⟩ | rect)
    · exact False.elim (empty f entry)
    · exact False.elim (by have eq := natSetCode_injective (ZFSet.pair_inj.1 equal).1; omega)
    · obtain ⟨t, _, c, _, b, _, d, _, g, _, h, _, qt, tuple, overlap⟩ := rect
      have equalT := (ZFSet.pair_inj.1 qt).2
      have coords := externalRectangleCode_inj.1
        (tuple.symm.trans (equalT.symm.trans (externalRectangleParameters_spec z).1))
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := coords
      exact overlap
  · intro overlap
    have params := externalRectangleParameters_spec z
    exact Or.inr (Or.inr ⟨SetMembers.raw z, SetMembers.raw_mem z,
      _, params.2.1, _, params.2.2.1, _, params.2.2.2.1, _, params.2.2.2.2.1, _, params.2.2.2.2.2.1,
      rfl, params.1, overlap⟩)

end GroundCompressionCompletion
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization Compression Compression.RecursiveMaps
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))

local notation "p" => completion.algebra.union.meet.toSmallMeetOrder
local notation "f" => completion.externalFamily group oldAction compression
local notation "U" => completion.algebra.union.fields 0
local notation "ru" => completion.algebra.union.fields 1
local notation "au" => completion.algebra.union.fields 12

theorem externalFamily_diagonal_iff
    (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0))
    (i : Option ((f).Child r)) (x y : SetMembers U) :
    ((f).flatVertex r i).toFun x = ((f).flatVertex r i).toFun y ↔ SetMembers.raw x = SetMembers.raw y :=
  ⟨fun same => congrArg SetMembers.raw (embedding_injective ((f).flatVertex r i).toMeetEmbedding same),
    fun same => congrArg ((f).flatVertex r i).toFun (SetMembers.raw_injective U same)⟩

theorem externalFamily_compression_overlap (task : SetMembers I) (x y : SetMembers U) :
    ((f).flatVertex (.inl task) none).toFun x = ((f).flatVertex (.inl task) (some ⟨()⟩)).toFun y ↔
      ZFSet.pair (SetMembers.raw y) (SetMembers.raw x) ∈ completion.externalMap task := by
  change (BinaryTiles.compression p (f).top (completion.externalCap task) (f).greatest
    (completion.externalCopy task)).left.toFun x =
    (BinaryTiles.compression p (f).top (completion.externalCap task) (f).greatest
      (completion.externalCopy task)).right.toFun y ↔ _
  rw [BinaryTiles.compression_identification]
  change Sum.inl x = Sum.inl ((completion.externalCopy task).toFun y).val ↔ _
  rw [Sum.inl.injEq, eq_comm]
  exact (completion.algebra.embedding _ _ (completion.externalMap_entry task)).smallValue_eq_iff y x

theorem externalFamily_separation_overlap (point : SetMembers P0) (x y : SetMembers U) :
    ((f).flatVertex (.inr (.inl point)) none).toFun x =
      ((f).flatVertex (.inr (.inl point)) (some ⟨()⟩)).toFun y ↔
      SetMembers.raw x = SetMembers.raw y ∧ ZFSet.pair (SetMembers.raw x) (SetMembers.raw point) ∈ ru := by
  let W := SetMembers.ofMem (SetMembers.raw point) (compression.subset (SetMembers.raw_mem point))
  change (BinaryTiles.separation p W).left.toFun x = (BinaryTiles.separation p W).right.toFun y ↔ _
  rw [eq_comm, (BinaryTiles.separation p W).overlap_exact]
  change (∃ _ : ZFSet.pair (SetMembers.raw y) (SetMembers.raw W) ∈ ru, y = x) ↔ _
  simp only [W, SetMembers.raw_ofMem]
  constructor
  · rintro ⟨lower, rfl⟩
    exact ⟨rfl, lower⟩
  · rintro ⟨same, lower⟩
    have equal := SetMembers.raw_injective U same
    exact ⟨by simpa only [← equal] using lower, equal.symm⟩

theorem externalFamily_rectangle_first_overlap
    (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) (x y : SetMembers U) :
    let v := externalRectangleParameters z
    ((f).flatVertex (.inr (.inr z)) none).toFun x =
      ((f).flatVertex (.inr (.inr z)) (some ⟨false⟩)).toFun y ↔
      ZFSet.pair (SetMembers.raw y) v.1 ∈ ru ∧
        ZFSet.pair (ZFSet.pair v.2.2.2.1 (SetMembers.raw y)) (SetMembers.raw x) ∈ au := by
  let rect := completion.externalRectangle group oldAction compression z
  let tile := rect.toInput (f).top (f).greatest
  change tile.root.toFun x = tile.first.toFun y ↔ _
  rw [eq_comm, tile.first_root_intersection]
  have fields := (((externalRectangleParameters_spec z).2).lift_compression compression oldAction).toSmallActionRectangle_fields
    group completion.algebra.union.action completion.algebra.union.meet
  have code : (p).le y tile.C ↔ ZFSet.pair (SetMembers.raw y) (externalRectangleParameters z).1 ∈ ru := by
    change ZFSet.pair (SetMembers.raw y) (SetMembers.raw rect.C) ∈ ru ↔ _
    rw [show SetMembers.raw rect.C = _ from fields.1]
  have actor : tile.g1.toFun y = x ↔
      ZFSet.pair (ZFSet.pair (externalRectangleParameters z).2.2.2.1 (SetMembers.raw y)) (SetMembers.raw x) ∈ au := by
    change completion.algebra.union.action.act rect.first y = x ↔ _
    rw [completion.algebra.union.action.act_eq_iff]
    rw [show SetMembers.raw rect.first = _ from fields.2.2.2.1]
  exact and_congr code actor

theorem externalFamily_rectangle_second_overlap
    (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) (x y : SetMembers U) :
    let v := externalRectangleParameters z
    ((f).flatVertex (.inr (.inr z)) none).toFun x =
      ((f).flatVertex (.inr (.inr z)) (some ⟨true⟩)).toFun y ↔
      ZFSet.pair (SetMembers.raw y) v.1 ∈ ru ∧
        ZFSet.pair (ZFSet.pair v.2.2.2.2 (SetMembers.raw y)) (SetMembers.raw x) ∈ au := by
  let rect := completion.externalRectangle group oldAction compression z
  let tile := rect.toInput (f).top (f).greatest
  change tile.root.toFun x = tile.second.toFun y ↔ _
  rw [eq_comm, tile.second_root_intersection]
  have fields := (((externalRectangleParameters_spec z).2).lift_compression compression oldAction).toSmallActionRectangle_fields
    group completion.algebra.union.action completion.algebra.union.meet
  have code : (p).le y tile.C ↔ ZFSet.pair (SetMembers.raw y) (externalRectangleParameters z).1 ∈ ru := by
    change ZFSet.pair (SetMembers.raw y) (SetMembers.raw rect.C) ∈ ru ↔ _
    rw [show SetMembers.raw rect.C = _ from fields.1]
  have actor : tile.g2.toFun y = x ↔
      ZFSet.pair (ZFSet.pair (externalRectangleParameters z).2.2.2.2 (SetMembers.raw y)) (SetMembers.raw x) ∈ au := by
    change completion.algebra.union.action.act rect.second y = x ↔ _
    rw [completion.algebra.union.action.act_eq_iff]
    rw [show SetMembers.raw rect.second = _ from fields.2.2.2.2]
  exact and_congr code actor

theorem externalFamily_rectangle_children_overlap
    (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) (x y : SetMembers U) :
    let v := externalRectangleParameters z
    ((f).flatVertex (.inr (.inr z)) (some ⟨false⟩)).toFun x =
      ((f).flatVertex (.inr (.inr z)) (some ⟨true⟩)).toFun y ↔
      SetMembers.raw x = SetMembers.raw y ∧ ZFSet.pair (SetMembers.raw x) v.2.1 ∈ ru := by
  let rect := completion.externalRectangle group oldAction compression z
  let tile := rect.toInput (f).top (f).greatest
  change tile.first.toFun x = tile.second.toFun y ↔ _
  rw [tile.children_intersection]
  have fields := (((externalRectangleParameters_spec z).2).lift_compression compression oldAction).toSmallActionRectangle_fields
    group completion.algebra.union.action completion.algebra.union.meet
  change (ZFSet.pair (SetMembers.raw x) (SetMembers.raw rect.B) ∈ ru ∧ x = y) ↔ _
  rw [show SetMembers.raw rect.B = _ from fields.2.1]
  rw [← (SetMembers.raw_injective U).eq_iff, and_comm]

end PartitionPilot.Forcing.GroundCompressionCompletion

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_ExternalTileVertexPresentation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))

theorem externalFamilyVertexCode_injective
    (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)) :
    Function.Injective (completion.externalFamilyVertexCode group oldAction compression r) := by
  rcases r with i | (x | z)
  all_goals
    intro v w equal
    cases v with
    | none =>
      cases w with
      | none => rfl
      | some w =>
        cases w with | up w =>
          cases w <;> simp only [externalFamilyVertexCode_root, externalFamilyVertexCode_compression,
            externalFamilyVertexCode_separation, externalFamilyVertexCode_rectangle,
            natSetCode_injective.eq_iff] at equal <;> contradiction
    | some v =>
      cases w with
      | none =>
        cases v with | up v =>
          cases v <;> simp only [externalFamilyVertexCode_root, externalFamilyVertexCode_compression,
            externalFamilyVertexCode_separation, externalFamilyVertexCode_rectangle,
            natSetCode_injective.eq_iff] at equal <;> contradiction
      | some w =>
        cases v with | up v =>
          cases w with | up w =>
            cases v <;> cases w <;> simp_all only [externalFamilyVertexCode_compression,
              externalFamilyVertexCode_separation, externalFamilyVertexCode_rectangle,
              natSetCode_injective.eq_iff, Bool.false_eq_true] <;> simp_all

theorem externalFamilyVertexCode_range
    (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)) (v : ZFSet.{u}) :
    (v = natSetCode 0 ∨ v = natSetCode 1 ∨
      (externalRequestIndexCode r ∈ ZFSet.prod {natSetCode 2} (externalRectangles P0 G r0 μ0 A0) ∧
        v = natSetCode 2)) ↔
    ∃ i, completion.externalFamilyVertexCode group oldAction compression r i = v := by
  rcases r with j | (x | z)
  · simp only [externalRequestIndexCode, ZFSet.pair_mem_prod, ZFSet.mem_singleton,
      natSetCode_injective.eq_iff, show ¬ (0 : Nat) = 2 by decide, false_and, or_false]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨none, rfl⟩
      · exact ⟨some ⟨()⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i with
      | none => exact Or.inl rfl
      | some i => exact Or.inr rfl
  · simp only [externalRequestIndexCode, ZFSet.pair_mem_prod, ZFSet.mem_singleton,
      natSetCode_injective.eq_iff, show ¬ (1 : Nat) = 2 by decide, false_and, or_false]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨none, rfl⟩
      · exact ⟨some ⟨()⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i with
      | none => exact Or.inl rfl
      | some i => exact Or.inr rfl
  · simp only [externalRequestIndexCode, ZFSet.pair_mem_prod, ZFSet.mem_singleton,
      SetMembers.raw_mem, and_self, true_and]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨none, rfl⟩
      · exact ⟨some ⟨false⟩, rfl⟩
      · exact ⟨some ⟨true⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i with
      | none => exact Or.inl rfl
      | some i =>
        cases i with | up b =>
          cases b
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)

noncomputable def externalFamilyTileVertexPresentation :
    Presentation (Sigma fun r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0) =>
      Option ((completion.externalFamily group oldAction compression).Child r) ×
        SetMembers (completion.algebra.union.fields 0)) where
  carrier := externalTileVertices (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0))
    (externalRectangles P0 G r0 μ0 A0) (completion.algebra.union.fields 0)
  encode v := ZFSet.pair (ZFSet.pair (externalRequestIndexCode v.1)
    (completion.externalFamilyVertexCode group oldAction compression v.1 v.2.1)) (SetMembers.raw v.2.2)
  injective := by
    rintro ⟨r, i, x⟩ ⟨s, j, y⟩ equal
    have outer := ZFSet.pair_inj.1 equal
    have inner := ZFSet.pair_inj.1 outer.1
    have same := externalRequestIndexCode_injective I P0 (externalRectangles P0 G r0 μ0 A0) inner.1
    cases same
    have vertex := completion.externalFamilyVertexCode_injective group oldAction compression r inner.2
    have point := SetMembers.raw_injective _ outer.2
    cases vertex
    cases point
    rfl
  mem_carrier z := by
    constructor
    · intro hz
      have shape : ∃ q i x, z = ZFSet.pair (ZFSet.pair q i) x := by
        rcases ZFSet.mem_union.1 hz with h | h
        all_goals
          obtain ⟨qi, hqi, x, _, rfl⟩ := ZFSet.mem_prod.1 h
          obtain ⟨q, _, i, _, rfl⟩ := ZFSet.mem_prod.1 hqi
          exact ⟨q, i, x, rfl⟩
      obtain ⟨q, i, x, rfl⟩ := shape
      obtain ⟨hqi, hx⟩ := (triple_mem_externalTileVertices _ _ _ _ _ _).1 hz
      have hq : q ∈ externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0) := by
        rcases hqi with ⟨hq, _⟩ | ⟨hq, _⟩
        · exact hq
        · exact ZFSet.mem_union.2 (Or.inr hq)
      obtain ⟨r, rfl⟩ := ((externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).mem_carrier q).1 hq
      have hv : i = natSetCode 0 ∨ i = natSetCode 1 ∨
          (externalRequestIndexCode r ∈ ZFSet.prod {natSetCode 2} (externalRectangles P0 G r0 μ0 A0) ∧
            i = natSetCode 2) := by tauto
      obtain ⟨v, rfl⟩ := (completion.externalFamilyVertexCode_range group oldAction compression r i).1 hv
      exact ⟨⟨r, v, SetMembers.ofMem x hx⟩, by simp only [SetMembers.raw_ofMem]; rfl⟩
    · rintro ⟨⟨r, i, x⟩, rfl⟩
      apply (triple_mem_externalTileVertices _ _ _ _ _ _).2
      refine ⟨?_, SetMembers.raw_mem x⟩
      have hv := (completion.externalFamilyVertexCode_range group oldAction compression r _).2 ⟨i, rfl⟩
      have hq := (externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem r
      tauto

theorem externalFamilyTileVertexPresentation_encode
    (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0))
    (i : Option ((completion.externalFamily group oldAction compression).Child r))
    (x : SetMembers (completion.algebra.union.fields 0)) :
    (completion.externalFamilyTileVertexPresentation group oldAction compression).encode ⟨r, i, x⟩ =
      ZFSet.pair (ZFSet.pair (externalRequestIndexCode r)
        (completion.externalFamilyVertexCode group oldAction compression r i)) (SetMembers.raw x) := rfl

end PartitionPilot.Forcing.GroundCompressionCompletion

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTileStarIncidence
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetFormula
universe u

noncomputable def tileStarTargetGraph (E R S Q C request generators multiplication : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (tileStarDartCarrier E R S) (tileStarDartCarrier E R S) (tileStarVertexCarrier Q E R)
    (tileStarReverseGraph E R S) (tileStarSourceGraph E R S Q C request generators multiplication)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFixedTopOrders
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

theorem fixedTopMeet_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P r : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets) : fixedTopMeet P r ∈ M.sets :=
  M.canonicalMeetGraph_mem pairing unions powers separation
    (M.fixedTopCarrier_mem pairing unions hP) (M.fixedTopOrder_mem pairing unions powers separation hP hr)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCompressionPrefixGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

variable {base limit : ZFSet.{u}}
variable (prior : ZFSet.{u} → ZFSet.{u}) (stages : Nat → ZFSet.{u}) (final : ZFSet.{u})

theorem compressionPrefixValue_stamp {stamps : ZFSet.{u}}
    (times : CompressionStampCode base stamps limit) (n : Nat) :
    compressionPrefixValue base limit prior stages final (compressionStamp base n) = stages n := by
  classical
  have notOld : ¬(compressionStamp base n ∈ base ∨ compressionStamp base n = base) :=
    fun h => h.elim (compressionStamp_not_old base n).1 (compressionStamp_not_old base n).2
  have witnessed : ∃ k, compressionStamp base n = compressionStamp base k := ⟨n, rfl⟩
  simp only [compressionPrefixValue, ite_eq_right notOld,
    ite_eq_right (times.stamp_ne_limit n), dite_eq_left witnessed]
  exact congrArg stages ((compressionStamp_injective base witnessed.choose_spec).symm)

theorem compressionPrefixValue_limit {stamps : ZFSet.{u}}
    (times : CompressionStampCode base stamps limit) :
    compressionPrefixValue base limit prior stages final limit = final := by
  classical
  have notOld : ¬(limit ∈ base ∨ limit = base) := by
    rintro (member | equal)
    · exact ZFSet.mem_asymm member times.base_mem_limit
    · have member := times.base_mem_limit
      rw [equal] at member
      exact ZFSet.mem_irrefl base member
  simp only [compressionPrefixValue, ite_eq_right notOld, ite_true, if_true]

theorem compressionPrefixValue_eq_prior_below {stamps t s : ZFSet.{u}}
    (times : CompressionStampCode base stamps limit)
    (old : t ∈ base ∨ t = base) (before : s ∈ t) :
    compressionPrefixValue base limit prior stages final s = prior s := by
  apply compressionPrefixValue_old prior stages final
  apply Or.inl
  rcases old with member | equal
  · exact (ordinalSetProperty_member times.ordinal times.base_mem_limit).1 t member s before
  · exact equal ▸ before

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem compressionPrefixValue_mem {stamps s : ZFSet.{u}}
    (times : CompressionStampCode base stamps limit)
    (priorGround : ∀ t, t ∈ base ∨ t = base → prior t ∈ M.sets)
    (stageGround : ∀ n, stages n ∈ M.sets) (finalGround : final ∈ M.sets)
    (cutoff : s ∈ insert limit limit) :
    compressionPrefixValue base limit prior stages final s ∈ M.sets := by
  rcases ZFSet.mem_insert_iff.1 cutoff with equal | before
  · rw [equal, compressionPrefixValue_limit prior stages final times]
    exact finalGround
  · rcases (times.mem_limit_iff s).1 before with member | equal | ⟨n, equal⟩
    · rw [compressionPrefixValue_old prior stages final (Or.inl member)]
      exact priorGround s (Or.inl member)
    · rw [compressionPrefixValue_old prior stages final (Or.inr equal)]
      exact priorGround s (Or.inr equal)
    · rw [equal, compressionPrefixValue_stamp prior stages final times n]
      exact stageGround n

end TransitiveGround

end

open SetFormula
universe u

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {T : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)

noncomputable def value (j : Fin 5) (s : ZFSet.{u}) : ZFSet.{u} :=
  (fields.graphFunction j).totalValue s

theorem value_entry (j : Fin 5) {s : ZFSet.{u}} (hs : s ∈ T) :
    ZFSet.pair s (fields.value j s) ∈ fields.graph j :=
  (fields.graphFunction j).totalValue_entry hs

theorem value_eq_of_entry (j : Fin 5) {s x : ZFSet.{u}}
    (entry : ZFSet.pair s x ∈ fields.graph j) : fields.value j s = x :=
  (fields.graphFunction j).totalValue_eq_of_entry entry

theorem value_ground (j : Fin 5) (s : ZFSet.{u}) : fields.value j s ∈ M.sets :=
  (fields.graphFunction j).totalValue_ground M (fields.graph_ground j) s

end GroundChronologyFields

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

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)
variable (core : ChronologyCoreCode T fields.bound C D rD fields.graph)
include core

theorem decoded_point {s : ZFSet.{u}} (hs : s ∈ T) :
    ChronologyPointCode T C D rD s (fields.value 0 s) (fields.value 1 s)
      (fields.value 2 s) (fields.value 3 s) (fields.value 4 s) :=
  core.point s hs _ _ _ _ _ (fields.value_entry 0 hs) (fields.value_entry 1 hs)
    (fields.value_entry 2 hs) (fields.value_entry 3 hs) (fields.value_entry 4 hs)

noncomputable def toHistory
    (layers : ∀ cutoff ∈ T, ∀ t ∈ T, t = cutoff ∨ t ∈ cutoff →
      CodedGrowthLayer M (fields.value 0) (fields.value 1) (fields.value 2)
        (fields.value 0 cutoff) (fields.value 1 cutoff) (fields.value 2 cutoff)
          (fields.value 3 cutoff) t) : GroundChronologicalHistory M T C D rD where
  space := fields.value 0
  order := fields.value 1
  meetGraph := fields.value 2
  birth := fields.value 3
  height := fields.value 4
  space_mem := fun s _ => fields.value_ground 0 s
  order_mem := fun s _ => fields.value_ground 1 s
  meet_mem := fun s _ => fields.value_ground 2 s
  birth_mem := fun s _ => fields.value_ground 3 s
  height_mem := fun s _ => fields.value_ground 4 s
  meet_order := fun _ hs => (fields.decoded_point core hs).meet
  birth_function := fun _ hs => (fields.decoded_point core hs).birth_function
  birth_bound := fun _ hs => (fields.decoded_point core hs).birth_bound
  old_meet := fun _ hs => (fields.decoded_point core hs).old_meet
  strict_height := fun _ hs => (fields.decoded_point core hs).strict_height
  layer := layers

end GroundChronologyFields
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundChronologicalHistory

open SetFormula
universe u
variable {M N : TransitiveGround.{u}} {T C Q qlt : ZFSet.{u}}
variable (history : GroundChronologicalHistory M T C Q qlt)

def of_inclusion (includes : M.sets ⊆ N.sets) : GroundChronologicalHistory N T C Q qlt where
  space := history.space
  order := history.order
  meetGraph := history.meetGraph
  birth := history.birth
  height := history.height
  space_mem := fun s hs => includes (history.space_mem s hs)
  order_mem := fun s hs => includes (history.order_mem s hs)
  meet_mem := fun s hs => includes (history.meet_mem s hs)
  birth_mem := fun s hs => includes (history.birth_mem s hs)
  height_mem := fun s hs => includes (history.height_mem s hs)
  meet_order := history.meet_order
  birth_function := history.birth_function
  birth_bound := history.birth_bound
  old_meet := history.old_meet
  strict_height := history.strict_height
  layer := fun cutoff hc t ht bounded => (history.layer cutoff hc t ht bounded).of_inclusion includes

end PartitionPilot.Forcing.GroundChronologicalHistory



namespace PartitionPilot.Forcing.GroundChronologyFields
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)

noncomputable def attainedBound : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.range (fun j : Fin 5 => functionGraphRange T (fields.graph j)))

theorem mem_attainedBound (y : ZFSet.{u}) :
    y ∈ fields.attainedBound ↔ ∃ j : Fin 5, ∃ s ∈ T, ZFSet.pair s y ∈ fields.graph j := by
  constructor
  · intro hy
    obtain ⟨R, hR, hy⟩ := ZFSet.mem_sUnion.1 hy
    obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 hR
    exact ⟨j, (mem_functionGraphRange T (fields.graph j) y).1 hy⟩
  · rintro ⟨j, s, hs, entry⟩
    exact ZFSet.mem_sUnion.2 ⟨functionGraphRange T (fields.graph j),
      ZFSet.mem_range.2 ⟨j, rfl⟩,
      (mem_functionGraphRange T (fields.graph j) y).2 ⟨s, hs, entry⟩⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)

include pairing unions separation in
theorem attainedBound_ground : fields.attainedBound ∈ M.sets :=
  M.union_mem unions (M.finite_range_mem pairing unions ⟨T, fields.time_ground⟩
    (fun j : Fin 5 => functionGraphRange T (fields.graph j))
    (fun j => M.functionGraphRange_mem unions separation fields.time_ground (fields.graph_ground j)))

noncomputable def normalizeBound : GroundChronologyFields M T where
  time_ground := fields.time_ground
  bound := fields.attainedBound
  bound_ground := fields.attainedBound_ground pairing unions separation
  graph := fields.graph
  graph_ground := fields.graph_ground
  function := by
    intro j
    refine ⟨?_, (fields.function j).2⟩
    intro z hz
    obtain ⟨s, hs, y, rfl⟩ := (fields.graphFunction j).shape z hz
    exact ZFSet.pair_mem_prod.2 ⟨hs, (fields.mem_attainedBound y).2 ⟨j, s, hs, hz⟩⟩

theorem normalizeBound_core (core : ChronologyCoreCode T fields.bound C D rD fields.graph) :
    ChronologyCoreCode T (fields.normalizeBound pairing unions separation).bound C D rD
      (fields.normalizeBound pairing unions separation).graph :=
  ⟨(fields.normalizeBound pairing unions separation).function, core.point⟩

end PartitionPilot.Forcing.GroundChronologyFields



namespace PartitionPilot.Forcing
open SetFormula
universe u





structure GroundSerializedChronology (M : TransitiveGround.{u}) (T C D rD : ZFSet.{u}) where
  fields : GroundChronologyFields M T
  ordinal : ordinalSetProperty T
  core : ChronologyCoreCode T fields.bound C D rD fields.graph
  layerBound : ZFSet.{u}
  layer_bound_ground : layerBound ∈ M.sets
  layers : ZFSet.{u}
  layers_ground : layers ∈ M.sets
  layer_function : ZFSet.IsFunc (chronologyPairs T) layerBound layers
  layer_code : ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s → ∀ z,
    ZFSet.pair (ZFSet.pair s t) z ∈ layers →
      GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z

namespace GroundSerializedChronology
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M T C D rD)

noncomputable def codeFields : Fin 3 → ZFSet.{u} :=
  Fin.cases serial.fields.code (Fin.cases serial.layerBound (fun _ => serial.layers))

noncomputable def code : ZFSet.{u} := nonemptyTupleCode 2 serial.codeFields

end GroundSerializedChronology
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyFieldAppend
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCompressionBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T base old : ZFSet.{u}}
variable {data : GroundCompressionUnionData M initial I Sources Reps G m one T}
variable (births : GroundCompressionBirthData M initial I Sources Reps G m one T data base old)

theorem union_function_successor :
    ZFSet.IsFunc (data.fields 0) (insert births.limit births.limit) births.birth :=
  isFunc_retarget_of_entries births.function
    (fun _ _ entry => ZFSet.mem_insert_of_mem _ (ZFSet.pair_mem_prod.1 (births.function.1 entry)).2)

theorem finite_function_successor (n : Nat) :
    ZFSet.IsFunc (initial.iterate M I Sources Reps G T (n + 1)).D
      (insert births.limit births.limit)
      (graphRestriction (initial.iterate M I Sources Reps G T (n + 1)).D births.birth) := by
  have restricted := (show FunctionGraphOn (data.fields 0) births.birth from
    ⟨births.limit, births.function⟩).restrict ((data.fieldUnion 0).subset (n + 1))
  apply isFunc_retarget_of_entries restricted.to_isFunc
  intro x t entry
  exact ZFSet.mem_insert_of_mem _
    (ZFSet.pair_mem_prod.1 (births.function.1 (pair_mem_graphRestriction.1 entry).1)).2

end GroundCompressionBirthData

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)

theorem finite_birth_bound
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) (n : Nat) {x t : ZFSet.{u}}
    (entry : ZFSet.pair x t ∈
      graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth) :
    t ∈ compressionStamp base n ∨ t = compressionStamp base n := by
  have before := state.canonical_birth_before_stamp pairing unions powers separation
    hI hSources hReps hG hT births.extension births.initial_bound (n + 1) entry
  rw [compressionStamp_succ] at before
  exact (ZFSet.mem_insert_iff.1 before).symm

end GroundCompressionState

namespace GroundChronologicalHistory
variable {M : TransitiveGround.{u}} {T0 C Q qlt base stamps limit s : ZFSet.{u}}
variable (history : GroundChronologicalHistory M T0 C Q qlt)

theorem prefix_birth_function_successor
    (times : CompressionStampCode base stamps limit)
    (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
    (prior : s ∈ base ∨ s = base) :
    ZFSet.IsFunc (history.space s) (insert limit limit) (history.birth s) := by
  have hs : s ∈ T0 := prior.elim (fun before => ordinal.1 base hBase s before)
    (fun equal => equal.symm ▸ hBase)
  have below : s ∈ limit := times.union.subset 0 (compressionStamp_old_mem prior 0)
  apply isFunc_retarget_of_entries (history.birth_function s hs)
  intro x t entry
  have hx := (ZFSet.pair_mem_prod.1 ((history.birth_function s hs).1 entry)).1
  have bounded := history.birth_bound s hs x hx t entry
  apply ZFSet.mem_insert_of_mem
  exact bounded.elim (fun equal => equal.symm ▸ below)
    (fun before => times.ordinal.1 s below t before)

end GroundChronologicalHistory

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)
variable (prior : GroundChronologicalHistory M T0 C Q qlt)

noncomputable def prefixFields : CompressionChronologyFields.{u} where
  space := compressionPrefixValue base births.limit prior.space
    (fun n => (state.data.iterate M I Sources Reps G T (n + 1)).D) (data.fields 0)
  order := compressionPrefixValue base births.limit prior.order
    (fun n => (state.data.iterate M I Sources Reps G T (n + 1)).rD) (data.fields 1)
  meetGraph := compressionPrefixValue base births.limit prior.meetGraph
    (fun n => (state.data.iterate M I Sources Reps G T (n + 1)).μD) (data.fields 2)
  birth := compressionPrefixValue base births.limit prior.birth
    (fun n => graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth) births.birth
  height := compressionPrefixValue base births.limit prior.height
    (fun n => heights.function.natValue (n + 1)) heights.height

theorem prefixFields_old {s : ZFSet.{u}} (before : s ∈ base ∨ s = base) :
    (state.prefixFields data births heights prior).space s = prior.space s ∧
    (state.prefixFields data births heights prior).order s = prior.order s ∧
    (state.prefixFields data births heights prior).meetGraph s = prior.meetGraph s ∧
    (state.prefixFields data births heights prior).birth s = prior.birth s ∧
    (state.prefixFields data births heights prior).height s = prior.height s := by
  dsimp only [prefixFields]
  exact ⟨compressionPrefixValue_old _ _ _ before,
    compressionPrefixValue_old _ _ _ before, compressionPrefixValue_old _ _ _ before,
    compressionPrefixValue_old _ _ _ before, compressionPrefixValue_old _ _ _ before⟩

theorem prefixFields_stamp (n : Nat) :
    (state.prefixFields data births heights prior).space (compressionStamp base n) =
      (state.data.iterate M I Sources Reps G T (n + 1)).D ∧
    (state.prefixFields data births heights prior).order (compressionStamp base n) =
      (state.data.iterate M I Sources Reps G T (n + 1)).rD ∧
    (state.prefixFields data births heights prior).meetGraph (compressionStamp base n) =
      (state.data.iterate M I Sources Reps G T (n + 1)).μD ∧
    (state.prefixFields data births heights prior).birth (compressionStamp base n) =
      graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth ∧
    (state.prefixFields data births heights prior).height (compressionStamp base n) =
      heights.function.natValue (n + 1) := by
  dsimp only [prefixFields]
  exact ⟨compressionPrefixValue_stamp _ _ _ births.times n,
    compressionPrefixValue_stamp _ _ _ births.times n, compressionPrefixValue_stamp _ _ _ births.times n,
    compressionPrefixValue_stamp _ _ _ births.times n, compressionPrefixValue_stamp _ _ _ births.times n⟩

theorem prefixFields_limit :
    (state.prefixFields data births heights prior).space births.limit = data.fields 0 ∧
    (state.prefixFields data births heights prior).order births.limit = data.fields 1 ∧
    (state.prefixFields data births heights prior).meetGraph births.limit = data.fields 2 ∧
    (state.prefixFields data births heights prior).birth births.limit = births.birth ∧
    (state.prefixFields data births heights prior).height births.limit = heights.height := by
  dsimp only [prefixFields]
  exact ⟨compressionPrefixValue_limit _ _ _ births.times,
    compressionPrefixValue_limit _ _ _ births.times, compressionPrefixValue_limit _ _ _ births.times,
    compressionPrefixValue_limit _ _ _ births.times, compressionPrefixValue_limit _ _ _ births.times⟩

end GroundCompressionState

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)
variable (prior : GroundChronologicalHistory M T0 C Q qlt)

theorem prefixFields_stage_laws
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
    {s : ZFSet.{u}} (cutoff : s ∈ insert births.limit births.limit) :
    let fields := state.prefixFields data births heights prior
    MeetOrderCode (fields.space s) (fields.order s) (fields.meetGraph s) ∧
    ZFSet.IsFunc (fields.space s) (insert births.limit births.limit) (fields.birth s) ∧
    (∀ x ∈ fields.space s, ∀ t, ZFSet.pair x t ∈ fields.birth s → t = s ∨ t ∈ s) ∧
    OldMeetCode (fields.order s) (fields.meetGraph s) (fields.birth s) ∧
    StrictLexHeightCode (fields.space s) C Q (fields.order s) (fields.height s) qlt := by
  classical
  dsimp only
  by_cases before : s ∈ base ∨ s = base
  · have hs := before.elim (fun member => ordinal.1 base hBase s member)
      (fun equal => equal.symm ▸ hBase)
    obtain ⟨space, order, meet, birth, height⟩ := state.prefixFields_old data births heights prior before
    rw [space, order, meet, birth, height]
    exact ⟨prior.meet_order s hs,
      prior.prefix_birth_function_successor births.times ordinal hBase before,
      prior.birth_bound s hs, prior.old_meet s hs, prior.strict_height s hs⟩
  · rcases ZFSet.mem_insert_iff.1 cutoff with rfl | below
    · obtain ⟨space, order, meet, birth, height⟩ := state.prefixFields_limit data births heights prior
      rw [space, order, meet, birth, height]
      exact ⟨data.meet, births.union_function_successor,
        fun _ _ _ entry => Or.inr (ZFSet.pair_mem_prod.1 (births.function.1 entry)).2,
        births.old_meet, heights.code⟩
    · have stamped : ∃ n, s = compressionStamp base n := by
        rcases (births.times.mem_limit_iff s).1 below with member | equal | stamped
        · exact False.elim (before (Or.inl member))
        · exact False.elim (before (Or.inr equal))
        · exact stamped
      obtain ⟨n, rfl⟩ := stamped
      obtain ⟨space, order, meet, birth, height⟩ := state.prefixFields_stamp data births heights prior n
      rw [space, order, meet, birth, height]
      exact ⟨(state.canonical_iterate_codes pairing unions powers separation
          hI hSources hReps hG hT (n + 1)).1,
        births.finite_function_successor n,
        fun _ _ _ entry => (state.finite_birth_bound data births pairing unions powers separation
          hI hSources hReps hG hT n entry).symm,
        births.finite_old_meet (n + 1), heights.finite (n + 1)⟩





theorem prefixFields_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
    {s : ZFSet.{u}} (cutoff : s ∈ insert births.limit births.limit) :
    (state.prefixFields data births heights prior).space s ∈ M.sets ∧
    (state.prefixFields data births heights prior).order s ∈ M.sets ∧
    (state.prefixFields data births heights prior).meetGraph s ∈ M.sets ∧
    (state.prefixFields data births heights prior).birth s ∈ M.sets ∧
    (state.prefixFields data births heights prior).height s ∈ M.sets := by
  have originalIndex {t : ZFSet.{u}} (before : t ∈ base ∨ t = base) : t ∈ T0 :=
    before.elim (fun h => ordinal.1 base hBase t h) (fun h => h ▸ hBase)
  have finite (n : Nat) :
      (state.data.iterate M I Sources Reps G T (n + 1)).D ∈ M.sets ∧
      (state.data.iterate M I Sources Reps G T (n + 1)).rD ∈ M.sets ∧
      (state.data.iterate M I Sources Reps G T (n + 1)).μD ∈ M.sets := by
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT (n + 1)
    rw [← equal]
    exact ⟨current.ground.carrier, current.ground.order, current.ground.meet⟩
  have finiteBirth (n : Nat) :
      graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth ∈ M.sets :=
    M.pair_right (M.transitive births.family_ground ((births.family_entries (n + 1) _).2 rfl))
  have finiteHeight (n : Nat) : heights.function.natValue (n + 1) ∈ M.sets :=
    M.pair_right (M.transitive heights.family_ground (heights.function.natValue_entry (n + 1)))
  dsimp only [prefixFields]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact TransitiveGround.compressionPrefixValue_mem _ _ _ M births.times
      (fun t ht => prior.space_mem t (originalIndex ht)) (fun n => (finite n).1) (data.ground 0) cutoff
  · exact TransitiveGround.compressionPrefixValue_mem _ _ _ M births.times
      (fun t ht => prior.order_mem t (originalIndex ht)) (fun n => (finite n).2.1) (data.ground 1) cutoff
  · exact TransitiveGround.compressionPrefixValue_mem _ _ _ M births.times
      (fun t ht => prior.meet_mem t (originalIndex ht)) (fun n => (finite n).2.2) (data.ground 2) cutoff
  · exact TransitiveGround.compressionPrefixValue_mem _ _ _ M births.times
      (fun t ht => prior.birth_mem t (originalIndex ht)) finiteBirth births.birth_ground cutoff
  · exact TransitiveGround.compressionPrefixValue_mem _ _ _ M births.times
      (fun t ht => prior.height_mem t (originalIndex ht)) finiteHeight heights.height_ground cutoff

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem pair_mem_terminalChronologyGraph (s f v x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ terminalChronologyGraph s f v ↔
      (x = s ∧ y = v) ∨ (ZFSet.pair x y ∈ f ∧ x ∈ s) := by
  rw [terminalChronologyGraph, ZFSet.mem_insert_iff, ZFSet.pair_inj, pair_mem_graphRestriction]

theorem terminalChronologyGraph_function {s f v : ZFSet.{u}}
    (function : FunctionGraphOn (insert s s) f) :
    FunctionGraphOn (insert s s) (terminalChronologyGraph s f v) := by
  refine ⟨insert v (ZFSet.sUnion (ZFSet.sUnion f)), ?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.1 hz with rfl | old
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert _ _, ZFSet.mem_insert _ _⟩
    · obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 old
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert_of_mem _ hx,
        ZFSet.mem_insert_of_mem _ (pair_second_mem_doubleUnion entry)⟩
  · intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with rfl | hx
    · refine ⟨v, (pair_mem_terminalChronologyGraph _ _ _ _ _).2 (Or.inl ⟨rfl,rfl⟩), ?_⟩
      intro y entry
      rcases (pair_mem_terminalChronologyGraph _ _ _ _ _).1 entry with new | old
      · exact new.2
      · exact False.elim (ZFSet.mem_irrefl _ old.2)
    · obtain ⟨y, entry, unique⟩ := function.to_isFunc.2 x (ZFSet.mem_insert_of_mem _ hx)
      refine ⟨y, (pair_mem_terminalChronologyGraph _ _ _ _ _).2 (Or.inr ⟨entry,hx⟩), ?_⟩
      intro y' entry'
      rcases (pair_mem_terminalChronologyGraph _ _ _ _ _).1 entry' with new | old
      · exact False.elim (ZFSet.mem_irrefl s (new.1 ▸ hx))
      · exact unique y' old.1

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {s : ZFSet.{u}}
variable (fields : GroundChronologyFields M (insert s s))
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
variable (newValues : Fin 5 → ZFSet.{u}) (ground : ∀ j, newValues j ∈ M.sets)

noncomputable def replaceTerminal : GroundChronologyFields M (insert s s) :=
  GroundChronologyFields.ofGraphs pairing unions fields.time_ground
    (fun j => terminalChronologyGraph s (fields.graph j) (newValues j))
    (fun j => M.insert_mem pairing unions
      (M.orderedPair_mem pairing (M.transitive fields.time_ground (ZFSet.mem_insert _ _)) (ground j))
      (M.graphRestriction_mem unions separation
        (M.transitive fields.time_ground (ZFSet.mem_insert _ _)) (fields.graph_ground j)))
    (fun j => terminalChronologyGraph_function ⟨fields.bound, fields.function j⟩)

end GroundChronologyFields

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundChronologyFields
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {T : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (newValues : Fin 5 → ZFSet.{u}) (ground : ∀ j, newValues j ∈ M.sets)

noncomputable def appendTime : GroundChronologyFields M (insert T T) :=
  GroundChronologyFields.ofGraphs pairing unions (M.insert_mem pairing unions fields.time_ground fields.time_ground)
    (fun j => insert (ZFSet.pair T (newValues j)) (fields.graph j))
    (fun j => M.insert_mem pairing unions (M.orderedPair_mem pairing fields.time_ground (ground j))
      (fields.graph_ground j))
    (fun j => (fields.graphFunction j).insert (ZFSet.mem_irrefl T) (newValues j))

theorem appendTime_graph (j : Fin 5) :
    (fields.appendTime pairing unions newValues ground).graph j =
      insert (ZFSet.pair T (newValues j)) (fields.graph j) := rfl

theorem appendTime_old_entries (j : Fin 5) {s y : ZFSet.{u}} (hs : s ∈ T) :
    ZFSet.pair s y ∈ (fields.appendTime pairing unions newValues ground).graph j ↔
      ZFSet.pair s y ∈ fields.graph j := by
  rw [appendTime_graph, ZFSet.mem_insert_iff, ZFSet.pair_inj]
  constructor
  · rintro (⟨rfl, _⟩ | entry)
    · exact False.elim (ZFSet.mem_irrefl _ hs)
    · exact entry
  · exact Or.inr

theorem appendTime_value_old (j : Fin 5) {s : ZFSet.{u}} (hs : s ∈ T) :
    (fields.appendTime pairing unions newValues ground).value j s = fields.value j s := by
  apply GroundChronologyFields.value_eq_of_entry
  exact (fields.appendTime_old_entries pairing unions newValues ground j hs).2 (fields.value_entry j hs)

end PartitionPilot.Forcing.GroundChronologyFields

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_CompressionPrefixCoinitiality
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

noncomputable def incoming_birth_layer_of_constancy
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {base birth bound stamp : ZFSet.{u}}
    (born : ZFSet.IsFunc state.data.D bound birth)
    (old : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (before : base ∈ stamp)
    (space : Space base = P0) (order : sourceOrder base = r0) (meet : sourceMeet base = μ0) :
    CodedGrowthLayer M Space sourceOrder sourceMeet state.data.currentCarrier
      state.data.currentOrder state.data.currentMeet (state.batch.batchBirth birth stamp) stamp := by
  apply state.batch.batchBirth_incoming_layer pairing unions powers separation
    state.ground.carrier state.ground.indices state.ground.spaces state.ground.relations
    state.ground.anchors state.ground.embeddings born old (fun _ => base) (fun _ => before)
  · intro i
    exact space.trans ((constant.space_entry_iff _ _).1
      (state.batch.space_entry ⟨SetMembers.raw i, SetMembers.raw_mem i⟩)).2.symm
  · intro i
    exact order.trans ((constant.relation_entry_iff _ _).1
      (state.batch.rel_entry ⟨SetMembers.raw i, SetMembers.raw_mem i⟩)).2.symm
  · intro i
    exact meet.trans ((constant.meet_entry_iff _ _).1
      (state.batch.meet_entry ⟨SetMembers.raw i, SetMembers.raw_mem i⟩)).2.symm

variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include hI hSources hReps hG hT

noncomputable def canonical_incoming_birth_layer
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {base stamps limit old birth : ZFSet.{u}}
    (code : NatBirthExtensionCode (fun n => (state.data.iterate M I Sources Reps G T n).D)
      (compressionStamp base) old birth)
    (born : ZFSet.IsFunc state.data.D limit old)
    (times : CompressionStampCode base stamps limit)
    (oldBound : ∀ x t, ZFSet.pair x t ∈ old → t ∈ base ∨ t = base)
    (space : Space base = P0) (order : sourceOrder base = r0) (meet : sourceMeet base = μ0)
    (n : Nat) :
    CodedGrowthLayer M Space sourceOrder sourceMeet
      (state.data.iterate M I Sources Reps G T n).currentCarrier
      (state.data.iterate M I Sources Reps G T n).currentOrder
      (state.data.iterate M I Sources Reps G T n).currentMeet
      (graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D birth)
      (compressionStamp base n) := by
  let current := state.iterate pairing unions powers separation hI hSources hReps hG hT n
  have equal : current.data = state.data.iterate M I Sources Reps G T n :=
    state.iterate_data pairing unions powers separation hI hSources hReps hG hT n
  have currentConstant : RecursiveTemplateConstancy P0 r0 μ0 current.data := by
    simpa only [equal] using constant.iterate M I Sources Reps G T n
  have finite : ZFSet.IsFunc current.data.D limit
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) := by
    simpa only [equal] using state.canonical_birth_function data pairing unions powers separation
      hI hSources hReps hG hT code born times n
  have earlier : ∀ x t, ZFSet.pair x t ∈
      graphRestriction (state.data.iterate M I Sources Reps G T n).D birth → t ∈ compressionStamp base n :=
    fun _ _ entry => state.canonical_birth_before_stamp pairing unions powers separation
      hI hSources hReps hG hT code oldBound n entry
  have result := current.incoming_birth_layer_of_constancy pairing unions powers separation
    currentConstant finite earlier (compressionStamp_base_mem base n) space order meet
  change CodedGrowthLayer M Space sourceOrder sourceMeet current.data.currentCarrier
    current.data.currentOrder current.data.currentMeet
    (taggedBirth current.data.D current.data.fresh
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth)
      (compressionStamp base n)) (compressionStamp base n) at result
  rw [state.canonical_birth_step pairing unions powers separation hI hSources hReps hG hT code born n]
  simpa only [equal] using result

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

noncomputable def ground_birth_incoming_layer
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    (space : Space base = P0) (order : sourceOrder base = r0) (meet : sourceMeet base = μ0)
    (n : Nat) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (data.fields 0) (data.fields 1)
      (data.fields 2) births.birth (compressionStamp base n) :=
  state.canonical_birth_layer_to_union data pairing unions powers separation
    hI hSources hReps hG hT births.extension births.initial_function (n + 1)
    ((compressionStamp_mem_iff base n (n + 1)).2 (Nat.lt_succ_self n))
    (state.canonical_incoming_birth_layer pairing unions powers separation data
      hI hSources hReps hG hT constant births.extension births.initial_function births.times
      births.initial_bound space order meet n)

noncomputable def ground_birth_prior_layer {t : ZFSet.{u}} (priorTime : t ∈ base ∨ t = base)
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet state.data.D state.data.rD state.data.μD old t) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (data.fields 0) (data.fields 1)
      (data.fields 2) births.birth t :=
  state.prior_birth_layer_to_union data pairing unions powers separation
    hI hSources hReps hG hT births.extension births.initial_function priorTime layer

omit pairing unions powers separation hI hSources hReps hG hT in
def ground_birth_limit_layer :
    CodedGrowthLayer M Space sourceOrder sourceMeet (data.fields 0) (data.fields 1)
      (data.fields 2) births.birth births.limit :=
  .empty_of_no_birth ⟨data.fields 0, data.ground 0⟩ (fun x _ => births.no_limit_birth x)

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
include pairing unions powers separation hI hSources hReps hG hT

section Transfer
variable {base limit old birth : ZFSet.{u}}
variable (code : NatBirthExtensionCode (fun n => (state.data.iterate M I Sources Reps G T n).D)
    (compressionStamp base) old birth)
variable (born : ZFSet.IsFunc state.data.D limit old)
include code born

noncomputable def canonical_birth_layer_to_finite (n k : Nat) (before : n ≤ k)
    {t : ZFSet.{u}} (earlier : t ∈ compressionStamp base n)
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet
      (state.data.iterate M I Sources Reps G T n).D
      (state.data.iterate M I Sources Reps G T n).rD
      (state.data.iterate M I Sources Reps G T n).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) t) :
    CodedGrowthLayer M Space sourceOrder sourceMeet
      (state.data.iterate M I Sources Reps G T k).D
      (state.data.iterate M I Sources Reps G T k).rD
      (state.data.iterate M I Sources Reps G T k).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T k).D birth) t := by
  have mono := fun n k h => (state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT (n := n) (k := k) h).1
  have growth := state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT before
  have ground : (state.data.iterate M I Sources Reps G T n).D ∈ M.sets := by
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT n
    rw [← equal]
    exact current.ground.carrier
  exact layer.of_literal_extension separation ground growth.1 growth.2.1 growth.2.2.1
    (NatBirthExtensionCode.restriction_mono mono before)
    (fun _ _ entry => code.earlier_fiber mono born
      (fun _ _ h => compressionStamp_subset base h) n earlier
      (pair_mem_graphRestriction.1 entry).1)

noncomputable def prior_birth_layer_to_finite (k : Nat) {t : ZFSet.{u}}
    (priorTime : t ∈ base ∨ t = base)
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet
      state.data.D state.data.rD state.data.μD old t) :
    CodedGrowthLayer M Space sourceOrder sourceMeet
      (state.data.iterate M I Sources Reps G T k).D
      (state.data.iterate M I Sources Reps G T k).rD
      (state.data.iterate M I Sources Reps G T k).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T k).D birth) t := by
  have mono := fun n k h => (state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT (n := n) (k := k) h).1
  have zero := code.restriction_zero mono born
  apply state.canonical_birth_layer_to_finite pairing unions powers separation
    hI hSources hReps hG hT code born 0 k (Nat.zero_le k) (compressionStamp_old_mem priorTime 0)
  rw [zero]
  simpa only [RecursiveStateData.iterate_zero] using layer
end Transfer

noncomputable def ground_birth_finite_all_layers
    (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
    {base old : ZFSet.{u}}
    (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    (space : Space base = P0) (order : sourceOrder base = r0) (meet : sourceMeet base = μ0)
    (prior : ∀ t, t ∈ base ∨ t = base →
      CodedGrowthLayer M Space sourceOrder sourceMeet state.data.D state.data.rD state.data.μD old t)
    (n : Nat) (t : ZFSet.{u}) (bound : t ∈ compressionStamp base n ∨ t = compressionStamp base n) :
    CodedGrowthLayer M Space sourceOrder sourceMeet
      (state.data.iterate M I Sources Reps G T (n + 1)).D
      (state.data.iterate M I Sources Reps G T (n + 1)).rD
      (state.data.iterate M I Sources Reps G T (n + 1)).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth) t := by
  have cases : t ∈ base ∨ t = base ∨ ∃ j, j ≤ n ∧ t = compressionStamp base j := by
    rcases bound with before | equal
    · rcases (mem_compressionStamp_iff base t n).1 before with old | equal | ⟨j, before, equal⟩
      · exact Or.inl old
      · exact Or.inr (Or.inl equal)
      · exact Or.inr (Or.inr ⟨j, Nat.le_of_lt before, equal⟩)
    · exact Or.inr (Or.inr ⟨n, Nat.le_refl n, equal⟩)
  apply Classical.choice
  rcases cases with old | equal | ⟨j, before, rfl⟩
  · exact ⟨state.prior_birth_layer_to_finite pairing unions powers separation
      hI hSources hReps hG hT births.extension births.initial_function (n + 1)
      (Or.inl old) (prior t (Or.inl old))⟩
  · exact ⟨state.prior_birth_layer_to_finite pairing unions powers separation
      hI hSources hReps hG hT births.extension births.initial_function (n + 1)
      (Or.inr equal) (prior t (Or.inr equal))⟩
  · exact ⟨state.canonical_birth_layer_to_finite pairing unions powers separation
      hI hSources hReps hG hT births.extension births.initial_function (j + 1) (n + 1)
      (Nat.add_le_add_right before 1)
      ((compressionStamp_mem_iff base j (j + 1)).2 (Nat.lt_succ_self j))
      (state.canonical_incoming_birth_layer pairing unions powers separation data
        hI hSources hReps hG hT constant births.extension births.initial_function births.times
        births.initial_bound space order meet j)⟩

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)

noncomputable def ground_birth_all_layers
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    (space : Space base = P0) (order : sourceOrder base = r0) (meet : sourceMeet base = μ0)
    (prior : ∀ t, t ∈ base ∨ t = base →
      CodedGrowthLayer M Space sourceOrder sourceMeet state.data.D state.data.rD state.data.μD old t)
    (t : ZFSet.{u}) (bound : t ∈ births.limit ∨ t = births.limit) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (data.fields 0) (data.fields 1)
      (data.fields 2) births.birth t := by
  apply Classical.choice
  rcases bound with before | rfl
  · rcases (births.times.mem_limit_iff t).1 before with original | same | ⟨n, rfl⟩
    · exact ⟨state.ground_birth_prior_layer data births pairing unions powers separation
        hI hSources hReps hG hT (Or.inl original) (prior t (Or.inl original))⟩
    · exact ⟨state.ground_birth_prior_layer data births pairing unions powers separation
        hI hSources hReps hG hT (Or.inr same) (prior t (Or.inr same))⟩
    · exact ⟨state.ground_birth_incoming_layer data births pairing unions powers separation
        hI hSources hReps hG hT constant space order meet n⟩
  · exact ⟨state.ground_birth_limit_layer data births⟩

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T
    data P0 C Q qlt original)
variable (prior : GroundChronologicalHistory M T0 C Q qlt)

theorem prefix_sources_eq_below {t s : ZFSet.{u}} (oldTime : t ∈ base ∨ t = base)
    (before : s ∈ t) :
    (state.prefixFields data births heights prior).space s = prior.space s ∧ (state.prefixFields data births heights prior).order s = prior.order s ∧
      (state.prefixFields data births heights prior).meetGraph s = prior.meetGraph s := by
  dsimp only [prefixFields]
  exact ⟨compressionPrefixValue_eq_prior_below _ _ _ births.times oldTime before,
    compressionPrefixValue_eq_prior_below _ _ _ births.times oldTime before,
    compressionPrefixValue_eq_prior_below _ _ _ births.times oldTime before⟩

variable (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
include ordinal hBase

noncomputable def prefix_old_layer {cutoff t : ZFSet.{u}}
    (oldCutoff : cutoff ∈ base ∨ cutoff = base) (bound : t = cutoff ∨ t ∈ cutoff) :
    CodedGrowthLayer M (state.prefixFields data births heights prior).space (state.prefixFields data births heights prior).order (state.prefixFields data births heights prior).meetGraph
      ((state.prefixFields data births heights prior).space cutoff) ((state.prefixFields data births heights prior).order cutoff) ((state.prefixFields data births heights prior).meetGraph cutoff) ((state.prefixFields data births heights prior).birth cutoff) t := by
  have hc : cutoff ∈ T0 := oldCutoff.elim
    (fun member => ordinal.1 base hBase cutoff member) (fun equal => equal.symm ▸ hBase)
  have ht : t ∈ T0 := bound.elim (fun equal => equal.symm ▸ hc)
    (fun before => ordinal.1 cutoff hc t before)
  have oldTime : t ∈ base ∨ t = base := by
    rcases bound with equal | before
    · exact equal.symm ▸ oldCutoff
    · apply Or.inl
      rcases oldCutoff with member | equal
      · exact ordinal.2 base hBase cutoff member t before
      · exact equal ▸ before
  have layer := (prior.layer cutoff hc t ht bound).congr_sources_below
    (fun s hs => (state.prefix_sources_eq_below data births heights prior oldTime hs).1.symm)
    (fun s hs => (state.prefix_sources_eq_below data births heights prior oldTime hs).2.1.symm)
    (fun s hs => (state.prefix_sources_eq_below data births heights prior oldTime hs).2.2.symm)
  have values := state.prefixFields_old data births heights prior oldCutoff
  simpa only [values.1, values.2.1, values.2.2.1, values.2.2.2.1] using layer

variable (initialDomain : state.data.D = P0) (initialOrder : state.data.rD = r0)
variable (initialMeet : state.data.μD = μ0)
variable (priorSpace : prior.space base = P0) (priorOrder : prior.order base = r0)
variable (priorMeet : prior.meetGraph base = μ0) (priorBirth : prior.birth base = old)
include initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth

noncomputable def prefix_base_layers (t : ZFSet.{u}) (before : t ∈ base ∨ t = base) :
    CodedGrowthLayer M (state.prefixFields data births heights prior).space (state.prefixFields data births heights prior).order (state.prefixFields data births heights prior).meetGraph
      state.data.D state.data.rD state.data.μD old t := by
  have layer := state.prefix_old_layer data births heights prior ordinal hBase
    (Or.inr rfl : base ∈ base ∨ base = base) before.symm
  have values := state.prefixFields_old data births heights prior (Or.inr rfl : base ∈ base ∨ base = base)
  simpa only [values.1, values.2.1, values.2.2.1, values.2.2.2.1,
    priorSpace, priorOrder, priorMeet, priorBirth, initialDomain, initialOrder, initialMeet] using layer

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
include pairing unions powers separation hI hSources hReps hG hT constant

noncomputable def prefix_finite_layers (n : Nat) (t : ZFSet.{u})
    (bound : t = compressionStamp base n ∨ t ∈ compressionStamp base n) :
    CodedGrowthLayer M (state.prefixFields data births heights prior).space (state.prefixFields data births heights prior).order (state.prefixFields data births heights prior).meetGraph
      ((state.prefixFields data births heights prior).space (compressionStamp base n)) ((state.prefixFields data births heights prior).order (compressionStamp base n))
      ((state.prefixFields data births heights prior).meetGraph (compressionStamp base n)) ((state.prefixFields data births heights prior).birth (compressionStamp base n)) t := by
  have atBase := state.prefixFields_old data births heights prior (Or.inr rfl : base ∈ base ∨ base = base)
  have layer := state.ground_birth_finite_all_layers pairing unions powers separation
    hI hSources hReps hG hT data births constant
    (atBase.1.trans priorSpace) (atBase.2.1.trans priorOrder) (atBase.2.2.1.trans priorMeet)
    (state.prefix_base_layers data births heights prior ordinal hBase initialDomain initialOrder
      initialMeet priorSpace priorOrder priorMeet priorBirth) n t bound.symm
  have values := state.prefixFields_stamp data births heights prior n
  simpa only [values.1, values.2.1, values.2.2.1, values.2.2.2.1] using layer

noncomputable def prefix_union_layers (t : ZFSet.{u})
    (bound : t = births.limit ∨ t ∈ births.limit) :
    CodedGrowthLayer M (state.prefixFields data births heights prior).space (state.prefixFields data births heights prior).order (state.prefixFields data births heights prior).meetGraph
      ((state.prefixFields data births heights prior).space births.limit) ((state.prefixFields data births heights prior).order births.limit)
      ((state.prefixFields data births heights prior).meetGraph births.limit) ((state.prefixFields data births heights prior).birth births.limit) t := by
  have atBase := state.prefixFields_old data births heights prior (Or.inr rfl : base ∈ base ∨ base = base)
  have layer := state.ground_birth_all_layers data births pairing unions powers separation
    hI hSources hReps hG hT constant
    (atBase.1.trans priorSpace) (atBase.2.1.trans priorOrder) (atBase.2.2.1.trans priorMeet)
    (state.prefix_base_layers data births heights prior ordinal hBase initialDomain initialOrder
      initialMeet priorSpace priorOrder priorMeet priorBirth) t bound.symm
  have values := state.prefixFields_limit data births heights prior
  simpa only [values.1, values.2.1, values.2.2.1, values.2.2.2.1] using layer

noncomputable def prefix_all_layers :
    ∀ cutoff ∈ insert births.limit births.limit, ∀ t ∈ insert births.limit births.limit,
      t = cutoff ∨ t ∈ cutoff → CodedGrowthLayer M (state.prefixFields data births heights prior).space (state.prefixFields data births heights prior).order (state.prefixFields data births heights prior).meetGraph
        ((state.prefixFields data births heights prior).space cutoff) ((state.prefixFields data births heights prior).order cutoff) ((state.prefixFields data births heights prior).meetGraph cutoff) ((state.prefixFields data births heights prior).birth cutoff) t := by
  intro cutoff hc t _ bound
  apply Classical.choice
  rcases ZFSet.mem_insert_iff.1 hc with equal | before
  · subst cutoff
    exact ⟨state.prefix_union_layers data births heights prior ordinal hBase initialDomain initialOrder
      initialMeet priorSpace priorOrder priorMeet priorBirth pairing unions powers separation
      hI hSources hReps hG hT constant t bound⟩
  · rcases (births.times.mem_limit_iff cutoff).1 before with oldTime | same | ⟨n, rfl⟩
    · exact ⟨state.prefix_old_layer data births heights prior ordinal hBase (Or.inl oldTime) bound⟩
    · exact ⟨state.prefix_old_layer data births heights prior ordinal hBase (Or.inr same) bound⟩
    · exact ⟨state.prefix_finite_layers data births heights prior ordinal hBase initialDomain initialOrder
        initialMeet priorSpace priorOrder priorMeet priorBirth pairing unions powers separation
        hI hSources hReps hG hT constant n t bound⟩

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)
variable (prior : GroundChronologicalHistory M T0 C Q qlt)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
variable (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
variable (initialDomain : state.data.D = P0) (initialOrder : state.data.rD = r0)
variable (initialMeet : state.data.μD = μ0)
variable (priorSpace : prior.space base = P0) (priorOrder : prior.order base = r0)
variable (priorMeet : prior.meetGraph base = μ0) (priorBirth : prior.birth base = old)

noncomputable def prefixHistory :
    GroundChronologicalHistory M (insert births.limit births.limit) C Q qlt where
  space := (state.prefixFields data births heights prior).space
  order := (state.prefixFields data births heights prior).order
  meetGraph := (state.prefixFields data births heights prior).meetGraph
  birth := (state.prefixFields data births heights prior).birth
  height := (state.prefixFields data births heights prior).height
  space_mem := fun _ hs => (state.prefixFields_ground data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).1
  order_mem := fun _ hs => (state.prefixFields_ground data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.1
  meet_mem := fun _ hs => (state.prefixFields_ground data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.2.1
  birth_mem := fun _ hs => (state.prefixFields_ground data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.2.2.1
  height_mem := fun _ hs => (state.prefixFields_ground data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.2.2.2
  meet_order := fun _ hs => (state.prefixFields_stage_laws data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).1
  birth_function := fun _ hs => (state.prefixFields_stage_laws data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.1
  birth_bound := fun _ hs => (state.prefixFields_stage_laws data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.2.1
  old_meet := fun _ hs => (state.prefixFields_stage_laws data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.2.2.1
  strict_height := fun _ hs => (state.prefixFields_stage_laws data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.2.2.2
  layer := state.prefix_all_layers data births heights prior ordinal hBase initialDomain initialOrder
    initialMeet priorSpace priorOrder priorMeet priorBirth pairing unions powers separation
    hI hSources hReps hG hT constant

end PartitionPilot.Forcing.GroundCompressionState



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologicalCompressionCoinitiality
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

structure GroundChronologicalCompression (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 C Q qlt original Targets Separators Filters base old T0 : ZFSet.{u})
    (prior : GroundChronologicalHistory M T0 C Q qlt) where
  born : GroundBornCompression M initial I Sources Reps G m one T τ P0 C Q qlt original
    Targets Separators Filters base old
  history : GroundChronologicalHistory M (insert born.births.limit born.births.limit) C Q qlt
  original_height : prior.height base = original
  old_values : ∀ s, s ∈ base ∨ s = base →
    history.space s = prior.space s ∧ history.order s = prior.order s ∧
      history.meetGraph s = prior.meetGraph s ∧ history.birth s = prior.birth s ∧
        history.height s = prior.height s
  stamp_values : ∀ n,
    history.space (compressionStamp base n) = (initial.iterate M I Sources Reps G T (n + 1)).D ∧
    history.order (compressionStamp base n) = (initial.iterate M I Sources Reps G T (n + 1)).rD ∧
    history.meetGraph (compressionStamp base n) = (initial.iterate M I Sources Reps G T (n + 1)).μD ∧
    history.birth (compressionStamp base n) =
      graphRestriction (initial.iterate M I Sources Reps G T (n + 1)).D born.births.birth ∧
    history.height (compressionStamp base n) = born.profiled.heighted.heights.function.natValue (n + 1)
  limit_values :
    history.space born.births.limit = born.profiled.heighted.completion.algebra.union.fields 0 ∧
    history.order born.births.limit = born.profiled.heighted.completion.algebra.union.fields 1 ∧
    history.meetGraph born.births.limit = born.profiled.heighted.completion.algebra.union.fields 2 ∧
    history.birth born.births.limit = born.births.birth ∧
    history.height born.births.limit = born.profiled.heighted.heights.height

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundInitialExternalGroup
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

noncomputable def externalRequestAlphabet (I P G r μ A : ZFSet.{u}) : ZFSet.{u} :=
  externalGeneratorAlphabet G (externalChildLetters I P (externalRectangles P G r μ A))

structure GroundExternalWordData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P r μ A : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ) : Prop where
  rectangles_ground : externalRectangles P G r μ A ∈ M.sets
  requests_ground : externalRequestCarrier I P (externalRectangles P G r μ A) ∈ M.sets
  letters_ground : externalChildLetters I P (externalRectangles P G r μ A) ∈ M.sets
  kinds_ground : externalRequestKinds I P (externalRectangles P G r μ A) ∈ M.sets
  payloads_ground : externalRequestPayloads I P (externalRectangles P G r μ A) ∈ M.sets
  kinds_function : FunctionGraphOn (externalRequestCarrier I P (externalRectangles P G r μ A))
    (externalRequestKinds I P (externalRectangles P G r μ A))
  payloads_function : FunctionGraphOn (externalRequestCarrier I P (externalRectangles P G r μ A))
    (externalRequestPayloads I P (externalRectangles P G r μ A))
  maps_ground : completion.externalMaps ∈ M.sets
  caps_ground : completion.externalCaps ∈ M.sets
  maps_function : FunctionGraphOn (ZFSet.prod {natSetCode 0} I) completion.externalMaps
  caps_function : ZFSet.IsFunc (ZFSet.prod {natSetCode 0} I)
    (completion.algebra.union.fields 0) completion.externalCaps
  alphabet_ground : externalRequestAlphabet I P G r μ A ∈ M.sets
  words_ground : M.finiteWords (externalRequestAlphabet I P G r μ A) ∈ M.sets
  append_ground : M.finiteWordAppendGraph (externalRequestAlphabet I P G r μ A) ∈ M.sets
  reverse_ground : M.finiteWordReverseGraph (externalRequestAlphabet I P G r μ A) ∈ M.sets
  length_ground : M.finiteWordLengthGraph (externalRequestAlphabet I P G r μ A) ∈ M.sets
  append_function : ZFSet.IsFunc
    (ZFSet.prod (M.finiteWords (externalRequestAlphabet I P G r μ A))
      (M.finiteWords (externalRequestAlphabet I P G r μ A)))
    (M.finiteWords (externalRequestAlphabet I P G r μ A))
    (M.finiteWordAppendGraph (externalRequestAlphabet I P G r μ A))
  reverse_function : ZFSet.IsFunc (M.finiteWords (externalRequestAlphabet I P G r μ A))
    (M.finiteWords (externalRequestAlphabet I P G r μ A))
    (M.finiteWordReverseGraph (externalRequestAlphabet I P G r μ A))
  length_function : ZFSet.IsFunc (M.finiteWords (externalRequestAlphabet I P G r μ A)) ZFSet.omega
    (M.finiteWordLengthGraph (externalRequestAlphabet I P G r μ A))

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionStarIncidence
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hG : G ∈ M.sets) (hLetters : externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0) ∈ M.sets)

noncomputable def externalFamilyGroupPresentation :
    letI := group.toGroup
    Presentation (External (SetMembers G) (completion.externalFamily group oldAction compression).Letters) := by
  letI := group.toGroup
  exact M.externalGroupPresentation pairing unions powers separation infinite (SetMembers.presentation G)
    (completion.externalFamilyLetterPresentation group oldAction compression) hG hLetters

theorem externalFamilyGroupPresentation_carrier :
    letI := group.toGroup
    (completion.externalFamilyGroupPresentation group oldAction compression pairing unions powers separation infinite hG hLetters).carrier =
      M.externalGroupCarrier G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one := by
  let := group.toGroup
  change M.externalGroupCarrier G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0))
    (((SetMembers.presentation G).product (SetMembers.presentation G)).graph (SetMembers.presentation G) (fun p => p.1 * p.2))
    ((SetMembers.presentation G).encode 1) = _
  rw [group.multiplication_graph_eq, group.identity_code_eq]

theorem externalFamilyGroupPresentation_multiplication :
    letI := group.toGroup
    let s := completion.externalFamilyGroupPresentation group oldAction compression pairing unions powers separation infinite hG hLetters
    M.externalGroupMultiplication G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one =
      (s.product s).graph s (fun p => p.1 * p.2) := by
  let := group.toGroup
  have equal := M.externalGroupMultiplication_eq_graph pairing unions powers separation infinite
    (SetMembers.presentation G) (completion.externalFamilyLetterPresentation group oldAction compression) hG hLetters
  rw [group.multiplication_graph_eq, group.identity_code_eq] at equal
  exact equal

theorem externalFamilyGroupPresentation_old :
    letI := group.toGroup
    let s := completion.externalFamilyGroupPresentation group oldAction compression pairing unions powers separation infinite hG hLetters
    M.externalOldInclusion G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one =
      (SetMembers.presentation G).graph s (old (SetMembers G) (completion.externalFamily group oldAction compression).Letters) := by
  let := group.toGroup
  have equal := M.externalOldInclusion_eq_graph pairing unions powers separation infinite
    (SetMembers.presentation G) (completion.externalFamilyLetterPresentation group oldAction compression) hG hLetters
  rw [group.multiplication_graph_eq, group.identity_code_eq] at equal
  exact equal

theorem externalFamilyGroupPresentation_generators :
    letI := group.toGroup
    let s := completion.externalFamilyGroupPresentation group oldAction compression pairing unions powers separation infinite hG hLetters
    M.externalChildGenerators G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one =
      (completion.externalFamilyLetterPresentation group oldAction compression).graph s
        (generator (SetMembers G) (completion.externalFamily group oldAction compression).Letters) := by
  let := group.toGroup
  have equal := M.externalChildGenerators_eq_graph pairing unions powers separation infinite
    (SetMembers.presentation G) (completion.externalFamilyLetterPresentation group oldAction compression) hG hLetters
  rw [group.multiplication_graph_eq, group.identity_code_eq] at equal
  exact equal

theorem externalFamilyGroupPresentation_identity :
    letI := group.toGroup
    let s := completion.externalFamilyGroupPresentation group oldAction compression pairing unions powers separation infinite hG hLetters
    M.externalGroupIdentity G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one = s.encode 1 := by
  let := group.toGroup
  have equal := M.externalGroupIdentity_eq_encode pairing unions powers separation infinite
    (SetMembers.presentation G) (completion.externalFamilyLetterPresentation group oldAction compression) hG hLetters
  rw [group.multiplication_graph_eq, group.identity_code_eq] at equal
  exact equal

end PartitionPilot.Forcing.GroundCompressionCompletion



namespace PartitionPilot.Forcing
open SetFormula
universe u

structure GroundExternalGeometryInputs (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m inv one T τ P r μ A : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ) : Prop where
  words : GroundExternalWordData M initial I Sources Reps G m one T τ P r μ A completion
  group : GroundExternalGroupData M G (externalChildLetters I P (externalRectangles P G r μ A)) m inv one
  old_inclusion_ground : M.externalOldInclusion G
    (externalChildLetters I P (externalRectangles P G r μ A)) m one ∈ M.sets
  old_inclusion_injection : InjectionCode G
    (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (M.externalOldInclusion G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
  generators_ground : M.externalChildGenerators G
    (externalChildLetters I P (externalRectangles P G r μ A)) m one ∈ M.sets
  generators_injection : InjectionCode (externalChildLetters I P (externalRectangles P G r μ A))
    (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (M.externalChildGenerators G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
  original : CompressionOriginalData P r μ A G (completion.algebra.union.fields 0)
    (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) (completion.algebra.union.fields 12)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u})
noncomputable def externalStarTarget (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  tileStarTargetGraph (M.externalGroupCarrier G S m one) R S (M.externalCosetCarrier G S m one)
    (M.externalCosetClassifier G S m one) (tileStarRequestGraph R S)
    (M.externalChildGenerators G S m one) (M.externalGroupMultiplication G S m one)
noncomputable def externalStarAdjacency (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  dartAdjacencyGraph (M.externalStarDarts G S R m one) (M.externalStarVertices G S R m one)
    (M.externalStarSource G S R m one) (M.externalStarTarget G S R m one)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CompressionExternalStepRealization
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

theorem triple_mem_externalFlatPlacements (E Requests U V S generators m w a b : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair w a) b ∈ externalFlatPlacements E Requests U V S generators m ↔
      w ∈ E ∧ a ∈ V ∧ b ∈ ZFSet.prod E U ∧
        ∃ q ∈ Requests, ∃ i ∈ externalRequestTags, ∃ x ∈ U, ∃ v ∈ E,
          a = ZFSet.pair (ZFSet.pair q i) x ∧ b = ZFSet.pair v x ∧
            ExternalFlatVertexWordCode E S generators m (natSetCode 0) (natSetCode 1) (natSetCode 2) q i w v := by
  rw [externalFlatPlacements, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, w', hw, a', ha, b', hb, q, hq, i, hi, x, hx, v, hv, equal, left, right, word⟩
    obtain ⟨wa, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 wa
    exact ⟨hw, ha, hb, q, hq, i, hi, x, hx, v, hv, left, right, word⟩
  · rintro ⟨hw, ha, hb, q, hq, i, hi, x, hx, v, hv, left, right, word⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hw, ha⟩, hb⟩,
      w, hw, a, ha, b, hb, q, hq, i, hi, x, hx, v, hv, rfl, left, right, word⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalFlatPlacements_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {E Requests U V S generators m : ZFSet.{u}}
    (hE : E ∈ M.sets) (hRequests : Requests ∈ M.sets) (hU : U ∈ M.sets) (hV : V ∈ M.sets)
    (hS : S ∈ M.sets) (hGenerators : generators ∈ M.sets) (hm : m ∈ M.sets) :
    externalFlatPlacements E Requests U V S generators m ∈ M.sets := by
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨U, hU⟩
  have hFirst : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  have hSecond : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions hFirst hFirst
  have single : ({natSetCode 2} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hSecond hSecond
  have hTags : externalRequestTags ∈ M.sets :=
    M.insert_mem pairing unions hZero (M.insert_mem pairing unions hFirst single)
  have hL := M.prod_mem pairing unions powers separation hE hU
  let params := extend E (extend Requests (extend externalRequestTags (extend U (extend V
    (extend (ZFSet.prod E U) (extend S (extend generators (extend m (extend (natSetCode 0)
      (extend (natSetCode 1) (extend (natSetCode 2) Fin.elim0)))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalFlatPlacementEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12) params
    (Fin.cases hE (Fin.cases hRequests (Fin.cases hTags (Fin.cases hU (Fin.cases hV (Fin.cases hL
      (Fin.cases hS (Fin.cases hGenerators (Fin.cases hm (Fin.cases hZero
        (Fin.cases hFirst (Fin.cases hSecond (fun i => Fin.elim0 i)))))))))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hE hV) hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalFlatPlacementEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12) (extend z params))
      (ZFSet.prod (ZFSet.prod E V) (ZFSet.prod E U)) = externalFlatPlacements E Requests U V S generators m := by
    apply ZFSet.ext
    intro z
    rw [externalFlatPlacements, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalFlatPlacementEntryFormula
      0 1 2 3 4 5 6 7 8 9 10 11 12 _)
  exact equal ▸ selected

end TransitiveGround





namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalFlatStepGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {E U G V old m A placements overlaps : ZFSet.{u}}
    (hE : E ∈ M.sets) (hU : U ∈ M.sets) (hG : G ∈ M.sets) (hV : V ∈ M.sets)
    (hOld : old ∈ M.sets) (hm : m ∈ M.sets) (hA : A ∈ M.sets)
    (hPlacements : placements ∈ M.sets) (hOverlaps : overlaps ∈ M.sets) :
    externalFlatStepGraph E U G V old m A placements overlaps ∈ M.sets := by
  have hL := M.prod_mem pairing unions powers separation hE hU
  let params := extend (ZFSet.prod E U) (extend E (extend U (extend G (extend V (extend old
    (extend m (extend A (extend placements (extend overlaps Fin.elim0)))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalFlatStepEntryFormula 0 1 2 3 4 5 6 7 8 9 10) params
    (Fin.cases hL (Fin.cases hE (Fin.cases hU (Fin.cases hG (Fin.cases hV (Fin.cases hOld
      (Fin.cases hm (Fin.cases hA (Fin.cases hPlacements (Fin.cases hOverlaps (fun i => Fin.elim0 i)))))))))))
    (M.prod_mem pairing unions powers separation hL hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalFlatStepEntryFormula 0 1 2 3 4 5 6 7 8 9 10) (extend z params))
      (ZFSet.prod (ZFSet.prod E U) (ZFSet.prod E U)) = externalFlatStepGraph E U G V old m A placements overlaps := by
    apply ZFSet.ext
    intro z
    rw [externalFlatStepGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalFlatStepEntryFormula 0 1 2 3 4 5 6 7 8 9 10 _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P r μ A : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion)

include data

theorem flat_relations_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) :
    completion.externalVertices P r μ A ∈ M.sets ∧ completion.externalOverlaps P r μ A ∈ M.sets ∧
      completion.externalPlacements P r μ A ∈ M.sets ∧ completion.externalFlatSteps P r μ A ∈ M.sets := by
  have vertices := M.externalTileVertices_mem pairing unions powers separation
    data.words.requests_ground data.words.rectangles_ground (completion.algebra.union.ground 0)
  have overlaps := M.externalRequestOverlapGraph_mem pairing unions powers separation
    data.words.requests_ground hP hG data.words.rectangles_ground data.words.maps_ground
    (completion.algebra.union.ground 0) (completion.algebra.union.ground 1) (completion.algebra.union.ground 12)
  have placements := M.externalFlatPlacements_mem pairing unions powers separation
    data.group.carrier_mem data.words.requests_ground (completion.algebra.union.ground 0) vertices
    data.words.letters_ground data.generators_ground data.group.multiplication_mem
  exact ⟨vertices, overlaps, placements, M.externalFlatStepGraph_mem pairing unions powers separation
    data.group.carrier_mem (completion.algebra.union.ground 0) hG vertices data.old_inclusion_ground
    data.group.multiplication_mem (completion.algebra.union.ground 12) placements overlaps⟩

theorem point_quotient_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) :
    let L := ZFSet.prod (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
      (completion.algebra.union.fields 0)
    completion.externalFlatEquivalence P r μ A ∈ M.sets ∧
      EquivalenceRelationCode L (completion.externalFlatEquivalence P r μ A) ∧
      completion.externalPointCarrier P r μ A ∈ M.sets ∧ completion.externalPointClassifier P r μ A ∈ M.sets ∧
      ZFSet.IsFunc L (completion.externalPointCarrier P r μ A) (completion.externalPointClassifier P r μ A) ∧
      (∀ C ∈ completion.externalPointCarrier P r μ A, ∃ x ∈ L,
        ZFSet.pair x C ∈ completion.externalPointClassifier P r μ A) ∧
      (∀ x y C D, ZFSet.pair x C ∈ completion.externalPointClassifier P r μ A →
        ZFSet.pair y D ∈ completion.externalPointClassifier P r μ A →
          (C = D ↔ ZFSet.pair x y ∈ completion.externalFlatEquivalence P r μ A)) := by
  dsimp only
  let L := ZFSet.prod (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (completion.algebra.union.fields 0)
  let p := SetMembers.presentation L
  let relation : SetMembers L → SetMembers L → Prop := fun x y =>
    ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ completion.externalFlatSteps P r μ A
  have hL : L ∈ M.sets := M.prod_mem pairing unions powers separation
    data.group.carrier_mem (completion.algebra.union.ground 0)
  exact M.finitePathQuotient_spec pairing unions separation infinite p relation (fun _ _ => Iff.rfl) hL powers
    (data.flat_relations_ground pairing unions powers separation hP hG).2.2.2
    (fun _ _ step => externalFlatStepGraph_symmetric step)

end GroundExternalGeometryInputs
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization Compression Compression.RecursiveMaps
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))

local notation "f" => completion.externalFamily group oldAction compression
local notation "U" => completion.algebra.union.fields 0
local notation "ru" => completion.algebra.union.fields 1
local notation "au" => completion.algebra.union.fields 12
local notation "Rects" => externalRectangles P0 G r0 μ0 A0
local notation "vcode" => completion.externalFamilyVertexCode group oldAction compression

theorem externalFamily_overlapCode_iff (r : ExternalRequestIndex I P0 Rects)
    (i j : Option ((f).Child r)) (x y : SetMembers U) :
    ExternalRequestOverlapCode P0 G Rects completion.externalMaps (⋃₀ ⋃₀ completion.externalMaps) ru au
      (natSetCode 0) (natSetCode 1) (natSetCode 2) (externalRequestIndexCode r)
      (vcode r i) (SetMembers.raw x) (vcode r j) (SetMembers.raw y) ↔
      ((f).flatVertex r i).toFun x = ((f).flatVertex r j).toFun y := by
  rcases r with task | (point | rect)
  · rcases i with _ | ⟨⟨⟨⟩⟩⟩ <;> rcases j with _ | ⟨⟨⟨⟩⟩⟩
    all_goals simp only [ExternalRequestOverlapCode, externalRequestIndexCode,
      externalFamilyVertexCode_root, externalFamilyVertexCode_compression,
      completion.externalOverlapForward_compression, natSetCode_injective.eq_iff]
    · simpa using (completion.externalFamily_diagonal_iff group oldAction compression (.inl task) none x y).symm
    · simpa using (completion.externalFamily_compression_overlap group oldAction compression task x y).symm
    · simpa only [Nat.one_ne_zero, Nat.zero_ne_one, false_and, true_and, or_false, false_or, eq_comm] using
        (completion.externalFamily_compression_overlap group oldAction compression task y x).symm
    · simpa using (completion.externalFamily_diagonal_iff group oldAction compression (.inl task) (some ⟨()⟩) x y).symm
  · rcases i with _ | ⟨⟨⟨⟩⟩⟩ <;> rcases j with _ | ⟨⟨⟨⟩⟩⟩
    all_goals simp only [ExternalRequestOverlapCode, externalRequestIndexCode,
      externalFamilyVertexCode_root, externalFamilyVertexCode_separation,
      completion.externalOverlapForward_separation, natSetCode_injective.eq_iff]
    · simpa using (completion.externalFamily_diagonal_iff group oldAction compression (.inr (.inl point)) none x y).symm
    · simpa using (completion.externalFamily_separation_overlap group oldAction compression point x y).symm
    · simpa only [Nat.one_ne_zero, Nat.zero_ne_one, false_and, true_and, or_false, false_or, eq_comm] using
        (completion.externalFamily_separation_overlap group oldAction compression point y x).symm
    · simpa using (completion.externalFamily_diagonal_iff group oldAction compression (.inr (.inl point)) (some ⟨()⟩) x y).symm
  · rcases i with _ | ⟨⟨a⟩⟩ <;> rcases j with _ | ⟨⟨b⟩⟩
    · simp only [ExternalRequestOverlapCode, externalRequestIndexCode,
        externalFamilyVertexCode_root, completion.externalOverlapForward_rectangle, natSetCode_injective.eq_iff]
      simpa using (completion.externalFamily_diagonal_iff group oldAction compression (.inr (.inr rect)) none x y).symm
    · cases b <;> simp only [ExternalRequestOverlapCode, externalRequestIndexCode,
        externalFamilyVertexCode_root, externalFamilyVertexCode_rectangle, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
        completion.externalOverlapForward_rectangle, natSetCode_injective.eq_iff]
      · simpa using (completion.externalFamily_rectangle_first_overlap group oldAction compression rect x y).symm
      · simpa using (completion.externalFamily_rectangle_second_overlap group oldAction compression rect x y).symm
    · cases a <;> simp only [ExternalRequestOverlapCode, externalRequestIndexCode,
        externalFamilyVertexCode_root, externalFamilyVertexCode_rectangle, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
        completion.externalOverlapForward_rectangle, natSetCode_injective.eq_iff]
      · simpa [eq_comm] using (completion.externalFamily_rectangle_first_overlap group oldAction compression rect y x).symm
      · simpa [eq_comm] using (completion.externalFamily_rectangle_second_overlap group oldAction compression rect y x).symm
    · cases a <;> cases b <;> simp only [ExternalRequestOverlapCode, externalRequestIndexCode,
        externalFamilyVertexCode_rectangle, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
        completion.externalOverlapForward_rectangle, natSetCode_injective.eq_iff]
      · simpa using (completion.externalFamily_diagonal_iff group oldAction compression (.inr (.inr rect)) (some ⟨false⟩) x y).symm
      · simpa using (completion.externalFamily_rectangle_children_overlap group oldAction compression rect x y).symm
      · simpa [eq_comm] using (completion.externalFamily_rectangle_children_overlap group oldAction compression rect y x).symm
      · simpa using (completion.externalFamily_diagonal_iff group oldAction compression (.inr (.inr rect)) (some ⟨true⟩) x y).symm

theorem externalFamilyVertexCode_mem_tags (r : ExternalRequestIndex I P0 Rects)
    (i : Option ((f).Child r)) : vcode r i ∈ externalRequestTags := by
  have range := (completion.externalFamilyVertexCode_range group oldAction compression r _).2 ⟨i, rfl⟩
  rcases range with equal | equal | ⟨_, equal⟩ <;> rw [equal] <;> simp [externalRequestTags]

theorem externalOverlaps_same_request
    (x y : Sigma fun r : ExternalRequestIndex I P0 Rects => Option ((f).Child r) × SetMembers U)
    (entry : ZFSet.pair
      ((completion.externalFamilyTileVertexPresentation group oldAction compression).encode x)
      ((completion.externalFamilyTileVertexPresentation group oldAction compression).encode y) ∈
        completion.externalOverlaps P0 r0 μ0 A0) : x.1 = y.1 := by
  obtain ⟨_, _, q, _, i, _, a, _, j, _, b, _, left, right, _⟩ :=
    (pair_mem_externalRequestOverlapGraph _ _ _ _ _ _ _ _ _ _).1 entry
  exact externalRequestIndexCode_injective I P0 Rects
    (((ZFSet.pair_inj.1 (ZFSet.pair_inj.1 left).1).1).trans
      ((ZFSet.pair_inj.1 (ZFSet.pair_inj.1 right).1).1).symm)

theorem externalOverlaps_entry_iff (r : ExternalRequestIndex I P0 Rects)
    (i j : Option ((f).Child r)) (x y : SetMembers U) :
    ZFSet.pair
      ((completion.externalFamilyTileVertexPresentation group oldAction compression).encode ⟨r, i, x⟩)
      ((completion.externalFamilyTileVertexPresentation group oldAction compression).encode ⟨r, j, y⟩) ∈
        completion.externalOverlaps P0 r0 μ0 A0 ↔
      ((f).flatVertex r i).toFun x = ((f).flatVertex r j).toFun y := by
  rw [← completion.externalFamily_overlapCode_iff group oldAction compression]
  constructor
  · intro entry
    obtain ⟨_, _, q, _, i', _, a, _, j', _, b, _, left, right, code⟩ :=
      (pair_mem_externalRequestOverlapGraph _ _ _ _ _ _ _ _ _ _).1 entry
    obtain ⟨leftPair, rfl⟩ := ZFSet.pair_inj.1 left
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 leftPair
    obtain ⟨rightPair, rfl⟩ := ZFSet.pair_inj.1 right
    obtain ⟨_, rfl⟩ := ZFSet.pair_inj.1 rightPair
    exact code
  · intro code
    exact (pair_mem_externalRequestOverlapGraph _ _ _ _ _ _ _ _ _ _).2
      ⟨(completion.externalFamilyTileVertexPresentation group oldAction compression).encode_mem ⟨r, i, x⟩,
        (completion.externalFamilyTileVertexPresentation group oldAction compression).encode_mem ⟨r, j, y⟩,
        externalRequestIndexCode r, (externalRequestPresentation I P0 Rects).encode_mem r,
        vcode r i, completion.externalFamilyVertexCode_mem_tags group oldAction compression r i,
        SetMembers.raw x, SetMembers.raw_mem x,
        vcode r j, completion.externalFamilyVertexCode_mem_tags group oldAction compression r j,
        SetMembers.raw y, SetMembers.raw_mem y, rfl, rfl, code⟩

end PartitionPilot.Forcing.GroundCompressionCompletion



namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))
local notation "family" => completion.externalFamily group oldAction compression
local notation "letters" => completion.externalFamilyLetterPresentation group oldAction compression
local notation "vertices" => completion.externalFamilyTileVertexPresentation group oldAction compression
local notation "U" => completion.algebra.union.fields 0
local notation "Rects" => externalRectangles P0 G r0 μ0 A0
local notation "S" => externalChildLetters I P0 Rects
local notation "E" => M.externalGroupCarrier G S m one
local notation "vcode" => completion.externalFamilyVertexCode group oldAction compression

theorem externalFamily_vertex_letter (r : ExternalRequestIndex I P0 Rects)
    (i : Option ((family).Child r)) (s : ZFSet.{u}) :
    ((vcode r i = natSetCode 1 ∧ s = ZFSet.pair (externalRequestIndexCode r) (natSetCode 0)) ∨
      (vcode r i = natSetCode 2 ∧ s = ZFSet.pair (externalRequestIndexCode r) (natSetCode 1))) ↔
      ∃ child : (family).Child r, i = some child ∧ s = (letters).encode ⟨r, child⟩ := by
  rcases r with task | (point | rect)
  · rcases i with _ | ⟨⟨⟨⟩⟩⟩
    · simp [externalFamilyVertexCode_root, natSetCode_injective.eq_iff]
    · constructor
      · rintro (⟨_, equal⟩ | ⟨equal, _⟩)
        · exact ⟨⟨()⟩, rfl, equal⟩
        · have bad : (1 : Nat) = 2 := natSetCode_injective equal
          omega
      · rintro ⟨⟨⟨⟩⟩, _, equal⟩
        exact Or.inl ⟨rfl, equal⟩
  · rcases i with _ | ⟨⟨⟨⟩⟩⟩
    · simp [externalFamilyVertexCode_root, natSetCode_injective.eq_iff]
    · constructor
      · rintro (⟨_, equal⟩ | ⟨equal, _⟩)
        · exact ⟨⟨()⟩, rfl, equal⟩
        · have bad : (1 : Nat) = 2 := natSetCode_injective equal
          omega
      · rintro ⟨⟨⟨⟩⟩, _, equal⟩
        exact Or.inl ⟨rfl, equal⟩
  · rcases i with _ | ⟨⟨b⟩⟩
    · simp [externalFamilyVertexCode_root, natSetCode_injective.eq_iff]
    · cases b
      · constructor
        · rintro (⟨_, equal⟩ | ⟨equal, _⟩)
          · exact ⟨⟨false⟩, rfl, equal⟩
          · have bad : (1 : Nat) = 2 := natSetCode_injective equal
            omega
        · rintro ⟨child, equal, code⟩
          have same := Option.some.inj equal
          subst child
          exact Or.inl ⟨rfl, code⟩
      · constructor
        · rintro (⟨equal, _⟩ | ⟨_, equal⟩)
          · have bad : (2 : Nat) = 1 := natSetCode_injective equal
            omega
          · exact ⟨⟨true⟩, rfl, equal⟩
        · rintro ⟨child, equal, code⟩
          have same := Option.some.inj equal
          subst child
          exact Or.inr ⟨rfl, code⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hG : G ∈ M.sets)
variable (hLetters : externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0) ∈ M.sets)
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction compression
  pairing unions powers separation infinite hG hLetters
include pairing unions powers separation infinite hG hLetters

theorem externalFlatVertexWordCode_iff (r : ExternalRequestIndex I P0 Rects)
    (i : Option ((family).Child r)) :
    letI := group.toGroup
    ∀ w v : External (SetMembers G) (family).Letters,
    ExternalFlatVertexWordCode E S (M.externalChildGenerators G S m one)
      (M.externalGroupMultiplication G S m one) (natSetCode 0) (natSetCode 1) (natSetCode 2)
      (externalRequestIndexCode r) (vcode r i) ((sGroup).encode w) ((sGroup).encode v) ↔
        v = (family).flatWord w r i := by
  let := group.toGroup
  intro w v
  have carrier := completion.externalFamilyGroupPresentation_carrier group oldAction compression
    pairing unions powers separation infinite hG hLetters
  have generators := completion.externalFamilyGroupPresentation_generators group oldAction compression
    pairing unions powers separation infinite hG hLetters
  have multiplication := completion.externalFamilyGroupPresentation_multiplication group oldAction compression
    pairing unions powers separation infinite hG hLetters
  constructor
  · rintro (⟨root, equal⟩ | ⟨letter, _, k, hk, childFields, gen, mul⟩)
    · have vertex : i = none := completion.externalFamilyVertexCode_injective group oldAction compression r root
      subst i
      exact (sGroup).injective equal
    · obtain ⟨child, rfl, rfl⟩ := (completion.externalFamily_vertex_letter group oldAction compression r i letter).1 childFields
      obtain ⟨g, rfl⟩ := ((sGroup).mem_carrier k).1 (carrier.symm ▸ hk)
      rw [generators] at gen
      have generatorEq := ((letters).pair_mem_graph (sGroup) _ ⟨r, child⟩ g).1 gen
      rw [multiplication] at mul
      have product := (((sGroup).product (sGroup)).pair_mem_graph (sGroup) (fun p => p.1 * p.2) (w, g) v).1 mul
      exact product.symm.trans (congrArg (fun g => w * g) generatorEq.symm)
  · intro equal
    subst v
    cases i with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some child =>
      let g := generator (SetMembers G) (family).Letters ⟨r, child⟩
      refine Or.inr ⟨(letters).encode ⟨r, child⟩, (letters).encode_mem ⟨r, child⟩,
        (sGroup).encode g, carrier ▸ (sGroup).encode_mem g,
        (completion.externalFamily_vertex_letter group oldAction compression r (some child) _).2 ⟨child, rfl, rfl⟩, ?_, ?_⟩
      · rw [generators]
        exact ((letters).pair_mem_graph (sGroup) _ ⟨r, child⟩ g).2 rfl
      · rw [multiplication]
        exact (((sGroup).product (sGroup)).pair_mem_graph (sGroup) (fun p => p.1 * p.2) (w, g) (w * g)).2 rfl

theorem externalPlacements_entry_iff :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters)
      (v : Sigma fun r : ExternalRequestIndex I P0 Rects => Option ((family).Child r) × SetMembers U)
      (z : External (SetMembers G) (family).Letters × SetMembers U),
    ZFSet.pair (ZFSet.pair ((sGroup).encode w) ((vertices).encode v))
      (((sGroup).product (SetMembers.presentation U)).encode z) ∈ completion.externalPlacements P0 r0 μ0 A0 ↔
        z = ((family).flatWord w v.1 v.2.1, v.2.2) := by
  let := group.toGroup
  intro w v z
  rcases v with ⟨r, i, x⟩
  have carrier := completion.externalFamilyGroupPresentation_carrier group oldAction compression
    pairing unions powers separation infinite hG hLetters
  constructor
  · intro entry
    obtain ⟨_, _, _, q, _, j, _, y, _, k, _, left, right, word⟩ :=
      (triple_mem_externalFlatPlacements _ _ _ _ _ _ _ _ _ _).1 entry
    obtain ⟨leftPair, rfl⟩ := ZFSet.pair_inj.1 left
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 leftPair
    obtain ⟨rfl, point⟩ := ZFSet.pair_inj.1 right
    exact Prod.ext
      ((completion.externalFlatVertexWordCode_iff group oldAction compression
        pairing unions powers separation infinite hG hLetters r i w z.1).1 word)
      (SetMembers.raw_injective U point)
  · intro equal
    subst z
    apply (triple_mem_externalFlatPlacements _ _ _ _ _ _ _ _ _ _).2
    refine ⟨carrier ▸ (sGroup).encode_mem w, (vertices).encode_mem ⟨r, i, x⟩,
      ZFSet.pair_mem_prod.2 ⟨carrier ▸ (sGroup).encode_mem _, SetMembers.raw_mem x⟩,
      externalRequestIndexCode r, (externalRequestPresentation I P0 Rects).encode_mem r,
      vcode r i, completion.externalFamilyVertexCode_mem_tags group oldAction compression r i,
      SetMembers.raw x, SetMembers.raw_mem x,
      (sGroup).encode ((family).flatWord w r i), carrier ▸ (sGroup).encode_mem _, rfl, rfl, ?_⟩
    exact (completion.externalFlatVertexWordCode_iff group oldAction compression
      pairing unions powers separation infinite hG hLetters r i w _).2 rfl

end PartitionPilot.Forcing.GroundCompressionCompletion



namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hG : G ∈ M.sets)
variable (hLetters : externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0) ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction compression
local notation "U" => completion.algebra.union.fields 0
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction compression
  pairing unions powers separation infinite hG hLetters

include pairing unions powers separation infinite hG hLetters in
theorem externalFlatSteps_iff :
    letI := group.toGroup
    let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
    ∀ x y : (family).FlatLabel (J := SetMembers G),
    ZFSet.pair (((sGroup).product (SetMembers.presentation U)).encode x)
      (((sGroup).product (SetMembers.presentation U)).encode y) ∈ completion.externalFlatSteps P0 r0 μ0 A0 ↔
      (family).FlatStep a x y := by
  let := group.toGroup
  dsimp only
  let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
  let s := sGroup
  let t := SetMembers.presentation U
  let g := SetMembers.presentation G
  let v := completion.externalFamilyTileVertexPresentation group oldAction compression
  have carrier := completion.externalFamilyGroupPresentation_carrier group oldAction compression
    pairing unions powers separation infinite hG hLetters
  have oldEntries : ∀ j w, ZFSet.pair (g.encode j) (s.encode w) ∈ M.externalOldInclusion G
      (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one ↔
      old (SetMembers G) (family).Letters j = w := by
    intro j w
    rw [completion.externalFamilyGroupPresentation_old group oldAction compression
      pairing unions powers separation infinite hG hLetters]
    exact g.pair_mem_graph s _ j w
  have mulEntries : ∀ w k l, ZFSet.pair (ZFSet.pair (s.encode w) (s.encode k)) (s.encode l) ∈
      M.externalGroupMultiplication G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one ↔
      w * k = l := by
    intro w k l
    rw [completion.externalFamilyGroupPresentation_multiplication group oldAction compression
      pairing unions powers separation infinite hG hLetters]
    exact (s.product s).pair_mem_graph s _ (w, k) l
  have actEntries : ∀ j x y, ZFSet.pair (ZFSet.pair (g.encode j) (t.encode x)) (t.encode y) ∈
      completion.algebra.union.fields 12 ↔ (a.iso j).toFun x = y :=
    fun j x y => (completion.algebra.union.action.toOrderAction_eq_iff group completion.algebra.union.meet j x y).symm
  intro x y
  have result := pair_mem_externalFlatStepGraph_iff (family) a s t g v oldEntries mulEntries actEntries
    (completion.externalPlacements_entry_iff group oldAction compression pairing unions powers separation infinite hG hLetters)
    (completion.externalOverlaps_same_request group oldAction compression)
    (completion.externalOverlaps_entry_iff group oldAction compression) x y
  change ZFSet.pair ((s.product t).encode x) ((s.product t).encode y) ∈
    externalFlatStepGraph s.carrier U G (completion.externalVertices P0 r0 μ0 A0) _ _ _ _ _ ↔ _ at result
  rw [carrier] at result
  exact result

end PartitionPilot.Forcing.GroundCompressionCompletion

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalColumnCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps
universe u

structure GroundExternalColumnData (M : TransitiveGround.{u}) (C K : ZFSet.{u}) where
  base : ZFSet.{u}
  sequence : ZFSet.{u}
  cap : ZFSet.{u}
  sequence_ground : sequence ∈ M.sets
  code : ExternalColumnCode C K base sequence cap
  range_ground : relationImage ZFSet.omega C sequence ∈ M.sets
  inverse_ground : relationConverse ZFSet.omega C sequence ∈ M.sets
  inverse_code : InjectionCode (relationImage ZFSet.omega C sequence) ZFSet.omega
    (relationConverse ZFSet.omega C sequence)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalFamilySlotCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization Compression.RecursiveMaps.TileRequests
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))

theorem externalFamilyVertexCode_eq_slot
    (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0))
    (i : Option ((completion.externalFamily group oldAction compression).Child r)) :
    completion.externalFamilyVertexCode group oldAction compression r i =
      natSetCode (((completion.externalFamily group oldAction compression).request r).vertexSlot i) := by
  cases r with
  | inl r => cases i <;> rfl
  | inr r =>
    cases r with
    | inl r => cases i <;> rfl
    | inr r =>
      cases i with
      | none => rfl
      | some b => cases b with | up b => cases b <;> rfl

end PartitionPilot.Forcing.GroundCompressionCompletion

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalLocalHeightSelection
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
universe u
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalPointMeet (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  canonicalMeetGraph (completion.externalPointCarrier P r μ A) (completion.externalPointOrder P r μ A)

end GroundCompressionCompletion

structure GroundExternalGeometryData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P r μ A : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ) : Prop where
  carrier_ground : completion.externalPointCarrier P r μ A ∈ M.sets
  classifier_ground : completion.externalPointClassifier P r μ A ∈ M.sets
  order_ground : completion.externalPointOrder P r μ A ∈ M.sets
  meet_ground : completion.externalPointMeet P r μ A ∈ M.sets
  action_ground : completion.externalPointAction P r μ A ∈ M.sets
  meet : MeetOrderCode (completion.externalPointCarrier P r μ A)
    (completion.externalPointOrder P r μ A) (completion.externalPointMeet P r μ A)
  action : PosetActionCode
    (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (completion.externalPointCarrier P r μ A)
    (M.externalGroupMultiplication G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (completion.externalPointOrder P r μ A) (completion.externalPointAction P r μ A)
  copies_ground : ∀ w ∈ M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one,
    completion.externalCopyGraph P r μ A w ∈ M.sets
  copies : ∀ w ∈ M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one,
    MeetEmbeddingCode (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
      (completion.algebra.union.fields 1) (completion.externalPointOrder P r μ A)
      (completion.algebra.union.fields 2) (completion.externalPointMeet P r μ A)
      (completion.externalCopyGraph P r μ A w)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "U" => completion.algebra.union.fields 0
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground

noncomputable def externalPointPresentation :
    letI := group.toGroup
    Presentation ((family).Node (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet)) := by
  letI := group.toGroup
  have hE : (sGroup).carrier ∈ M.sets := by
    rw [completion.externalFamilyGroupPresentation_carrier]
    exact data.group.carrier_mem
  exact M.flatCopyPresentation pairing unions powers separation infinite (family)
    (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet)
    (sGroup) (SetMembers.presentation U)
    (completion.externalFlatSteps_iff group oldAction data.original pairing unions powers separation infinite
      hG data.words.letters_ground) hE (completion.algebra.union.ground 0)

theorem externalPointPresentation_carrier :
    letI := group.toGroup
    (data.externalPointPresentation group oldAction pairing unions powers separation infinite hG).carrier =
      completion.externalPointCarrier P0 r0 μ0 A0 := by
  let := group.toGroup
  change equivalenceClasses (ZFSet.prod (sGroup).carrier U)
    (M.finitePathClosure (ZFSet.prod (sGroup).carrier U) (completion.externalFlatSteps P0 r0 μ0 A0)) = _
  rw [completion.externalFamilyGroupPresentation_carrier]
  rfl

theorem externalPointClassifier_entry_iff :
    letI := group.toGroup
    let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
    let q := data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
    ∀ (w : External (SetMembers G) (family).Letters) (x : SetMembers U) (z : (family).Node a),
      ZFSet.pair (ZFSet.pair ((sGroup).encode w) (SetMembers.raw x)) (q.encode z) ∈
        completion.externalPointClassifier P0 r0 μ0 A0 ↔ ((family).copy a w).toFun x = z := by
  let := group.toGroup
  dsimp only
  have hE : (sGroup).carrier ∈ M.sets := by
    rw [completion.externalFamilyGroupPresentation_carrier]
    exact data.group.carrier_mem
  have entries := M.flatCopyClassifier_entry_iff pairing unions powers separation infinite (family)
    (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet)
    (sGroup) (SetMembers.presentation U)
    (completion.externalFlatSteps_iff group oldAction data.original pairing unions powers separation infinite
      hG data.words.letters_ground) hE (completion.algebra.union.ground 0)
  intro w x z
  have entry := entries w x z
  change ZFSet.pair (ZFSet.pair ((sGroup).encode w) (SetMembers.raw x))
    ((data.externalPointPresentation group oldAction pairing unions powers separation infinite hG).encode z) ∈
    equivalenceClassifier (ZFSet.prod (sGroup).carrier U)
      (M.finitePathClosure (ZFSet.prod (sGroup).carrier U) (completion.externalFlatSteps P0 r0 μ0 A0)) ↔ _ at entry
  rw [completion.externalFamilyGroupPresentation_carrier] at entry
  exact entry

theorem externalGeometry_entries :
    letI := group.toGroup
    let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
    let q := data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
    (∀ x y, ZFSet.pair (q.encode x) (q.encode y) ∈ completion.externalPointOrder P0 r0 μ0 A0 ↔
      ((family).gluedOrder a).le x y) ∧
    (∀ x y z, ZFSet.pair (ZFSet.pair (q.encode x) (q.encode y)) (q.encode z) ∈
      completion.externalPointMeet P0 r0 μ0 A0 ↔ ((family).gluedOrder a).meet x y = z) ∧
    (∀ w x y, ZFSet.pair (ZFSet.pair ((sGroup).encode w) (q.encode x)) (q.encode y) ∈
      completion.externalPointAction P0 r0 μ0 A0 ↔ (family).translate a w x = y) ∧
    (∀ w x y, ZFSet.pair (SetMembers.raw x) (q.encode y) ∈
      completion.externalCopyGraph P0 r0 μ0 A0 ((sGroup).encode w) ↔ ((family).copy a w).toFun x = y) := by
  let := group.toGroup
  dsimp only
  let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
  let q := data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
  let s := sGroup
  let t := SetMembers.presentation U
  have classed := data.externalPointClassifier_entry_iff group oldAction pairing unions powers separation infinite hG
  have sCarrier := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qCarrier := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have multiplication := completion.externalFamilyGroupPresentation_multiplication group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  change s.carrier = M.externalGroupCarrier G
    (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one at sCarrier
  change q.carrier = completion.externalPointCarrier P0 r0 μ0 A0 at qCarrier
  change M.externalGroupMultiplication G
    (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one =
      (s.product s).graph s (fun p => p.1 * p.2) at multiplication
  have tCarrier : t.carrier = U := rfl
  have related : ∀ x y, ZFSet.pair (t.encode x) (t.encode y) ∈ completion.algebra.union.fields 1 ↔
      completion.algebra.union.meet.toSmallMeetOrder.le x y := fun _ _ => Iff.rfl
  have order := flatCopy_order_iff (family) a s t q classed related
  have meet := q.canonicalMeetGraph_iff ((family).gluedOrder a) order
  have action := flatCopy_action_iff (family) a s t q classed
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [sCarrier, tCarrier, qCarrier, GroundCompressionCompletion.externalPointOrder] using order
  · simpa only [sCarrier, tCarrier, qCarrier, GroundCompressionCompletion.externalPointOrder,
      GroundCompressionCompletion.externalPointMeet] using meet
  · simpa only [sCarrier, tCarrier, qCarrier, ← multiplication,
      GroundCompressionCompletion.externalPointAction] using action
  · intro w x y
    change ZFSet.pair (t.encode x) (q.encode y) ∈ flatCopyEmbeddingGraph U
      (completion.externalPointCarrier P0 r0 μ0 A0) (completion.externalPointClassifier P0 r0 μ0 A0) (s.encode w) ↔ _
    rw [pair_mem_flatCopyEmbeddingGraph]
    exact ⟨fun entry => (classed w x y).1 entry.2.2,
      fun equal => ⟨SetMembers.raw_mem x, qCarrier ▸ q.encode_mem y, (classed w x y).2 equal⟩⟩

include data group oldAction pairing unions powers separation infinite hG in
theorem externalGeometryData (hP : P0 ∈ M.sets) :
    GroundExternalGeometryData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 completion := by
  let := group.toGroup
  let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
  let s := sGroup
  let t := SetMembers.presentation U
  let q := data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
  have classed := data.externalPointClassifier_entry_iff group oldAction pairing unions powers separation infinite hG
  have sCarrier := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qCarrier := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have multiplication := completion.externalFamilyGroupPresentation_multiplication group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  change s.carrier = M.externalGroupCarrier G
    (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one at sCarrier
  change q.carrier = completion.externalPointCarrier P0 r0 μ0 A0 at qCarrier
  change M.externalGroupMultiplication G
    (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one =
      (s.product s).graph s (fun p => p.1 * p.2) at multiplication
  have tCarrier : t.carrier = U := rfl
  have identity := completion.externalFamilyGroupPresentation_identity group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  change M.externalGroupIdentity G
    (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one = s.encode 1 at identity
  have quot := data.point_quotient_ground pairing unions powers separation infinite hP hG
  have hQ := quot.2.2.1
  have hClassifier := quot.2.2.2.1
  have hOrder := M.flatCopyOrderGraph_mem pairing unions powers separation data.group.carrier_mem
    (completion.algebra.union.ground 0) hQ hClassifier (completion.algebra.union.ground 1)
  have related : ∀ x y, ZFSet.pair (t.encode x) (t.encode y) ∈ completion.algebra.union.fields 1 ↔
      completion.algebra.union.meet.toSmallMeetOrder.le x y := fun _ _ => Iff.rfl
  refine ⟨hQ, hClassifier, hOrder, M.canonicalMeetGraph_mem pairing unions powers separation hQ hOrder,
    M.flatCopyActionGraph_mem pairing unions powers separation data.group.carrier_mem
      (completion.algebra.union.ground 0) hQ hClassifier data.group.multiplication_mem, ?_, ?_, ?_, ?_⟩
  · have code := flatCopy_meetOrder (family) a s t q classed related
    simpa only [sCarrier, tCarrier, qCarrier, GroundCompressionCompletion.externalPointOrder,
      GroundCompressionCompletion.externalPointMeet] using code
  · have code := flatCopy_actionCode (family) a s t q classed related
    simpa only [sCarrier, tCarrier, qCarrier, ← multiplication, ← identity,
      GroundCompressionCompletion.externalPointOrder, GroundCompressionCompletion.externalPointAction] using code
  · intro w hw
    exact M.flatCopyEmbeddingGraph_mem pairing unions powers separation (completion.algebra.union.ground 0)
      hQ hClassifier (M.transitive data.group.carrier_mem hw)
  · intro w hw
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 (sCarrier.symm ▸ hw)
    have code := flatCopyEmbeddingGraph_code (family) a s t q classed related
      (fun x y z => (completion.algebra.union.meet.toSmallMeetOrder_meet_eq_iff x y z).symm) w
    simpa only [sCarrier, tCarrier, qCarrier, GroundCompressionCompletion.externalPointOrder,
      GroundCompressionCompletion.externalPointMeet, GroundCompressionCompletion.externalCopyGraph] using code

end PartitionPilot.Forcing.GroundExternalGeometryInputs



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (P r μ A : ZFSet.{u})
local notation "Requests" => externalRequestCarrier I P (externalRectangles P G r μ A)
local notation "Q" => completion.externalPointCarrier P r μ A

noncomputable def localTileCarrier (request : ZFSet.{u}) : ZFSet.{u} :=
  relationFiber Q (completion.localTilePoints P r μ A) request

noncomputable def localTileOrder (request : ZFSet.{u}) : ZFSet.{u} :=
  relationFiber (completion.externalPointOrder P r μ A)
    (indexedSuborderGraph Requests Q (completion.externalPointOrder P r μ A)
      (completion.localTilePoints P r μ A)) request

noncomputable def localTileMeet (request : ZFSet.{u}) : ZFSet.{u} :=
  relationFiber (completion.externalPointMeet P r μ A)
    (indexedSubmeetGraph Requests Q (completion.externalPointMeet P r μ A)
      (completion.localTilePoints P r μ A)) request

noncomputable def localTileCarriers : ZFSet.{u} :=
  M.relationFiberFamily Requests Q (completion.localTilePoints P r μ A)

noncomputable def localTileOrders : ZFSet.{u} :=
  M.relationFiberFamily Requests (completion.externalPointOrder P r μ A)
    (indexedSuborderGraph Requests Q (completion.externalPointOrder P r μ A)
      (completion.localTilePoints P r μ A))

noncomputable def localTileMeets : ZFSet.{u} :=
  M.relationFiberFamily Requests (completion.externalPointMeet P r μ A)
    (indexedSubmeetGraph Requests Q (completion.externalPointMeet P r μ A)
      (completion.localTilePoints P r μ A))

end GroundCompressionCompletion

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure GroundExternalLocalHeightData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ) where
  family : ZFSet.{u}
  family_ground : family ∈ M.sets
  function : ZFSet.IsFunc (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0))
    (M.groundRelations (completion.externalPointCarrier P0 r0 μ0 A0) D) family
  values : ∀ i h, ZFSet.pair i h ∈ family → h ∈ M.sets ∧
    IntervalHeightCode (completion.localTileCarrier P0 r0 μ0 A0 i)
      (completion.localTileOrder P0 r0 μ0 A0 i) D rD lo hi h ∧
    relationImage (completion.localTileCarrier P0 r0 μ0 A0 i) D h ∈ M.sets ∧
    M.groundEmbeddable (relationImage (completion.localTileCarrier P0 r0 μ0 A0 i) D h) ZFSet.omega

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalTileCoordinateRealization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundExternalLocalHeightData
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (heights : GroundExternalLocalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi completion)
noncomputable def coordinates : ZFSet.{u} :=
  transportedTileCoordinates
    (M.externalStarVertices G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0))
      (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)) m one)
    (M.externalGroupCarrier G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one)
    (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0))
    (completion.externalPointCarrier P0 r0 μ0 A0) D
    (completion.externalPointAction P0 r0 μ0 A0) heights.family

end PartitionPilot.Forcing.GroundExternalLocalHeightData

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundExternalStarSupports
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
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (P r μ A : ZFSet.{u})
local notation "letters" => externalChildLetters I P (externalRectangles P G r μ A)
local notation "requests" => externalRequestCarrier I P (externalRectangles P G r μ A)
local notation "Q" => completion.externalPointCarrier P r μ A
local notation "vertices" => M.externalStarVertices G letters requests m one

noncomputable def externalStarSupports : ZFSet.{u} :=
  externalStarSupportGraph vertices Q (M.externalGroupCarrier G letters m one)
    (completion.algebra.union.fields 0) (M.externalCosetCarrier G letters m one) requests
    (M.externalCosetClassifier G letters m one) (completion.externalPointClassifier P r μ A)
    (completion.localTilePoints P r μ A) (completion.externalPointAction P r μ A)
    (natSetCode 0) (natSetCode 1)

end GroundCompressionCompletion

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalStarOverlaps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u})
noncomputable def externalStarRoot (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair (natSetCode 0) (equivalenceClass (M.externalGroupCarrier G S m one)
    (M.externalCosetEquivalence G S m one) (M.externalGroupIdentity G S m one))
noncomputable def externalStarDepth (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  M.relationDepthGraph (M.externalStarVertices G S R m one) (M.externalStarAdjacency G S R m one)
    (M.externalStarRoot G S m one)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundExternalOldAction
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "U" => completion.algebra.union.fields 0
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "qPoint" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)

theorem externalCopyGraph_eq_graph :
    letI := group.toGroup
    let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
    ∀ w, completion.externalCopyGraph P0 r0 μ0 A0 ((sGroup).encode w) =
      (SetMembers.presentation U).graph (qPoint) ((family).copy a w).toFun := by
  let := group.toGroup
  dsimp only
  intro w
  have classed := data.externalPointClassifier_entry_iff group oldAction pairing unions powers separation infinite hG
  have graph := flatCopyEmbeddingGraph_eq_graph (family)
    (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet)
    (sGroup) (SetMembers.presentation U) (qPoint) classed w
  rw [data.externalPointPresentation_carrier] at graph
  exact graph

include data group oldAction pairing unions powers separation infinite hG in
theorem externalCopy_ideal {w : ZFSet.{u}} (hw : w ∈ M.externalGroupCarrier G letters m one) :
    IdealEmbeddingCode U (completion.externalPointCarrier P0 r0 μ0 A0)
      (completion.algebra.union.fields 1) (completion.externalPointOrder P0 r0 μ0 A0)
      (completion.algebra.union.fields 2) (completion.externalPointMeet P0 r0 μ0 A0)
      (completion.externalCopyGraph P0 r0 μ0 A0 w) := by
  let := group.toGroup
  let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
  let s := sGroup
  let q := qPoint
  have sCarrier := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 (sCarrier.symm ▸ hw)
  have entries := data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG
  have code := (SetMembers.presentation U).idealEmbeddingCode q ((family).copy a w)
    (fun _ _ => Iff.rfl) entries.1
    (fun x y z => (completion.algebra.union.meet.toSmallMeetOrder_meet_eq_iff x y z).symm) entries.2.1
  rw [← data.externalCopyGraph_eq_graph group oldAction pairing unions powers separation infinite hG w] at code
  dsimp only [q] at code
  rw [data.externalPointPresentation_carrier] at code
  exact code

include data group oldAction pairing unions powers separation infinite hG in
theorem externalIdentityCopy_ideal :
    IdealEmbeddingCode U (completion.externalPointCarrier P0 r0 μ0 A0)
      (completion.algebra.union.fields 1) (completion.externalPointOrder P0 r0 μ0 A0)
      (completion.algebra.union.fields 2) (completion.externalPointMeet P0 r0 μ0 A0)
      (completion.externalCopyGraph P0 r0 μ0 A0 (M.externalGroupIdentity G letters m one)) :=
  data.externalCopy_ideal group oldAction pairing unions powers separation infinite hG
    data.group.group_code.identity_mem

end PartitionPilot.Forcing.GroundExternalGeometryInputs



namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "U" => completion.algebra.union.fields 0
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "qPoint" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "copyGraph" => completion.externalCopyGraph P0 r0 μ0 A0 (M.externalGroupIdentity G letters m one)

include data group oldAction pairing unions powers separation infinite hG in
theorem externalIdentityCopy_equivariant {g g' x y x' y' : ZFSet.{u}}
    (actor : ZFSet.pair g g' ∈ M.externalOldInclusion G letters m one)
    (first : ZFSet.pair x x' ∈ copyGraph) (second : ZFSet.pair y y' ∈ copyGraph)
    (acted : ZFSet.pair (ZFSet.pair g x) y ∈ completion.algebra.union.fields 12) :
    ZFSet.pair (ZFSet.pair g' x') y' ∈ completion.externalPointAction P0 r0 μ0 A0 := by
  let := group.toGroup
  let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
  rw [completion.externalFamilyGroupPresentation_old group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground] at actor
  obtain ⟨g, equal⟩ := ((SetMembers.presentation G).mem_graph (sGroup) _ _).1 actor
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  have identity := completion.externalFamilyGroupPresentation_identity group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  rw [identity, data.externalCopyGraph_eq_graph group oldAction pairing unions powers separation infinite hG 1] at first second
  obtain ⟨x, equal⟩ := ((SetMembers.presentation U).mem_graph (qPoint) _ _).1 first
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  obtain ⟨y, equal⟩ := ((SetMembers.presentation U).mem_graph (qPoint) _ _).1 second
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  have actionEq := (completion.algebra.union.action.toOrderAction_eq_iff group completion.algebra.union.meet g x y).2 acted
  have entries := data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG
  apply (entries.2.2.1 _ _ _).2
  change (((family).externalAction a).iso (old (SetMembers G) (family).Letters g)).toFun
    (((family).copy a 1).toFun x) = ((family).copy a 1).toFun y
  rw [(family).extends_old_action, actionEq]

include data group oldAction pairing unions powers separation infinite hG in
theorem externalIdentityCopy_agreement (hP : P0 ∈ M.sets)
    {g h g' h' v v' : ZFSet.{u}}
    (firstActor : ZFSet.pair g g' ∈ M.externalOldInclusion G letters m one)
    (secondActor : ZFSet.pair h h' ∈ M.externalOldInclusion G letters m one)
    (image : ZFSet.pair v v' ∈ copyGraph)
    (agree : ActionAgreementBelow U (completion.algebra.union.fields 1)
      (completion.algebra.union.fields 12) g h v) :
    ActionAgreementBelow (completion.externalPointCarrier P0 r0 μ0 A0)
      (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointAction P0 r0 μ0 A0) g' h' v' := by
  have ideal := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  have firstShape := ZFSet.pair_mem_prod.1 (data.old_inclusion_injection.function.1 firstActor)
  have secondShape := ZFSet.pair_mem_prod.1 (data.old_inclusion_injection.function.1 secondActor)
  exact ideal.actionAgreementBelow completion.algebra.union.action geometry.action
    firstShape.1 firstShape.2 secondShape.2 image agree
    (fun _ _ _ _ _ _ first second acted => data.externalIdentityCopy_equivariant group oldAction
      pairing unions powers separation infinite hG firstActor first second acted)
    (fun _ _ _ _ _ _ first second acted => data.externalIdentityCopy_equivariant group oldAction
      pairing unions powers separation infinite hG secondActor first second acted)

include data group oldAction pairing unions powers separation infinite hG in
theorem externalOriginal_agreement (hP : P0 ∈ M.sets)
    {g h g' h' v v' : ZFSet.{u}}
    (firstActor : ZFSet.pair g g' ∈ M.externalOldInclusion G letters m one)
    (secondActor : ZFSet.pair h h' ∈ M.externalOldInclusion G letters m one)
    (hv : v ∈ P0) (image : ZFSet.pair v v' ∈ copyGraph)
    (agree : ActionAgreementBelow P0 r0 A0 g h v) :
    ActionAgreementBelow (completion.externalPointCarrier P0 r0 μ0 A0)
      (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointAction P0 r0 μ0 A0) g' h' v' := by
  have hg := (ZFSet.pair_mem_prod.1 (data.old_inclusion_injection.function.1 firstActor)).1
  have hh := (ZFSet.pair_mem_prod.1 (data.old_inclusion_injection.function.1 secondActor)).1
  exact data.externalIdentityCopy_agreement group oldAction pairing unions powers separation infinite hG hP
    firstActor secondActor image (data.original.agreement g hg h hh v hv agree)

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_ExternalOwnerCoordinateLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (P r μ A : ZFSet.{u})
noncomputable def externalSeedCarrier : ZFSet.{u} :=
  relationImage (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
    (completion.externalIdentityCopyGraph P r μ A)
noncomputable def externalSeedHeight (C D seed : ZFSet.{u}) : ZFSet.{u} :=
  pushedHeightGraph (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
    (ZFSet.prod C D) (completion.externalIdentityCopyGraph P r μ A) seed

end GroundCompressionCompletion



namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
noncomputable def externalStarOwner (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  leastSupportGraph
    (M.externalStarVertices G (externalChildLetters I P (externalRectangles P G r μ A))
      (externalRequestCarrier I P (externalRectangles P G r μ A)) m one)
    (completion.externalPointCarrier P r μ A)
    (M.externalStarDepth G (externalChildLetters I P (externalRectangles P G r μ A))
      (externalRequestCarrier I P (externalRectangles P G r μ A)) m one)
    (completion.externalStarSupports P r μ A)

end GroundCompressionCompletion

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing
universe u
namespace GroundExternalLocalHeightData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (localHeights : GroundExternalLocalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 D rD lo hi completion)

noncomputable def externalHeightGraph (C seed columns : ZFSet.{u}) : ZFSet.{u} :=
  externalOwnerHeightGraph (completion.externalSeedCarrier P0 r0 μ0 A0)
    (completion.externalPointCarrier P0 r0 μ0 A0)
    (M.externalStarVertices G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0))
      (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)) m one) C D
    (completion.externalSeedHeight P0 r0 μ0 A0 C D seed)
    (completion.externalStarOwner P0 r0 μ0 A0)
    (M.externalStarDepth G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0))
      (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)) m one)
    columns localHeights.coordinates

end GroundExternalLocalHeightData

structure GroundExternalHeightData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ) where
  localHeights : GroundExternalLocalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi completion
  columns : GroundExternalColumnData M C (heightColumns (completion.externalSeedCarrier P0 r0 μ0 A0) C D
    (completion.externalSeedHeight P0 r0 μ0 A0 C D seed))
  height_ground : localHeights.externalHeightGraph C seed columns.sequence ∈ M.sets
  code : StrictLexHeightCode (completion.externalPointCarrier P0 r0 μ0 A0) C D
    (completion.externalPointOrder P0 r0 μ0 A0) (localHeights.externalHeightGraph C seed columns.sequence) rD
  range_ground : relationImage (completion.externalPointCarrier P0 r0 μ0 A0) (ZFSet.prod C D)
    (localHeights.externalHeightGraph C seed columns.sequence) ∈ M.sets
  range_countable : M.groundEmbeddable (relationImage (completion.externalPointCarrier P0 r0 μ0 A0) (ZFSet.prod C D)
    (localHeights.externalHeightGraph C seed columns.sequence)) ZFSet.omega
  preserves_seed : ∀ x y z, ZFSet.pair x y ∈ completion.externalIdentityCopyGraph P0 r0 μ0 A0 →
    (ZFSet.pair y z ∈ localHeights.externalHeightGraph C seed columns.sequence ↔ ZFSet.pair x z ∈ seed)
  below_cap : ∀ x a d, ZFSet.pair x (ZFSet.pair a d) ∈ localHeights.externalHeightGraph C seed columns.sequence →
    a ∈ columns.cap

namespace GroundExternalHeightData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
noncomputable def height (data : GroundExternalHeightData M initial I Sources Reps G m one T τ
    P0 r0 μ0 A0 C D rD lo hi seed completion) : ZFSet.{u} :=
  data.localHeights.externalHeightGraph C seed data.columns.sequence

end GroundExternalHeightData

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalTileSlotSupportRealization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundCompressionCompletion
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
noncomputable def externalTileSlotPoints (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  externalTileSlotSupports
    (M.externalStarVertices G (externalChildLetters I P (externalRectangles P G r μ A))
      (externalRequestCarrier I P (externalRectangles P G r μ A)) m one)
    (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (externalRequestCarrier I P (externalRectangles P G r μ A))
    (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
    (completion.externalPointAction P r μ A) (completion.localTileVertexImages P r μ A)

end PartitionPilot.Forcing.GroundCompressionCompletion

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFixedTopStep
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

namespace TransitiveGround

open SetFormula

theorem fixedTopAction_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G P A : ZFSet.{u}} (hG : G ∈ M.sets) (hP : P ∈ M.sets) (hA : A ∈ M.sets) :
    fixedTopAction G P A ∈ M.sets := by
  have singleton : ({P} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hP hP
  let params := extend G (extend P Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.fixedTopActionEntryFormula 0 1 2) params
    (Fin.cases hG (Fin.cases hP (fun i => Fin.elim0 i)))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hG singleton) singleton)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.fixedTopActionEntryFormula 0 1 2) (extend z params))
      (ZFSet.prod (ZFSet.prod G {P}) {P}) =
      ZFSet.sep (fun z => ∃ g ∈ G, z = ZFSet.pair (ZFSet.pair g P) P)
        (ZFSet.prod (ZFSet.prod G {P}) {P}) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_fixedTopActionEntryFormula 0 1 2 _)
  exact M.binary_union_mem pairing unions hA (equal ▸ selected)

end TransitiveGround

end

section
universe u

namespace IdealEmbeddingCode
variable {P Q rP rQ μP μQ e : ZFSet.{u}}
variable (code : IdealEmbeddingCode P Q rP rQ μP μQ e)
include code

theorem fixedTop (target : MeetOrderCode Q rQ μQ) :
    IdealEmbeddingCode P (fixedTopCarrier Q) rP (fixedTopOrder Q rQ) μP (fixedTopMeet Q rQ) e := by
  refine ⟨⟨⟨⟨?_, code.injection.function.2⟩, code.injection.injective⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro z entry
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (code.injection.function.1 entry)
    exact ZFSet.pair_mem_prod.2 ⟨hx, fixedTopCarrier_old hy⟩
  · intro x y x' y' lower first second
    exact fixedTopOrder_subset Q rQ (code.monotone x y x' y' lower first second)
  · intro x y z x' y' z' meet first second third
    exact fixedTopMeet_subset target (code.map_meet x y z x' y' z' meet first second third)
  · intro x y x' y' first second lower
    have hy' := (ZFSet.pair_mem_prod.1 (code.injection.function.1 second)).2
    exact code.reflect x y x' y' first second ((fixedTopOrder_old_iff hy').1 lower)
  · intro v v' z image _ lower
    have hv' := (ZFSet.pair_mem_prod.1 (code.injection.function.1 image)).2
    exact code.ideal v v' z image (fixedTopOrder_no_new_below target.order hv' lower)
      ((fixedTopOrder_old_iff hv').1 lower)

end IdealEmbeddingCode

end

open SetRealization
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPreparationFamilyImages
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundCompressionCompletion
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
noncomputable def externalOwnerSlots (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  leastSlotOwnerGraph (completion.externalSeedCarrier P r μ A)
    (completion.externalPointCarrier P r μ A)
    (M.externalStarVertices G (externalChildLetters I P (externalRectangles P G r μ A))
      (externalRequestCarrier I P (externalRectangles P G r μ A)) m one)
    (completion.externalStarOwner P r μ A) (completion.externalTileSlotPoints P r μ A)

end PartitionPilot.Forcing.GroundCompressionCompletion

end

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalOwnerDepth (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  let letters := externalChildLetters I P (externalRectangles P G r μ A)
  let requests := externalRequestCarrier I P (externalRectangles P G r μ A)
  relationCompose (completion.externalPointCarrier P r μ A)
    (M.externalStarVertices G letters requests m one) ZFSet.omega
    (completion.externalStarOwner P r μ A) (M.externalStarDepth G letters requests m one)

noncomputable def externalOwnerLevelPairs (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  pairedGraph (ownerFresh (completion.externalSeedCarrier P r μ A) (completion.externalPointCarrier P r μ A))
    ZFSet.omega (natSetCode 3) (completion.externalOwnerDepth P r μ A) (completion.externalOwnerSlots P r μ A)

noncomputable def externalOwnerLevels (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (ownerFresh (completion.externalSeedCarrier P r μ A) (completion.externalPointCarrier P r μ A))
    (ZFSet.prod ZFSet.omega (natSetCode 3)) ZFSet.omega
    (completion.externalOwnerLevelPairs P r μ A) depthSlotGraph
end GroundCompressionCompletion

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundExternalBirthLayers
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PartitionPilot.Forcing.GroundCompressionCompletion
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
noncomputable def externalSeedBirth (P r μ A times birth : ZFSet.{u}) : ZFSet.{u} :=
  pushedHeightGraph (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
    times (completion.externalIdentityCopyGraph P r μ A) birth

end PartitionPilot.Forcing.GroundCompressionCompletion

end


namespace PartitionPilot.Forcing
universe u
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
noncomputable def externalBirthGraph (P r μ A oldTimes oldBirth limit stamps : ZFSet.{u}) : ZFSet.{u} :=
  ownerBirthGraph (completion.externalSeedCarrier P r μ A) (completion.externalPointCarrier P r μ A)
    limit (completion.externalSeedBirth P r μ A oldTimes oldBirth)
    (completion.externalOwnerLevels P r μ A) stamps

end GroundCompressionCompletion

structure GroundExternalBirthData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P r μ A oldTimes oldBirth : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ) where
  stamps : ZFSet.{u}
  limit : ZFSet.{u}
  stamps_ground : stamps ∈ M.sets
  limit_ground : limit ∈ M.sets
  times : CompressionStampCode oldTimes stamps limit
  seed_function : ZFSet.IsFunc (completion.externalSeedCarrier P r μ A) oldTimes
    (completion.externalSeedBirth P r μ A oldTimes oldBirth)
  birth_ground : completion.externalBirthGraph P r μ A oldTimes oldBirth limit stamps ∈ M.sets
  function : ZFSet.IsFunc (completion.externalPointCarrier P r μ A) limit
    (completion.externalBirthGraph P r μ A oldTimes oldBirth limit stamps)
  old_meet : OldMeetCode (completion.externalPointOrder P r μ A) (completion.externalPointMeet P r μ A)
    (completion.externalBirthGraph P r μ A oldTimes oldBirth limit stamps)
  preserves_seed : ∀ x y t, ZFSet.pair x y ∈ completion.externalIdentityCopyGraph P r μ A →
    (ZFSet.pair y t ∈ completion.externalBirthGraph P r μ A oldTimes oldBirth limit stamps ↔
      ZFSet.pair x t ∈ oldBirth)

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P r μ A oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalBirthData M initial I Sources Reps G m one T τ P r μ A oldTimes oldBirth completion)
noncomputable def birth : ZFSet.{u} :=
  completion.externalBirthGraph P r μ A oldTimes oldBirth data.limit data.stamps

end GroundExternalBirthData

end PartitionPilot.Forcing




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBoundedExternalBirths
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalBoundedAction (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  fixedTopAction (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (completion.externalPointCarrier P r μ A) (completion.externalPointAction P r μ A)

end GroundCompressionCompletion

structure GroundExternalBoundedGeometryData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P r μ A : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ) : Prop where
  carrier_ground : completion.externalBoundedCarrier P r μ A ∈ M.sets
  order_ground : completion.externalBoundedOrder P r μ A ∈ M.sets
  meet_ground : completion.externalBoundedMeet P r μ A ∈ M.sets
  action_ground : completion.externalBoundedAction P r μ A ∈ M.sets
  meet : MeetOrderCode (completion.externalBoundedCarrier P r μ A)
    (completion.externalBoundedOrder P r μ A) (completion.externalBoundedMeet P r μ A)
  action : PosetActionCode
    (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (completion.externalBoundedCarrier P r μ A)
    (M.externalGroupMultiplication G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (completion.externalBoundedOrder P r μ A) (completion.externalBoundedAction P r μ A)
  copies_ground : ∀ w ∈ M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one,
    completion.externalCopyGraph P r μ A w ∈ M.sets
  copies : ∀ w ∈ M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one,
    IdealEmbeddingCode (completion.algebra.union.fields 0) (completion.externalBoundedCarrier P r μ A)
      (completion.algebra.union.fields 1) (completion.externalBoundedOrder P r μ A)
      (completion.algebra.union.fields 2) (completion.externalBoundedMeet P r μ A)
      (completion.externalCopyGraph P r μ A w)
  top_mem : completion.externalPointCarrier P r μ A ∈ completion.externalBoundedCarrier P r μ A
  greatest : ∀ x ∈ completion.externalBoundedCarrier P r μ A,
    ZFSet.pair x (completion.externalPointCarrier P r μ A) ∈ completion.externalBoundedOrder P r μ A
  strict_top : ∀ x ∈ completion.externalPointCarrier P r μ A,
    ZFSet.pair (completion.externalPointCarrier P r μ A) x ∉ completion.externalBoundedOrder P r μ A
  fixes_top : ∀ g ∈ M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one,
    ZFSet.pair (ZFSet.pair g (completion.externalPointCarrier P r μ A))
      (completion.externalPointCarrier P r μ A) ∈ completion.externalBoundedAction P r μ A

end

namespace GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P0 ∈ M.sets)
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "copyGraph" => completion.externalCopyGraph P0 r0 μ0 A0 (M.externalGroupIdentity G letters m one)
include data group oldAction pairing unions powers separation infinite hG hP

theorem externalBoundedGeometryData :
    GroundExternalBoundedGeometryData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 completion := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  exact ⟨M.fixedTopCarrier_mem pairing unions geometry.carrier_ground,
    M.fixedTopOrder_mem pairing unions powers separation geometry.carrier_ground geometry.order_ground,
    M.fixedTopMeet_mem pairing unions powers separation geometry.carrier_ground geometry.order_ground,
    M.fixedTopAction_mem pairing unions powers separation data.group.carrier_mem
      geometry.carrier_ground geometry.action_ground,
    fixedTopMeet_code geometry.meet, geometry.action.fixedTop geometry.meet.order data.group.group_code.identity_mem,
    geometry.copies_ground,
    fun _ hw => (data.externalCopy_ideal group oldAction pairing unions powers separation infinite hG hw).fixedTop geometry.meet,
    fixedTopCarrier_top _, fun _ hx => fixedTopOrder_greatest hx,
    fun _ hx => (fixedTopOrder_strict_top geometry.meet.order hx).2,
    fun _ hg => fixedTopAction_fixes_top hg⟩

theorem externalBoundedCopy_bottom {w b b' : ZFSet.{u}}
    (hw : w ∈ M.externalGroupCarrier G letters m one)
    (least : ∀ x ∈ completion.algebra.union.fields 0, ZFSet.pair b x ∈ completion.algebra.union.fields 1)
    (image : ZFSet.pair b b' ∈ completion.externalCopyGraph P0 r0 μ0 A0 w) :
    ∀ y ∈ completion.externalBoundedCarrier P0 r0 μ0 A0,
      ZFSet.pair b' y ∈ completion.externalBoundedOrder P0 r0 μ0 A0 := by
  have geometry := data.externalBoundedGeometryData group oldAction pairing unions powers separation infinite hG hP
  exact (geometry.copies w hw).preserves_bottom geometry.meet least image

theorem externalBoundedOriginal_agreement {g h g' h' v v' : ZFSet.{u}}
    (firstActor : ZFSet.pair g g' ∈ M.externalOldInclusion G letters m one)
    (secondActor : ZFSet.pair h h' ∈ M.externalOldInclusion G letters m one)
    (hv : v ∈ P0) (image : ZFSet.pair v v' ∈ copyGraph)
    (agree : ActionAgreementBelow P0 r0 A0 g h v) :
    ActionAgreementBelow (completion.externalBoundedCarrier P0 r0 μ0 A0)
      (completion.externalBoundedOrder P0 r0 μ0 A0) (completion.externalBoundedAction P0 r0 μ0 A0) g' h' v' := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  have oldAgree := data.externalOriginal_agreement group oldAction pairing unions powers separation infinite hG hP
    firstActor secondActor hv image agree
  have hv' := (ZFSet.pair_mem_prod.1
    ((geometry.copies _ data.group.group_code.identity_mem).injection.function.1 image)).2
  exact oldAgree.fixedTop geometry.meet.order geometry.action hv'

end GroundExternalGeometryInputs

open SetFormula
universe u
namespace GroundExternalHeightData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)

noncomputable def boundedHeight : ZFSet.{u} :=
  fixedTopHeightGraph (completion.externalPointCarrier P0 r0 μ0 A0) heights.height heights.columns.cap lo

end GroundExternalHeightData

structure GroundBoundedExternalHeightData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
    (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed completion) : Prop where
  height_ground : heights.boundedHeight ∈ M.sets
  code : StrictLexHeightCode (completion.externalBoundedCarrier P0 r0 μ0 A0) C D
    (completion.externalBoundedOrder P0 r0 μ0 A0) heights.boundedHeight rD
  old_entries : ∀ x ∈ completion.externalPointCarrier P0 r0 μ0 A0, ∀ y,
    ZFSet.pair x y ∈ heights.boundedHeight ↔ ZFSet.pair x y ∈ heights.height
  top_entries : ∀ y, ZFSet.pair (completion.externalPointCarrier P0 r0 μ0 A0) y ∈ heights.boundedHeight ↔
    y = ZFSet.pair heights.columns.cap lo
  range_eq : relationImage (completion.externalBoundedCarrier P0 r0 μ0 A0) (ZFSet.prod C D) heights.boundedHeight =
    insert (ZFSet.pair heights.columns.cap lo)
      (relationImage (completion.externalPointCarrier P0 r0 μ0 A0) (ZFSet.prod C D) heights.height)
  range_ground : relationImage (completion.externalBoundedCarrier P0 r0 μ0 A0) (ZFSet.prod C D) heights.boundedHeight ∈ M.sets
  range_countable : M.groundEmbeddable
    (relationImage (completion.externalBoundedCarrier P0 r0 μ0 A0) (ZFSet.prod C D) heights.boundedHeight) ZFSet.omega
  preserves_seed : ∀ x y z, ZFSet.pair x y ∈ completion.externalIdentityCopyGraph P0 r0 μ0 A0 →
    (ZFSet.pair y z ∈ heights.boundedHeight ↔ ZFSet.pair x z ∈ seed)
  weak_bound : ∀ x y, ZFSet.pair x y ∈ heights.boundedHeight →
    y = ZFSet.pair heights.columns.cap lo ∨ ZFSet.pair y (ZFSet.pair heights.columns.cap lo) ∈ lexHeightOrder C D rD

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)

noncomputable def boundedBirth : ZFSet.{u} :=
  fixedTopBirth (completion.externalPointCarrier P0 r0 μ0 A0) births.birth births.limit

end GroundExternalBirthData

structure GroundBoundedExternalBirthData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
    (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 oldTimes oldBirth completion) : Prop where
  times_ground : insert births.limit births.limit ∈ M.sets
  birth_ground : births.boundedBirth ∈ M.sets
  function : ZFSet.IsFunc (completion.externalBoundedCarrier P0 r0 μ0 A0)
    (insert births.limit births.limit) births.boundedBirth
  old_meet : OldMeetCode (completion.externalBoundedOrder P0 r0 μ0 A0)
    (completion.externalBoundedMeet P0 r0 μ0 A0) births.boundedBirth
  old_entries : ∀ x ∈ completion.externalPointCarrier P0 r0 μ0 A0, ∀ t,
    ZFSet.pair x t ∈ births.boundedBirth ↔ ZFSet.pair x t ∈ births.birth
  top_entries : ∀ t, ZFSet.pair (completion.externalPointCarrier P0 r0 μ0 A0) t ∈ births.boundedBirth ↔
    t = births.limit
  new_fiber : ∀ x, ZFSet.pair x births.limit ∈ births.boundedBirth ↔
    x = completion.externalPointCarrier P0 r0 μ0 A0
  birth_bound : ∀ x t, ZFSet.pair x t ∈ births.boundedBirth → t ∈ births.limit ∨ t = births.limit
  preserves_seed : ∀ x y t, ZFSet.pair x y ∈ completion.externalIdentityCopyGraph P0 r0 μ0 A0 →
    (ZFSet.pair y t ∈ births.boundedBirth ↔ ZFSet.pair x t ∈ oldBirth)
  new_fiber_ground : ({completion.externalPointCarrier P0 r0 μ0 A0} : ZFSet.{u}) ∈ M.sets
  new_fiber_countable : M.groundEmbeddable {completion.externalPointCarrier P0 r0 μ0 A0} ZFSet.omega

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainTransitionLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundMainTransition
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def identity (stage : GroundMainStage M C D rD) : GroundMainTransition stage stage where
  points := identityFunctionGraph stage.carrier
  actors := identityFunctionGraph stage.actors
  points_ground := M.identityFunctionGraph_mem pairing unions powers separation stage.carrier_ground
  actors_ground := M.identityFunctionGraph_mem pairing unions powers separation stage.actors_ground
  point_embedding := by
    refine ⟨identityFunctionGraph_injection _, ?_, ?_⟩
    · intro x y x' y' lower first second
      obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 first
      obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 second
      exact lower
    · intro x y z x' y' z' meet first second third
      obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 first
      obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 second
      obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 third
      exact meet
  order_iff := by
    intro x y x' y' first second
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 first
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 second
    exact Iff.rfl
  group_embedding := GroupEmbeddingCode.identity stage.group_code
  equivariant := by
    intro g g' x y x' y' actor first second acted
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 actor
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 first
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 second
    exact acted
  bottom := (pair_mem_identityFunctionGraph _ _ _).2 ⟨rfl, stage.bottom_mem⟩
  height := by
    intro x y z entry
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 entry
    exact Iff.rfl
  agreement := by
    intro g h g' h' v v' first second image agree
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 first
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 second
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 image
    exact agree

noncomputable def comp {source middle target : GroundMainStage M C D rD}
    (first : GroundMainTransition source middle) (second : GroundMainTransition middle target) :
    GroundMainTransition source target where
  points := relationCompose source.carrier middle.carrier target.carrier first.points second.points
  actors := relationCompose source.actors middle.actors target.actors first.actors second.actors
  points_ground := M.relationCompose_mem pairing unions powers separation source.carrier_ground
    middle.carrier_ground target.carrier_ground first.points_ground second.points_ground
  actors_ground := M.relationCompose_mem pairing unions powers separation source.actors_ground
    middle.actors_ground target.actors_ground first.actors_ground second.actors_ground
  point_embedding := first.point_embedding.compose second.point_embedding
  order_iff := by
    intro x y x' y' xx yy
    obtain ⟨_, _, a, _, xa, ax⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 xx
    obtain ⟨_, _, b, _, yb, by'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 yy
    exact (second.order_iff a b x' y' ax by').trans (first.order_iff x y a b xa yb)
  group_embedding := first.group_embedding.compose second.group_embedding
  equivariant := by
    intro g g' x y x' y' actor xx yy acted
    obtain ⟨_, _, a, _, ga, ag⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 actor
    obtain ⟨_, _, b, _, xb, bx⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 xx
    obtain ⟨_, _, c, _, yc, cy⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 yy
    exact second.equivariant a g' b c x' y' ag bx cy (first.equivariant g a x y b c ga xb yc acted)
  bottom := (pair_mem_relationCompose _ _ _ _ _ _ _).2
    ⟨source.bottom_mem, target.bottom_mem, middle.bottom, middle.bottom_mem, first.bottom, second.bottom⟩
  height := by
    intro x y z entry
    obtain ⟨_, _, a, _, xa, ay⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    exact (second.height a y z ay).trans (first.height x a z xa)
  agreement := by
    intro g h g' h' v v' gg hh vv agree
    obtain ⟨_, _, a, _, ga, ag⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 gg
    obtain ⟨_, _, b, _, hb, bh⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 hh
    obtain ⟨_, _, w, _, vw, wv⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 vv
    exact second.agreement a b g' h' w v' ag bh wv (first.agreement g h a b v w ga hb vw agree)

end PartitionPilot.Forcing.GroundMainTransition

namespace PartitionPilot.Forcing.GroundMainTransition
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

@[simp] theorem identity_comp {source target : GroundMainStage M C D rD}
    (f : GroundMainTransition source target) :
    comp pairing unions powers separation (identity pairing unions powers separation source) f = f := by
  apply ext
  · exact relationCompose_identity_left f.point_embedding.injection.function.1
  · exact relationCompose_identity_left f.group_embedding.injection.function.1

@[simp] theorem comp_identity {source target : GroundMainStage M C D rD}
    (f : GroundMainTransition source target) :
    comp pairing unions powers separation f (identity pairing unions powers separation target) = f := by
  apply ext
  · exact relationCompose_identity_right f.point_embedding.injection.function.1
  · exact relationCompose_identity_right f.group_embedding.injection.function.1

theorem comp_assoc {source first second target : GroundMainStage M C D rD}
    (f : GroundMainTransition source first) (g : GroundMainTransition first second)
    (h : GroundMainTransition second target) :
    comp pairing unions powers separation (comp pairing unions powers separation f g) h =
      comp pairing unions powers separation f (comp pairing unions powers separation g h) := by
  apply ext
  · exact relationCompose_assoc source.carrier first.carrier second.carrier target.carrier f.points g.points h.points
  · exact relationCompose_assoc source.actors first.actors second.actors target.actors f.actors g.actors h.actors

end PartitionPilot.Forcing.GroundMainTransition

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainTransitionValidity
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
namespace GroundMainTransition
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source target : GroundMainStage M C D rD}

theorem laws (transition : GroundMainTransition source target) :
    MainTransitionLaws source.carrier target.carrier source.order target.order source.meetGraph
      target.meetGraph source.actors target.actors source.multiplication target.multiplication
      source.identity target.identity source.action target.action source.bottom target.bottom
      source.height target.height transition.points transition.actors :=
  ⟨transition.point_embedding, transition.order_iff, transition.group_embedding,
    transition.equivariant, transition.bottom, transition.height, transition.agreement⟩

def ofLaws {points actors : ZFSet.{u}}
    (hPoints : points ∈ M.sets) (hActors : actors ∈ M.sets)
    (valid : MainTransitionLaws source.carrier target.carrier source.order target.order source.meetGraph
      target.meetGraph source.actors target.actors source.multiplication target.multiplication
      source.identity target.identity source.action target.action source.bottom target.bottom
      source.height target.height points actors) : GroundMainTransition source target where
  points := points
  actors := actors
  points_ground := hPoints
  actors_ground := hActors
  point_embedding := valid.point_embedding
  order_iff := valid.order_iff
  group_embedding := valid.group_embedding
  equivariant := valid.equivariant
  bottom := valid.bottom
  height := valid.height
  agreement := valid.agreement

end GroundMainTransition

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundTwoStageMainDiagram
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

structure GroundChronologicalMainStage (M : TransitiveGround.{u}) (C D rD : ZFSet.{u}) where
  stage : GroundMainStage M C D rD
  cutoff : ZFSet.{u}
  cutoff_ground : cutoff ∈ M.sets
  cutoff_ordinal : ordinalSetProperty cutoff
  history : GroundChronologicalHistory M (insert cutoff cutoff) C D rD
  carrier_eq : history.space cutoff = stage.carrier
  order_eq : history.order cutoff = stage.order
  meet_eq : history.meetGraph cutoff = stage.meetGraph
  height_eq : history.height cutoff = stage.height

namespace GroundChronologicalMainStage
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundChronologicalMainStage M C D rD)

def birth : ZFSet.{u} := stage.history.birth stage.cutoff

theorem birth_function : ZFSet.IsFunc stage.stage.carrier (insert stage.cutoff stage.cutoff) stage.birth := by
  rw [← stage.carrier_eq]
  exact stage.history.birth_function stage.cutoff (ZFSet.mem_insert _ _)

theorem birth_bound {x t : ZFSet.{u}} (entry : ZFSet.pair x t ∈ stage.birth) :
    t = stage.cutoff ∨ t ∈ stage.cutoff := by
  have hx := (ZFSet.pair_mem_prod.1 (stage.birth_function.1 entry)).1
  rw [← stage.carrier_eq] at hx
  exact stage.history.birth_bound stage.cutoff (ZFSet.mem_insert _ _) x hx t entry

theorem old_meet : OldMeetCode stage.stage.order stage.stage.meetGraph stage.birth := by
  rw [← stage.order_eq, ← stage.meet_eq]
  exact stage.history.old_meet stage.cutoff (ZFSet.mem_insert _ _)

end GroundChronologicalMainStage

structure GroundChronologicalMainTransition {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
    (source target : GroundChronologicalMainStage M C D rD) where
  map : GroundMainTransition source.stage target.stage
  cutoff_le : source.cutoff = target.cutoff ∨ source.cutoff ∈ target.cutoff
  birth : ∀ x y t, ZFSet.pair x y ∈ map.points →
    (ZFSet.pair y t ∈ target.birth ↔ ZFSet.pair x t ∈ source.birth)
  history_prefix : ∀ s, s = source.cutoff ∨ s ∈ source.cutoff →
    target.history.space s = source.history.space s ∧
    target.history.order s = source.history.order s ∧
    target.history.meetGraph s = source.history.meetGraph s ∧
    target.history.birth s = source.history.birth s ∧
    target.history.height s = source.history.height s

namespace GroundChronologicalMainTransition
open SetFormula
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

theorem prefix_bound {source target : GroundChronologicalMainStage M C D rD}
    (transition : GroundChronologicalMainTransition source target) {s : ZFSet.{u}}
    (before : s = source.cutoff ∨ s ∈ source.cutoff) : s = target.cutoff ∨ s ∈ target.cutoff := by
  rcases transition.cutoff_le with equal | lower
  · exact equal ▸ before
  · right
    rcases before with rfl | before
    · exact lower
    · exact target.cutoff_ordinal.1 source.cutoff lower s before

noncomputable def identity (stage : GroundChronologicalMainStage M C D rD) :
    GroundChronologicalMainTransition stage stage where
  map := GroundMainTransition.identity pairing unions powers separation stage.stage
  cutoff_le := Or.inl rfl
  birth := by
    intro x y t entry
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 entry
    exact Iff.rfl
  history_prefix := fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩

noncomputable def comp {source middle target : GroundChronologicalMainStage M C D rD}
    (first : GroundChronologicalMainTransition source middle)
    (second : GroundChronologicalMainTransition middle target) :
    GroundChronologicalMainTransition source target where
  map := first.map.comp pairing unions powers separation second.map
  cutoff_le := second.prefix_bound first.cutoff_le
  birth := by
    intro x y t entry
    obtain ⟨_, _, z, _, xz, zy⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    exact (second.birth z y t zy).trans (first.birth x z t xz)
  history_prefix := by
    intro s before
    have a := first.history_prefix s before
    have b := second.history_prefix s (first.prefix_bound before)
    exact ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1,
      b.2.2.2.1.trans a.2.2.2.1, b.2.2.2.2.trans a.2.2.2.2⟩

@[ext] theorem ext {source target : GroundChronologicalMainStage M C D rD}
    {first second : GroundChronologicalMainTransition source target} (same : first.map = second.map) :
    first = second := by
  cases first
  cases second
  cases same
  rfl

end GroundChronologicalMainTransition

end

namespace GroundChronologicalMainTransition
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source middle target : GroundChronologicalMainStage M C D rD}

def CoversOldBirths (transition : GroundChronologicalMainTransition source target) : Prop :=
  OldBirthFiberCoverageCode source.stage.carrier transition.map.points target.birth source.cutoff

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

theorem identity_coversOldBirths (stage : GroundChronologicalMainStage M C D rD) :
    (identity pairing unions powers separation stage).CoversOldBirths := by
  intro y t entry _
  have hy := (ZFSet.pair_mem_prod.1 (stage.birth_function.1 entry)).1
  exact ⟨y, hy, (pair_mem_identityFunctionGraph _ _ _).2 ⟨rfl, hy⟩⟩

theorem CoversOldBirths.comp
    {first : GroundChronologicalMainTransition source middle}
    {second : GroundChronologicalMainTransition middle target}
    (firstCoverage : first.CoversOldBirths) (secondCoverage : second.CoversOldBirths) :
    (first.comp pairing unions powers separation second).CoversOldBirths := by
  intro y t entry before
  have middleTime := first.prefix_bound before
  obtain ⟨z, hz, zy⟩ := secondCoverage y t entry middleTime
  have intermediate := (second.birth z y t zy).1 entry
  obtain ⟨x, hx, xz⟩ := firstCoverage z t intermediate before
  have hy := (ZFSet.pair_mem_prod.1 (target.birth_function.1 entry)).1
  exact ⟨x, hx, (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hx, hy, z, hz, xz, zy⟩⟩

end GroundChronologicalMainTransition

namespace GroundChronologicalMainTransition
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

@[simp] theorem identity_comp {source target : GroundChronologicalMainStage M C D rD}
    (f : GroundChronologicalMainTransition source target) :
    comp pairing unions powers separation (identity pairing unions powers separation source) f = f := by
  apply ext
  exact GroundMainTransition.identity_comp pairing unions powers separation f.map

@[simp] theorem comp_identity {source target : GroundChronologicalMainStage M C D rD}
    (f : GroundChronologicalMainTransition source target) :
    comp pairing unions powers separation f (identity pairing unions powers separation target) = f := by
  apply ext
  exact GroundMainTransition.comp_identity pairing unions powers separation f.map

theorem comp_assoc {source first second target : GroundChronologicalMainStage M C D rD}
    (f : GroundChronologicalMainTransition source first)
    (g : GroundChronologicalMainTransition first second)
    (h : GroundChronologicalMainTransition second target) :
    comp pairing unions powers separation (comp pairing unions powers separation f g) h =
      comp pairing unions powers separation f (comp pairing unions powers separation g h) := by
  apply ext
  exact GroundMainTransition.comp_assoc pairing unions powers separation f.map g.map h.map

end GroundChronologicalMainTransition

section
open SetFormula
universe u v

structure GroundChronologicalMainDiagram (M : TransitiveGround.{u}) (C D rD : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (I : Type v) [Preorder I] where
  stage : I → GroundChronologicalMainStage M C D rD
  transition : ∀ {i j}, i ≤ j → GroundChronologicalMainTransition (stage i) (stage j)
  self : ∀ i, transition (le_refl i) =
    GroundChronologicalMainTransition.identity pairing unions powers separation (stage i)
  comp : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k), transition (le_trans hij hjk) =
    (transition hij).comp pairing unions powers separation (transition hjk)

namespace GroundChronologicalMainDiagram
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Preorder I]

def CoversOldBirths (diagram : GroundChronologicalMainDiagram M C D rD pairing unions powers separation I) : Prop :=
  ∀ {i j} (before : i ≤ j), (diagram.transition before).CoversOldBirths

end GroundChronologicalMainDiagram

end

namespace GroundChronologicalMainDiagram
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {source target : GroundChronologicalMainStage M C D rD}
variable (step : GroundChronologicalMainTransition source target)

def twoStageStage (source target : GroundChronologicalMainStage M C D rD) :
    Fin 2 → GroundChronologicalMainStage M C D rD :=
  Fin.cases source (fun _ => target)

noncomputable def twoStageTransition : ∀ {i j : Fin 2}, i ≤ j →
    GroundChronologicalMainTransition (twoStageStage source target i) (twoStageStage source target j) := by
  intro i j before
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact GroundChronologicalMainTransition.identity pairing unions powers separation source
    | succ j => exact step
  | succ i =>
    cases j using Fin.cases with
    | zero => exact False.elim (Nat.not_succ_le_zero i.val before)
    | succ j => exact GroundChronologicalMainTransition.identity pairing unions powers separation target

theorem twoStageTransition_self (i : Fin 2) :
    twoStageTransition pairing unions powers separation step (le_refl i) =
      GroundChronologicalMainTransition.identity pairing unions powers separation (twoStageStage source target i) := by
  rcases twoStage_index_cases i with rfl | rfl <;> rfl

theorem twoStageTransition_comp {i j k : Fin 2} (hij : i ≤ j) (hjk : j ≤ k) :
    twoStageTransition pairing unions powers separation step (le_trans hij hjk) =
      (twoStageTransition pairing unions powers separation step hij).comp pairing unions powers separation
        (twoStageTransition pairing unions powers separation step hjk) := by
  rcases twoStage_index_cases i with rfl | rfl <;>
    rcases twoStage_index_cases j with rfl | rfl <;>
      rcases twoStage_index_cases k with rfl | rfl
  · exact (GroundChronologicalMainTransition.identity_comp pairing unions powers separation _).symm
  · exact (GroundChronologicalMainTransition.identity_comp pairing unions powers separation step).symm
  · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hjk)
  · exact (GroundChronologicalMainTransition.comp_identity pairing unions powers separation step).symm
  · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hij)
  · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hij)
  · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hjk)
  · exact (GroundChronologicalMainTransition.identity_comp pairing unions powers separation _).symm

noncomputable def twoStage : GroundChronologicalMainDiagram M C D rD pairing unions powers separation (Fin 2) where
  stage := twoStageStage source target
  transition := twoStageTransition pairing unions powers separation step
  self := twoStageTransition_self pairing unions powers separation step
  comp := twoStageTransition_comp pairing unions powers separation step

theorem twoStage_coversOldBirths (coverage : step.CoversOldBirths) :
    (twoStage pairing unions powers separation step).CoversOldBirths := by
  intro i j before
  rcases twoStage_index_cases i with rfl | rfl <;> rcases twoStage_index_cases j with rfl | rfl
  · exact GroundChronologicalMainTransition.identity_coversOldBirths pairing unions powers separation source
  · exact coverage
  · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) before)
  · exact GroundChronologicalMainTransition.identity_coversOldBirths pairing unions powers separation target

end GroundChronologicalMainDiagram

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFixedTopTerminal
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

namespace GroundChronologicalHistory
variable {M : TransitiveGround.{u}} {s C D rD : ZFSet.{u}}
variable (history : GroundChronologicalHistory M (insert s s) C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (ordinal : ordinalSetProperty s) (hs : s ∈ M.sets)
variable (earlier : ∀ x t, ZFSet.pair x t ∈ history.birth s → t ∈ s)
variable (newHeight : ZFSet.{u}) (hHeight : newHeight ∈ M.sets)
variable (heightCode : StrictLexHeightCode (fixedTopCarrier (history.space s)) C D
  (fixedTopOrder (history.space s) (history.order s)) newHeight rD)

local notation "time" => s
local notation "times" => (insert s s)
local notation "P" => history.space s
local notation "r" => history.order s
local notation "born" => history.birth s
local notation "space'" => appendHistoryValue time history.space (fixedTopCarrier P)
local notation "order'" => appendHistoryValue time history.order (fixedTopOrder P r)
local notation "meet'" => appendHistoryValue time history.meetGraph (fixedTopMeet P r)
local notation "birth'" => appendHistoryValue time history.birth (fixedTopBirth P born s)
local notation "height'" => appendHistoryValue time history.height newHeight

noncomputable def replaceTerminalFixedTop : GroundChronologicalHistory M times C D rD := by
  classical
  have terminal : s ∈ times := ZFSet.mem_insert_iff.2 (Or.inl rfl)
  have hP := history.space_mem s terminal
  have hr := history.order_mem s terminal
  have meet := history.meet_order s terminal
  have function := history.birth_function s terminal
  have inside : ∀ t ∈ times, ∀ z ∈ t, z ∈ s := by
    intro t ht z hz
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · exact hz
    · exact ordinal.1 t ht z hz
  have sourceSpace : ∀ t ∈ times, ∀ z ∈ t, history.space z = space' z :=
    fun t ht z hz => (appendHistoryValue_old (inside t ht z hz) _ _).symm
  have sourceOrder : ∀ t ∈ times, ∀ z ∈ t, history.order z = order' z :=
    fun t ht z hz => (appendHistoryValue_old (inside t ht z hz) _ _).symm
  have sourceMeet : ∀ t ∈ times, ∀ z ∈ t, history.meetGraph z = meet' z :=
    fun t ht z hz => (appendHistoryValue_old (inside t ht z hz) _ _).symm
  refine {
    space := space', order := order', meetGraph := meet', birth := birth', height := height'
    space_mem := ?_, order_mem := ?_, meet_mem := ?_, birth_mem := ?_, height_mem := ?_
    meet_order := ?_, birth_function := ?_, birth_bound := ?_, old_meet := ?_
    strict_height := ?_, layer := ?_ }
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using M.fixedTopCarrier_mem pairing unions hP
    · simpa only [appendHistoryValue_old ht] using history.space_mem t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using M.fixedTopOrder_mem pairing unions powers separation hP hr
    · simpa only [appendHistoryValue_old ht] using history.order_mem t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using M.fixedTopMeet_mem pairing unions powers separation hP hr
    · simpa only [appendHistoryValue_old ht] using history.meet_mem t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using
        M.fixedTopBirth_mem pairing unions hP (history.birth_mem _ terminal) hs
    · simpa only [appendHistoryValue_old ht] using history.birth_mem t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using hHeight
    · simpa only [appendHistoryValue_old ht] using history.height_mem t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using fixedTopMeet_code meet
    · simpa only [appendHistoryValue_old ht] using history.meet_order t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using fixedTopBirth_function function terminal
    · simpa only [appendHistoryValue_old ht] using
        history.birth_function t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simp only [appendHistoryValue_at]
      exact fun x _ a entry => fixedTopBirth_bound earlier x a entry
    · simpa only [appendHistoryValue_old ht] using
        history.birth_bound t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using
        fixedTopBirth_oldMeet meet function earlier (history.old_meet _ terminal)
    · simpa only [appendHistoryValue_old ht] using history.old_meet t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using heightCode
    · simpa only [appendHistoryValue_old ht] using history.strict_height t (ZFSet.mem_insert_iff.2 (Or.inr ht))
  · intro cutoff hc t ht bound
    by_cases equal : cutoff = s
    · subst cutoff
      simp only [appendHistoryValue_at]
      have layer := M.fixedTopBirth_layers pairing separation hP meet function earlier
        (fun a ha => history.layer s terminal a (ZFSet.mem_insert_iff.2 (Or.inr ha)) (Or.inr ha))
        t bound
      exact layer.congr_sources_below (sourceSpace t ht) (sourceOrder t ht) (sourceMeet t ht)
    · have hc := (ZFSet.mem_insert_iff.1 hc).resolve_left equal
      simpa only [appendHistoryValue_old hc] using
        (history.layer cutoff (ZFSet.mem_insert_iff.2 (Or.inr hc)) t ht bound).congr_sources_below
          (sourceSpace t ht) (sourceOrder t ht) (sourceMeet t ht)

local notation "extended" => history.replaceTerminalFixedTop pairing unions powers separation ordinal hs earlier newHeight hHeight heightCode

theorem replaceTerminalFixedTop_old {t : ZFSet.{u}} (ht : t ∈ time) :
    (extended).space t = history.space t ∧ (extended).order t = history.order t ∧
      (extended).meetGraph t = history.meetGraph t ∧ (extended).birth t = history.birth t ∧
      (extended).height t = history.height t := by
  exact ⟨appendHistoryValue_old ht _ _, appendHistoryValue_old ht _ _, appendHistoryValue_old ht _ _,
    appendHistoryValue_old ht _ _, appendHistoryValue_old ht _ _⟩

theorem replaceTerminalFixedTop_terminal :
    (extended).space time = fixedTopCarrier P ∧ (extended).order time = fixedTopOrder P r ∧
      (extended).meetGraph time = fixedTopMeet P r ∧ (extended).birth time = fixedTopBirth P born s ∧
      (extended).height time = newHeight := by
  exact ⟨appendHistoryValue_at _ _ _, appendHistoryValue_at _ _ _, appendHistoryValue_at _ _ _,
    appendHistoryValue_at _ _ _, appendHistoryValue_at _ _ _⟩

end GroundChronologicalHistory
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_ExternalChronologyStageLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "r" => completion.externalPointOrder P0 r0 μ0 A0
local notation "μ" => completion.externalPointMeet P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0

noncomputable def cutoff (_births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion) (n : Nat) : ZFSet.{u} :=
  ownerLevelPrefix P B levels (natSetCode n)

variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)
noncomputable def cutoffOrder (n : Nat) : ZFSet.{u} := heightOrderRestriction (births.cutoff n) r
noncomputable def cutoffMeet (n : Nat) : ZFSet.{u} := graphRestriction (ZFSet.prod (births.cutoff n) (births.cutoff n)) μ
noncomputable def cutoffBirth (n : Nat) : ZFSet.{u} := graphRestriction (births.cutoff n) births.birth
noncomputable def cutoffHeight (height : ZFSet.{u}) (n : Nat) : ZFSet.{u} := graphRestriction (births.cutoff n) height

theorem cutoff_subset (n : Nat) : births.cutoff n ⊆ B :=
  ownerLevelPrefix_subset (fun _ hx => (mem_relationImage _ _ _ _).1 hx |>.1) levels (natSetCode n)

end PartitionPilot.Forcing.GroundExternalBirthData



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalProfilePreservation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace MeetEmbeddingCode
universe u
variable {P U Q rP rU rQ μP μU μQ e : ZFSet.{u}}
variable (code : MeetEmbeddingCode U Q rU rQ μU μQ e)
include code

theorem restrictSource (subset : P ⊆ U)
    (order : ∀ x ∈ P, ∀ y ∈ P, ZFSet.pair x y ∈ rP → ZFSet.pair x y ∈ rU)
    (meet : ∀ x ∈ P, ∀ y ∈ P, ∀ z, ZFSet.pair (ZFSet.pair x y) z ∈ μP →
      ZFSet.pair (ZFSet.pair x y) z ∈ μU) :
    MeetEmbeddingCode P Q rP rQ μP μQ (graphRestriction P e) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [graphRestriction_eq_sep code.injection.function]
    exact code.injection.restrict subset
  · intro x y x' y' lower first second
    obtain ⟨first, hx⟩ := pair_mem_graphRestriction.1 first
    obtain ⟨second, hy⟩ := pair_mem_graphRestriction.1 second
    exact code.monotone x y x' y' (order x hx y hy lower) first second
  · intro x y z x' y' z' entry first second third
    obtain ⟨first, hx⟩ := pair_mem_graphRestriction.1 first
    obtain ⟨second, hy⟩ := pair_mem_graphRestriction.1 second
    have third := (pair_mem_graphRestriction.1 third).1
    exact code.map_meet x y z x' y' z' (meet x hx y hy z entry) first second third

end MeetEmbeddingCode

section
open SetFormula
universe u

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem canonical_iterate_bottom {b : ZFSet.{u}} (hb : b ∈ state.data.D)
    (least : ∀ x ∈ state.data.D, ZFSet.pair b x ∈ state.data.rD) (n : Nat) :
    let current := state.data.iterate M I Sources Reps G T n
    b ∈ current.D ∧ ∀ x ∈ current.D, ZFSet.pair b x ∈ current.rD := by
  induction n with
  | zero => exact ⟨hb, least⟩
  | succ n ih =>
    change b ∈ (state.data.iterate M I Sources Reps G T n).currentCarrier ∧
      ∀ x ∈ (state.data.iterate M I Sources Reps G T n).currentCarrier,
        ZFSet.pair b x ∈ (state.data.iterate M I Sources Reps G T n).currentOrder
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid
      pairing unions powers separation hI hSources hReps hG hT n
    rw [← equal] at ih ⊢
    exact current.batch.batch_bottom ih.1 ih.2

theorem union_bottom
    (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
    {b : ZFSet.{u}} (hb : b ∈ state.data.D)
    (least : ∀ x ∈ state.data.D, ZFSet.pair b x ∈ state.data.rD) :
    b ∈ data.fields 0 ∧ ∀ x ∈ data.fields 0, ZFSet.pair b x ∈ data.fields 1 := by
  have carrier : NatUnionCode (fun n => (state.data.iterate M I Sources Reps G T n).D) (data.fields 0) :=
    data.fieldUnion 0
  have order : NatUnionCode (fun n => (state.data.iterate M I Sources Reps G T n).rD) (data.fields 1) :=
    data.fieldUnion 1
  refine ⟨carrier.subset 0 hb, ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := (carrier x).1 hx
  exact order.subset n ((state.canonical_iterate_bottom pairing unions powers separation
    hI hSources hReps hG hT hb least n).2 x hn)

end GroundCompressionState

namespace GroundCompressionOrigin
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)

include origin in
theorem union_bottom
    (data : GroundCompressionUnionData M initial I Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (initialDomain : initial.D = P0) (initialOrder : initial.rD = r0)
    {b : ZFSet.{u}} (hb : b ∈ P0) (least : ∀ x ∈ P0, ZFSet.pair b x ∈ r0) :
    b ∈ data.fields 0 ∧ ∀ x ∈ data.fields 0, ZFSet.pair b x ∈ data.fields 1 := by
  obtain ⟨seed, state, equal⟩ := origin
  cases equal
  apply state.union_bottom pairing unions powers separation hI hSources hReps hG hT data
  · simpa only [initialDomain] using hb
  · simpa only [initialDomain, initialOrder] using least

end GroundCompressionOrigin
end

section
universe u
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalOriginalEmbedding (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  graphRestriction P (completion.externalCopyGraph P r μ A
    (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one))

theorem externalOriginalEmbedding_entry_iff (P r μ A x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ completion.externalOriginalEmbedding P r μ A ↔
      ZFSet.pair x y ∈ completion.externalCopyGraph P r μ A
        (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one) ∧ x ∈ P :=
  pair_mem_graphRestriction

end GroundCompressionCompletion

namespace GroundExternalGeometryInputs
open SetFormula
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P0 ∈ M.sets)
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "originalGraph" => completion.externalOriginalEmbedding P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG hP

theorem externalOriginalEmbedding_mem : originalGraph ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  exact M.graphRestriction_mem unions separation hP (geometry.copies_ground _ data.group.group_code.identity_mem)

theorem externalOriginalEmbedding_code :
    MeetEmbeddingCode P0 (completion.externalBoundedCarrier P0 r0 μ0 A0)
      r0 (completion.externalBoundedOrder P0 r0 μ0 A0) μ0 (completion.externalBoundedMeet P0 r0 μ0 A0)
      originalGraph := by
  have geometry := data.externalBoundedGeometryData group oldAction pairing unions powers separation infinite hG hP
  exact (geometry.copies _ data.group.group_code.identity_mem).toMeetEmbeddingCode.restrictSource
    data.original.subset (fun x hx y hy => (data.original.order x hx y hy).2)
    (fun x hx y hy z => (data.original.meet x hx y hy z).2)

theorem externalOriginalEmbedding_order_iff {x y x' y' : ZFSet.{u}}
    (first : ZFSet.pair x x' ∈ originalGraph) (second : ZFSet.pair y y' ∈ originalGraph) :
    ZFSet.pair x' y' ∈ completion.externalBoundedOrder P0 r0 μ0 A0 ↔ ZFSet.pair x y ∈ r0 := by
  obtain ⟨first, hx⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 x x').1 first
  obtain ⟨second, hy⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 y y').1 second
  have geometry := data.externalBoundedGeometryData group oldAction pairing unions powers separation infinite hG hP
  exact ((geometry.copies _ data.group.group_code.identity_mem).order_iff first second).trans
    (data.original.order x hx y hy)

theorem externalOriginalEmbedding_equivariant {g g' x y x' y' : ZFSet.{u}}
    (actor : ZFSet.pair g g' ∈ M.externalOldInclusion G letters m one)
    (first : ZFSet.pair x x' ∈ originalGraph) (second : ZFSet.pair y y' ∈ originalGraph)
    (acted : ZFSet.pair (ZFSet.pair g x) y ∈ A0) :
    ZFSet.pair (ZFSet.pair g' x') y' ∈ completion.externalBoundedAction P0 r0 μ0 A0 := by
  obtain ⟨first, hx⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 x x').1 first
  have second := ((completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 y y').1 second).1
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  have hx' := (ZFSet.pair_mem_prod.1
    ((geometry.copies _ data.group.group_code.identity_mem).injection.function.1 first)).2
  exact (fixedTopAction_old_iff hx').2 (data.externalIdentityCopy_equivariant group oldAction
    pairing unions powers separation infinite hG actor first second ((data.original.action g x hx y).2 acted))

theorem externalOriginalEmbedding_agreement {g h g' h' v v' : ZFSet.{u}}
    (firstActor : ZFSet.pair g g' ∈ M.externalOldInclusion G letters m one)
    (secondActor : ZFSet.pair h h' ∈ M.externalOldInclusion G letters m one)
    (image : ZFSet.pair v v' ∈ originalGraph) (agree : ActionAgreementBelow P0 r0 A0 g h v) :
    ActionAgreementBelow (completion.externalBoundedCarrier P0 r0 μ0 A0)
      (completion.externalBoundedOrder P0 r0 μ0 A0) (completion.externalBoundedAction P0 r0 μ0 A0) g' h' v' := by
  obtain ⟨image, hv⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 v v').1 image
  exact data.externalBoundedOriginal_agreement group oldAction pairing unions powers separation infinite hG hP
    firstActor secondActor hv image agree

end GroundExternalGeometryInputs
end

namespace GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 Filters : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (initialDomain : initial.D = P0) (initialOrder : initial.rD = r0)
local notation "B" => completion.externalBoundedCarrier P0 r0 μ0 A0
local notation "rB" => completion.externalBoundedOrder P0 r0 μ0 A0
local notation "embedding" => completion.externalOriginalEmbedding P0 r0 μ0 A0
include data origin group action pairing unions powers separation infinite hI hSources hReps hG hT hP0 initialDomain initialOrder

theorem externalOriginalEmbedding_bottom {b b' : ZFSet.{u}}
    (least : ∀ x ∈ P0, ZFSet.pair b x ∈ r0)
    (image : ZFSet.pair b b' ∈ embedding) :
    b' ∈ B ∧ ∀ y ∈ B, ZFSet.pair b' y ∈ rB := by
  obtain ⟨copied, hb⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 b b').1 image
  have bottom := origin.union_bottom completion.algebra.union pairing unions powers separation
    hI hSources hReps hG hT initialDomain initialOrder hb least
  have code := data.externalOriginalEmbedding_code group action pairing unions powers separation infinite hG hP0
  exact ⟨(ZFSet.pair_mem_prod.1 (code.injection.function.1 image)).2,
    data.externalBoundedCopy_bottom group action pairing unions powers separation infinite hG hP0
      data.group.group_code.identity_mem bottom.2 copied⟩

end GroundExternalGeometryInputs

open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialExternalChronology
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
universe u

structure GroundChronologicalExternal (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
    (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 oldTimes oldBirth completion)
    (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 C D rD lo hi seed completion)
    (prior : GroundChronologicalHistory M T0 C D rD) where
  inputs : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion
  history : GroundChronologicalHistory M (insert births.limit births.limit) C D rD
  old_values : ∀ s, s ∈ oldTimes ∨ s = oldTimes →
    history.space s = prior.space s ∧ history.order s = prior.order s ∧
      history.meetGraph s = prior.meetGraph s ∧ history.birth s = prior.birth s ∧ history.height s = prior.height s
  stamp_values : ∀ n,
    history.space (compressionStamp oldTimes n) = births.cutoff n ∧
    history.order (compressionStamp oldTimes n) = births.cutoffOrder n ∧
    history.meetGraph (compressionStamp oldTimes n) = births.cutoffMeet n ∧
    history.birth (compressionStamp oldTimes n) = births.cutoffBirth n ∧
    history.height (compressionStamp oldTimes n) = births.cutoffHeight heights.height n
  limit_values :
    history.space births.limit = completion.externalPointCarrier P0 r0 μ0 A0 ∧
    history.order births.limit = completion.externalPointOrder P0 r0 μ0 A0 ∧
    history.meetGraph births.limit = completion.externalPointMeet P0 r0 μ0 A0 ∧
    history.birth births.limit = births.birth ∧ history.height births.limit = heights.height
  bounded_history : GroundChronologicalHistory M (insert births.limit births.limit) C D rD
  bounded_old_values : ∀ s ∈ births.limit,
    bounded_history.space s = history.space s ∧ bounded_history.order s = history.order s ∧
    bounded_history.meetGraph s = history.meetGraph s ∧ bounded_history.birth s = history.birth s ∧
    bounded_history.height s = history.height s
  bounded_values :
    bounded_history.space births.limit = completion.externalBoundedCarrier P0 r0 μ0 A0 ∧
    bounded_history.order births.limit = completion.externalBoundedOrder P0 r0 μ0 A0 ∧
    bounded_history.meetGraph births.limit = completion.externalBoundedMeet P0 r0 μ0 A0 ∧
    bounded_history.birth births.limit = births.boundedBirth ∧
    bounded_history.height births.limit = heights.boundedHeight

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 Filters C D rD lo hi seed : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (initialDomain : initial.D = P0) (initialOrder : initial.rD = r0)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (boundedHeights : GroundBoundedExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion heights)
variable (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
variable {b b' : ZFSet.{u}} (least : ∀ x ∈ P0, ZFSet.pair b x ∈ r0)
variable (image : ZFSet.pair b b' ∈ completion.externalOriginalEmbedding P0 r0 μ0 A0)
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)

noncomputable def externalMainStage : GroundMainStage M C D rD :=
  let geometry := data.externalBoundedGeometryData group action pairing unions powers separation infinite hG hP0
  let bottom := data.externalOriginalEmbedding_bottom origin group action pairing unions powers separation infinite
    hI hSources hReps hG hT hP0 initialDomain initialOrder least image
  { carrier := completion.externalBoundedCarrier P0 r0 μ0 A0
    order := completion.externalBoundedOrder P0 r0 μ0 A0
    meetGraph := completion.externalBoundedMeet P0 r0 μ0 A0
    actors := M.externalGroupCarrier G letters m one
    multiplication := M.externalGroupMultiplication G letters m one
    inverse := M.externalGroupInverse G letters m inv one
    identity := M.externalGroupIdentity G letters m one
    action := completion.externalBoundedAction P0 r0 μ0 A0
    bottom := b'
    top := completion.externalPointCarrier P0 r0 μ0 A0
    height := heights.boundedHeight
    carrier_ground := geometry.carrier_ground
    order_ground := geometry.order_ground
    meet_ground := geometry.meet_ground
    actors_ground := data.group.carrier_mem
    multiplication_ground := data.group.multiplication_mem
    inverse_ground := data.group.inverse_mem
    action_ground := geometry.action_ground
    height_ground := boundedHeights.height_ground
    columns_ground := hC
    coordinates_ground := hD
    coordinate_order_ground := hrD
    meet := geometry.meet
    group_code := data.group.group_code
    action_code := geometry.action
    bottom_mem := bottom.1
    least := bottom.2
    top_mem := geometry.top_mem
    greatest := geometry.greatest
    height_code := boundedHeights.code
    height_range_ground := boundedHeights.range_ground
    height_range_countable := boundedHeights.range_countable }

end GroundExternalGeometryInputs

namespace GroundChronologicalExternal
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 Filters : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable {births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion}
variable {heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion}
variable {prior : GroundChronologicalHistory M T0 C D rD}
variable (external : GroundChronologicalExternal M initial I Sources Reps G m inv one T τ
  P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 completion births heights prior)
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (initialDomain : initial.D = P0) (initialOrder : initial.rD = r0)
variable (boundedHeights : GroundBoundedExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion heights)
variable (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
variable {b b' : ZFSet.{u}} (least : ∀ x ∈ P0, ZFSet.pair b x ∈ r0)
variable (image : ZFSet.pair b b' ∈ completion.externalOriginalEmbedding P0 r0 μ0 A0)

noncomputable def toMainStage : GroundChronologicalMainStage M C D rD where
  stage := external.inputs.externalMainStage origin group action pairing unions powers separation infinite
    hI hSources hReps hG hT hP0 initialDomain initialOrder heights boundedHeights hC hD hrD least image
  cutoff := births.limit
  cutoff_ground := births.limit_ground
  cutoff_ordinal := births.times.ordinal
  history := external.bounded_history
  carrier_eq := external.bounded_values.1
  order_eq := external.bounded_values.2.1
  meet_eq := external.bounded_values.2.2.1
  height_eq := external.bounded_values.2.2.2.2

theorem toMainStage_birth :
    (external.toMainStage origin group action pairing unions powers separation infinite hI hSources hReps
      hG hT hP0 initialDomain initialOrder boundedHeights hC hD hrD least image).birth = births.boundedBirth :=
  external.bounded_values.2.2.2.1

end GroundChronologicalExternal
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalMainTransition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace GroundCompressionBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T base old : ZFSet.{u}}
variable {union : GroundCompressionUnionData M initial I Sources Reps G m one T}

theorem original_entry_iff (births : GroundCompressionBirthData M initial I Sources Reps G m one T union base old)
    {x t : ZFSet.{u}} (hx : x ∈ initial.D) :
    ZFSet.pair x t ∈ births.birth ↔ ZFSet.pair x t ∈ old := by
  have restriction : ZFSet.pair x t ∈ births.birth ↔
      ZFSet.pair x t ∈ graphRestriction initial.D births.birth := by
    rw [pair_mem_graphRestriction]
    exact ⟨fun entry => ⟨entry, hx⟩, And.left⟩
  exact restriction.trans (congrArg (fun f => ZFSet.pair x t ∈ f) births.original).to_iff

end GroundCompressionBirthData

namespace GroundExternalHeightData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi original : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (compressionHeights : GroundCompressionHeightData M initial I Sources Reps G m one T
  completion.algebra.union P0 C D rD original)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi compressionHeights.height completion)

theorem bounded_preserves_original
    (bounded : GroundBoundedExternalHeightData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 C D rD lo hi compressionHeights.height completion heights)
    {x y z : ZFSet.{u}}
    (image : ZFSet.pair x y ∈ completion.externalOriginalEmbedding P0 r0 μ0 A0) :
    ZFSet.pair y z ∈ heights.boundedHeight ↔ ZFSet.pair x z ∈ original := by
  obtain ⟨copied, hx⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 x y).1 image
  exact (bounded.preserves_seed x y z copied).trans (compressionHeights.original_entries x hx z)

end GroundExternalHeightData

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 base old : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (compressionBirths : GroundCompressionBirthData M initial I Sources Reps G m one T
  completion.algebra.union base old)
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 compressionBirths.limit compressionBirths.birth completion)

theorem bounded_preserves_original
    (bounded : GroundBoundedExternalBirthData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 compressionBirths.limit compressionBirths.birth completion births)
    (initialDomain : initial.D = P0) {x y t : ZFSet.{u}}
    (image : ZFSet.pair x y ∈ completion.externalOriginalEmbedding P0 r0 μ0 A0) :
    ZFSet.pair y t ∈ births.boundedBirth ↔ ZFSet.pair x t ∈ old := by
  obtain ⟨copied, hx⟩ := (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 x y).1 image
  rw [← initialDomain] at hx
  exact (bounded.preserves_seed x y t copied).trans (compressionBirths.original_entry_iff hx)

end GroundExternalBirthData
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (source : GroundMainStage M C D rD)
variable {initial : RecursiveStateData.{u}} {I Sources Reps T Filters lo hi : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps source.actors
  source.multiplication source.identity T source.top}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps source.actors
  source.multiplication source.inverse source.identity T source.top source.carrier source.order
  source.meetGraph source.action completion)
variable (origin : GroundCompressionOrigin M initial source.carrier source.order source.meetGraph source.action
  source.top I Sources Reps source.actors source.multiplication source.inverse source.identity T Filters)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets) (hT : T ∈ M.sets)
variable (initialDomain : initial.D = source.carrier) (initialOrder : initial.rD = source.order)
variable (compressionHeights : GroundCompressionHeightData M initial I Sources Reps source.actors
  source.multiplication source.identity T completion.algebra.union source.carrier C D rD source.height)
variable (heights : GroundExternalHeightData M initial I Sources Reps source.actors source.multiplication
  source.identity T source.top source.carrier source.order source.meetGraph source.action
  C D rD lo hi compressionHeights.height completion)
variable (boundedHeights : GroundBoundedExternalHeightData M initial I Sources Reps source.actors
  source.multiplication source.identity T source.top source.carrier source.order source.meetGraph source.action
  C D rD lo hi compressionHeights.height completion heights)
variable {b' : ZFSet.{u}} (image : ZFSet.pair source.bottom b' ∈
  completion.externalOriginalEmbedding source.carrier source.order source.meetGraph source.action)

noncomputable def externalTransition :
    GroundMainTransition source
      (data.externalMainStage origin source.group_code source.action_code pairing unions powers separation infinite
        hI hSources hReps source.actors_ground hT source.carrier_ground initialDomain initialOrder
        heights boundedHeights source.columns_ground source.coordinates_ground source.coordinate_order_ground
        source.least image) where
  points := completion.externalOriginalEmbedding source.carrier source.order source.meetGraph source.action
  actors := M.externalOldInclusion source.actors
    (externalChildLetters I source.carrier
      (externalRectangles source.carrier source.actors source.order source.meetGraph source.action))
    source.multiplication source.identity
  points_ground := data.externalOriginalEmbedding_mem source.group_code source.action_code
    pairing unions powers separation infinite source.actors_ground source.carrier_ground
  actors_ground := data.old_inclusion_ground
  point_embedding := data.externalOriginalEmbedding_code source.group_code source.action_code
    pairing unions powers separation infinite source.actors_ground source.carrier_ground
  order_iff := fun _ _ _ _ first second => data.externalOriginalEmbedding_order_iff
    source.group_code source.action_code pairing unions powers separation infinite
    source.actors_ground source.carrier_ground first second
  group_embedding := M.externalOldInclusion_groupEmbedding pairing unions powers separation infinite
    source.group_code source.actors_ground data.words.letters_ground
  equivariant := fun _ _ _ _ _ _ actor first second acted => data.externalOriginalEmbedding_equivariant
    source.group_code source.action_code pairing unions powers separation infinite
    source.actors_ground source.carrier_ground actor first second acted
  bottom := image
  height := fun _ _ _ entry => heights.bounded_preserves_original compressionHeights boundedHeights entry
  agreement := fun _ _ _ _ _ _ first second point agree => data.externalOriginalEmbedding_agreement
    source.group_code source.action_code pairing unions powers separation infinite
    source.actors_ground source.carrier_ground first second point agree

end PartitionPilot.Forcing.GroundMainStage

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainSuccessorProfilePreservation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundChronologicalMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (source : GroundChronologicalMainStage M C D rD)
variable {initial : RecursiveStateData.{u}} {I Sources Reps T Targets Separators Filters lo hi : ZFSet.{u}}
variable (compression : GroundChronologicalCompression M initial I Sources Reps source.stage.actors
  source.stage.multiplication source.stage.identity T source.stage.top source.stage.carrier C D rD
  source.stage.height Targets Separators Filters source.cutoff source.birth
  (insert source.cutoff source.cutoff) source.history)
variable {births : GroundExternalBirthData M initial I Sources Reps source.stage.actors
  source.stage.multiplication source.stage.identity T source.stage.top source.stage.carrier source.stage.order
  source.stage.meetGraph source.stage.action compression.born.births.limit compression.born.births.birth
  compression.born.profiled.heighted.completion}
variable {heights : GroundExternalHeightData M initial I Sources Reps source.stage.actors
  source.stage.multiplication source.stage.identity T source.stage.top source.stage.carrier source.stage.order
  source.stage.meetGraph source.stage.action C D rD lo hi compression.born.profiled.heighted.heights.height
  compression.born.profiled.heighted.completion}
variable (external : GroundChronologicalExternal M initial I Sources Reps source.stage.actors
  source.stage.multiplication source.stage.inverse source.stage.identity T source.stage.top source.stage.carrier
  source.stage.order source.stage.meetGraph source.stage.action compression.born.births.limit compression.born.births.birth
  C D rD lo hi compression.born.profiled.heighted.heights.height
  (insert compression.born.births.limit compression.born.births.limit)
  compression.born.profiled.heighted.completion births heights compression.history)
variable (origin : GroundCompressionOrigin M initial source.stage.carrier source.stage.order source.stage.meetGraph
  source.stage.action source.stage.top I Sources Reps source.stage.actors source.stage.multiplication
  source.stage.inverse source.stage.identity T Filters)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets) (hT : T ∈ M.sets)
variable (initialDomain : initial.D = source.stage.carrier) (initialOrder : initial.rD = source.stage.order)
variable (boundedHeights : GroundBoundedExternalHeightData M initial I Sources Reps source.stage.actors
  source.stage.multiplication source.stage.identity T source.stage.top source.stage.carrier source.stage.order
  source.stage.meetGraph source.stage.action C D rD lo hi compression.born.profiled.heighted.heights.height
  compression.born.profiled.heighted.completion heights)
variable (boundedBirths : GroundBoundedExternalBirthData M initial I Sources Reps source.stage.actors
  source.stage.multiplication source.stage.identity T source.stage.top source.stage.carrier source.stage.order
  source.stage.meetGraph source.stage.action compression.born.births.limit compression.born.births.birth
  compression.born.profiled.heighted.completion births)
variable {b' : ZFSet.{u}} (image : ZFSet.pair source.stage.bottom b' ∈
  compression.born.profiled.heighted.completion.externalOriginalEmbedding
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action)

include compression in
theorem external_cutoff_strict : source.cutoff ∈ births.limit :=
  births.times.ordinal.1 compression.born.births.limit births.times.base_mem_limit
    source.cutoff compression.born.births.times.base_mem_limit

noncomputable def externalTransition :
    GroundChronologicalMainTransition source
      (external.toMainStage origin source.stage.group_code source.stage.action_code pairing unions powers separation
        infinite hI hSources hReps source.stage.actors_ground hT source.stage.carrier_ground
        initialDomain initialOrder boundedHeights source.stage.columns_ground source.stage.coordinates_ground
        source.stage.coordinate_order_ground source.stage.least image) where
  map := source.stage.externalTransition external.inputs origin pairing unions powers separation infinite
    hI hSources hReps hT initialDomain initialOrder compression.born.profiled.heighted.heights heights boundedHeights image
  cutoff_le := Or.inr (source.external_cutoff_strict compression)
  birth := by
    intro x y t entry
    rw [external.toMainStage_birth]
    exact births.bounded_preserves_original compression.born.births boundedBirths initialDomain entry
  history_prefix := by
    intro s before
    have first : s ∈ compression.born.births.limit := by
      rcases before with rfl | before
      · exact compression.born.births.times.base_mem_limit
      · exact compression.born.births.times.ordinal.1 source.cutoff
          compression.born.births.times.base_mem_limit s before
    have final : s ∈ births.limit := births.times.ordinal.1 compression.born.births.limit
      births.times.base_mem_limit s first
    have a := compression.old_values s before.symm
    have b := external.old_values s (Or.inl first)
    have c := external.bounded_old_values s final
    exact ⟨c.1.trans (b.1.trans a.1), c.2.1.trans (b.2.1.trans a.2.1),
      c.2.2.1.trans (b.2.2.1.trans a.2.2.1), c.2.2.2.1.trans (b.2.2.2.1.trans a.2.2.2.1),
      c.2.2.2.2.trans (b.2.2.2.2.trans a.2.2.2.2)⟩

end GroundChronologicalMainStage

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainStageInvariant
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetFormula SetRealization
universe u

namespace GroundChronologicalMainStage
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}

structure Invariant (source : GroundChronologicalMainStage M C D rD) (K Labels : ZFSet.{u}) : Prop where
  points_small : GroundBelow M source.stage.carrier K
  actors_small : GroundBelow M source.stage.actors K
  labels_small : GroundBelow M Labels K
  points_rank : ZFSet.rank source.stage.carrier < ZFSet.rank K
  actors_rank : ZFSet.rank source.stage.actors < ZFSet.rank K
  labels_rank : ZFSet.rank Labels < ZFSet.rank K
  cutoff_mem : source.cutoff ∈ K
  columns_rank : ZFSet.rank C < ZFSet.rank K
  coordinates_rank : ZFSet.rank D < ZFSet.rank K

end GroundChronologicalMainStage

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LinkedMainInvariantCodes
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

def LinkedMainInvariantCode (M : TransitiveGround.{u})
    (K Labels C D P G cutoff serial : ZFSet.{u}) : Prop :=
  GroundBelow M P K ∧ GroundBelow M G K ∧ GroundBelow M Labels K ∧
    ZFSet.rank P < ZFSet.rank K ∧ ZFSet.rank G < ZFSet.rank K ∧
    ZFSet.rank Labels < ZFSet.rank K ∧ cutoff ∈ K ∧
    ZFSet.rank C < ZFSet.rank K ∧ ZFSet.rank D < ZFSet.rank K ∧
    ZFSet.rank serial < ZFSet.rank K

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundChronologicalTransitionTransport
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundChronologicalMainTransition
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source target first second : GroundChronologicalMainStage M C D rD}

noncomputable def retargetEq
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    GroundChronologicalMainTransition first second := by
  cases sourceEqual
  cases targetEqual
  exact transition

end PartitionPilot.Forcing.GroundChronologicalMainTransition

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionFiniteFieldGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)

noncomputable def prefixFiniteField (j : Fin 5) (n : Nat) : ZFSet.{u} :=
  Fin.cases (state.data.iterate M I Sources Reps G T (n + 1)).D
    (Fin.cases (state.data.iterate M I Sources Reps G T (n + 1)).rD
      (Fin.cases (state.data.iterate M I Sources Reps G T (n + 1)).μD
        (Fin.cases (graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth)
          (fun _ => heights.function.natValue (n + 1))))) j

noncomputable def prefixTerminalField (j : Fin 5) : ZFSet.{u} :=
  Fin.cases (data.fields 0) (Fin.cases (data.fields 1) (Fin.cases (data.fields 2)
    (Fin.cases births.birth (fun _ => heights.height)))) j

end PartitionPilot.Forcing.GroundCompressionState

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalSlotCopies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula SetRealization Compression Compression.RecursiveMaps.CosetGeometry
universe u

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalSlotCopyRelation (P r μ A j : ZFSet.{u}) : ZFSet.{u} :=
  externalSlotCopyGraph
    (M.externalStarVertices G (externalChildLetters I P (externalRectangles P G r μ A))
      (externalRequestCarrier I P (externalRectangles P G r μ A)) m one)
    (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (externalRequestCarrier I P (externalRectangles P G r μ A))
    (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
    (completion.externalPointAction P r μ A) (completion.localTileVertexImages P r μ A) j

noncomputable def externalSlotCopyMaps (P r μ A Active j : ZFSet.{u}) : ZFSet.{u} :=
  M.indexedRelationSections Active (completion.algebra.union.fields 0)
    (completion.externalPointCarrier P r μ A) (completion.externalSlotCopyRelation P r μ A j)
end GroundCompressionCompletion

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

structure SerializedChronologyCode (T V C D rD N : ZFSet.{u})
    (graphs : Fin 5 → ZFSet.{u}) (W layers : ZFSet.{u}) : Prop where
  ordinal : ordinalSetProperty T
  core : ChronologyCoreCode T V C D rD graphs
  function : ZFSet.IsFunc (chronologyPairs T) W layers
  entries : ChronologyLayerEntries T N graphs layers

namespace GroundSerializedChronology
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}

theorem raw_code (serial : GroundSerializedChronology M T C D rD) :
    SerializedChronologyCode T serial.fields.bound C D rD ZFSet.omega
      serial.fields.graph serial.layerBound serial.layers := by
  refine ⟨serial.ordinal, serial.core, serial.layer_function, ?_⟩
  intro s hs t ht earlier L r μ birth z eL er eμ eb entry
  have code := serial.layer_code s hs t ht earlier z entry
  rw [serial.fields.value_eq_of_entry 0 eL, serial.fields.value_eq_of_entry 1 er,
    serial.fields.value_eq_of_entry 2 eμ, serial.fields.value_eq_of_entry 3 eb] at code
  exact code
end GroundSerializedChronology

end PartitionPilot.Forcing

end

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
universe u

namespace GroundChronologicalHistory
noncomputable def fieldValue {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
    (prior : GroundChronologicalHistory M T C D rD) : Fin 5 → ZFSet.{u} → ZFSet.{u} :=
  Fin.cases prior.space (Fin.cases prior.order (Fin.cases prior.meetGraph
    (Fin.cases prior.birth (fun _ => prior.height))))

end GroundChronologicalHistory




namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {T U cutoff : ZFSet.{u}}

theorem graphPrefixCode_iff_values (source : GroundChronologyFields M T)
    (target : GroundChronologyFields M U)
    (domains : ∀ s, s = cutoff ∨ s ∈ cutoff → s ∈ T ∧ s ∈ U) :
    ChronologyGraphPrefixCode cutoff source.graph target.graph ↔
      ∀ j s, s = cutoff ∨ s ∈ cutoff → source.value j s = target.value j s := by
  constructor
  · intro code j s before
    exact (target.value_eq_of_entry j
      ((code j s before _).1 (source.value_entry j (domains s before).1))).symm
  · intro values j s before x
    constructor
    · intro entry
      have equal := (values j s before).symm.trans (source.value_eq_of_entry j entry)
      exact equal ▸ target.value_entry j (domains s before).2
    · intro entry
      have equal := (values j s before).trans (target.value_eq_of_entry j entry)
      exact equal ▸ source.value_entry j (domains s before).1

end GroundChronologyFields

namespace GroundChronologicalMainTransition
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source target : GroundChronologicalMainStage M C D rD}
variable (sourceFields : GroundChronologyFields M (insert source.cutoff source.cutoff))
variable (targetFields : GroundChronologyFields M (insert target.cutoff target.cutoff))
variable (sourceAgreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
  sourceFields.value j s = source.history.fieldValue j s)
variable (targetAgreement : ∀ j s, s ∈ insert target.cutoff target.cutoff →
  targetFields.value j s = target.history.fieldValue j s)

include sourceAgreement targetAgreement

def ofFieldLaws (map : GroundMainTransition source.stage target.stage)
    (valid : ChronologicalTransitionLaws map.points source.cutoff target.cutoff source.birth target.birth
      sourceFields.graph targetFields.graph) : GroundChronologicalMainTransition source target where
  map := map
  cutoff_le := valid.cutoff_le
  birth := valid.birth
  history_prefix := by
    intro s before
    have bound : s = target.cutoff ∨ s ∈ target.cutoff := by
      rcases valid.cutoff_le with equal | lower
      · exact equal ▸ before
      · exact Or.inr (before.elim (fun equal => equal.symm ▸ lower)
          (fun hs => target.cutoff_ordinal.1 source.cutoff lower s hs))
    have values := (sourceFields.graphPrefixCode_iff_values targetFields (fun a earlier => by
      refine ⟨ZFSet.mem_insert_iff.2 earlier, ZFSet.mem_insert_iff.2 ?_⟩
      rcases valid.cutoff_le with equal | lower
      · exact equal ▸ earlier
      · exact Or.inr (earlier.elim (fun equal => equal.symm ▸ lower)
          (fun ha => target.cutoff_ordinal.1 source.cutoff lower a ha)))).1 valid.history_prefix
    have same (j : Fin 5) : target.history.fieldValue j s = source.history.fieldValue j s := by
      rw [← sourceAgreement j s (ZFSet.mem_insert_iff.2 before),
        ← targetAgreement j s (ZFSet.mem_insert_iff.2 bound)]
      exact (values j s before).symm
    exact ⟨same 0, same 1, same 2, same 3, same 4⟩

end GroundChronologicalMainTransition
end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)
variable (priorFields : GroundChronologyFields M T0)
variable (prior : GroundChronologicalHistory M T0 C Q qlt)

noncomputable def prefixGraph (finiteGraphs : Fin 5 → ZFSet.{u}) (j : Fin 5) : ZFSet.{u} :=
  compressionPrefixGraph base births.limit (priorFields.graph j) (finiteGraphs j) births.stamps
    (state.prefixTerminalField data births heights j)

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing
open SetFormula
universe u

structure GroundLinkedMainStage (M : TransitiveGround.{u}) (K Labels C D rD : ZFSet.{u}) where
  main : GroundChronologicalMainStage M C D rD
  serial : GroundSerializedChronology M (insert main.cutoff main.cutoff) C D rD
  agreement : ∀ j s, s ∈ insert main.cutoff main.cutoff →
    serial.fields.value j s = main.history.fieldValue j s
  invariant : main.Invariant K Labels
  serial_rank : ZFSet.rank serial.code < ZFSet.rank K

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (linked : GroundLinkedMainStage M K Labels C D rD)

noncomputable def code : ZFSet.{u} :=
  linkedMainStageCode linked.main.stage.code linked.main.cutoff linked.serial.code

theorem terminal_values :
    linked.serial.fields.value 0 linked.main.cutoff = linked.main.stage.carrier ∧
    linked.serial.fields.value 1 linked.main.cutoff = linked.main.stage.order ∧
    linked.serial.fields.value 2 linked.main.cutoff = linked.main.stage.meetGraph ∧
    linked.serial.fields.value 3 linked.main.cutoff = linked.main.birth ∧
    linked.serial.fields.value 4 linked.main.cutoff = linked.main.stage.height :=
  ⟨(linked.agreement 0 _ (ZFSet.mem_insert _ _)).trans linked.main.carrier_eq,
    (linked.agreement 1 _ (ZFSet.mem_insert _ _)).trans linked.main.order_eq,
    (linked.agreement 2 _ (ZFSet.mem_insert _ _)).trans linked.main.meet_eq,
    linked.agreement 3 _ (ZFSet.mem_insert _ _),
    (linked.agreement 4 _ (ZFSet.mem_insert _ _)).trans linked.main.height_eq⟩

theorem invariant_code : LinkedMainInvariantCode M K Labels C D linked.main.stage.carrier
    linked.main.stage.actors linked.main.cutoff linked.serial.code :=
  ⟨linked.invariant.points_small, linked.invariant.actors_small, linked.invariant.labels_small,
    linked.invariant.points_rank, linked.invariant.actors_rank, linked.invariant.labels_rank,
    linked.invariant.cutoff_mem, linked.invariant.columns_rank, linked.invariant.coordinates_rank,
    linked.serial_rank⟩

end GroundLinkedMainStage

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u v
namespace GroundChronologicalMainDiagram
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Preorder I]
variable (diagram : GroundChronologicalMainDiagram M C D rD pairing unions powers separation I)

noncomputable def pointSystem (upper : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k) : CodedDirectSystem.{u} I where
  carrier i := (diagram.stage i).stage.carrier
  map before := (diagram.transition before).map.points
  injection before := (diagram.transition before).map.point_embedding.injection
  identity := by
    intro i
    rw [diagram.self]
    rfl
  composition := by
    intro i j k first second
    rw [diagram.comp first second]
    rfl
  common_upper := upper

noncomputable def actorSystem (upper : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k) : CodedDirectSystem.{u} I where
  carrier i := (diagram.stage i).stage.actors
  map before := (diagram.transition before).map.actors
  injection before := (diagram.transition before).map.group_embedding.injection
  identity := by
    intro i
    rw [diagram.self]
    rfl
  composition := by
    intro i j k first second
    rw [diagram.comp first second]
    rfl
  common_upper := upper

end GroundChronologicalMainDiagram

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundLinkedMainStageCodeLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u v

def LinkedMainStageRawCode (M : TransitiveGround.{u}) (K Labels C D rD N z : ZFSet.{u})
    (f : Fin 24 → ZFSet.{u}) : Prop :=
  z = linkedMainStageCode (f 22) (f 11) (f 23) ∧
  f 22 = mainStageCode (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9) (f 10) ∧
  MainStageValidity M (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9) (f 10) C D rD ∧
  f 21 = nonemptyTupleCode 6 (Fin.cases (f 12) (Fin.cases (f 13) (linkedChronologyGraphs f))) ∧
  f 23 = serializedChronologyCode (f 12) (f 13) (linkedChronologyGraphs f) (f 19) (f 20) ∧
  SerializedChronologyCode (f 12) (f 13) C D rD N (linkedChronologyGraphs f) (f 19) (f 20) ∧
  ordinalSetProperty (f 11) ∧ f 12 = insert (f 11) (f 11) ∧
  ZFSet.pair (f 11) (f 0) ∈ f 14 ∧ ZFSet.pair (f 11) (f 1) ∈ f 15 ∧
  ZFSet.pair (f 11) (f 2) ∈ f 16 ∧ ZFSet.pair (f 11) (f 10) ∈ f 18 ∧
  LinkedMainInvariantCode M K Labels C D (f 0) (f 3) (f 11) (f 23)

end

section
open SetFormula
universe u

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (linked : GroundLinkedMainStage M K Labels C D rD)

noncomputable def rawFields : Fin 24 → ZFSet.{u} :=
  (Fin.cases (linked.main.stage.carrier) (Fin.cases (linked.main.stage.order) (Fin.cases (linked.main.stage.meetGraph) (Fin.cases (linked.main.stage.actors) (Fin.cases (linked.main.stage.multiplication) (Fin.cases (linked.main.stage.inverse) (Fin.cases (linked.main.stage.identity) (Fin.cases (linked.main.stage.action) (Fin.cases (linked.main.stage.bottom) (Fin.cases (linked.main.stage.top) (Fin.cases (linked.main.stage.height) (Fin.cases (linked.main.cutoff) (Fin.cases (insert linked.main.cutoff linked.main.cutoff) (Fin.cases (linked.serial.fields.bound) (Fin.cases (linked.serial.fields.graph 0) (Fin.cases (linked.serial.fields.graph 1) (Fin.cases (linked.serial.fields.graph 2) (Fin.cases (linked.serial.fields.graph 3) (Fin.cases (linked.serial.fields.graph 4) (Fin.cases (linked.serial.layerBound) (Fin.cases (linked.serial.layers) (Fin.cases (linked.serial.fields.code) (Fin.cases (linked.main.stage.code) (fun _ => linked.serial.code))))))))))))))))))))))))

theorem rawFields_graphs : linkedChronologyGraphs linked.rawFields = linked.serial.fields.graph := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (fun i => Fin.elim0 i))))) j

theorem rawFields_code : LinkedMainStageRawCode M K Labels C D rD ZFSet.omega linked.code linked.rawFields := by
  unfold LinkedMainStageRawCode
  rw [linked.rawFields_graphs]
  refine ⟨rfl, rfl, linked.main.stage.validity, rfl, rfl, linked.serial.raw_code,
    linked.main.cutoff_ordinal, rfl, ?_, ?_, ?_, ?_, linked.invariant_code⟩
  · change ZFSet.pair linked.main.cutoff linked.main.stage.carrier ∈ linked.serial.fields.graph 0
    rw [← linked.terminal_values.1]
    exact linked.serial.fields.value_entry 0 (ZFSet.mem_insert _ _)
  · change ZFSet.pair linked.main.cutoff linked.main.stage.order ∈ linked.serial.fields.graph 1
    rw [← linked.terminal_values.2.1]
    exact linked.serial.fields.value_entry 1 (ZFSet.mem_insert _ _)
  · change ZFSet.pair linked.main.cutoff linked.main.stage.meetGraph ∈ linked.serial.fields.graph 2
    rw [← linked.terminal_values.2.2.1]
    exact linked.serial.fields.value_entry 2 (ZFSet.mem_insert _ _)
  · change ZFSet.pair linked.main.cutoff linked.main.stage.height ∈ linked.serial.fields.graph 4
    rw [← linked.terminal_values.2.2.2.2]
    exact linked.serial.fields.value_entry 4 (ZFSet.mem_insert _ _)

end GroundLinkedMainStage

namespace LinkedMainStageRawCode
variable {M : TransitiveGround.{u}} {K Labels C D rD N z : ZFSet.{u}}
variable {f g : Fin 24 → ZFSet.{u}}

theorem fields_unique (first : LinkedMainStageRawCode M K Labels C D rD N z f)
    (second : LinkedMainStageRawCode M K Labels C D rD N z g) : f = g := by
  obtain ⟨fo, fa, _, fh, fs, _⟩ := first
  obtain ⟨go, ga, _, gh, gs, _⟩ := second
  have outer := linkedMainStageCode_inj.1 (fo.symm.trans go)
  have stage := nonemptyTupleCode_injective 10 (fa.symm.trans (outer.1.trans ga))
  have serial := nonemptyTupleCode_injective 2 (fs.symm.trans (outer.2.2.trans gs))
  have history := nonemptyTupleCode_injective 6 (congrFun serial 0)
  have h21 : f 21 = g 21 := fh.trans ((congrFun serial 0).trans gh.symm)
  funext j
  exact (show ∀ j : Fin 24, f j = g j from (Fin.cases (congrFun stage 0) (Fin.cases (congrFun stage 1) (Fin.cases (congrFun stage 2) (Fin.cases (congrFun stage 3) (Fin.cases (congrFun stage 4) (Fin.cases (congrFun stage 5) (Fin.cases (congrFun stage 6) (Fin.cases (congrFun stage 7) (Fin.cases (congrFun stage 8) (Fin.cases (congrFun stage 9) (Fin.cases (congrFun stage 10) (Fin.cases (outer.2.1) (Fin.cases (congrFun history 0) (Fin.cases (congrFun history 1) (Fin.cases (congrFun history 2) (Fin.cases (congrFun history 3) (Fin.cases (congrFun history 4) (Fin.cases (congrFun history 5) (Fin.cases (congrFun history 6) (Fin.cases (congrFun serial 1) (Fin.cases (congrFun serial 2) (Fin.cases (h21) (Fin.cases (outer.1) (Fin.cases (outer.2.2) (fun i => Fin.elim0 i)))))))))))))))))))))))))) j

end LinkedMainStageRawCode
end

namespace GroundLinkedMainStage
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}

structure SameCode (first second : GroundLinkedMainStage M K Labels C D rD) : Prop where
  stage : first.main.stage = second.main.stage
  cutoff : first.main.cutoff = second.main.cutoff
  serial_code : first.serial.code = second.serial.code
  raw_fields : first.rawFields = second.rawFields
  field_graphs : first.serial.fields.graph = second.serial.fields.graph

theorem same_code (first second : GroundLinkedMainStage M K Labels C D rD)
    (equal : first.code = second.code) : SameCode first second := by
  have outer := linkedMainStageCode_inj.1 equal
  have other : LinkedMainStageRawCode M K Labels C D rD ZFSet.omega first.code second.rawFields :=
    equal.symm ▸ second.rawFields_code
  have fields := first.rawFields_code.fields_unique other
  refine ⟨GroundMainStage.code_injective outer.1, outer.2.1, outer.2.2, fields, ?_⟩
  rw [← first.rawFields_graphs, ← second.rawFields_graphs, fields]

namespace SameCode
variable {first second : GroundLinkedMainStage M K Labels C D rD}
variable (same : SameCode first second)
include same

theorem serial_values (j : Fin 5) (s : ZFSet.{u}) :
    first.serial.fields.value j s = second.serial.fields.value j s := by
  classical
  by_cases hs : s ∈ insert first.main.cutoff first.main.cutoff
  · have entry := first.serial.fields.value_entry j hs
    rw [same.field_graphs] at entry
    exact (second.serial.fields.value_eq_of_entry j entry).symm
  · have ht : s ∉ insert second.main.cutoff second.main.cutoff := by
      simpa only [same.cutoff] using hs
    change (first.serial.fields.graphFunction j).totalValue s =
      (second.serial.fields.graphFunction j).totalValue s
    rw [FunctionGraphOn.totalValue_outside _ hs, FunctionGraphOn.totalValue_outside _ ht]

theorem history_values (j : Fin 5) (s : ZFSet.{u})
    (hs : s ∈ insert first.main.cutoff first.main.cutoff) :
    first.main.history.fieldValue j s = second.main.history.fieldValue j s := by
  have ht : s ∈ insert second.main.cutoff second.main.cutoff := by
    simpa only [same.cutoff] using hs
  rw [← first.agreement j s hs, ← second.agreement j s ht]
  exact same.serial_values j s

theorem birth : first.main.birth = second.main.birth := by
  have equal := same.history_values 3 first.main.cutoff (ZFSet.mem_insert _ _)
  exact equal.trans (congrArg second.main.history.birth same.cutoff)

theorem history_five (s : ZFSet.{u}) (before : s = first.main.cutoff ∨ s ∈ first.main.cutoff) :
    first.main.history.space s = second.main.history.space s ∧
    first.main.history.order s = second.main.history.order s ∧
    first.main.history.meetGraph s = second.main.history.meetGraph s ∧
    first.main.history.birth s = second.main.history.birth s ∧
    first.main.history.height s = second.main.history.height s :=
  ⟨same.history_values 0 s (ZFSet.mem_insert_iff.2 before),
    same.history_values 1 s (ZFSet.mem_insert_iff.2 before),
    same.history_values 2 s (ZFSet.mem_insert_iff.2 before),
    same.history_values 3 s (ZFSet.mem_insert_iff.2 before),
    same.history_values 4 s (ZFSet.mem_insert_iff.2 before)⟩

end SameCode

end GroundLinkedMainStage

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

namespace GroundChronologicalMainTransition
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target chosenSource chosenTarget : GroundLinkedMainStage M K Labels C D rD}
def retargetLinked (transition : GroundChronologicalMainTransition source.main target.main)
    (sourceCode : source.code = chosenSource.code) (targetCode : target.code = chosenTarget.code) : GroundChronologicalMainTransition chosenSource.main chosenTarget.main := by
  have first := source.same_code chosenSource sourceCode
  have second := target.same_code chosenTarget targetCode
  let points := transition.map.points
  let actors := transition.map.actors
  have ordinary : MainTransitionLaws source.main.stage.carrier target.main.stage.carrier
      source.main.stage.order target.main.stage.order source.main.stage.meetGraph target.main.stage.meetGraph
      source.main.stage.actors target.main.stage.actors source.main.stage.multiplication target.main.stage.multiplication
      source.main.stage.identity target.main.stage.identity source.main.stage.action target.main.stage.action
      source.main.stage.bottom target.main.stage.bottom source.main.stage.height target.main.stage.height points actors :=
    transition.map.laws
  rw [first.stage, second.stage] at ordinary
  let map : GroundMainTransition chosenSource.main.stage chosenTarget.main.stage :=
    GroundMainTransition.ofLaws transition.map.points_ground transition.map.actors_ground ordinary
  refine { map := map, cutoff_le := ?_, birth := ?_, history_prefix := ?_ }
  · simpa only [first.cutoff, second.cutoff] using transition.cutoff_le
  · intro x y t entry
    rw [← first.birth, ← second.birth]
    exact transition.birth x y t entry
  · intro s before
    have oldBefore : s = source.main.cutoff ∨ s ∈ source.main.cutoff := by
      simpa only [first.cutoff] using before
    have original := transition.history_prefix s oldBefore
    have lower := first.history_five s oldBefore
    have upper := second.history_five s (transition.prefix_bound oldBefore)
    exact ⟨upper.1.symm.trans (original.1.trans lower.1),
      upper.2.1.symm.trans (original.2.1.trans lower.2.1),
      upper.2.2.1.symm.trans (original.2.2.1.trans lower.2.2.1),
      upper.2.2.2.1.symm.trans (original.2.2.2.1.trans lower.2.2.2.1),
      upper.2.2.2.2.symm.trans (original.2.2.2.2.trans lower.2.2.2.2)⟩

variable (transition : GroundChronologicalMainTransition source.main target.main)
variable (sourceCode : source.code = chosenSource.code) (targetCode : target.code = chosenTarget.code)

theorem retargetLinked_code :
    (transition.retargetLinked sourceCode targetCode).map.code = transition.map.code := rfl

theorem retargetLinked_coversOldBirths_iff :
    (transition.retargetLinked sourceCode targetCode).CoversOldBirths ↔ transition.CoversOldBirths := by
  have first := source.same_code chosenSource sourceCode
  have second := target.same_code chosenTarget targetCode
  change OldBirthFiberCoverageCode chosenSource.main.stage.carrier transition.map.points
    chosenTarget.main.birth chosenSource.main.cutoff ↔ _
  rw [← first.stage, ← second.birth, ← first.cutoff]
  rfl

theorem retargetLinked_coversOldBirths (coverage : transition.CoversOldBirths) :
    (transition.retargetLinked sourceCode targetCode).CoversOldBirths :=
  (transition.retargetLinked_coversOldBirths_iff sourceCode targetCode).2 coverage

end GroundChronologicalMainTransition

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainDiagramAppend
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundChronologicalMainDiagram
open SetFormula
universe u v w
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Preorder I] {J : Type w} [Preorder J]
variable (diagram : GroundChronologicalMainDiagram M C D rD pairing unions powers separation I)
variable (f : J → I) (mono : Monotone f)

def reindex : GroundChronologicalMainDiagram M C D rD pairing unions powers separation J where
  stage j := diagram.stage (f j)
  transition before := diagram.transition (mono before)
  self j := diagram.self (f j)
  comp first second := diagram.comp (mono first) (mono second)

end PartitionPilot.Forcing.GroundChronologicalMainDiagram



namespace PartitionPilot.Forcing.GroundChronologicalMainDiagram
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Preorder I]
variable (diagram : GroundChronologicalMainDiagram M C D rD pairing unions powers separation I)

structure Cone (target : GroundChronologicalMainStage M C D rD) where
  leg : ∀ i, GroundChronologicalMainTransition (diagram.stage i) target
  coherent : ∀ {i j} (before : i ≤ j),
    (diagram.transition before).comp pairing unions powers separation (leg j) = leg i

noncomputable def coneOfLast (last : I) (greatest : ∀ i, i ≤ last)
    {target : GroundChronologicalMainStage M C D rD}
    (step : GroundChronologicalMainTransition (diagram.stage last) target) : diagram.Cone target where
  leg i := (diagram.transition (greatest i)).comp pairing unions powers separation step
  coherent := by
    intro i j before
    rw [← GroundChronologicalMainTransition.comp_assoc, ← diagram.comp]

namespace Cone
variable {diagram} {target : GroundChronologicalMainStage M C D rD} (cone : diagram.Cone target)

def appendStage (_cone : diagram.Cone target) : WithTop I → GroundChronologicalMainStage M C D rD
  | none => target
  | some i => diagram.stage i

noncomputable def appendTransition {i j : WithTop I} (before : i ≤ j) :
    GroundChronologicalMainTransition (cone.appendStage i) (cone.appendStage j) := by
  cases i with
  | top =>
    cases j with
    | top => exact GroundChronologicalMainTransition.identity pairing unions powers separation target
    | coe j => exact False.elim (WithTop.not_top_le_coe j before)
  | coe i =>
    cases j with
    | top => exact cone.leg i
    | coe j => exact diagram.transition (WithTop.coe_le_coe.mp before)

theorem appendTransition_self (i : WithTop I) :
    cone.appendTransition (le_refl i) =
      GroundChronologicalMainTransition.identity pairing unions powers separation (cone.appendStage i) := by
  cases i with
  | top => rfl
  | coe i => exact diagram.self i

theorem appendTransition_comp {i j k : WithTop I} (hij : i ≤ j) (hjk : j ≤ k) :
    cone.appendTransition (le_trans hij hjk) =
      (cone.appendTransition hij).comp pairing unions powers separation (cone.appendTransition hjk) := by
  cases i with
  | top =>
    cases j with
    | coe j => exact False.elim (WithTop.not_top_le_coe j hij)
    | top =>
      cases k with
      | coe k => exact False.elim (WithTop.not_top_le_coe k hjk)
      | top => exact (GroundChronologicalMainTransition.identity_comp pairing unions powers separation _).symm
  | coe i =>
    cases j with
    | top =>
      cases k with
      | coe k => exact False.elim (WithTop.not_top_le_coe k hjk)
      | top => exact (GroundChronologicalMainTransition.comp_identity pairing unions powers separation _).symm
    | coe j =>
      cases k with
      | top => exact (cone.coherent (WithTop.coe_le_coe.mp hij)).symm
      | coe k => exact diagram.comp (WithTop.coe_le_coe.mp hij) (WithTop.coe_le_coe.mp hjk)

noncomputable def append :
    GroundChronologicalMainDiagram M C D rD pairing unions powers separation (WithTop I) where
  stage := cone.appendStage
  transition := cone.appendTransition
  self := cone.appendTransition_self
  comp := cone.appendTransition_comp

theorem append_coverage (old : diagram.CoversOldBirths)
    (legs : ∀ i, (cone.leg i).CoversOldBirths) : cone.append.CoversOldBirths := by
  intro i j before
  cases i with
  | top =>
    cases j with
    | top => exact GroundChronologicalMainTransition.identity_coversOldBirths pairing unions powers separation target
    | coe j => exact False.elim (WithTop.not_top_le_coe j before)
  | coe i =>
    cases j with
    | top => exact legs i
    | coe j => exact old (WithTop.coe_le_coe.mp before)

end Cone

theorem coneOfLast_coverage (last : I) (greatest : ∀ i, i ≤ last)
    {target : GroundChronologicalMainStage M C D rD}
    (step : GroundChronologicalMainTransition (diagram.stage last) target)
    (old : diagram.CoversOldBirths) (covered : step.CoversOldBirths) :
    (diagram.coneOfLast last greatest step).append.CoversOldBirths :=
  Cone.append_coverage _ old (fun i => (old (greatest i)).comp pairing unions powers separation covered)

end PartitionPilot.Forcing.GroundChronologicalMainDiagram

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainTaskCapFulfillment
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

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def boundedCapImages (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose I (completion.algebra.union.fields 0) (completion.externalBoundedCarrier P r μ A)
    (completion.algebra.caps τ) (completion.externalCopyGraph P r μ A
      (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one))

end GroundCompressionCompletion

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixPreservedSeeds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundChronologicalMainTransition
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source middle target first second : GroundChronologicalMainStage M C D rD}

def PreservesOldProfiles (transition : GroundChronologicalMainTransition source target) : Prop :=
  OldProfilePreservationCode source.stage.carrier source.stage.order source.stage.meetGraph
    target.stage.carrier target.stage.order target.stage.meetGraph transition.map.points
    (M.groundPower source.stage.carrier)

end GroundChronologicalMainTransition

end PartitionPilot.Forcing




end OAI
end


