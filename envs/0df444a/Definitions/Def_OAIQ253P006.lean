-- Prove2me | Definitions.Def_OAIQ253P006
-- name    : OAIQ253P006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:59:38.921691+00:00
-- url     : https://prove2.me/theorems/f37acf9d-1d07-425b-871d-2fc4e160a23c
-- title:
--   Definitions bundle OAIQ253P006 of the split of OpenAI, The Partition Principle does not imply Choice
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 255 declarations of OpenAI's Lean: 98 definitions, 8 inductive types or structures and 149 theorems. The definitions and types are `OAI.PartitionPilot.Forcing.GroundExternalBirthData.chronologicalData`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.chronologyFields`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.chronologyGraph`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.chronologyHistory`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.chronology_all_layers`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.chronology_base_layer`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.chronology_finite_layers`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.chronology_old_layer`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.chronology_union_layers`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.cutoffFamily`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.cutoffField`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.cutoffFieldFamily`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.groundChronologyFields`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.layerComponents`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.layerFiber`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.layerIndices`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.layerMaps`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.layerOwners`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.layerWitness`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.serializedFields`, `OAI.PartitionPilot.Forcing.GroundExternalBirthData.terminalField`, `OAI.PartitionPilot.Forcing.GroundExternalGeometryInputs.externalBirthCopyVertex`, `OAI.PartitionPilot.Forcing.GroundExternalGeometryInputs.externalBirth_cutoff_fresh_layer`, `OAI.PartitionPilot.Forcing.GroundExternalGeometryInputs.externalBirth_cutoff_prior_layer`, `OAI.PartitionPilot.Forcing.GroundExternalGeometryInputs.externalBirth_fresh_layer`, `OAI.PartitionPilot.Forcing.GroundExternalGeometryInputs.externalBirth_prior_layer`, `OAI.PartitionPilot.Forcing.GroundExternalGeometryInputs.externalCosetPresentation`, `OAI.PartitionPilot.Forcing.GroundExternalGeometryInputs.externalStarDartPresentation`, `OAI.PartitionPilot.Forcing.GroundExternalGeometryInputs.externalStarEdgePresentation`, `OAI.PartitionPilot.Forcing.GroundExternalGeometryInputs.externalStarVertexPresentation`, `OAI.PartitionPilot.Forcing.GroundExternalGeometryInputs.localTilePresentation`, `OAI.PartitionPilot.Forcing.GroundInitialMainSeedData`, `OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData`, `OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData.compressionCapImages`, `OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData.successorOutputValues`, `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel`, `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.preservedMainPrefixes`, `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.recursionPrefixes`, `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.validChronologies`, `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.validMainPrefixes` and 66 more.
--
--   **Sources.** They come from these modules of lean/OAI/SetTheory, in whole or in part: `PartitionPrinciple_Definability_DepthSlotCodes`, `PartitionPrinciple_Definability_ExternalStarOverlapRealization`, `PartitionPrinciple_Definability_ExternalTileSlotSupportRealization`, `PartitionPrinciple_Definability_GroundDepthSlotCodes`, `PartitionPrinciple_Definability_GroundExternalCutoffFieldGraphs`, `PartitionPrinciple_Definability_LinkedMainTransitionRawCodes`, `PartitionPrinciple_Definability_TileStarIncidenceRealization`, `PartitionPrinciple_Forcing_GroundExternalStarSupports`, `PartitionPrinciple_Forcing_GroundMainConditionalTotality`, `PartitionPrinciple_Forcing_GroundMainPrefixLimitActionLaws`, `PartitionPrinciple_Forcing_MainPrefixConditionalStepCodes`, `PartitionPrinciple_Geometry_ExternalOwnerCoordinateLaws`, `PartitionPrinciple_Geometry_GroundCompressionStarIncidence`, `PartitionPrinciple_Geometry_GroundExternalCutoffLayers`, `PartitionPrinciple_Geometry_GroundExternalLocalHeightFamilies`, `PartitionPrinciple_Geometry_GroundExternalLocalHeightSelection`, `PartitionPrinciple_Geometry_GroundExternalSerializedCore`, `PartitionPrinciple_Geometry_GroundExternalStarOverlaps`, `PartitionPrinciple_Geometry_GroundIndexedClassInclusions`, `PartitionPrinciple_Geometry_GroundInitialSeedSerializationRanks`, `PartitionPrinciple_Geometry_GroundLinkedProfilePreservation`, `PartitionPrinciple_Geometry_GroundLinkedTransitionRetarget`, `PartitionPrinciple_Geometry_GroundMainFinalRowOrdinaryZF`, `PartitionPrinciple_Geometry_GroundMainFinalRowTerms`, `PartitionPrinciple_Geometry_GroundMainTaskCapFulfillment`, `PartitionPrinciple_Geometry_GroundPreparationFamilyImages`, `PartitionPrinciple_Geometry_GroundSerializedCandidateLevels`, `PartitionPrinciple_Geometry_GroundTileStarIncidence`, `PartitionPrinciple_Geometry_TileStarIncomingCodes`, `PartitionPrinciple_Transfinite_CodedMainPrefixSystems`, `PartitionPrinciple_Transfinite_ExternalBirthLayerSeparation`, `PartitionPrinciple_Transfinite_ExternalChronologyStageLaws`, `PartitionPrinciple_Transfinite_GroundCompressionPrefixGraphs`, `PartitionPrinciple_Transfinite_GroundExternalBirthLayers`, `PartitionPrinciple_Transfinite_GroundInaccessibleOrdinalClosure`, `PartitionPrinciple_Transfinite_GroundInitialExternalChronology`, `PartitionPrinciple_Transfinite_GroundInitialPreservedMainPrefix`, `PartitionPrinciple_Transfinite_GroundLinkedMainStageCodeLaws`, `PartitionPrinciple_Transfinite_GroundLinkedMainStageLevels`, `PartitionPrinciple_Transfinite_GroundMainFinalChronology`, `PartitionPrinciple_Transfinite_GroundMainOrdinalConstructionData`, `PartitionPrinciple_Transfinite_GroundMainPrefixConePreservation`, `PartitionPrinciple_Transfinite_GroundMainPrefixDecoding`, `PartitionPrinciple_Transfinite_GroundMainPrefixFieldFamilies`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitBottom`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitChronologyCore`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitCoverageGraph`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitGroupLaws`, `PartitionPrinciple_Transfinite_GroundMainPrefixPreservedSeeds`, `PartitionPrinciple_Transfinite_GroundMainPrefixPriorFields`, `PartitionPrinciple_Transfinite_GroundMainPrefixRawCoveredAppend`, `PartitionPrinciple_Transfinite_GroundMainPrefixSelectedStepTotality`, `PartitionPrinciple_Transfinite_GroundMainSuccessorProfilePreservation`, `PartitionPrinciple_Transfinite_GroundOmegaOneTaskBearingSuccessorFunction`, `PartitionPrinciple_Transfinite_GroundSerializedChronologyTimeEquality`, `PartitionPrinciple_Transfinite_GroundTaskBearingSuccessorDecoding`, `PartitionPrinciple_Transfinite_MainPrefixHistoryUnionRecognition`.
--
--   **Imports.** It imports the published bundle `Def_PartitionPrinciple`; the bundles `OAIQ253P004` and `OAIQ253P005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ253P009`; the statement `OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData.exists_rankedTargetSerialization`; the proof of `OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData.exists_rankedTargetSerialization`.
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

theorem mem_depthSlotGraph (z : ZFSet.{u}) : z ∈ depthSlotGraph ↔
    ∃ n ∈ ZFSet.omega, ∃ j ∈ natSetCode 3, ∃ k ∈ ZFSet.omega,
      ∃ t ∈ ZFSet.omega, z = ZFSet.pair (ZFSet.pair n j) k ∧
        ZFSet.pair (ZFSet.pair (natSetCode 3) n) t ∈ natMulGraph ∧
        ZFSet.pair (ZFSet.pair t j) k ∈ natAddGraph := by
  constructor
  · exact fun hz => (ZFSet.mem_sep.1 hz).2
  · rintro ⟨n, hn, j, hj, k, hk, t, ht, rfl, mul, add⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hn, hj⟩, hk⟩,
      n, hn, j, hj, k, hk, t, ht, rfl, mul, add⟩

theorem pair_mem_depthSlotGraph (n j k : Nat) :
    ZFSet.pair (ZFSet.pair (natSetCode n) (natSetCode j)) (natSetCode k) ∈ depthSlotGraph.{u} ↔
      j < 3 ∧ k = depthSlotIndex n j := by
  rw [mem_depthSlotGraph]
  constructor
  · rintro ⟨n', _, j', hj, k', _, t, ht, equal, mul, add⟩
    obtain ⟨left, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    obtain ⟨t, rfl⟩ := (mem_omega_iff_natSetCode t).1 ht
    have product := (pair_mem_natMulGraph 3 n t).1 mul
    have sum := (pair_mem_natAddGraph t j k).1 add
    exact ⟨(natSetCode_mem_iff j 3).1 hj, by simp only [depthSlotIndex, product] at sum ⊢; exact sum⟩
  · rintro ⟨hj, rfl⟩
    exact ⟨natSetCode n, natSetCode_mem_omega n, natSetCode j, (natSetCode_mem_iff j 3).2 hj,
      natSetCode (depthSlotIndex n j), natSetCode_mem_omega _, natSetCode (3 * n),
      natSetCode_mem_omega _, rfl, (pair_mem_natMulGraph 3 n _).2 rfl,
      (pair_mem_natAddGraph (3 * n) j _).2 rfl⟩

theorem depthSlotGraph_eq : depthSlotGraph.{u} =
    (natPresentation.product (natInitialPresentation 3)).graph natPresentation
      (fun p => ⟨depthSlotIndex p.1.down p.2.down.val⟩) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨n, hn, j, hj, k, hk, _, _, rfl, _⟩ := (mem_depthSlotGraph z).1 hz
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    obtain ⟨j, bound, rfl⟩ := (mem_natSetCode j 3).1 hj
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
    have equal := ((pair_mem_depthSlotGraph n j k).1 hz).2
    exact ((natPresentation.product (natInitialPresentation 3)).mem_graph natPresentation _ _).2
      ⟨(⟨n⟩, ⟨⟨j, bound⟩⟩), by simp only [Presentation.product, natPresentation, natInitialPresentation, equal]⟩
  · intro hz
    obtain ⟨p, rfl⟩ := ((natPresentation.product (natInitialPresentation 3)).mem_graph natPresentation _ z).1 hz
    exact (pair_mem_depthSlotGraph p.1.down p.2.down.val _).2 ⟨p.2.down.isLt, rfl⟩

theorem depthSlotGraph_function :
    ZFSet.IsFunc (ZFSet.prod ZFSet.omega (natSetCode 3)) ZFSet.omega depthSlotGraph.{u} := by
  rw [depthSlotGraph_eq]
  exact (natPresentation.product (natInitialPresentation 3)).graph_isFunc natPresentation _

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInaccessibleOrdinalClosure
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundInaccessibleConditions
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hK : K ∈ M.sets)
include conditions pairing unions powers separation infinite hK

theorem successor_mem {α : ZFSet.{u}} (hα : α ∈ K) : insert α α ∈ K := by
  have hOne := M.natSetCode_mem separation infinite 1
  have oneBelow := conditions.1.1 ZFSet.omega conditions.2.1 _ (natSetCode_mem_omega 1)
  have ground := M.constantFamilyGraph_mem pairing unions powers separation hOne (M.transitive hK hα)
  have constant := constantFamilyGraph_function (natSetCode 1) α
  have function : ZFSet.IsFunc (natSetCode 1) K (constantFamilyGraph (natSetCode 1) α) := by
    refine ⟨?_, constant.2⟩
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (constant.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx, (ZFSet.mem_singleton.1 hy) ▸ hα⟩
  obtain ⟨δ, hδ, bounded⟩ := conditions.2.2.1 (natSetCode 1) oneBelow _ ground function
  have less := bounded (natSetCode 0) α
    ((pair_mem_constantFamilyGraph (natSetCode 1) α _ _).2
      ⟨(natSetCode_mem_iff 0 1).2 (by decide), rfl⟩)
  obtain ⟨a, eqA⟩ := (ordinalSetProperty_iff α).1 (ordinalSetProperty_member conditions.1 hα)
  obtain ⟨d, eqD⟩ := (ordinalSetProperty_iff δ).1 (ordinalSetProperty_member conditions.1 hδ)
  obtain ⟨k, eqK⟩ := (ordinalSetProperty_iff K).1 conditions.1
  rw [eqA, eqD, mem_ordinalCode_iff] at less
  rw [eqD, eqK, mem_ordinalCode_iff] at hδ
  rw [eqA, eqK, ← ordinalCode_succ, mem_ordinalCode_iff]
  exact (Order.succ_le_iff.2 less).trans_lt hδ

theorem rank_isLimit : Order.IsSuccLimit (ZFSet.rank K) := by
  apply Ordinal.isSuccLimit_iff.2
  refine ⟨ne_of_gt (bot_le.trans_lt (ZFSet.rank_lt_of_mem conditions.2.1)), ?_⟩
  rw [Order.isSuccPrelimit_iff_succ_lt]
  intro a ha
  have hα : ordinalCode a ∈ K := by
    rw [ordinalSetProperty_eq_code_rank K conditions.1]
    exact (mem_ordinalCode_iff a (ZFSet.rank K)).2 ha
  have bound := ZFSet.rank_lt_of_mem (conditions.successor_mem pairing unions powers separation infinite hK hα)
  rw [← ordinalCode_succ, rank_ordinalCode] at bound
  exact bound

end PartitionPilot.Forcing.GroundInaccessibleConditions

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
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {T U L E : ZFSet.{u}} (hT : T ∈ M.sets) (hU : U ∈ M.sets)
variable (hL : L ∈ M.sets) (hE : E ∈ M.sets)
include pairing unions powers separation hT hU hL hE

theorem indexedClassInclusions_mem : M.indexedClassInclusions T U L E ∈ M.sets :=
  M.indexedRelationSections_mem pairing unions powers separation hT hU
    (M.equivalenceClasses_mem powers separation hL hE)
    (M.equivalenceClassifier_mem pairing unions powers separation hL hE)

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



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem relationPathLengths_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A R root : ZFSet.{u}} (hA : A ∈ M.sets) (hR : R ∈ M.sets) (hRoot : root ∈ M.sets) :
    M.relationPathLengths A R root ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  have hPaths := M.finiteWords_mem pairing unions powers separation infinite hA
  have hZero := M.empty_mem ⟨A, hA⟩
  let params := extend ZFSet.omega (extend A (extend R (extend root (extend (M.finiteWords A) (extend ∅ Fin.elim0)))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.iterationEntryFormula 0 1 2 3 4 5 6)
    params (Fin.cases hOmega (Fin.cases hA (Fin.cases hR (Fin.cases hRoot (Fin.cases hPaths
      (Fin.cases hZero (fun i => Fin.elim0 i))))))) (M.prod_mem pairing unions powers separation hOmega hA)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.iterationEntryFormula 0 1 2 3 4 5 6)
      (extend z params)) (ZFSet.prod ZFSet.omega A) = M.relationPathLengths A R root := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, relationPathLengths, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_iterationEntryFormula _ _ _ _ _ _ _ _ rfl)
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem relationDepthGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A R root : ZFSet.{u}} (hA : A ∈ M.sets) (hR : R ∈ M.sets) (hRoot : root ∈ M.sets) :
    M.relationDepthGraph A R root ∈ M.sets :=
  M.shortestLengthGraph_mem pairing unions powers separation infinite hA
    (M.relationPathLengths_mem pairing unions powers separation infinite hA hR hRoot)
end TransitiveGround

end PartitionPilot.Forcing



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

section
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u

def signedPresentation {A : Type u} (s : Presentation A) : Presentation (A × Bool) where
  carrier := ZFSet.prod s.carrier (natSetCode 2)
  encode p := ZFSet.pair (s.encode p.1) (externalSignCode p.2)
  injective := by
    intro p q equal
    have parts := ZFSet.pair_inj.1 equal
    exact Prod.ext (s.injective parts.1) (externalSignCode_injective parts.2)
  mem_carrier z := by
    constructor
    · intro hz
      obtain ⟨a, ha, b, hb, equal⟩ := ZFSet.mem_prod.1 hz
      obtain ⟨a, rfl⟩ := (s.mem_carrier a).1 ha
      obtain ⟨b, rfl⟩ := (mem_natTwo_iff_externalSignCode b).1 hb
      exact ⟨(a, b), equal.symm⟩
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ZFSet.pair_mem_prod.2 ⟨s.encode_mem a, (mem_natTwo_iff_externalSignCode _).2 ⟨b, rfl⟩⟩

variable {J S R : Type u} [Group J]
variable (e : Presentation (External J S)) (s : Presentation S) (r : Presentation R)
variable (q : Presentation (Vertex J S))

noncomputable def tileStarDartPresentation : Presentation (TileStars.Dart J S R) := signedPresentation (tileStarEdgePresentation e s r)

end

open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

include pairing unions powers separation in
theorem tileStarTargetGraph_mem {E R S Q C request generators multiplication : ZFSet.{u}}
    (hE : E ∈ M.sets) (hR : R ∈ M.sets) (hS : S ∈ M.sets) (hQ : Q ∈ M.sets)
    (hC : C ∈ M.sets) (hrequest : request ∈ M.sets) (hgenerators : generators ∈ M.sets)
    (hmultiplication : multiplication ∈ M.sets) :
    tileStarTargetGraph E R S Q C request generators multiplication ∈ M.sets := by
  have carriers := M.tileStarCarriers_mem pairing unions powers separation hQ hE hR hS
  exact M.relationCompose_mem pairing unions powers separation carriers.2.2 carriers.2.2 carriers.1
    (M.tileStarReverseGraph_mem pairing unions powers separation hE hR hS)
    (M.tileStarSourceGraph_mem pairing unions powers separation hE hR hS hQ hC hrequest hgenerators hmultiplication)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TileStarIncidenceRealization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps.CosetGeometry
universe u
variable {J S R : Type u} [Group J]
variable (e : Presentation (External J S)) (s : Presentation S) (r : Presentation R)
variable (q : Presentation (Vertex J S)) (request : S → R)
variable {C req gens mul : ZFSet.{u}}
variable (classed : ∀ w v, ZFSet.pair (e.encode w) (q.encode v) ∈ C ↔ point J S w = v)
variable (requested : ∀ a b, ZFSet.pair (s.encode a) (r.encode b) ∈ req ↔ request a = b)
variable (generated : ∀ a b, ZFSet.pair (s.encode a) (e.encode b) ∈ gens ↔ generator J S a = b)
variable (multiplied : ∀ a b c, ZFSet.pair (ZFSet.pair (e.encode a) (e.encode b)) (e.encode c) ∈ mul ↔ a * b = c)
local notation "vP" => tileStarVertexPresentation e r q
local notation "eP" => tileStarEdgePresentation e s r
local notation "dP" => tileStarDartPresentation e s r

include classed requested generated multiplied in
theorem tileStar_source_entry (d : TileStars.Dart J S R) :
    TileStarSourceEntry e.carrier r.carrier s.carrier q.carrier (tileStarEdgeCarrier e.carrier r.carrier s.carrier)
      C req gens mul ((dP).encode d) ((vP).encode (TileStars.source J S R request d)) := by
  rcases d with ⟨⟨w, a⟩ | ⟨w, a⟩, b⟩ <;> cases b
  · exact ⟨(eP).encode (.inl (w, a)), (eP).encode_mem _, Or.inl
      ⟨e.encode w, e.encode_mem w, r.encode a, r.encode_mem a, rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
  · exact ⟨(eP).encode (.inl (w, a)), (eP).encode_mem _, Or.inl
      ⟨e.encode w, e.encode_mem w, r.encode a, r.encode_mem a, rfl, Or.inl
        ⟨rfl, q.encode (point J S w), q.encode_mem _, (classed _ _).2 rfl, rfl⟩⟩⟩
  · exact ⟨(eP).encode (.inr (w, a)), (eP).encode_mem _, Or.inr
      ⟨e.encode w, e.encode_mem w, s.encode a, s.encode_mem a, rfl, Or.inr
        ⟨rfl, e.encode (generator J S a), e.encode_mem _, e.encode (w * generator J S a), e.encode_mem _,
          q.encode (point J S (w * generator J S a)), q.encode_mem _, (generated _ _).2 rfl,
          (multiplied _ _ _).2 rfl, (classed _ _).2 rfl, rfl⟩⟩⟩
  · exact ⟨(eP).encode (.inr (w, a)), (eP).encode_mem _, Or.inr
      ⟨e.encode w, e.encode_mem w, s.encode a, s.encode_mem a, rfl, Or.inl
        ⟨rfl, r.encode (request a), r.encode_mem _, (requested _ _).2 rfl, rfl⟩⟩⟩

include classed requested generated multiplied in
theorem tileStar_source_entry_iff (d : TileStars.Dart J S R) (v : TileStars.Vertex J S R) :
    TileStarSourceEntry e.carrier r.carrier s.carrier q.carrier (tileStarEdgeCarrier e.carrier r.carrier s.carrier)
      C req gens mul ((dP).encode d) ((vP).encode v) ↔ TileStars.source J S R request d = v := by
  constructor
  · rintro ⟨edge, _, first | second⟩
    · obtain ⟨w, hw, a, ha, rfl, forward | backward⟩ := first
      all_goals obtain ⟨w, rfl⟩ := (e.mem_carrier w).1 hw
      all_goals obtain ⟨a, rfl⟩ := (r.mem_carrier a).1 ha
      · obtain ⟨hd, c, hc, member, hv⟩ := forward
        obtain ⟨c, rfl⟩ := (q.mem_carrier c).1 hc
        have deq : d = (.inl (w, a), true) := (dP).injective hd
        have veq : v = .inl c := (vP).injective hv
        rw [deq, veq]
        exact congrArg Sum.inl ((classed w c).1 member)
      · obtain ⟨hd, hv⟩ := backward
        have deq : d = (.inl (w, a), false) := (dP).injective hd
        have veq : v = .inr (w, a) := (vP).injective hv
        rw [deq, veq]
        rfl
    · obtain ⟨w, hw, a, ha, rfl, forward | backward⟩ := second
      all_goals obtain ⟨w, rfl⟩ := (e.mem_carrier w).1 hw
      all_goals obtain ⟨a, rfl⟩ := (s.mem_carrier a).1 ha
      · obtain ⟨hd, b, hb, member, hv⟩ := forward
        obtain ⟨b, rfl⟩ := (r.mem_carrier b).1 hb
        have deq : d = (.inr (w, a), true) := (dP).injective hd
        have veq : v = .inr (w, b) := (vP).injective hv
        rw [deq, veq]
        exact congrArg (fun b => Sum.inr (w, b)) ((requested a b).1 member)
      · obtain ⟨hd, k, hk, b, hb, c, hc, gen, product, member, hv⟩ := backward
        obtain ⟨k, rfl⟩ := (e.mem_carrier k).1 hk
        obtain ⟨b, rfl⟩ := (e.mem_carrier b).1 hb
        obtain ⟨c, rfl⟩ := (q.mem_carrier c).1 hc
        have deq : d = (.inr (w, a), false) := (dP).injective hd
        have veq : v = .inl c := (vP).injective hv
        rw [deq, veq]
        change Sum.inl (point J S (w * generator J S a)) = Sum.inl c
        rw [(generated a k).1 gen, (multiplied w k b).1 product, (classed b c).1 member]
  · intro equal
    rw [← equal]
    exact tileStar_source_entry e s r q request classed requested generated multiplied d

include classed requested generated multiplied in
theorem tileStar_source_iff (d : TileStars.Dart J S R) (v : TileStars.Vertex J S R) :
    ZFSet.pair ((dP).encode d) ((vP).encode v) ∈
      tileStarSourceGraph e.carrier r.carrier s.carrier q.carrier C req gens mul ↔
        TileStars.source J S R request d = v := by
  rw [pair_mem_tileStarSourceGraph]
  exact ⟨fun h => (tileStar_source_entry_iff e s r q request classed requested generated multiplied d v).1 h.2.2,
    fun h => ⟨(dP).encode_mem d, (vP).encode_mem v,
      (tileStar_source_entry_iff e s r q request classed requested generated multiplied d v).2 h⟩⟩

theorem tileStar_reverse_iff (d v : TileStars.Dart J S R) :
    ZFSet.pair ((dP).encode d) ((dP).encode v) ∈ tileStarReverseGraph e.carrier r.carrier s.carrier ↔
      TileStars.reverse J S R d = v := by
  rw [pair_mem_tileStarReverseGraph]
  constructor
  · rintro ⟨_, _, edge, he, ⟨hd, hv⟩ | ⟨hd, hv⟩⟩
    all_goals obtain ⟨edge, rfl⟩ := ((eP).mem_carrier edge).1 he
    · have deq : d = (edge, false) := (dP).injective hd
      have veq : v = (edge, true) := (dP).injective hv
      rw [deq, veq]; rfl
    · have deq : d = (edge, true) := (dP).injective hd
      have veq : v = (edge, false) := (dP).injective hv
      rw [deq, veq]; rfl
  · intro equal
    refine ⟨(dP).encode_mem d, (dP).encode_mem v, ?_⟩
    rw [← equal]
    rcases d with ⟨edge, b⟩
    cases b
    · exact ⟨(eP).encode edge, (eP).encode_mem edge, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨(eP).encode edge, (eP).encode_mem edge, Or.inr ⟨rfl, rfl⟩⟩

include classed requested generated multiplied in
theorem tileStar_target_iff (d : TileStars.Dart J S R) (v : TileStars.Vertex J S R) :
    ZFSet.pair ((dP).encode d) ((vP).encode v) ∈
      tileStarTargetGraph e.carrier r.carrier s.carrier q.carrier C req gens mul ↔
        TileStars.target J S R request d = v := by
  rw [tileStarTargetGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, a, ha, hd, hv⟩
    obtain ⟨a, rfl⟩ := ((dP).mem_carrier a).1 ha
    have rev := (tileStar_reverse_iff e s r d a).1 hd
    have src := (tileStar_source_iff e s r q request classed requested generated multiplied a v).1 hv
    change TileStars.source J S R request (TileStars.reverse J S R d) = v
    rw [rev]
    exact src
  · intro equal
    exact ⟨(dP).encode_mem d, (vP).encode_mem v, (dP).encode (TileStars.reverse J S R d),
      (dP).encode_mem _, (tileStar_reverse_iff e s r _ _).2 rfl,
      (tileStar_source_iff e s r q request classed requested generated multiplied _ _).2 equal⟩

include classed requested generated multiplied in
theorem tileStar_adjacency_iff (x y : TileStars.Vertex J S R) :
    ZFSet.pair ((vP).encode x) ((vP).encode y) ∈ dartAdjacencyGraph
      (tileStarDartCarrier e.carrier r.carrier s.carrier) (tileStarVertexCarrier q.carrier e.carrier r.carrier)
      (tileStarSourceGraph e.carrier r.carrier s.carrier q.carrier C req gens mul)
      (tileStarTargetGraph e.carrier r.carrier s.carrier q.carrier C req gens mul) ↔
      ∃ d : TileStars.Dart J S R, TileStars.source J S R request d = x ∧ TileStars.target J S R request d = y := by
  rw [dartAdjacencyGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, d, hd, hs, ht⟩
    obtain ⟨d, rfl⟩ := ((dP).mem_carrier d).1 hd
    exact ⟨d, (tileStar_source_iff e s r q request classed requested generated multiplied d x).1
      ((pair_mem_relationConverse _ _ _ _ _).1 hs).2.2,
      (tileStar_target_iff e s r q request classed requested generated multiplied d y).1 ht⟩
  · rintro ⟨d, hs, ht⟩
    exact ⟨(vP).encode_mem x, (vP).encode_mem y, (dP).encode d, (dP).encode_mem d,
      (pair_mem_relationConverse _ _ _ _ _).2 ⟨(dP).encode_mem d, (vP).encode_mem x,
        (tileStar_source_iff e s r q request classed requested generated multiplied d x).2 hs⟩,
      (tileStar_target_iff e s r q request classed requested generated multiplied d y).2 ht⟩

end PartitionPilot.Forcing

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

open SetFormula
universe u

theorem compressionPrefixGraph_exact {base limit old stages stamps final : ZFSet.{u}}
    (times : CompressionStampCode base stamps limit)
    (prior : ZFSet.{u} → ZFSet.{u}) (finite : Nat → ZFSet.{u})
    (oldEntries : ∀ s, s ∈ base ∨ s = base → ∀ y, ZFSet.pair s y ∈ old ↔ y = prior s)
    (finiteEntries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ stages ↔ y = finite n)
    (s y : ZFSet.{u}) :
    ZFSet.pair s y ∈ compressionPrefixGraph base limit old stages stamps final ↔
      s ∈ insert limit limit ∧ y = compressionPrefixValue base limit prior finite final s := by
  rw [compressionPrefixGraph_entries times]
  constructor
  · rintro (⟨rfl,equal⟩ | ⟨before,entry⟩ | ⟨n,rfl,entry⟩)
    · exact ⟨ZFSet.mem_insert _ _, equal.trans (compressionPrefixValue_limit prior finite final times).symm⟩
    · exact ⟨ZFSet.mem_insert_of_mem _ ((times.mem_limit_iff s).2
        (before.elim Or.inl (fun h => Or.inr (Or.inl h)))),
        ((oldEntries s before y).1 entry).trans
          (compressionPrefixValue_old prior finite final before).symm⟩
    · exact ⟨ZFSet.mem_insert_of_mem _ (times.stamp_mem_limit n),
        ((finiteEntries n y).1 entry).trans
          (compressionPrefixValue_stamp prior finite final times n).symm⟩
  · rintro ⟨hs,equal⟩
    rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
    · exact Or.inl ⟨rfl,equal.trans (compressionPrefixValue_limit prior finite final times)⟩
    · rcases (times.mem_limit_iff s).1 hs with before | same | ⟨n,rfl⟩
      · exact Or.inr (Or.inl ⟨Or.inl before, (oldEntries s (Or.inl before) y).2
          (equal.trans (compressionPrefixValue_old prior finite final (Or.inl before)))⟩)
      · exact Or.inr (Or.inl ⟨Or.inr same, (oldEntries s (Or.inr same) y).2
          (equal.trans (compressionPrefixValue_old prior finite final (Or.inr same)))⟩)
      · exact Or.inr (Or.inr ⟨n,rfl,(finiteEntries n y).2
          (equal.trans (compressionPrefixValue_stamp prior finite final times n))⟩)

theorem compressionPrefixGraph_function {base limit old stages stamps final : ZFSet.{u}}
    (times : CompressionStampCode base stamps limit)
    (prior : ZFSet.{u} → ZFSet.{u}) (finite : Nat → ZFSet.{u})
    (oldEntries : ∀ s, s ∈ base ∨ s = base → ∀ y, ZFSet.pair s y ∈ old ↔ y = prior s)
    (finiteEntries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ stages ↔ y = finite n) :
    FunctionGraphOn (insert limit limit) (compressionPrefixGraph base limit old stages stamps final) := by
  let graph := compressionPrefixGraph base limit old stages stamps final
  have entries := compressionPrefixGraph_exact (final := final) times prior finite oldEntries finiteEntries
  refine ⟨ZFSet.sUnion (ZFSet.sUnion graph), ?_, ?_⟩
  · intro z hz
    have shape : ∃ s y, z = ZFSet.pair s y := by
      rcases ZFSet.mem_insert_iff.1 hz with rfl | member
      · exact ⟨limit,final,rfl⟩
      · rcases ZFSet.mem_union.1 member with left | right
        · obtain ⟨s,_,y,rfl,_⟩ := mem_graphRestriction.1 left
          exact ⟨s,y,rfl⟩
        · obtain ⟨s,_,_,_,y,_,rfl,_,_⟩ := (mem_relationCompose _ _ _ _ _ _).1 right
          exact ⟨s,y,rfl⟩
    obtain ⟨s,y,rfl⟩ := shape
    exact ZFSet.pair_mem_prod.2 ⟨((entries s y).1 hz).1,pair_second_mem_doubleUnion hz⟩
  · intro s hs
    exact ⟨compressionPrefixValue base limit prior finite final s,
      (entries s _).2 ⟨hs,rfl⟩, fun y hy => ((entries s y).1 hy).2⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem compressionPrefixGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {base limit old stages stamps final : ZFSet.{u}}
    (hOmega : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    (hBase : base ∈ M.sets) (hLimit : limit ∈ M.sets) (hOld : old ∈ M.sets)
    (hStages : stages ∈ M.sets) (hStamps : stamps ∈ M.sets) (hFinal : final ∈ M.sets) :
    compressionPrefixGraph base limit old stages stamps final ∈ M.sets := by
  have hBefore := M.insert_mem pairing unions hBase hBase
  have hBound := M.union_mem unions (M.union_mem unions hStages)
  exact M.insert_mem pairing unions (M.orderedPair_mem pairing hLimit hFinal)
    (M.binary_union_mem pairing unions (M.graphRestriction_mem unions separation hBefore hOld)
      (M.relationCompose_mem pairing unions powers separation hLimit hOmega hBound
        (M.relationConverse_mem pairing unions powers separation hOmega hLimit hStamps) hStages))

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

theorem code_ground (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    serial.code ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 2 serial.codeFields
    (Fin.cases (serial.fields.code_ground pairing)
      (Fin.cases serial.layer_bound_ground (fun _ => serial.layers_ground)))

end GroundSerializedChronology
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundSerializedChronology
universe u
variable {M : TransitiveGround.{u}} {T T' C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M T C D rD)

def castTime (equal : T = T') : GroundSerializedChronology M T' C D rD := equal ▸ serial

end PartitionPilot.Forcing.GroundSerializedChronology

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



namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground

theorem externalCoset_old_entries :
    letI := group.toGroup
    ∀ j k, ZFSet.pair ((SetMembers.presentation G).encode j) ((sGroup).encode k) ∈
      M.externalOldInclusion G letters m one ↔ old (SetMembers G) (family).Letters j = k := by
  let := group.toGroup
  intro j k
  rw [completion.externalFamilyGroupPresentation_old group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground]
  exact Presentation.pair_mem_graph _ _ _ _ _

theorem externalCoset_mul_entries :
    letI := group.toGroup
    ∀ (w k v : External (SetMembers G) (family).Letters), ZFSet.pair (ZFSet.pair ((sGroup).encode w) ((sGroup).encode k)) ((sGroup).encode v) ∈
      M.externalGroupMultiplication G letters m one ↔ w * k = v := by
  let := group.toGroup
  intro w k v
  rw [completion.externalFamilyGroupPresentation_multiplication group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground]
  exact Presentation.pair_mem_graph ((sGroup).product (sGroup)) (sGroup) (fun p => p.1 * p.2) (w, k) v

noncomputable def externalCosetPresentation :
    letI := group.toGroup
    Presentation (Vertex (SetMembers G) (family).Letters) := by
  letI := group.toGroup
  exact Forcing.externalCosetPresentation (sGroup) (SetMembers.presentation G)
    (data.externalCoset_old_entries group oldAction pairing unions powers separation infinite hG)
    (data.externalCoset_mul_entries group oldAction pairing unions powers separation infinite hG)

theorem externalCosetPresentation_carrier :
    letI := group.toGroup
    (data.externalCosetPresentation group oldAction pairing unions powers separation infinite hG).carrier =
      M.externalCosetCarrier G letters m one := by
  let := group.toGroup
  change equivalenceClasses (sGroup).carrier (externalCosetRelation (sGroup).carrier G
    (M.externalOldInclusion G letters m one) (M.externalGroupMultiplication G letters m one)) = _
  rw [completion.externalFamilyGroupPresentation_carrier]
  rfl

theorem externalCosetClassifier_entry_iff :
    letI := group.toGroup
    let q := data.externalCosetPresentation group oldAction pairing unions powers separation infinite hG
    ∀ w v, ZFSet.pair ((sGroup).encode w) (q.encode v) ∈ M.externalCosetClassifier G letters m one ↔
      point (SetMembers G) (family).Letters w = v := by
  let := group.toGroup
  dsimp only
  have entries := Forcing.externalCosetClassifier_entry_iff (sGroup) (SetMembers.presentation G)
    (data.externalCoset_old_entries group oldAction pairing unions powers separation infinite hG)
    (data.externalCoset_mul_entries group oldAction pairing unions powers separation infinite hG)
  rw [completion.externalFamilyGroupPresentation_carrier] at entries
  exact entries

include data pairing unions powers separation hG in
theorem externalCosets_ground :
    M.externalCosetEquivalence G letters m one ∈ M.sets ∧
      M.externalCosetCarrier G letters m one ∈ M.sets ∧ M.externalCosetClassifier G letters m one ∈ M.sets := by
  have relation := M.externalCosetRelation_mem pairing unions powers separation data.group.carrier_mem hG
    data.old_inclusion_ground data.group.multiplication_mem
  exact ⟨relation, M.equivalenceClasses_mem powers separation data.group.carrier_mem relation,
    M.equivalenceClassifier_mem pairing unions powers separation data.group.carrier_mem relation⟩

end GroundExternalGeometryInputs




namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "rectangles" => externalRectangles P0 G r0 μ0 A0
local notation "letters" => externalChildLetters I P0 rectangles
local notation "requests" => externalRequestCarrier I P0 rectangles
local notation "family" => completion.externalFamily group oldAction data.original
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "sLetter" => completion.externalFamilyLetterPresentation group oldAction data.original
local notation "sRequest" => externalRequestPresentation I P0 rectangles
local notation "sCoset" => data.externalCosetPresentation group oldAction pairing unions powers separation infinite hG

noncomputable def externalStarVertexPresentation :
    letI := group.toGroup
    Presentation (TileStars.Vertex (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)) := by
  letI := group.toGroup
  exact tileStarVertexPresentation (sGroup) (sRequest) (sCoset)

noncomputable def externalStarEdgePresentation :
    letI := group.toGroup
    Presentation (TileStars.Edge (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)) := by
  letI := group.toGroup
  exact tileStarEdgePresentation (sGroup) (sLetter) (sRequest)

noncomputable def externalStarDartPresentation :
    letI := group.toGroup
    Presentation (TileStars.Dart (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)) := by
  letI := group.toGroup
  exact tileStarDartPresentation (sGroup) (sLetter) (sRequest)

theorem externalStarPresentations_carriers :
    letI := group.toGroup
    (data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG).carrier =
      M.externalStarVertices G letters requests m one ∧
    (data.externalStarEdgePresentation group oldAction pairing unions powers separation infinite hG).carrier =
      M.externalStarEdges G letters requests m one ∧
    (data.externalStarDartPresentation group oldAction pairing unions powers separation infinite hG).carrier =
      M.externalStarDarts G letters requests m one := by
  let := group.toGroup
  change tileStarVertexCarrier (sCoset).carrier (sGroup).carrier requests = _ ∧
    tileStarEdgeCarrier (sGroup).carrier requests (sLetter).carrier = _ ∧
    tileStarDartCarrier (sGroup).carrier requests (sLetter).carrier = _
  rw [data.externalCosetPresentation_carrier, completion.externalFamilyGroupPresentation_carrier,
    completion.externalFamilyLetterPresentation_carrier]
  exact ⟨rfl, rfl, rfl⟩

include data pairing unions powers separation hG in
theorem externalStarCarriers_ground :
    M.externalStarVertices G letters requests m one ∈ M.sets ∧
      M.externalStarEdges G letters requests m one ∈ M.sets ∧
      M.externalStarDarts G letters requests m one ∈ M.sets := by
  exact M.tileStarCarriers_mem pairing unions powers separation
    (data.externalCosets_ground pairing unions powers separation hG).2.1
    data.group.carrier_mem data.words.requests_ground data.words.letters_ground

end GroundExternalGeometryInputs
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

theorem externalRequestChildCode_mem {I P R : ZFSet.{u}}
    (r : ExternalRequestIndex I P R) (c : ExternalRequestChild r) :
    externalRequestChildCode r c ∈ natSetCode 2 := by
  rcases r with i | (x | r)
  · exact (mem_natTwo_iff_externalSignCode _).2 ⟨false, rfl⟩
  · exact (mem_natTwo_iff_externalSignCode _).2 ⟨false, rfl⟩
  · exact (mem_natTwo_iff_externalSignCode _).2 ⟨c.down, rfl⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem tileStarRequestGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {R S : ZFSet.{u}} (hR : R ∈ M.sets) (hS : S ∈ M.sets) : tileStarRequestGraph R S ∈ M.sets := by
  have hz : natSetCode 0 ∈ M.sets := M.empty_mem ⟨R, hR⟩
  have ho : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hz hz
  have ht : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions ho ho
  exact M.graphRestriction_mem unions separation hS (M.productFirst_mem pairing unions powers separation hR ht)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u})
noncomputable def externalStarIncidence (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  dartIncidenceGraph (M.externalStarSource G S R m one) (M.externalStarTarget G S R m one)

end TransitiveGround

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "rectangles" => externalRectangles P0 G r0 μ0 A0
local notation "letters" => externalChildLetters I P0 rectangles
local notation "requests" => externalRequestCarrier I P0 rectangles
local notation "family" => completion.externalFamily group oldAction data.original
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "sLetter" => completion.externalFamilyLetterPresentation group oldAction data.original
local notation "sRequest" => externalRequestPresentation I P0 rectangles
local notation "sCoset" => data.externalCosetPresentation group oldAction pairing unions powers separation infinite hG
local notation "sVertex" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG

theorem externalStar_request_entries :
    ∀ (a : (family).Letters) b, ZFSet.pair ((sLetter).encode a) ((sRequest).encode b) ∈
      tileStarRequestGraph requests letters ↔ a.1 = b := by
  intro a b
  let child := externalRequestChildCode a.1 (cast (completion.externalFamily_child group oldAction data.original a.1) a.2)
  have shape : (sLetter).encode a = ZFSet.pair ((sRequest).encode a.1) child := rfl
  have member := (sLetter).encode_mem a
  rw [shape] at member ⊢
  exact (pair_mem_tileStarRequestGraph ((sRequest).encode_mem a.1)
    (externalRequestChildCode_mem _ _) member).trans
    ⟨fun h => (sRequest).injective h, congrArg (sRequest).encode⟩

theorem externalStar_generator_entries :
    letI := group.toGroup
    ∀ a b, ZFSet.pair ((sLetter).encode a) ((sGroup).encode b) ∈ M.externalChildGenerators G letters m one ↔
      generator (SetMembers G) (family).Letters a = b := by
  let := group.toGroup
  intro a b
  rw [completion.externalFamilyGroupPresentation_generators group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground]
  exact Presentation.pair_mem_graph (sLetter) (sGroup) _ a b

theorem externalStarAdjacency_iff :
    letI := group.toGroup
    ∀ (x y : TileStars.Vertex (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)), ZFSet.pair ((sVertex).encode x) ((sVertex).encode y) ∈ M.externalStarAdjacency G letters requests m one ↔
      ∃ d : TileStars.Dart (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles),
        TileStars.source (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) d = x ∧
        TileStars.target (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) d = y := by
  let := group.toGroup
  intro x y
  have entries := tileStar_adjacency_iff (sGroup) (sLetter) (sRequest) (sCoset) (fun a => a.1)
    (data.externalCosetClassifier_entry_iff group oldAction pairing unions powers separation infinite hG)
    (data.externalStar_request_entries group oldAction)
    (data.externalStar_generator_entries group oldAction pairing unions powers separation infinite hG)
    (data.externalCoset_mul_entries group oldAction pairing unions powers separation infinite hG) x y
  rw [completion.externalFamilyGroupPresentation_carrier, completion.externalFamilyLetterPresentation_carrier,
    data.externalCosetPresentation_carrier] at entries
  exact entries

include data pairing unions powers separation hG in
theorem externalStarIncidence_ground :
    tileStarRequestGraph requests letters ∈ M.sets ∧
    M.externalStarSource G letters requests m one ∈ M.sets ∧
    M.externalStarTarget G letters requests m one ∈ M.sets ∧
    M.externalStarReverse G letters requests m one ∈ M.sets ∧
    M.externalStarIncidence G letters requests m one ∈ M.sets ∧
    M.externalStarAdjacency G letters requests m one ∈ M.sets := by
  have req := M.tileStarRequestGraph_mem pairing unions powers separation data.words.requests_ground data.words.letters_ground
  have cosets := data.externalCosets_ground pairing unions powers separation hG
  have carriers := data.externalStarCarriers_ground pairing unions powers separation hG
  have src := M.tileStarSourceGraph_mem pairing unions powers separation data.group.carrier_mem
    data.words.requests_ground data.words.letters_ground cosets.2.1 cosets.2.2 req
    data.generators_ground data.group.multiplication_mem
  have tgt := M.tileStarTargetGraph_mem pairing unions powers separation data.group.carrier_mem
    data.words.requests_ground data.words.letters_ground cosets.2.1 cosets.2.2 req
    data.generators_ground data.group.multiplication_mem
  have rev := M.tileStarReverseGraph_mem pairing unions powers separation data.group.carrier_mem
    data.words.requests_ground data.words.letters_ground
  exact ⟨req, src, tgt, rev, M.dartIncidenceGraph_mem pairing unions src tgt,
    M.dartAdjacencyGraph_mem pairing unions powers separation carriers.2.2 carriers.1 src tgt⟩

end GroundExternalGeometryInputs
end PartitionPilot.Forcing

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
open SetFormula
universe u

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "R" => completion.externalPointOrder P0 r0 μ0 A0
local notation "μ" => completion.externalPointMeet P0 r0 μ0 A0
local notation "images" => completion.localTileVertexImages P0 r0 μ0 A0
local notation "domains" => completion.localTilePoints P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG hP0

theorem localTileGroundInputs :
    Q ∈ M.sets ∧ R ∈ M.sets ∧ μ ∈ M.sets ∧ images ∈ M.sets ∧ domains ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have flat := data.flat_relations_ground pairing unions powers separation hP0 hG
  have product := M.prod_mem pairing unions powers separation data.group.carrier_mem (completion.algebra.union.ground 0)
  have sectionGround := M.indexedRelationSection_mem pairing unions powers separation flat.1 product
    flat.2.2.1 data.group.identity_mem
  have imageGround : images ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    flat.1 product geometry.carrier_ground sectionGround geometry.classifier_ground
  have domainGround : domains ∈ M.sets := M.vertexImageDomains_mem pairing unions powers separation
    data.words.requests_ground (M.natSetCode_mem separation infinite 3) (completion.algebra.union.ground 0)
    geometry.carrier_ground flat.1 imageGround
  exact ⟨geometry.carrier_ground, geometry.order_ground, geometry.meet_ground, imageGround, domainGround⟩

end GroundExternalGeometryInputs

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalLocalHeightFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression Compression.RecursiveMaps.CosetGeometry
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
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "vertices" => completion.externalFamilyTileVertexPresentation group oldAction data.original
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "vcode" => completion.externalFamilyVertexCode group oldAction data.original
include data group oldAction pairing unions powers separation infinite hG

theorem localTileVertexImages_entry_iff :
    letI := group.toGroup
    ∀ (r : Index) (i : Option ((family).Child r)) (x : SetMembers U) (y : (family).Node (action)),
      ZFSet.pair ((vertices).encode ⟨r, i, x⟩) ((q).encode y) ∈
        completion.localTileVertexImages P0 r0 μ0 A0 ↔
          ((family).copy (action) ((family).flatWord 1 r i)).toFun x = y := by
  let := group.toGroup
  intro r i x y
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have identity := completion.externalFamilyGroupPresentation_identity group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have placements := completion.externalPlacements_entry_iff group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have classed := data.externalPointClassifier_entry_iff group oldAction pairing unions powers separation infinite hG
  rw [GroundCompressionCompletion.localTileVertexImages, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, z, hz, placed, classified⟩
    have hz' : z ∈ ((s).product (SetMembers.presentation U)).carrier := by
      change z ∈ ZFSet.prod (s).carrier U
      rw [sc]
      exact hz
    obtain ⟨⟨w, a⟩, rfl⟩ := (((s).product (SetMembers.presentation U)).mem_carrier z).1 hz'
    have placed' := ((pair_mem_indexedRelationSection _ _ _ _ _ _).1 placed).2.2
    rw [identity] at placed'
    have same := (placements 1 ⟨r, i, x⟩ (w, a)).1 placed'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact (classed _ _ _).1 classified
  · intro equal
    let z := (((s).product (SetMembers.presentation U)).encode ((family).flatWord 1 r i, x))
    have hz : z ∈ ZFSet.prod (M.externalGroupCarrier G
        (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one) U := by
      rw [← sc]
      exact ((s).product (SetMembers.presentation U)).encode_mem _
    refine ⟨(vertices).encode_mem _, qc ▸ (q).encode_mem _, z, hz, ?_, (classed _ _ _).2 equal⟩
    apply (pair_mem_indexedRelationSection _ _ _ _ _ _).2
    refine ⟨(vertices).encode_mem _, hz, ?_⟩
    rw [identity]
    exact (placements 1 ⟨r, i, x⟩ _).2 rfl

theorem localTileCarrier_image :
    letI := group.toGroup
    ∀ (r : Index) (z : ZFSet.{u}),
      z ∈ completion.localTileCarrier P0 r0 μ0 A0 (externalRequestIndexCode r) ↔
        ∃ x : ((family).tile r).Space, (q).encode (((family).placedTile (action) 1 r).toFun x) = z := by
  let := group.toGroup
  intro r z
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have vertexEntries := data.localTileVertexImages_entry_iff group oldAction pairing unions powers separation infinite hG
  constructor
  · intro hz
    obtain ⟨hzQ, domain⟩ := (mem_relationFiber _ _ _ _).1 hz
    obtain ⟨z, rfl⟩ := ((q).mem_carrier z).1 (qc.symm ▸ hzQ)
    obtain ⟨_, _, j, _, x, hx, vertex, image⟩ :=
      (pair_mem_vertexImageDomains _ _ _ _ _ _ _ _).1 domain
    have shape := (triple_mem_externalTileVertices _ _ _ _ _ _).1 vertex
    have range : j = natSetCode 0 ∨ j = natSetCode 1 ∨
        (externalRequestIndexCode r ∈ ZFSet.prod {natSetCode 2} (externalRectangles P0 G r0 μ0 A0) ∧
          j = natSetCode 2) := by tauto
    obtain ⟨i, rfl⟩ := (completion.externalFamilyVertexCode_range group oldAction data.original r j).1 range
    let x' := SetMembers.ofMem x hx
    have copied : ((family).copy (action) ((family).flatWord 1 r i)).toFun x' = z :=
      (vertexEntries r i x' z).1 (by simpa only [GroundCompressionCompletion.externalFamilyTileVertexPresentation_encode, x', SetMembers.raw_ofMem] using image)
    refine ⟨((family).flatVertex r i).toFun x', ?_⟩
    rw [(family).flatVertex_copy, copied]
  · rintro ⟨z, rfl⟩
    obtain ⟨i, x, rfl⟩ := (family).flatVertex_cover r z
    apply (mem_relationFiber _ _ _ _).2
    refine ⟨qc ▸ (q).encode_mem _, ?_⟩
    apply (pair_mem_vertexImageDomains _ _ _ _ _ _ _ _).2
    have range := (completion.externalFamilyVertexCode_range group oldAction data.original r _).2 ⟨i, rfl⟩
    have hj : vcode r i ∈ natSetCode 3 := by
      rcases range with equal | equal | ⟨_, equal⟩
      all_goals rw [equal]; exact (natSetCode_mem_iff _ 3).2 (by decide)
    refine ⟨(externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem r,
      qc ▸ (q).encode_mem _, vcode r i, hj, SetMembers.raw x, SetMembers.raw_mem x,
      (vertices).encode_mem ⟨r, i, x⟩, ?_⟩
    apply (vertexEntries r i x _).2
    exact ((family).flatVertex_copy (action) 1 r i x).symm

noncomputable def localTilePresentation (r : Index) :
    letI := group.toGroup
    Presentation (((family).tile r).Space) := by
  letI := group.toGroup
  exact {
    carrier := completion.localTileCarrier P0 r0 μ0 A0 (externalRequestIndexCode r)
    encode := fun x => (q).encode (((family).placedTile (action) 1 r).toFun x)
    injective := fun _ _ equal => embedding_injective ((family).placedTile (action) 1 r).toMeetEmbedding ((q).injective equal)
    mem_carrier := data.localTileCarrier_image group oldAction pairing unions powers separation infinite hG r }

end PartitionPilot.Forcing.GroundExternalGeometryInputs




namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression Compression.RecursiveMaps.CosetGeometry
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
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "vcode" => completion.externalFamilyVertexCode group oldAction data.original
local notation "vertexGraph(" r "," i ")" => indexedRelationSection U Q (completion.localTileVertexImages P0 r0 μ0 A0)
  (ZFSet.pair (externalRequestIndexCode r) (vcode r i))
include data group oldAction pairing unions powers separation infinite hG

omit pairing unions powers separation infinite hG in
theorem localTileVertexCode_mem (r : Index) (i : Option ((family).Child r)) : vcode r i ∈ natSetCode 3 := by
  have range := (completion.externalFamilyVertexCode_range group oldAction data.original r _).2 ⟨i, rfl⟩
  rcases range with equal | equal | ⟨_, equal⟩
  all_goals rw [equal]; exact (natSetCode_mem_iff _ 3).2 (by decide)

end PartitionPilot.Forcing.GroundExternalGeometryInputs




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

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
include data group oldAction pairing unions powers separation infinite hG hP0

theorem externalStarSupports_ground : completion.externalStarSupports P0 r0 μ0 A0 ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have cosets := data.externalCosets_ground pairing unions powers separation hG
  exact M.externalStarSupportGraph_mem pairing unions powers separation
    (data.externalStarCarriers_ground pairing unions powers separation hG).1 geometry.carrier_ground
    data.group.carrier_mem (completion.algebra.union.ground 0) cosets.2.1 data.words.requests_ground
    cosets.2.2 geometry.classifier_ground
    (data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0).2.2.2.2
    geometry.action_ground (M.natSetCode_mem separation infinite 0) (M.natSetCode_mem separation infinite 1)

end GroundExternalGeometryInputs
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

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "rectangles" => externalRectangles P0 G r0 μ0 A0
local notation "letters" => externalChildLetters I P0 rectangles
local notation "requests" => externalRequestCarrier I P0 rectangles
local notation "family" => completion.externalFamily group oldAction data.original
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "sVertex" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG

theorem externalStarRoot_eq_encode :
    letI := group.toGroup
    M.externalStarRoot G letters m one =
      (sVertex).encode (TileStars.root (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)) := by
  let instRootEncodeGroup := group.toGroup
  change ZFSet.pair (natSetCode 0) (equivalenceClass (M.externalGroupCarrier G letters m one)
    (M.externalCosetEquivalence G letters m one) (M.externalGroupIdentity G letters m one)) =
    ZFSet.pair (natSetCode 0) (equivalenceClass (sGroup).carrier
      (externalCosetRelation (sGroup).carrier G (M.externalOldInclusion G letters m one)
        (M.externalGroupMultiplication G letters m one)) ((sGroup).encode 1))
  rw [completion.externalFamilyGroupPresentation_carrier,
    completion.externalFamilyGroupPresentation_identity group oldAction data.original
      pairing unions powers separation infinite hG data.words.letters_ground]
  rfl

include data group oldAction pairing unions powers separation infinite hG in
theorem externalStarRoot_mem : M.externalStarRoot G letters m one ∈ M.sets := by
  let instRootMembershipGroup := group.toGroup
  rw [data.externalStarRoot_eq_encode group oldAction pairing unions powers separation infinite hG]
  have members := data.externalStarCarriers_ground pairing unions powers separation hG
  have carriers := data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG
  exact M.transitive (carriers.1.symm ▸ members.1) ((sVertex).encode_mem _)

theorem externalStarDepth_eq_graph :
    letI := group.toGroup
    M.externalStarDepth G letters requests m one = (sVertex).graph natPresentation
      (fun x => ⟨TileStars.depth (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) x⟩) := by
  let instDepthGraphGroup := group.toGroup
  have carriers := data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG
  have members := data.externalStarCarriers_ground pairing unions powers separation hG
  have eq := TileStars.depthGraph_eq_graph (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)
    (fun a => a.1) M pairing unions separation infinite (sVertex)
    (data.externalStarAdjacency_iff group oldAction pairing unions powers separation infinite hG)
    (carriers.1.symm ▸ members.1)
  rw [carriers.1, ← data.externalStarRoot_eq_encode group oldAction pairing unions powers separation infinite hG] at eq
  exact eq

include data group oldAction pairing unions powers separation infinite hG in
theorem externalStarDepth_ground_function :
    M.externalStarDepth G letters requests m one ∈ M.sets ∧
      ZFSet.IsFunc (M.externalStarVertices G letters requests m one) ZFSet.omega
        (M.externalStarDepth G letters requests m one) := by
  let instDepthFunctionGroup := group.toGroup
  have members := data.externalStarCarriers_ground pairing unions powers separation hG
  have adjacency := (data.externalStarIncidence_ground pairing unions powers separation hG).2.2.2.2.2
  refine ⟨M.relationDepthGraph_mem pairing unions powers separation infinite members.1 adjacency
    (data.externalStarRoot_mem group oldAction pairing unions powers separation infinite hG), ?_⟩
  rw [data.externalStarDepth_eq_graph group oldAction pairing unions powers separation infinite hG]
  have function := (sVertex).graph_isFunc natPresentation
    (fun x => ⟨TileStars.depth (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) x⟩)
  rw [(data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1] at function
  exact function

theorem externalStarDepth_iff :
    letI := group.toGroup
    ∀ x n, ZFSet.pair ((sVertex).encode x) (natSetCode n) ∈ M.externalStarDepth G letters requests m one ↔
      n = TileStars.depth (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) x := by
  let instDepthEntryGroup := group.toGroup
  intro x n
  rw [data.externalStarDepth_eq_graph group oldAction pairing unions powers separation infinite hG]
  have entry := (sVertex).pair_mem_graph natPresentation
    (fun x => ⟨TileStars.depth (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) x⟩) x ⟨n⟩
  exact entry.trans ⟨fun equal => (congrArg ULift.down equal).symm, fun equal => congrArg ULift.up equal.symm⟩

end GroundExternalGeometryInputs

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalStarOverlapRealization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression Compression.RecursiveMaps.CosetGeometry
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
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "c" => data.externalCosetPresentation group oldAction pairing unions powers separation infinite hG
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
include data group oldAction pairing unions powers separation infinite hG

theorem externalStarSupports_iff :
    letI := group.toGroup
    ∀ (v : TileStars.Vertex (SetMembers G) (family).Letters Index) (y : (family).Node (action)),
      ZFSet.pair ((vpres).encode v) ((q).encode y) ∈ completion.externalStarSupports P0 r0 μ0 A0 ↔
        ∃ x : (family).Space v, (((family).diagram (action)).vertex v).toFun x = y := by
  let := group.toGroup
  intro v y
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have cc := data.externalCosetPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have vc := (data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1
  have cosets := data.externalCosetClassifier_entry_iff group oldAction pairing unions powers separation infinite hG
  have copied := data.externalPointClassifier_entry_iff group oldAction pairing unions powers separation infinite hG
  have acted := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.1
  have localImage := data.localTileCarrier_image group oldAction pairing unions powers separation infinite hG
  rw [GroundCompressionCompletion.externalStarSupports, pair_mem_externalStarSupportGraph]
  constructor
  · rintro ⟨_, _, body⟩
    cases v with
    | inl coset =>
      rcases body with cosetBody | tileBody
      · obtain ⟨c', _, w, hw, x, hx, equal, classified, image⟩ := cosetBody
        change ZFSet.pair (natSetCode 0) ((c).encode coset) = ZFSet.pair (natSetCode 0) c' at equal
        obtain rfl : (c).encode coset = c' := (ZFSet.pair_inj.1 equal).2
        obtain ⟨w, rfl⟩ := ((s).mem_carrier w).1 (sc.symm ▸ hw)
        have atCoset := (cosets w coset).1 classified
        obtain rfl := atCoset
        let x' := SetMembers.ofMem x hx
        refine ⟨((action).chart w).toFun x', ?_⟩
        exact (copied w x' y).1 (by simpa only [x', SetMembers.raw_ofMem] using image)
      · obtain ⟨_, _, _, _, _, _, equal, _⟩ := tileBody
        change ZFSet.pair (natSetCode 0) _ = ZFSet.pair (natSetCode 1) _ at equal
        exact False.elim (Nat.zero_ne_one (natSetCode_injective (ZFSet.pair_inj.1 equal).1))
    | inr wr =>
      rcases wr with ⟨w, r⟩
      rcases body with cosetBody | tileBody
      · obtain ⟨_, _, _, _, _, _, equal, _⟩ := cosetBody
        change ZFSet.pair (natSetCode 1) _ = ZFSet.pair (natSetCode 0) _ at equal
        exact False.elim (Nat.zero_ne_one (natSetCode_injective (ZFSet.pair_inj.1 equal).1.symm))
      · obtain ⟨w', _, r', _, x, hx, equal, localEntry, actionEntry⟩ := tileBody
        change ZFSet.pair (natSetCode 1) (ZFSet.pair ((s).encode w) (externalRequestIndexCode r)) =
          ZFSet.pair (natSetCode 1) (ZFSet.pair w' r') at equal
        obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 (ZFSet.pair_inj.1 equal).2
        obtain ⟨x', rfl⟩ := (localImage r x).1 ((mem_relationFiber _ _ _ _).2 ⟨hx, localEntry⟩)
        have translated := (acted w (((family).placedTile (action) 1 r).toFun x') y).1 actionEntry
        rw [(family).translate_tile, mul_one] at translated
        exact ⟨x', translated⟩
  · rintro ⟨x, image⟩
    refine ⟨vc ▸ (vpres).encode_mem v, qc ▸ (q).encode_mem y, ?_⟩
    cases v with
    | inl coset =>
      obtain ⟨w, rfl⟩ := representative_exists (SetMembers G) (family).Letters coset
      apply Or.inl
      let z := ((action).chart w).inverse x
      refine ⟨(c).encode (point (SetMembers G) (family).Letters w), cc ▸ (c).encode_mem _,
        (s).encode w, sc ▸ (s).encode_mem w, SetMembers.raw z, SetMembers.raw_mem z, rfl,
        (cosets _ _).2 rfl, (copied w z y).2 ?_⟩
      change (((family).diagram (action)).vertex (.inl (point (SetMembers G) (family).Letters w))).toFun
        (((action).chart w).toFun (((action).chart w).inverse x)) = y
      erw [((action).chart w).right_inverse]
      exact image
    | inr wr =>
      rcases wr with ⟨w, r⟩
      apply Or.inr
      let z := ((family).placedTile (action) 1 r).toFun x
      have localEntry := (mem_relationFiber _ _ _ _).1 ((localImage r ((q).encode z)).2 ⟨x, rfl⟩)
      refine ⟨(s).encode w, sc ▸ (s).encode_mem w, externalRequestIndexCode r,
        (externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem r,
        (q).encode z, qc ▸ (q).encode_mem z, rfl, localEntry.2, (acted w z y).2 ?_⟩
      change (family).translate (action) w (((family).placedTile (action) 1 r).toFun x) = y
      erw [(family).translate_tile, mul_one]
      exact image

end PartitionPilot.Forcing.GroundExternalGeometryInputs




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

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "rectangles" => externalRectangles P0 G r0 μ0 A0
local notation "letters" => externalChildLetters I P0 rectangles
local notation "requests" => externalRequestCarrier I P0 rectangles
local notation "family" => completion.externalFamily group oldAction data.original
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "scheme" => TileStars.Spaces.scheme
  (Compression.RecursiveMaps.TileRequests.Family.diagram (family) (action))
local notation "sVertex" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG

theorem externalStarOwner_iff :
    letI := group.toGroup
    ∀ x v, ZFSet.pair ((q).encode x) ((sVertex).encode v) ∈ completion.externalStarOwner P0 r0 μ0 A0 ↔
      (scheme).LeastSupport v x := by
  let := group.toGroup
  intro x v
  have entry := leastSupportGraph_entry (sVertex) (q) (scheme).depth (scheme).Supports
    (data.externalStarDepth_iff group oldAction pairing unions powers separation infinite hG)
    (data.externalStarSupports_iff group oldAction pairing unions powers separation infinite hG) x v
  rw [(data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1,
    data.externalPointPresentation_carrier] at entry
  exact entry

include data group oldAction pairing unions powers separation infinite hG in
theorem externalStarOwner_ground_function (hP0 : P0 ∈ M.sets) :
    completion.externalStarOwner P0 r0 μ0 A0 ∈ M.sets ∧
      ZFSet.IsFunc (completion.externalPointCarrier P0 r0 μ0 A0)
        (M.externalStarVertices G letters requests m one) (completion.externalStarOwner P0 r0 μ0 A0) := by
  let := group.toGroup
  have vertices := (data.externalStarCarriers_ground pairing unions powers separation hG).1
  have points := (data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0).carrier_ground
  have depths := (data.externalStarDepth_ground_function group oldAction pairing unions powers separation infinite hG).1
  have supports := data.externalStarSupports_ground group oldAction pairing unions powers separation infinite hG hP0
  refine ⟨M.leastSupportGraph_mem pairing unions powers separation infinite vertices points depths supports, ?_⟩
  have function := leastSupportGraph_function (sVertex) (q) (scheme).depth (scheme).Supports
    (data.externalStarDepth_iff group oldAction pairing unions powers separation infinite hG)
    (data.externalStarSupports_iff group oldAction pairing unions powers separation infinite hG)
    (scheme).existsUnique_leastSupport
  rw [(data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1,
    data.externalPointPresentation_carrier] at function
  exact function

end GroundExternalGeometryInputs
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
local notation "rectangles" => externalRectangles P0 G r0 μ0 A0
local notation "letters" => externalChildLetters I P0 rectangles
local notation "requests" => externalRequestCarrier I P0 rectangles
local notation "family" => completion.externalFamily group oldAction data.original
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "scheme" => TileStars.Spaces.scheme
  (Compression.RecursiveMaps.TileRequests.Family.diagram (family) (action))
local notation "sVertex" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "oldCopy" => completion.externalCopyGraph P0 r0 μ0 A0 (M.externalGroupIdentity G letters m one)
local notation "oldImage" => relationImage U Q oldCopy

theorem externalStarOwner_subset : completion.externalStarOwner P0 r0 μ0 A0 ⊆
    ZFSet.prod Q (M.externalStarVertices G letters requests m one) := by
  intro z hz
  unfold GroundCompressionCompletion.externalStarOwner leastSupportGraph at hz
  exact (ZFSet.mem_sep.1 hz).1

include data group oldAction pairing unions powers separation infinite hG in
theorem externalStarOwner_order_depth {x y v w : ZFSet.{u}} {n k : Nat}
    (lower : ZFSet.pair x y ∈ completion.externalPointOrder P0 r0 μ0 A0)
    (first : ZFSet.pair x v ∈ completion.externalStarOwner P0 r0 μ0 A0)
    (second : ZFSet.pair y w ∈ completion.externalStarOwner P0 r0 μ0 A0)
    (firstDepth : ZFSet.pair v (natSetCode n) ∈ M.externalStarDepth G letters requests m one)
    (secondDepth : ZFSet.pair w (natSetCode k) ∈ M.externalStarDepth G letters requests m one) :
    n ≤ k ∧ (n = k → v = w) := by
  let := group.toGroup
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have vc := (data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1
  have firstShape := ZFSet.pair_mem_prod.1 (externalStarOwner_subset first)
  have secondShape := ZFSet.pair_mem_prod.1 (externalStarOwner_subset second)
  obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ firstShape.1)
  obtain ⟨y, rfl⟩ := ((q).mem_carrier y).1 (qc.symm ▸ secondShape.1)
  obtain ⟨v, rfl⟩ := ((sVertex).mem_carrier v).1 (vc.symm ▸ firstShape.2)
  obtain ⟨w, rfl⟩ := ((sVertex).mem_carrier w).1 (vc.symm ▸ secondShape.2)
  have firstOwner := (data.externalStarOwner_iff group oldAction pairing unions powers separation infinite hG x v).1 first
  have secondOwner := (data.externalStarOwner_iff group oldAction pairing unions powers separation infinite hG y w).1 second
  have order := ((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).1 x y).1 lower
  have hn := (data.externalStarDepth_iff group oldAction pairing unions powers separation infinite hG v n).1 firstDepth
  have hk := (data.externalStarDepth_iff group oldAction pairing unions powers separation infinite hG w k).1 secondDepth
  refine ⟨?_, ?_⟩
  · rw [hn, hk]
    exact (scheme).leastSupport_depth_mono firstOwner secondOwner order
  · intro same
    exact congrArg (sVertex).encode ((scheme).leastSupport_eq_of_depth_eq firstOwner secondOwner order
      (hn.symm.trans (same.trans hk)))

include data group oldAction pairing unions powers separation infinite hG in
theorem externalStarOwner_root_iff :
    ∀ x, ZFSet.pair x (M.externalStarRoot G letters m one) ∈ completion.externalStarOwner P0 r0 μ0 A0 ↔
      x ∈ oldImage := by
  let := group.toGroup
  intro x
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have rootEq := data.externalStarRoot_eq_encode group oldAction pairing unions powers separation infinite hG
  have identity := completion.externalFamilyGroupPresentation_identity group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have copies := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.2
  constructor
  · intro entry
    have hx := (ZFSet.pair_mem_prod.1 (externalStarOwner_subset entry)).1
    obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ hx)
    rw [rootEq, data.externalStarOwner_iff group oldAction pairing unions powers separation infinite hG] at entry
    obtain ⟨a, image⟩ := ((family).leastSupport_root_copy_iff (action) x).1 entry
    refine (mem_relationImage _ _ _ _).2 ⟨hx, SetMembers.raw a, SetMembers.raw_mem a, ?_⟩
    have copyEntry := (copies 1 a x).2 image
    rw [← identity] at copyEntry
    exact copyEntry
  · intro hx
    obtain ⟨member, a, ha, entry⟩ := (mem_relationImage _ _ _ _).1 hx
    obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ member)
    let a' := SetMembers.ofMem a ha
    have copyEntry : ZFSet.pair (SetMembers.raw a') ((q).encode x) ∈
        completion.externalCopyGraph P0 r0 μ0 A0 ((sGroup).encode 1) := by
      simpa only [identity, a', SetMembers.raw_ofMem] using entry
    have image := (copies 1 a' x).1 copyEntry
    rw [rootEq, data.externalStarOwner_iff group oldAction pairing unions powers separation infinite hG]
    exact ((family).leastSupport_root_copy_iff (action) x).2 ⟨a', image⟩

theorem externalStarOwner_fresh_tile :
    letI := group.toGroup
    ∀ x v, ZFSet.pair x v ∈ completion.externalStarOwner P0 r0 μ0 A0 → x ∉ oldImage →
      ∃ w r, ∃ y : ((family).tile r).Space,
        v = (sVertex).encode (.inr (w, r)) ∧ x = (q).encode (((family).placedTile (action) w r).toFun y) ∧
        ¬ ((family).tile r).order.le y
          (((family).diagram (action)).localGlue (.inr (w, r)) ((family).tile_depth_ne_zero (action) w r)).rightAnchor := by
  let := group.toGroup
  intro x v entry fresh
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have vc := (data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1
  have shape := ZFSet.pair_mem_prod.1 (externalStarOwner_subset entry)
  obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ shape.1)
  obtain ⟨v, rfl⟩ := ((sVertex).mem_carrier v).1 (vc.symm ▸ shape.2)
  have least := (data.externalStarOwner_iff group oldAction pairing unions powers separation infinite hG x v).1 entry
  rcases (family).leastSupport_cases (action) v x least with ⟨rfl, _⟩ | ⟨w, r, y, rfl, eq, outside⟩
  · apply False.elim
    apply fresh
    apply (data.externalStarOwner_root_iff group oldAction pairing unions powers separation infinite hG _).1
    rw [data.externalStarRoot_eq_encode group oldAction pairing unions powers separation infinite hG]
    exact entry
  · exact ⟨w, r, y, rfl, congrArg (q).encode eq.symm, outside⟩

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
local notation "rectangles" => externalRectangles P0 G r0 μ0 A0
local notation "letters" => externalChildLetters I P0 rectangles
local notation "requests" => externalRequestCarrier I P0 rectangles
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "seedCarrier" => completion.externalSeedCarrier P0 r0 μ0 A0

include data group oldAction pairing unions powers separation infinite hG

theorem externalSeedCarrier_lower {x y : ZFSet.{u}} (hx : x ∈ Q) (hy : y ∈ seedCarrier)
    (lower : ZFSet.pair x y ∈ completion.externalPointOrder P0 r0 μ0 A0) : x ∈ seedCarrier := by
  have ideal := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  obtain ⟨_, a, _, entry⟩ := (mem_relationImage _ _ _ _).1 hy
  obtain ⟨b, hb, _, image⟩ := ideal.ideal a y x entry hx lower
  exact (mem_relationImage _ _ _ _).2 ⟨hx, b, hb, image⟩

theorem externalStarOwner_order {x y v w n k : ZFSet.{u}}
    (lower : ZFSet.pair x y ∈ completion.externalPointOrder P0 r0 μ0 A0)
    (first : ZFSet.pair x v ∈ completion.externalStarOwner P0 r0 μ0 A0)
    (second : ZFSet.pair y w ∈ completion.externalStarOwner P0 r0 μ0 A0)
    (firstDepth : ZFSet.pair v n ∈ M.externalStarDepth G letters requests m one)
    (secondDepth : ZFSet.pair w k ∈ M.externalStarDepth G letters requests m one) :
    (n = k ∨ n ∈ k) ∧ (n = k → v = w) := by
  have depthFunction := (data.externalStarDepth_ground_function group oldAction pairing unions powers separation infinite hG).2
  have hn := (ZFSet.pair_mem_prod.1 (depthFunction.1 firstDepth)).2
  have hk := (ZFSet.pair_mem_prod.1 (depthFunction.1 secondDepth)).2
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
  have laws := data.externalStarOwner_order_depth group oldAction pairing unions powers separation infinite hG
    lower first second firstDepth secondDepth
  refine ⟨?_, fun same => laws.2 (natSetCode_injective same)⟩
  rcases Nat.lt_or_eq_of_le laws.1 with less | same
  · exact Or.inr ((natSetCode_mem_iff _ _).2 less)
  · exact Or.inl (congrArg natSetCode same)

end PartitionPilot.Forcing.GroundExternalGeometryInputs




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



namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression Compression.RecursiveMaps.CosetGeometry
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
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "vcode" => completion.externalFamilyVertexCode group oldAction data.original
local notation "slots" => completion.externalTileSlotPoints P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG

theorem externalTileSlotPoints_entry :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index)
      (i : Option ((family).Child r)) (y : (family).Node (action)),
      ZFSet.pair (ZFSet.pair ((vpres).encode (.inr (w, r))) (vcode r i)) ((q).encode y) ∈ slots ↔
        ∃ x : SetMembers U,
          ((family).placedTile (action) w r).toFun (((family).flatVertex r i).toFun x) = y := by
  let := group.toGroup
  intro w r i y
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have vc := (data.externalStarPresentations_carriers group oldAction pairing unions powers separation infinite hG).1
  have acted := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.1
  rw [GroundCompressionCompletion.externalTileSlotPoints, pair_mem_externalTileSlotSupports]
  constructor
  · rintro ⟨_, _, _, w', _, r', _, x, hx, z, hz, equal, copied, moved⟩
    change ZFSet.pair (natSetCode 1) (ZFSet.pair ((s).encode w) (externalRequestIndexCode r)) =
      ZFSet.pair (natSetCode 1) (ZFSet.pair w' r') at equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 (ZFSet.pair_inj.1 equal).2
    obtain ⟨z, rfl⟩ := ((q).mem_carrier z).1 (qc.symm ▸ hz)
    let x' := SetMembers.ofMem x hx
    have copied' := (data.localTileVertexImages_entry_iff group oldAction pairing unions powers separation infinite hG
      r i x' z).1 (by simpa only [GroundCompressionCompletion.externalFamilyTileVertexPresentation_encode,
        x', SetMembers.raw_ofMem] using copied)
    have moved' := (acted w z y).1 moved
    rw [← copied', ← (family).flatVertex_copy, (family).translate_tile, mul_one] at moved'
    exact ⟨x', moved'⟩
  · rintro ⟨x, rfl⟩
    refine ⟨vc ▸ (vpres).encode_mem _, data.localTileVertexCode_mem group oldAction r i,
      qc ▸ (q).encode_mem _, (s).encode w, sc ▸ (s).encode_mem _, externalRequestIndexCode r,
      (externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem _,
      SetMembers.raw x, SetMembers.raw_mem x,
      (q).encode (((family).placedTile (action) 1 r).toFun (((family).flatVertex r i).toFun x)),
      qc ▸ (q).encode_mem _, rfl, ?_, ?_⟩
    · apply (data.localTileVertexImages_entry_iff group oldAction pairing unions powers separation infinite hG r i x _).2
      exact ((family).flatVertex_copy (action) 1 r i x).symm
    · apply (acted w _ _).2
      rw [(family).translate_tile, mul_one]

theorem externalTileSlotPoints_ground (hP0 : P0 ∈ M.sets) : slots ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have localGround := data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0
  exact M.externalTileSlotSupports_mem pairing unions powers separation infinite
    (data.externalStarCarriers_ground pairing unions powers separation hG).1 data.group.carrier_mem
    data.words.requests_ground (completion.algebra.union.ground 0) geometry.carrier_ground
    geometry.action_ground localGround.2.2.2.1

theorem externalTileSlotPoints_decode {v j x : ZFSet.{u}}
    (supported : ZFSet.pair (ZFSet.pair v j) x ∈ slots) :
    letI := group.toGroup
    ∃ (w : External (SetMembers G) (family).Letters) (r : Index)
      (i : Option ((family).Child r)) (a : SetMembers U),
      v = (vpres).encode (.inr (w, r)) ∧ j = vcode r i ∧
      x = (q).encode (((family).placedTile (action) w r).toFun (((family).flatVertex r i).toFun a)) := by
  let := group.toGroup
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have raw := (pair_mem_externalTileSlotSupports _ _ _ _ _ _ _ _ _ _).1 supported
  obtain ⟨_, _, hx, w, hw, r, hr, a, _, z, _, equal, copied, _⟩ := raw
  obtain ⟨w, rfl⟩ := ((s).mem_carrier w).1 (sc.symm ▸ hw)
  obtain ⟨r, rfl⟩ := ((externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).mem_carrier r).1 hr
  obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ hx)
  have vertex : ZFSet.pair (ZFSet.pair (externalRequestIndexCode r) j) a ∈
      completion.externalVertices P0 r0 μ0 A0 :=
    ((pair_mem_relationCompose _ _ _ _ _ _ _).1 copied).1
  have shape := (triple_mem_externalTileVertices _ _ _ _ _ _).1 vertex
  have range : j = natSetCode 0 ∨ j = natSetCode 1 ∨
      (externalRequestIndexCode r ∈ ZFSet.prod {natSetCode 2} (externalRectangles P0 G r0 μ0 A0) ∧
        j = natSetCode 2) := by tauto
  obtain ⟨i, rfl⟩ := (completion.externalFamilyVertexCode_range group oldAction data.original r j).1 range
  have ev : v = (vpres).encode (.inr (w, r)) := equal
  subst v
  obtain ⟨a, ha⟩ := (data.externalTileSlotPoints_entry group oldAction pairing unions powers separation infinite hG
    w r i x).1 supported
  exact ⟨w, r, i, a, rfl, rfl, congrArg (q).encode ha.symm⟩

theorem externalTileSlotPoints_owner_cover {x v : ZFSet.{u}}
    (fresh : x ∉ completion.externalSeedCarrier P0 r0 μ0 A0)
    (owned : ZFSet.pair x v ∈ completion.externalStarOwner P0 r0 μ0 A0) :
    ∃ j ∈ natSetCode 3, ZFSet.pair (ZFSet.pair v j) x ∈ slots := by
  let := group.toGroup
  obtain ⟨w, r, a, rfl, rfl, _⟩ := data.externalStarOwner_fresh_tile group oldAction pairing unions powers
    separation infinite hG x v owned fresh
  obtain ⟨i, b, rfl⟩ := (family).flatVertex_cover r a
  exact ⟨vcode r i, data.localTileVertexCode_mem group oldAction r i,
    (data.externalTileSlotPoints_entry group oldAction pairing unions powers separation infinite hG w r i _).2 ⟨b, rfl⟩⟩

theorem externalTileSlotPoints_lower {v j x y : ZFSet.{u}}
    (hx : x ∈ Q) (lower : ZFSet.pair x y ∈ completion.externalPointOrder P0 r0 μ0 A0)
    (supported : ZFSet.pair (ZFSet.pair v j) y ∈ slots) :
    ZFSet.pair (ZFSet.pair v j) x ∈ slots := by
  let := group.toGroup
  obtain ⟨w, r, i, a, rfl, rfl, rfl⟩ :=
    data.externalTileSlotPoints_decode group oldAction pairing unions powers separation infinite hG supported
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  obtain ⟨x, rfl⟩ := ((q).mem_carrier x).1 (qc.symm ▸ hx)
  have below := ((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).1 x _).1 lower
  rw [(family).flatVertex_copy] at below
  obtain ⟨b, equal⟩ := ((family).copy (action) ((family).flatWord w r i)).ideal a x below
  apply (data.externalTileSlotPoints_entry group oldAction pairing unions powers separation infinite hG w r i x).2
  exact ⟨b, ((family).flatVertex_copy (action) w r i b).trans equal⟩

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundDepthSlotCodes
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

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem depthSlotGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) : depthSlotGraph ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  have hThree := M.natSetCode_mem separation infinite 3
  have hMul := M.natMulGraph_mem pairing unions powers separation infinite
  have hAdd := M.natAddGraph_mem pairing unions powers separation infinite
  let params := extend ZFSet.omega (extend (natSetCode 3) (extend natMulGraph (extend natAddGraph Fin.elim0)))
  have selected := M.bounded_separation_mem separation BoundedFormula.depthSlotEntryFormula params
    (Fin.cases hOmega (Fin.cases hThree (Fin.cases hMul (Fin.cases hAdd (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hOmega hThree) hOmega)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.depthSlotEntryFormula (extend z params))
      (ZFSet.prod (ZFSet.prod ZFSet.omega (natSetCode 3)) ZFSet.omega) = depthSlotGraph := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep, BoundedFormula.truth_depthSlotEntryFormula, depthSlotGraph]
    rfl
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

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

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
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
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "slots" => completion.externalOwnerSlots P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG

theorem externalSeedCarrier_ground (hP0 : P0 ∈ M.sets) : P ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  exact M.relationImage_mem separation (completion.algebra.union.ground 0) geometry.carrier_ground
    (geometry.copies_ground _ data.group.group_code.identity_mem)

theorem externalOwnerSlots_ground_function (hP0 : P0 ∈ M.sets) :
    slots ∈ M.sets ∧ ZFSet.IsFunc (ownerFresh P B) (natSetCode 3) slots := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have owner := data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0
  refine ⟨M.leastSlotOwnerGraph_mem pairing unions powers separation infinite
    (data.externalSeedCarrier_ground group oldAction pairing unions powers separation infinite hG hP0)
    geometry.carrier_ground (data.externalStarCarriers_ground pairing unions powers separation hG).1 owner.1
    (data.externalTileSlotPoints_ground group oldAction pairing unions powers separation infinite hG hP0), ?_⟩
  apply leastSlotOwnerGraph_function owner.2
  intro x _ fresh v owned
  exact data.externalTileSlotPoints_owner_cover group oldAction pairing unions powers separation infinite hG fresh owned

theorem externalOwnerSlots_monotone (hP0 : P0 ∈ M.sets) {x y v w n j k : ZFSet.{u}}
    (lower : ZFSet.pair x y ∈ completion.externalPointOrder P0 r0 μ0 A0)
    (firstOwner : ZFSet.pair x v ∈ completion.externalStarOwner P0 r0 μ0 A0)
    (secondOwner : ZFSet.pair y w ∈ completion.externalStarOwner P0 r0 μ0 A0)
    (firstDepth : ZFSet.pair v n ∈ M.externalStarDepth G letters requests m one)
    (secondDepth : ZFSet.pair w n ∈ M.externalStarDepth G letters requests m one)
    (first : ZFSet.pair x j ∈ slots) (second : ZFSet.pair y k ∈ slots) : j = k ∨ j ∈ k := by
  apply leastSlotOwnerGraph_monotone first second
  · intro v' w' ownedX ownedY
    have function := (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
    have unique : FunctionGraphOn B (completion.externalStarOwner P0 r0 μ0 A0) := ⟨_, function⟩
    have vx := unique.unique ownedX firstOwner
    have wy := unique.unique ownedY secondOwner
    subst v'
    subst w'
    exact (data.externalStarOwner_order group oldAction pairing unions powers separation infinite hG
      lower firstOwner secondOwner firstDepth secondDepth).2 rfl
  · intro v _ j _ x hx y _ lower supported
    exact data.externalTileSlotPoints_lower group oldAction pairing unions powers separation infinite hG hx lower supported
  · exact lower

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "F" => ownerFresh P B
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "owners" => completion.externalStarOwner P0 r0 μ0 A0
local notation "depths" => M.externalStarDepth G letters requests m one
local notation "ownerDepth" => completion.externalOwnerDepth P0 r0 μ0 A0
local notation "slots" => completion.externalOwnerSlots P0 r0 μ0 A0
local notation "pairs" => completion.externalOwnerLevelPairs P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG

theorem externalOwnerDepth_ground_function (hP0 : P0 ∈ M.sets) :
    ownerDepth ∈ M.sets ∧ ZFSet.IsFunc B ZFSet.omega ownerDepth := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have owner := data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0
  have depth := data.externalStarDepth_ground_function group oldAction pairing unions powers separation infinite hG
  exact ⟨M.relationCompose_mem pairing unions powers separation geometry.carrier_ground
    (data.externalStarCarriers_ground pairing unions powers separation hG).1
    (M.omega_mem separation infinite) owner.1 depth.1,
    relationCompose_function_of_subset owner.2 depth.2 (fun _ h => h)⟩

theorem externalOwnerLevelPairs_ground_function (hP0 : P0 ∈ M.sets) :
    pairs ∈ M.sets ∧ ZFSet.IsFunc F (ZFSet.prod ZFSet.omega (natSetCode 3)) pairs := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have depth := data.externalOwnerDepth_ground_function group oldAction pairing unions powers separation infinite hG hP0
  have slot := data.externalOwnerSlots_ground_function group oldAction pairing unions powers separation infinite hG hP0
  exact ⟨M.pairedGraph_mem pairing unions powers separation
    (M.ownerFresh_mem separation
      (data.externalSeedCarrier_ground group oldAction pairing unions powers separation infinite hG hP0) geometry.carrier_ground)
    (M.omega_mem separation infinite) (M.natSetCode_mem separation infinite 3) depth.1 slot.1,
    pairedGraph_function_of_subset depth.2 slot.2 (fun x h => ((mem_ownerFresh P B x).1 h).1)⟩

theorem externalOwnerLevels_ground_function (hP0 : P0 ∈ M.sets) :
    levels ∈ M.sets ∧ ZFSet.IsFunc F ZFSet.omega levels := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have pairCode := data.externalOwnerLevelPairs_ground_function group oldAction pairing unions powers separation infinite hG hP0
  have hOmega := M.omega_mem separation infinite
  exact ⟨M.relationCompose_mem pairing unions powers separation
    (M.ownerFresh_mem separation
      (data.externalSeedCarrier_ground group oldAction pairing unions powers separation infinite hG hP0) geometry.carrier_ground)
    (M.prod_mem pairing unions powers separation hOmega (M.natSetCode_mem separation infinite 3)) hOmega
    pairCode.1 (M.depthSlotGraph_mem pairing unions powers separation infinite),
    relationCompose_function_of_subset pairCode.2 depthSlotGraph_function (fun _ h => h)⟩

theorem externalOwnerLevels_entry_iff (hP0 : P0 ∈ M.sets) (x : ZFSet.{u}) (k : Nat) :
    ZFSet.pair x (natSetCode k) ∈ levels ↔ x ∈ F ∧
      ∃ v, ∃ n j : Nat, j < 3 ∧ ZFSet.pair x v ∈ owners ∧
        ZFSet.pair v (natSetCode n) ∈ depths ∧ ZFSet.pair x (natSetCode j) ∈ slots ∧
          k = depthSlotIndex n j := by
  change ZFSet.pair x (natSetCode k) ∈ relationCompose F (ZFSet.prod ZFSet.omega (natSetCode 3))
    ZFSet.omega pairs depthSlotGraph ↔ _
  rw [pair_mem_relationCompose]
  constructor
  · rintro ⟨hx, _, p, hp, pairEntry, rankEntry⟩
    obtain ⟨n, hn, j, hj, rfl⟩ := ZFSet.mem_prod.1 hp
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    obtain ⟨j, bound, rfl⟩ := (mem_natSetCode j 3).1 hj
    have pairParts := (pair_mem_pairedGraph _ _ _ _ _ _ _ _).1 pairEntry
    obtain ⟨_, _, v, _, owned, depth⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 pairParts.2.2.2.1
    exact ⟨hx, v, n, j, bound, owned, depth, pairParts.2.2.2.2,
      ((pair_mem_depthSlotGraph n j k).1 rankEntry).2⟩
  · rintro ⟨hx, v, n, j, bound, owned, depth, slot, rfl⟩
    have owner := (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
    have hv := (ZFSet.pair_mem_prod.1 (owner.1 owned)).2
    have hn := natSetCode_mem_omega n
    have hj := (natSetCode_mem_iff j 3).2 bound
    refine ⟨hx, natSetCode_mem_omega _, ZFSet.pair (natSetCode n) (natSetCode j),
      ZFSet.pair_mem_prod.2 ⟨hn, hj⟩, ?_, (pair_mem_depthSlotGraph n j _).2 ⟨bound, rfl⟩⟩
    apply (pair_mem_pairedGraph _ _ _ _ _ _ _ _).2
    refine ⟨hx, hn, hj, ?_, slot⟩
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨((mem_ownerFresh P B x).1 hx).1, hn, v, hv, owned, depth⟩

theorem externalOwnerLevels_monotone (hP0 : P0 ∈ M.sets) {x y : ZFSet.{u}} {k l : Nat}
    (lower : ZFSet.pair x y ∈ completion.externalPointOrder P0 r0 μ0 A0)
    (first : ZFSet.pair x (natSetCode k) ∈ levels)
    (second : ZFSet.pair y (natSetCode l) ∈ levels) : k ≤ l := by
  obtain ⟨_, v, n, j, hj, xv, vn, xj, rfl⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 x k).1 first
  obtain ⟨_, w, m, i, hi, yw, wm, yi, rfl⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 y l).1 second
  have depthOrder := data.externalStarOwner_order_depth group oldAction pairing unions powers separation infinite hG
    lower xv yw vn wm
  apply (depthSlotIndex_le_iff hj hi).2
  rcases Nat.lt_or_eq_of_le depthOrder.1 with less | same
  · exact Or.inl less
  · subst m
    have slotOrder := data.externalOwnerSlots_monotone group oldAction pairing unions powers separation infinite hG hP0
      lower xv yw vn wm xj yi
    refine Or.inr ⟨rfl, ?_⟩
    rcases slotOrder with equal | less
    · exact (natSetCode_injective equal).le
    · exact ((natSetCode_mem_iff j i).1 less).le

end GroundExternalGeometryInputs

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula SetRealization
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
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "owners" => completion.externalStarOwner P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG

theorem externalOwnerLevels_meet_lower (hP0 : P0 ∈ M.sets)
    {x y z v w : ZFSet.{u}} {k l : Nat}
    (firstOwner : ZFSet.pair x v ∈ owners) (secondOwner : ZFSet.pair y w ∈ owners)
    (different : v ≠ w) (first : ZFSet.pair x (natSetCode k) ∈ levels)
    (second : ZFSet.pair y (natSetCode k) ∈ levels)
    (meetEntry : ZFSet.pair (ZFSet.pair x y) z ∈ completion.externalPointMeet P0 r0 μ0 A0)
    (third : ZFSet.pair z (natSetCode l) ∈ levels) : l < k := by
  obtain ⟨_, v', n, j, hj, xv, vn, xj, eqK⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 x k).1 first
  obtain ⟨_, w', m, i, hi, yw, wm, yi, eqK'⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 y k).1 second
  obtain ⟨_, u, p, q, hq, zu, up, zq, eqL⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 z l).1 third
  have ownerCode : FunctionGraphOn B owners :=
    ⟨_, (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2⟩
  have hv := ownerCode.unique xv firstOwner
  have hw := ownerCode.unique yw secondOwner
  subst v'
  subst w'
  have same := ((depthSlotIndex_eq_iff hj hi).1 (eqK.symm.trans eqK')).1
  subst m
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have left := data.externalStarOwner_order_depth group oldAction pairing unions powers separation infinite hG
    (geometry.meet.lower_left x y z meetEntry) zu firstOwner up vn
  have right := data.externalStarOwner_order_depth group oldAction pairing unions powers separation infinite hG
    (geometry.meet.lower_right x y z meetEntry) zu secondOwner up wm
  have less : p < n := by
    apply Nat.lt_of_le_of_ne left.1
    intro equal
    exact different ((left.2 equal).symm.trans (right.2 equal))
  rw [eqL, eqK]
  exact (depthSlotIndex_lt_iff hq hj).2 (Or.inl less)

theorem externalOwnerLevels_meet_old_or_lower (hP0 : P0 ∈ M.sets)
    {x y z v w : ZFSet.{u}} {k : Nat}
    (firstOwner : ZFSet.pair x v ∈ owners) (secondOwner : ZFSet.pair y w ∈ owners)
    (different : v ≠ w) (first : ZFSet.pair x (natSetCode k) ∈ levels)
    (second : ZFSet.pair y (natSetCode k) ∈ levels)
    (meetEntry : ZFSet.pair (ZFSet.pair x y) z ∈ completion.externalPointMeet P0 r0 μ0 A0) :
    z ∈ P ∨ ∃ l < k, ZFSet.pair z (natSetCode l) ∈ levels := by
  by_cases old : z ∈ P
  · exact Or.inl old
  · have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
    have hz := (ZFSet.pair_mem_prod.1 (geometry.meet.order.relation (geometry.meet.lower_left x y z meetEntry))).1
    have code := (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
    obtain ⟨l, entry, _⟩ := code.2 z ((mem_ownerFresh P B z).2 ⟨hz, old⟩)
    have hl := (ZFSet.pair_mem_prod.1 (code.1 entry)).2
    obtain ⟨l, rfl⟩ := (mem_omega_iff_natSetCode l).1 hl
    exact Or.inr ⟨l, data.externalOwnerLevels_meet_lower group oldAction pairing unions powers separation infinite hG hP0
      firstOwner secondOwner different first second meetEntry entry, entry⟩

end PartitionPilot.Forcing.GroundExternalGeometryInputs

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula SetRealization Compression.RecursiveMaps.CosetGeometry
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
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "V" => M.externalStarVertices G letters requests m one
local notation "owners" => completion.externalStarOwner P0 r0 μ0 A0
local notation "depths" => M.externalStarDepth G letters requests m one
local notation "supports" => completion.externalStarSupports P0 r0 μ0 A0
local notation "slotPoints" => completion.externalTileSlotPoints P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0
local notation "family" => completion.externalFamily group oldAction data.original
include data group oldAction pairing unions powers separation infinite hG

theorem externalTileSlotPoints_support {v j x : ZFSet.{u}}
    (supported : ZFSet.pair (ZFSet.pair v j) x ∈ slotPoints) : ZFSet.pair v x ∈ supports := by
  let := group.toGroup
  obtain ⟨w, r, i, a, rfl, rfl, rfl⟩ :=
    data.externalTileSlotPoints_decode group oldAction pairing unions powers separation infinite hG supported
  apply (data.externalStarSupports_iff group oldAction pairing unions powers separation infinite hG _ _).2
  exact ⟨((family).flatVertex r i).toFun a, rfl⟩

theorem externalOwnerLevels_slot_bound (hP0 : P0 ∈ M.sets) {v x : ZFSet.{u}} {n j k : Nat}
    (supported : ZFSet.pair (ZFSet.pair v (natSetCode j)) x ∈ slotPoints)
    (depth : ZFSet.pair v (natSetCode n) ∈ depths)
    (level : ZFSet.pair x (natSetCode k) ∈ levels) : k ≤ depthSlotIndex n j := by
  obtain ⟨hx, u, d, i, hi, owned, ownerDepth, slot, equal⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 x k).1 level
  have support := data.externalTileSlotPoints_support group oldAction pairing unions powers separation infinite hG supported
  have shape := (pair_mem_externalTileSlotSupports _ _ _ _ _ _ _ _ _ _).1 supported
  have hj := shape.2.1
  have ownerFunction := (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  have depthCode : FunctionGraphOn V depths :=
    ⟨_, (data.externalStarDepth_ground_function group oldAction pairing unions powers separation infinite hG).2⟩
  have least := (pair_mem_leastSupportGraph _ _ _ _ _ _).1 owned
  obtain ⟨a, _, ua, minimal⟩ := least.2.2.2
  have eqA := depthCode.unique ua ownerDepth
  subst a
  have before : d ≤ n := Nat.le_of_not_gt (fun less => minimal v shape.1 (natSetCode n)
    (natSetCode_mem_omega n) support depth ((natSetCode_mem_iff n d).2 less))
  rw [equal]
  apply (depthSlotIndex_le_iff hi ((natSetCode_mem_iff j 3).1 hj)).2
  rcases Nat.lt_or_eq_of_le before with less | same
  · exact Or.inl less
  · subst d
    have tileOwned : ZFSet.pair x v ∈ owners :=
      (pair_mem_leastSupportGraph _ _ _ _ _ _).2
        ⟨((mem_ownerFresh P B x).1 hx).1, shape.1, support,
          natSetCode n, natSetCode_mem_omega n, depth, minimal⟩
    have leastSlot := ((pair_mem_leastSlotOwnerGraph_of_owner ownerFunction tileOwned).1 slot).2.2
    have slotOrder := leastSlot.le ((natSetCode_mem_iff i 3).2 hi) hj supported
    refine Or.inr ⟨rfl, ?_⟩
    rcases slotOrder with same | less
    · exact (natSetCode_injective same).le
    · exact ((natSetCode_mem_iff i j).1 less).le

theorem externalSlotCopy_old_or_level_bound (hP0 : P0 ∈ M.sets)
    {v x : ZFSet.{u}} {n j : Nat}
    (supported : ZFSet.pair (ZFSet.pair v (natSetCode j)) x ∈ slotPoints)
    (depth : ZFSet.pair v (natSetCode n) ∈ depths) :
    x ∈ P ∨ ∃ k ≤ depthSlotIndex n j, ZFSet.pair x (natSetCode k) ∈ levels := by
  by_cases old : x ∈ P
  · exact Or.inl old
  · have shape := (pair_mem_externalTileSlotSupports _ _ _ _ _ _ _ _ _ _).1 supported
    have function := (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
    obtain ⟨k, level, _⟩ := function.2 x ((mem_ownerFresh P B x).2 ⟨shape.2.2.1, old⟩)
    have hk := (ZFSet.pair_mem_prod.1 (function.1 level)).2
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
    exact Or.inr ⟨k, data.externalOwnerLevels_slot_bound group oldAction pairing unions powers separation infinite hG hP0
      supported depth level, level⟩

end PartitionPilot.Forcing.GroundExternalGeometryInputs

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


namespace PartitionPilot.Forcing
universe u

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P r μ A oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalBirthData M initial I Sources Reps G m one T τ P r μ A oldTimes oldBirth completion)

include data
theorem old_before {x a : ZFSet.{u}}
    (entry : ZFSet.pair x a ∈ completion.externalSeedBirth P r μ A oldTimes oldBirth) (n : Nat) :
    a ∈ compressionStamp oldTimes n :=
  compressionStamp_old_mem (Or.inl (ZFSet.pair_mem_prod.1 (data.seed_function.1 entry)).2) n

theorem no_limit_birth (x : ZFSet.{u}) : ZFSet.pair x data.limit ∉ data.birth :=
  fun entry => ZFSet.mem_irrefl data.limit (ZFSet.pair_mem_prod.1 (data.function.1 entry)).2

end GroundExternalBirthData

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression Compression.RecursiveMaps.CosetGeometry
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
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0

noncomputable def externalBirthCopyVertex (k : Nat) (r : Index) : Option ((family).Child r) := by
  classical
  exact if h : ∃ i, ((family).request r).vertexSlot i = k % 3 then Classical.choose h else none

theorem externalBirthCopyVertex_eq (k : Nat) (r : Index) (i : Option ((family).Child r))
    (slot : ((family).request r).vertexSlot i = k % 3) :
    data.externalBirthCopyVertex group oldAction k r = i := by
  classical
  have existsSlot : ∃ j, ((family).request r).vertexSlot j = k % 3 := ⟨i, slot⟩
  simp only [externalBirthCopyVertex, dite_eq_left existsSlot]
  exact ((family).request r).vertexSlot_injective ((Classical.choose_spec existsSlot).trans slot.symm)

include data group oldAction pairing unions powers separation infinite hG

theorem externalBirthCopy_witness (hP0 : P0 ∈ M.sets) (k : Nat) {x : ZFSet.{u}}
    (level : ZFSet.pair x (natSetCode k) ∈ completion.externalOwnerLevels P0 r0 μ0 A0) :
    letI := group.toGroup
    ∃ w r, ZFSet.pair x ((vpres).encode (.inr (w, r))) ∈ completion.externalStarOwner P0 r0 μ0 A0 ∧
      x ∈ relationImage U B (completion.externalCopyGraph P0 r0 μ0 A0
        ((s).encode ((family).flatWord w r (data.externalBirthCopyVertex group oldAction k r)))) := by
  let := group.toGroup
  have owner := (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  obtain ⟨_, v, n, j, hj, owned, _, slot, rank⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 x k).1 level
  have selected := (pair_mem_leastSlotOwnerGraph_of_owner owner owned).1 slot
  obtain ⟨w, r, i, a, eqV, eqJ, eqX⟩ :=
    data.externalTileSlotPoints_decode group oldAction pairing unions powers separation infinite hG selected.2.2.1
  have ji : j = ((family).request r).vertexSlot i := by
    apply natSetCode_injective
    exact eqJ.trans (completion.externalFamilyVertexCode_eq_slot group oldAction data.original r i)
  have chosen : data.externalBirthCopyVertex group oldAction k r = i := by
    apply data.externalBirthCopyVertex_eq group oldAction
    rw [← ji, rank, depthSlotIndex, Nat.add_mod]
    simp only [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt hj]
  refine ⟨w, r, eqV ▸ owned, ?_⟩
  rw [chosen, eqX, (family).flatVertex_copy]
  have qc := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  rw [data.externalCopyGraph_eq_graph group oldAction pairing unions powers separation infinite hG]
  apply (mem_relationImage _ _ _ _).2
  exact ⟨qc ▸ (q).encode_mem _, SetMembers.raw a, SetMembers.raw_mem a,
    ((SetMembers.presentation U).pair_mem_graph (q) _ a _).2 rfl⟩

end PartitionPilot.Forcing.GroundExternalGeometryInputs



namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula SetRealization Compression.RecursiveMaps.CosetGeometry
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
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "U" => completion.algebra.union.fields 0
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "owners" => completion.externalStarOwner P0 r0 μ0 A0
local notation "depths" => M.externalStarDepth G letters requests m one
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0
local notation "family" => completion.externalFamily group oldAction data.original
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
include data group oldAction pairing unions powers separation infinite hG

theorem externalBirthCopy_level_slot (hP0 : P0 ∈ M.sets) :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index) (k : Nat) {x : ZFSet.{u}},
      ZFSet.pair x ((vpres).encode (.inr (w, r))) ∈ owners →
      ZFSet.pair x (natSetCode k) ∈ levels →
        ∃ n, ZFSet.pair ((vpres).encode (.inr (w, r))) (natSetCode n) ∈ depths ∧
          k = depthSlotIndex n (((family).request r).vertexSlot (data.externalBirthCopyVertex group oldAction k r)) := by
  let := group.toGroup
  intro w r k x active level
  obtain ⟨_, v, n, j, hj, owned, depth, slot, rank⟩ :=
    (data.externalOwnerLevels_entry_iff group oldAction pairing unions powers separation infinite hG hP0 x k).1 level
  have owner := (data.externalStarOwner_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  have sameOwner := (show FunctionGraphOn B owners from ⟨_, owner⟩).unique owned active
  subst v
  have selected := (pair_mem_leastSlotOwnerGraph_of_owner owner active).1 slot
  obtain ⟨w', r', i, _, eqV, eqJ, _⟩ :=
    data.externalTileSlotPoints_decode group oldAction pairing unions powers separation infinite hG selected.2.2.1
  have same := Sum.inr.inj ((vpres).injective eqV)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  have ji : j = ((family).request r).vertexSlot i :=
    natSetCode_injective (eqJ.trans (completion.externalFamilyVertexCode_eq_slot group oldAction data.original r i))
  have chosen : data.externalBirthCopyVertex group oldAction k r = i := by
    apply data.externalBirthCopyVertex_eq group oldAction
    rw [← ji, rank, depthSlotIndex, Nat.add_mod]
    simp only [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt hj]
  exact ⟨n, depth, by rw [chosen, ← ji]; exact rank⟩

theorem externalBirthCopy_level_bound (hP0 : P0 ∈ M.sets) :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters) (r : Index) (k : Nat) {x u y : ZFSet.{u}},
      ZFSet.pair x ((vpres).encode (.inr (w, r))) ∈ owners →
      ZFSet.pair x (natSetCode k) ∈ levels →
      ZFSet.pair u y ∈ completion.externalCopyGraph P0 r0 μ0 A0
        ((s).encode ((family).flatWord w r (data.externalBirthCopyVertex group oldAction k r))) →
      y ∈ P ∨ ∃ l ≤ k, ZFSet.pair y (natSetCode l) ∈ levels := by
  let := group.toGroup
  intro w r k x u y active level copied
  obtain ⟨n, depth, rank⟩ := data.externalBirthCopy_level_slot group oldAction pairing unions powers separation infinite hG hP0
    w r k active level
  let i := data.externalBirthCopyVertex group oldAction k r
  rw [data.externalCopyGraph_eq_graph group oldAction pairing unions powers separation infinite hG] at copied
  obtain ⟨a, equal⟩ := ((SetMembers.presentation U).mem_graph (q) _ _).1 copied
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  have supported := (data.externalTileSlotPoints_entry group oldAction pairing unions powers separation infinite hG
    w r i ((family).copy (action) ((family).flatWord w r i) |>.toFun a)).2
    ⟨a, (family).flatVertex_copy (action) w r i a⟩
  rw [completion.externalFamilyVertexCode_eq_slot group oldAction data.original r i] at supported
  have bound := data.externalSlotCopy_old_or_level_bound group oldAction pairing unions powers separation infinite hG hP0
    supported depth
  rw [← rank] at bound
  exact bound

end PartitionPilot.Forcing.GroundExternalGeometryInputs




namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0
local notation "owner" => completion.externalStarOwner P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG hP0 births

noncomputable def externalBirth_fresh_layer
    (Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u})
    (atSpace : Space oldTimes = U)
    (atOrder : sourceOrder oldTimes = completion.algebra.union.fields 1)
    (atMeet : sourceMeet oldTimes = completion.algebra.union.fields 2) (k : Nat) :
    CodedGrowthLayer M Space sourceOrder sourceMeet B (completion.externalPointOrder P0 r0 μ0 A0)
      (completion.externalPointMeet P0 r0 μ0 A0) births.birth (compressionStamp oldTimes k) := by
  classical
  letI := group.toGroup
  let Copies := External (SetMembers G) (family).Letters × Index
  let e (v : Copies) := completion.externalCopyGraph P0 r0 μ0 A0
    ((s).encode ((family).flatWord v.1 v.2 (data.externalBirthCopyVertex group oldAction k v.2)))
  let Slice := {x : ZFSet.{u} // x ∈ ownerFresh P B ∧ ZFSet.pair x (natSetCode k) ∈ levels}
  have witnesses (x : Slice) : ∃ v : Copies,
      ZFSet.pair x.val ((vpres).encode (.inr v)) ∈ owner ∧ x.val ∈ relationImage U B (e v) := by
    obtain ⟨w, r, owned, covered⟩ :=
      data.externalBirthCopy_witness group oldAction pairing unions powers separation infinite hG hP0 k x.property.2
    exact ⟨(w, r), owned, covered⟩
  let pick (x : Slice) : Copies := Classical.choose (witnesses x)
  have selected (x : Slice) :
      ZFSet.pair x.val ((vpres).encode (.inr (pick x))) ∈ owner ∧
        x.val ∈ relationImage U B (e (pick x)) := Classical.choose_spec (witnesses x)
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have levelCode := (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have oldSubset : P ⊆ B := fun _ hx => ((mem_relationImage _ _ _ _).1 hx).1
  have times : oldTimes ⊆ births.limit := fun _ ht =>
    births.times.union.subset 0 (compressionStamp_old_mem (Or.inl ht) 0)
  have oldBefore : ∀ x a n t, ZFSet.pair x a ∈ completion.externalSeedBirth P0 r0 μ0 A0 oldTimes oldBirth →
      ZFSet.pair (natSetCode n) t ∈ births.stamps → a ∈ t := by
    intro x a n t entry stamp
    rw [(births.times.entries n t).1 stamp]
    exact births.old_before entry n
  refine ownerBirthGraph_separated births.seed_function oldSubset times levelCode births.times.ownerStampCode
    oldBefore ((births.times.entries k _).2 rfl) Copies (fun _ => oldTimes) e
    (fun _ => compressionStamp_base_mem oldTimes k) ?_ ?_ pick ?_ ?_
  · intro v
    exact geometry.copies_ground _ (sc ▸ (s).encode_mem _)
  · intro v
    rw [atSpace, atOrder, atMeet]
    exact geometry.copies _ (sc ▸ (s).encode_mem _)
  · intro x _
    rw [atSpace]
    exact (selected x).2
  · intro x y _ _ different
    have differentOwners : (vpres).encode (.inr (pick x)) ≠ (vpres).encode (.inr (pick y)) := by
      intro equal
      exact different (Sum.inr.inj ((vpres).injective equal))
    have hx := ((mem_ownerFresh P B x.val).1 x.property.1).1
    have hy := ((mem_ownerFresh P B y.val).1 y.property.1).1
    obtain ⟨z, meetEntry, _⟩ := geometry.meet.operation.2 (ZFSet.pair x.val y.val) (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    refine ⟨z, (ZFSet.pair_mem_prod.1 (geometry.meet.operation.1 meetEntry)).2, meetEntry, ?_⟩
    exact data.externalOwnerLevels_meet_old_or_lower group oldAction pairing unions powers separation infinite hG hP0
      (selected x).1 (selected y).1 differentOwners x.property.2 y.property.2 meetEntry

end PartitionPilot.Forcing.GroundExternalGeometryInputs

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


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem chronologyRestriction_mem (kind : Fin 3) {P f : ZFSet.{u}}
    (hP : P ∈ M.sets) (hf : f ∈ M.sets) : chronologyRestriction kind P f ∈ M.sets := by
  exact Fin.cases (M.graphRestriction_mem unions separation hP hf)
    (Fin.cases (M.heightOrderRestriction_mem pairing unions powers separation hP hf)
      (fun _ => M.graphRestriction_mem unions separation
        (M.prod_mem pairing unions powers separation hP hP) hf)) kind

theorem chronologyRestrictionFamily_entries (kind : Fin 3) {I Ps f : ZFSet.{u}}
    (hPs : Ps ∈ M.sets) (hf : f ∈ M.sets) (function : FunctionGraphOn I Ps)
    {i P : ZFSet.{u}} (entry : ZFSet.pair i P ∈ Ps) (q : ZFSet.{u}) :
    ZFSet.pair i q ∈ M.chronologyRestrictionFamily kind I Ps f ↔
      q = chronologyRestriction kind P f := by
  constructor
  · intro member
    obtain ⟨_, j, _, Q, _, w, _, equal, input, output⟩ := ZFSet.mem_sep.1 member
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.1 equal
    exact function.unique input entry ▸ output
  · intro equal
    have hP := M.pair_right (M.transitive hPs entry)
    have subset : chronologyRestriction kind P f ⊆ f := by
      exact Fin.cases (graphRestriction_subset _ _)
        (Fin.cases (fun _ hz => (ZFSet.mem_sep.1 hz).1)
          (fun _ => graphRestriction_subset _ _)) kind
    have bound := (M.mem_groundPower f q).2 ⟨equal.symm ▸
      M.chronologyRestriction_mem pairing unions powers separation kind hP hf,
      fun z hz => subset (equal ▸ hz)⟩
    have hi := (ZFSet.pair_mem_prod.1 (function.to_isFunc.1 entry)).1
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi,bound⟩, i,hi,P,
      pair_second_mem_doubleUnion entry,q,bound,rfl,entry,equal⟩

theorem chronologyRestrictionFamily_function (kind : Fin 3) {I Ps f : ZFSet.{u}}
    (hPs : Ps ∈ M.sets) (hf : f ∈ M.sets) (function : FunctionGraphOn I Ps) :
    ZFSet.IsFunc I (M.groundPower f) (M.chronologyRestrictionFamily kind I Ps f) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro i hi
  obtain ⟨P, entry, _⟩ := function.to_isFunc.2 i hi
  have exactEntries := M.chronologyRestrictionFamily_entries pairing unions powers separation kind hPs hf function entry
  exact ⟨chronologyRestriction kind P f, (exactEntries _).2 rfl, fun q hq => (exactEntries q).1 hq⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "r" => completion.externalPointOrder P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0

noncomputable def cutoffFamily (_births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion) : ZFSet.{u} :=
  M.ownerLevelPrefixFamily P B levels

variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)

theorem cutoff_old (n : Nat) : P ⊆ births.cutoff n := ownerLevelPrefix_old _ _ _ _

theorem cutoff_birth_function (n : Nat) :
    ZFSet.IsFunc (births.cutoff n) births.limit (births.cutoffBirth n) := by
  have restricted := (show FunctionGraphOn B births.birth from ⟨births.limit, births.function⟩).restrict (births.cutoff_subset n)
  apply isFunc_retarget_of_entries restricted.to_isFunc
  intro x t entry
  exact (ZFSet.pair_mem_prod.1 (births.function.1 (pair_mem_graphRestriction.1 entry).1)).2

theorem cutoff_old_meet (n : Nat) : OldMeetCode (births.cutoffOrder n) (births.cutoffMeet n) (births.cutoffBirth n) := by
  intro x y z a b c ya xb before notLower xy zc
  have hx := (pair_mem_graphRestriction.1 xb).2
  have hy := (pair_mem_graphRestriction.1 ya).2
  exact births.old_meet x y z a b c (pair_mem_graphRestriction.1 ya).1 (pair_mem_graphRestriction.1 xb).1 before
    (fun lower => notLower ((pair_mem_heightOrderRestriction _ _ _ _).2 ⟨lower, hx, hy⟩))
    (pair_mem_graphRestriction.1 xy).1 (pair_mem_graphRestriction.1 zc).1

theorem cutoff_birth_bound
    (levelFunction : ZFSet.IsFunc (ownerFresh P B) ZFSet.omega levels)
    (n : Nat) {x t : ZFSet.{u}} (entry : ZFSet.pair x t ∈ births.cutoffBirth n) :
    t ∈ compressionStamp oldTimes n ∨ t = compressionStamp oldTimes n := by
  classical
  obtain ⟨entry, hx⟩ := pair_mem_graphRestriction.1 entry
  by_cases old : x ∈ P
  · exact Or.inl (births.old_before ((ownerBirthGraph_old_iff old).1 entry) n)
  · obtain ⟨_, k, hk, level, bound⟩ := (mem_ownerLevelPrefix_fresh old).1 hx
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
    obtain ⟨_, _, j, actualLevel, stamp⟩ := (ownerBirthGraph_fresh_nat_iff births.seed_function old).1 entry
    have equal : j = k := natSetCode_injective
      ((show FunctionGraphOn (ownerFresh P B) levels from ⟨ZFSet.omega, levelFunction⟩).unique actualLevel level)
    subst j
    rw [(births.times.entries k t).1 stamp]
    rcases bound with same | before
    · exact Or.inr (congrArg (compressionStamp oldTimes) (natSetCode_injective same))
    · exact Or.inl ((compressionStamp_mem_iff oldTimes k n).2 ((natSetCode_mem_iff _ _).1 before))

variable {inv : ZFSet.{u}}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
include data group action pairing unions powers separation infinite hG hP0

theorem cutoffFamily_spec : births.cutoffFamily ∈ M.sets ∧ FunctionGraphOn ZFSet.omega births.cutoffFamily ∧
    ∀ n : Nat, ∀ Q, ZFSet.pair (natSetCode n) Q ∈ births.cutoffFamily ↔ Q = births.cutoff n := by
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
  have hSeed := data.externalSeedCarrier_ground group action pairing unions powers separation infinite hG hP0
  have hLevels := (data.externalOwnerLevels_ground_function group action pairing unions powers separation infinite hG hP0).1
  have spec := M.ownerLevelPrefixFamily_spec pairing unions powers separation infinite hSeed geometry.carrier_ground hLevels
    (fun _ hx => (mem_relationImage _ _ _ _).1 hx |>.1)
  exact ⟨spec.1, spec.2.1, fun n Q => (spec.2.2 (natSetCode n) Q).trans (and_iff_right (natSetCode_mem_omega n))⟩

theorem cutoff_lower (n : Nat) :
    ∀ x ∈ B, ∀ y ∈ births.cutoff n, ZFSet.pair x y ∈ r → x ∈ births.cutoff n := by
  have levelFunction := (data.externalOwnerLevels_ground_function group action pairing unions powers separation infinite hG hP0).2
  apply ownerLevelPrefix_lower (natSetCode_mem_omega n)
    (fun _ hx _ hy lower => data.externalSeedCarrier_lower group action pairing unions powers separation infinite hG hx hy lower) levelFunction
  intro x _ _ y _ _ k l first second lower
  have hk := (ZFSet.pair_mem_prod.1 (levelFunction.1 first)).2
  have hl := (ZFSet.pair_mem_prod.1 (levelFunction.1 second)).2
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
  obtain ⟨l, rfl⟩ := (mem_omega_iff_natSetCode l).1 hl
  have before := data.externalOwnerLevels_monotone group action pairing unions powers separation infinite hG hP0 lower first second
  rcases Nat.lt_or_eq_of_le before with less | same
  · exact Or.inr ((natSetCode_mem_iff _ _).2 less)
  · exact Or.inl (congrArg natSetCode same)

theorem cutoff_fields {C D rD lo hi seed : ZFSet.{u}}
    (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 C D rD lo hi seed completion)
    (n : Nat) :
    births.cutoff n ∈ M.sets ∧ births.cutoffOrder n ∈ M.sets ∧ births.cutoffMeet n ∈ M.sets ∧
      births.cutoffBirth n ∈ M.sets ∧ births.cutoffHeight heights.height n ∈ M.sets ∧
      MeetOrderCode (births.cutoff n) (births.cutoffOrder n) (births.cutoffMeet n) ∧
      ZFSet.IsFunc (births.cutoff n) births.limit (births.cutoffBirth n) ∧
      OldMeetCode (births.cutoffOrder n) (births.cutoffMeet n) (births.cutoffBirth n) ∧
      StrictLexHeightCode (births.cutoff n) C D (births.cutoffOrder n) (births.cutoffHeight heights.height n) rD ∧
      ∀ x t, ZFSet.pair x t ∈ births.cutoffBirth n → t ∈ compressionStamp oldTimes n ∨ t = compressionStamp oldTimes n := by
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
  have levelCode := data.externalOwnerLevels_ground_function group action pairing unions powers separation infinite hG hP0
  have hSeed := data.externalSeedCarrier_ground group action pairing unions powers separation infinite hG hP0
  have hQ := M.ownerLevelPrefix_mem pairing unions powers separation infinite hSeed geometry.carrier_ground levelCode.1
    (fun _ hx => (mem_relationImage _ _ _ _).1 hx |>.1) (natSetCode_mem_omega n)
  refine ⟨hQ, M.heightOrderRestriction_mem pairing unions powers separation hQ geometry.order_ground,
    M.graphRestriction_mem unions separation (M.prod_mem pairing unions powers separation hQ hQ) geometry.meet_ground,
    M.graphRestriction_mem unions separation hQ births.birth_ground,
    M.graphRestriction_mem unions separation hQ heights.height_ground,
    geometry.meet.restrict_lower (births.cutoff_subset n)
      (births.cutoff_lower data group action pairing unions powers separation infinite hG hP0 n),
    births.cutoff_birth_function n, births.cutoff_old_meet n,
    heights.code.restrict_order (births.cutoff_subset n), ?_⟩
  intro x t entry
  exact births.cutoff_birth_bound levelCode.2 n entry

end PartitionPilot.Forcing.GroundExternalBirthData



namespace PartitionPilot.Forcing.GroundExternalBirthData
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundChronologicalHistory M T0 C D rD)

noncomputable def chronologyFields : CompressionChronologyFields.{u} where
  space := compressionPrefixValue oldTimes births.limit prior.space births.cutoff
    (completion.externalPointCarrier P0 r0 μ0 A0)
  order := compressionPrefixValue oldTimes births.limit prior.order births.cutoffOrder
    (completion.externalPointOrder P0 r0 μ0 A0)
  meetGraph := compressionPrefixValue oldTimes births.limit prior.meetGraph births.cutoffMeet
    (completion.externalPointMeet P0 r0 μ0 A0)
  birth := compressionPrefixValue oldTimes births.limit prior.birth births.cutoffBirth births.birth
  height := compressionPrefixValue oldTimes births.limit prior.height (births.cutoffHeight heights.height) heights.height

theorem chronologyFields_old {s : ZFSet.{u}} (before : s ∈ oldTimes ∨ s = oldTimes) :
    (births.chronologyFields heights prior).space s = prior.space s ∧
    (births.chronologyFields heights prior).order s = prior.order s ∧
    (births.chronologyFields heights prior).meetGraph s = prior.meetGraph s ∧
    (births.chronologyFields heights prior).birth s = prior.birth s ∧
    (births.chronologyFields heights prior).height s = prior.height s := by
  dsimp only [chronologyFields]
  exact ⟨compressionPrefixValue_old _ _ _ before, compressionPrefixValue_old _ _ _ before,
    compressionPrefixValue_old _ _ _ before, compressionPrefixValue_old _ _ _ before,
    compressionPrefixValue_old _ _ _ before⟩

theorem chronologyFields_stamp (n : Nat) :
    (births.chronologyFields heights prior).space (compressionStamp oldTimes n) = births.cutoff n ∧
    (births.chronologyFields heights prior).order (compressionStamp oldTimes n) = births.cutoffOrder n ∧
    (births.chronologyFields heights prior).meetGraph (compressionStamp oldTimes n) = births.cutoffMeet n ∧
    (births.chronologyFields heights prior).birth (compressionStamp oldTimes n) = births.cutoffBirth n ∧
    (births.chronologyFields heights prior).height (compressionStamp oldTimes n) = births.cutoffHeight heights.height n := by
  dsimp only [chronologyFields]
  exact ⟨compressionPrefixValue_stamp _ _ _ births.times n, compressionPrefixValue_stamp _ _ _ births.times n,
    compressionPrefixValue_stamp _ _ _ births.times n, compressionPrefixValue_stamp _ _ _ births.times n,
    compressionPrefixValue_stamp _ _ _ births.times n⟩

theorem chronologyFields_limit :
    (births.chronologyFields heights prior).space births.limit = completion.externalPointCarrier P0 r0 μ0 A0 ∧
    (births.chronologyFields heights prior).order births.limit = completion.externalPointOrder P0 r0 μ0 A0 ∧
    (births.chronologyFields heights prior).meetGraph births.limit = completion.externalPointMeet P0 r0 μ0 A0 ∧
    (births.chronologyFields heights prior).birth births.limit = births.birth ∧
    (births.chronologyFields heights prior).height births.limit = heights.height := by
  dsimp only [chronologyFields]
  exact ⟨compressionPrefixValue_limit _ _ _ births.times, compressionPrefixValue_limit _ _ _ births.times,
    compressionPrefixValue_limit _ _ _ births.times, compressionPrefixValue_limit _ _ _ births.times,
    compressionPrefixValue_limit _ _ _ births.times⟩

end PartitionPilot.Forcing.GroundExternalBirthData



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundChronologicalHistory M T0 C D rD)

theorem chronologyFields_stage_laws
    (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
    (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
    (ordinal : ordinalSetProperty T0) (hOld : oldTimes ∈ T0)
    {s : ZFSet.{u}} (cutoff : s ∈ insert births.limit births.limit) :
    let fields := births.chronologyFields heights prior
    MeetOrderCode (fields.space s) (fields.order s) (fields.meetGraph s) ∧
      ZFSet.IsFunc (fields.space s) (insert births.limit births.limit) (fields.birth s) ∧
      (∀ x ∈ fields.space s, ∀ t, ZFSet.pair x t ∈ fields.birth s → t = s ∨ t ∈ s) ∧
      OldMeetCode (fields.order s) (fields.meetGraph s) (fields.birth s) ∧
      StrictLexHeightCode (fields.space s) C D (fields.order s) (fields.height s) rD := by
  classical
  dsimp only
  by_cases before : s ∈ oldTimes ∨ s = oldTimes
  · have hs := before.elim (fun member => ordinal.1 oldTimes hOld s member)
      (fun equal => equal.symm ▸ hOld)
    obtain ⟨space, order, meet, birth, height⟩ := births.chronologyFields_old heights prior before
    rw [space, order, meet, birth, height]
    exact ⟨prior.meet_order s hs,
      prior.prefix_birth_function_successor births.times ordinal hOld before,
      prior.birth_bound s hs, prior.old_meet s hs, prior.strict_height s hs⟩
  · rcases ZFSet.mem_insert_iff.1 cutoff with rfl | below
    · obtain ⟨space, order, meet, birth, height⟩ := births.chronologyFields_limit heights prior
      rw [space, order, meet, birth, height]
      have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
      exact ⟨geometry.meet, isFunc_retarget_of_entries births.function
          (fun _ _ entry => ZFSet.mem_insert_of_mem _ (ZFSet.pair_mem_prod.1 (births.function.1 entry)).2),
        fun _ _ _ entry => Or.inr (ZFSet.pair_mem_prod.1 (births.function.1 entry)).2,
        births.old_meet, heights.code⟩
    · have stamped : ∃ n, s = compressionStamp oldTimes n := by
        rcases (births.times.mem_limit_iff s).1 below with member | equal | stamped
        · exact False.elim (before (Or.inl member))
        · exact False.elim (before (Or.inr equal))
        · exact stamped
      obtain ⟨n, rfl⟩ := stamped
      obtain ⟨space, order, meet, birth, height⟩ := births.chronologyFields_stamp heights prior n
      rw [space, order, meet, birth, height]
      have fields := births.cutoff_fields data group action pairing unions powers separation infinite hG hP0 heights n
      obtain ⟨_, _, _, _, _, meetCode, born, oldMeet, strict, bound⟩ := fields
      exact ⟨meetCode, isFunc_retarget_of_entries born
          (fun _ _ entry => ZFSet.mem_insert_of_mem _ (ZFSet.pair_mem_prod.1 (born.1 entry)).2),
        fun x _ t entry => (bound x t entry).symm, oldMeet, strict⟩

end PartitionPilot.Forcing.GroundExternalBirthData

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundExternalCutoffFieldGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)

noncomputable def cutoffField : Fin 5 → Nat → ZFSet.{u} :=
  Fin.cases births.cutoff (Fin.cases births.cutoffOrder (Fin.cases births.cutoffMeet
    (Fin.cases births.cutoffBirth (fun _ => births.cutoffHeight heights.height))))

noncomputable def terminalField : Fin 5 → ZFSet.{u} :=
  Fin.cases (completion.externalPointCarrier P0 r0 μ0 A0)
    (Fin.cases (completion.externalPointOrder P0 r0 μ0 A0)
      (Fin.cases (completion.externalPointMeet P0 r0 μ0 A0)
        (Fin.cases births.birth (fun _ => heights.height))))

noncomputable def cutoffFieldFamily : Fin 5 → ZFSet.{u} :=
  Fin.cases births.cutoffFamily
    (Fin.cases (M.chronologyRestrictionFamily 1 ZFSet.omega births.cutoffFamily
      (completion.externalPointOrder P0 r0 μ0 A0))
    (Fin.cases (M.chronologyRestrictionFamily 2 ZFSet.omega births.cutoffFamily
      (completion.externalPointMeet P0 r0 μ0 A0))
    (Fin.cases (M.chronologyRestrictionFamily 0 ZFSet.omega births.cutoffFamily births.birth)
      (fun _ => M.chronologyRestrictionFamily 0 ZFSet.omega births.cutoffFamily heights.height))))

variable {inv : ZFSet.{u}}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
include data group action pairing unions powers separation infinite hG hP0

theorem terminalField_ground (j : Fin 5) : births.terminalField heights j ∈ M.sets := by
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
  exact Fin.cases geometry.carrier_ground (Fin.cases geometry.order_ground
    (Fin.cases geometry.meet_ground (Fin.cases births.birth_ground (fun _ => heights.height_ground)))) j

theorem cutoffFieldFamily_spec (j : Fin 5) :
    births.cutoffFieldFamily heights j ∈ M.sets ∧
      FunctionGraphOn ZFSet.omega (births.cutoffFieldFamily heights j) ∧
      ∀ n y, ZFSet.pair (natSetCode n) y ∈ births.cutoffFieldFamily heights j ↔
        y = births.cutoffField heights j n := by
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
  have domains := births.cutoffFamily_spec data group action pairing unions powers separation infinite hG hP0
  have hOmega := M.omega_mem separation infinite
  have restrictions (kind : Fin 3) {f : ZFSet.{u}} (hf : f ∈ M.sets) :
      M.chronologyRestrictionFamily kind ZFSet.omega births.cutoffFamily f ∈ M.sets ∧
      FunctionGraphOn ZFSet.omega (M.chronologyRestrictionFamily kind ZFSet.omega births.cutoffFamily f) ∧
      ∀ n y, ZFSet.pair (natSetCode n) y ∈ M.chronologyRestrictionFamily kind ZFSet.omega births.cutoffFamily f ↔
        y = chronologyRestriction kind (births.cutoff n) f :=
    ⟨M.chronologyRestrictionFamily_mem pairing unions powers separation kind hOmega domains.1 hf,
      ⟨_, M.chronologyRestrictionFamily_function pairing unions powers separation kind domains.1 hf domains.2.1⟩,
      fun n y => M.chronologyRestrictionFamily_entries pairing unions powers separation kind
        domains.1 hf domains.2.1 ((domains.2.2 n _).2 rfl) y⟩
  exact Fin.cases domains (Fin.cases (restrictions 1 geometry.order_ground)
    (Fin.cases (restrictions 2 geometry.meet_ground)
      (Fin.cases (restrictions 0 births.birth_ground) (fun _ => restrictions 0 heights.height_ground)))) j

end PartitionPilot.Forcing.GroundExternalBirthData

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalCutoffLayers
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "vpres" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "Index" => ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "P" => completion.externalSeedCarrier P0 r0 μ0 A0
local notation "levels" => completion.externalOwnerLevels P0 r0 μ0 A0
local notation "owner" => completion.externalStarOwner P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG hP0 births

noncomputable def externalBirth_cutoff_fresh_layer
    (Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u})
    (atSpace : Space oldTimes = U)
    (atOrder : sourceOrder oldTimes = completion.algebra.union.fields 1)
    (atMeet : sourceMeet oldTimes = completion.algebra.union.fields 2)
    (k n : Nat) (before : k ≤ n) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (births.cutoff n) (births.cutoffOrder n)
      (births.cutoffMeet n) (births.cutoffBirth n) (compressionStamp oldTimes k) := by
  classical
  letI := group.toGroup
  let Copies := External (SetMembers G) (family).Letters × Index
  let Slice := {x : ZFSet.{u} // x ∈ ownerFresh P B ∧ ZFSet.pair x (natSetCode k) ∈ levels}
  let Active := {v : Copies // ∃ x : Slice, ZFSet.pair x.val ((vpres).encode (.inr v)) ∈ owner}
  let e (v : Active) := completion.externalCopyGraph P0 r0 μ0 A0
    ((s).encode ((family).flatWord v.val.1 v.val.2 (data.externalBirthCopyVertex group oldAction k v.val.2)))
  have witnesses (x : Slice) : ∃ v : Active,
      ZFSet.pair x.val ((vpres).encode (.inr v.val)) ∈ owner ∧ x.val ∈ relationImage U B (e v) := by
    obtain ⟨w, r, owned, covered⟩ :=
      data.externalBirthCopy_witness group oldAction pairing unions powers separation infinite hG hP0 k x.property.2
    exact ⟨⟨(w, r), x, owned⟩, owned, covered⟩
  let pick (x : Slice) : Active := Classical.choose (witnesses x)
  have selected (x : Slice) :
      ZFSet.pair x.val ((vpres).encode (.inr (pick x).val)) ∈ owner ∧
        x.val ∈ relationImage U B (e (pick x)) := Classical.choose_spec (witnesses x)
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have levelCode := (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).2
  have sc := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have values (v : Active) : ∀ x y, ZFSet.pair x y ∈ e v → y ∈ births.cutoff n := by
    intro x y entry
    obtain ⟨active, owned⟩ := v.property
    rcases data.externalBirthCopy_level_bound group oldAction pairing unions powers separation infinite hG hP0
      v.val.1 v.val.2 k owned active.property.2 entry with old | ⟨l, bound, level⟩
    · exact births.cutoff_old n old
    · have fresh := (mem_ownerFresh P B y).1 (ZFSet.pair_mem_prod.1 (levelCode.1 level)).1
      apply (mem_ownerLevelPrefix _ _ _ _ _).2
      refine Or.inr ⟨fresh.1, fresh.2, natSetCode l, natSetCode_mem_omega l, level, ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_trans bound before) with less | same
      · exact Or.inr ((natSetCode_mem_iff _ _).2 less)
      · exact Or.inl (congrArg natSetCode same)
  have cutoffMeet := geometry.meet.restrict_lower (births.cutoff_subset n)
    (births.cutoff_lower data group oldAction pairing unions powers separation infinite hG hP0 n)
  have oldSubset : P ⊆ B := fun _ hx => ((mem_relationImage _ _ _ _).1 hx).1
  have times : oldTimes ⊆ births.limit := fun _ ht =>
    births.times.union.subset 0 (compressionStamp_old_mem (Or.inl ht) 0)
  have oldBefore : ∀ x a j t, ZFSet.pair x a ∈ completion.externalSeedBirth P0 r0 μ0 A0 oldTimes oldBirth →
      ZFSet.pair (natSetCode j) t ∈ births.stamps → a ∈ t := by
    intro x a j t entry stamp
    rw [(births.times.entries j t).1 stamp]
    exact births.old_before entry j
  have layer : CodedGrowthLayer M Space sourceOrder sourceMeet (births.cutoff n) (births.cutoffOrder n)
      (births.cutoffMeet n) births.birth (compressionStamp oldTimes k) := by
    refine ownerBirthGraph_separated births.seed_function oldSubset times levelCode births.times.ownerStampCode
      oldBefore ((births.times.entries k _).2 rfl) Active (fun _ => oldTimes) e
      (fun _ => compressionStamp_base_mem oldTimes k) ?_ ?_ pick ?_ ?_
    · intro v
      exact geometry.copies_ground _ (sc ▸ (s).encode_mem _)
    · intro v
      rw [atSpace, atOrder, atMeet]
      exact (geometry.copies _ (sc ▸ (s).encode_mem _)).restrictTarget (values v)
    · intro x hx
      rw [atSpace]
      obtain ⟨_, u, hu, entry⟩ := (mem_relationImage _ _ _ _).1 (selected x).2
      exact (mem_relationImage _ _ _ _).2 ⟨hx, u, hu, entry⟩
    · intro x y hx hy different
      have differentOwners : (vpres).encode (.inr (pick x).val) ≠ (vpres).encode (.inr (pick y).val) := by
        intro equal
        exact different (Subtype.ext (Sum.inr.inj ((vpres).injective equal)))
      obtain ⟨z, meetEntry, _⟩ := geometry.meet.operation.2 (ZFSet.pair x.val y.val)
        (ZFSet.pair_mem_prod.2 ⟨births.cutoff_subset n hx, births.cutoff_subset n hy⟩)
      refine ⟨z, (ZFSet.pair_mem_prod.1 (geometry.meet.operation.1 meetEntry)).2,
        pair_mem_graphRestriction.2 ⟨meetEntry, ZFSet.pair_mem_prod.2 ⟨hx, hy⟩⟩, ?_⟩
      exact data.externalOwnerLevels_meet_old_or_lower group oldAction pairing unions powers separation infinite hG hP0
        (selected x).1 (selected y).1 differentOwners x.property.2 y.property.2 meetEntry
  exact layer.restrictBirth cutoffMeet

end PartitionPilot.Forcing.GroundExternalGeometryInputs

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


namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "r" => completion.externalPointOrder P0 r0 μ0 A0
local notation "μ" => completion.externalPointMeet P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG hP0 births

noncomputable def externalBirth_prior_layer
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}} {t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet U
      (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) oldBirth t)
    (groundSources : ∀ s ∈ t, Space s ∈ M.sets)
    (oldFunction : ZFSet.IsFunc U oldTimes oldBirth) (oldTime : t ∈ oldTimes ∨ t = oldTimes) :
    CodedGrowthLayer M Space sourceOrder sourceMeet B r μ births.birth t := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have embedding := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  apply layer.ownerBirth_pushforward pairing unions powers separation (completion.algebra.union.ground 0)
    geometry.carrier_ground (geometry.copies_ground _ data.group.group_code.identity_mem)
    (M.omega_mem separation infinite) groundSources completion.algebra.union.meet
    embedding.toMeetEmbeddingCode (fun _ hx => hx) oldFunction
  intro n a entry
  rw [(births.times.entries n a).1 entry]
  exact compressionStamp_old_mem oldTime n

noncomputable def externalBirth_cutoff_prior_layer
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}} {t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet U
      (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) oldBirth t)
    (groundSources : ∀ s ∈ t, Space s ∈ M.sets)
    (oldFunction : ZFSet.IsFunc U oldTimes oldBirth) (oldTime : t ∈ oldTimes ∨ t = oldTimes)
    (n : Nat) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (births.cutoff n)
      (births.cutoffOrder n) (births.cutoffMeet n) (births.cutoffBirth n) t := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have embedding := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  have hQ := M.ownerLevelPrefix_mem pairing unions powers separation infinite
    (data.externalSeedCarrier_ground group oldAction pairing unions powers separation infinite hG hP0)
    geometry.carrier_ground
    (data.externalOwnerLevels_ground_function group oldAction pairing unions powers separation infinite hG hP0).1
    (fun _ hx => (mem_relationImage _ _ _ _).1 hx |>.1) (natSetCode_mem_omega n)
  have restricted := embedding.toMeetEmbeddingCode.restrictTarget (Q := births.cutoff n) (by
    intro x y copied
    have bounds := ZFSet.pair_mem_prod.1 (embedding.injection.function.1 copied)
    exact births.cutoff_old n ((mem_relationImage _ _ _ _).2 ⟨bounds.2, x, bounds.1, copied⟩))
  have transported : CodedGrowthLayer M Space sourceOrder sourceMeet (births.cutoff n)
      (births.cutoffOrder n) (births.cutoffMeet n) births.birth t := by
    apply layer.ownerBirth_pushforward pairing unions powers separation (completion.algebra.union.ground 0)
      hQ (geometry.copies_ground _ data.group.group_code.identity_mem) (M.omega_mem separation infinite)
      groundSources completion.algebra.union.meet restricted (births.cutoff_subset n) oldFunction
    intro k a entry
    rw [(births.times.entries k a).1 entry]
    exact compressionStamp_old_mem oldTime k
  exact transported.restrictBirth
    (geometry.meet.restrict_lower (births.cutoff_subset n)
      (births.cutoff_lower data group oldAction pairing unions powers separation infinite hG hP0 n))

end PartitionPilot.Forcing.GroundExternalGeometryInputs



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundChronologicalHistory M T0 C D rD)

theorem chronologyFields_ground
    (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
    (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
    (ordinal : ordinalSetProperty T0) (hOld : oldTimes ∈ T0)
    {s : ZFSet.{u}} (cutoff : s ∈ insert births.limit births.limit) :
    let fields := births.chronologyFields heights prior
    fields.space s ∈ M.sets ∧ fields.order s ∈ M.sets ∧ fields.meetGraph s ∈ M.sets ∧
      fields.birth s ∈ M.sets ∧ fields.height s ∈ M.sets := by
  classical
  dsimp only
  by_cases before : s ∈ oldTimes ∨ s = oldTimes
  · have hs := before.elim (fun member => ordinal.1 oldTimes hOld s member)
      (fun equal => equal.symm ▸ hOld)
    obtain ⟨space, order, meet, birth, height⟩ := births.chronologyFields_old heights prior before
    rw [space, order, meet, birth, height]
    exact ⟨prior.space_mem s hs, prior.order_mem s hs, prior.meet_mem s hs,
      prior.birth_mem s hs, prior.height_mem s hs⟩
  · rcases ZFSet.mem_insert_iff.1 cutoff with rfl | below
    · obtain ⟨space, order, meet, birth, height⟩ := births.chronologyFields_limit heights prior
      rw [space, order, meet, birth, height]
      have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
      exact ⟨geometry.carrier_ground, geometry.order_ground, geometry.meet_ground,
        births.birth_ground, heights.height_ground⟩
    · have stamped : ∃ n, s = compressionStamp oldTimes n := by
        rcases (births.times.mem_limit_iff s).1 below with member | equal | stamped
        · exact False.elim (before (Or.inl member))
        · exact False.elim (before (Or.inr equal))
        · exact stamped
      obtain ⟨n, rfl⟩ := stamped
      obtain ⟨space, order, meet, birth, height⟩ := births.chronologyFields_stamp heights prior n
      rw [space, order, meet, birth, height]
      have fields := births.cutoff_fields data group action pairing unions powers separation infinite hG hP0 heights n
      exact ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1⟩

end PartitionPilot.Forcing.GroundExternalBirthData




namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundChronologicalHistory M T0 C D rD)
local notation "fields" => births.chronologyFields heights prior
local notation "U" => completion.algebra.union.fields 0

theorem chronology_sources_eq_below {t s : ZFSet.{u}}
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) (before : s ∈ t) :
    (fields).space s = prior.space s ∧ (fields).order s = prior.order s ∧
      (fields).meetGraph s = prior.meetGraph s := by
  dsimp only [chronologyFields]
  exact ⟨compressionPrefixValue_eq_prior_below _ _ _ births.times oldTime before,
    compressionPrefixValue_eq_prior_below _ _ _ births.times oldTime before,
    compressionPrefixValue_eq_prior_below _ _ _ births.times oldTime before⟩

variable (ordinal : ordinalSetProperty T0) (hOldTimes : oldTimes ∈ T0)
include ordinal hOldTimes

noncomputable def chronology_old_layer {cutoff t : ZFSet.{u}}
    (oldCutoff : cutoff ∈ oldTimes ∨ cutoff = oldTimes) (bound : t = cutoff ∨ t ∈ cutoff) :
    CodedGrowthLayer M (fields).space (fields).order (fields).meetGraph
      ((fields).space cutoff) ((fields).order cutoff) ((fields).meetGraph cutoff) ((fields).birth cutoff) t := by
  have hc : cutoff ∈ T0 := oldCutoff.elim
    (fun member => ordinal.1 oldTimes hOldTimes cutoff member) (fun equal => equal.symm ▸ hOldTimes)
  have ht : t ∈ T0 := bound.elim (fun equal => equal.symm ▸ hc)
    (fun before => ordinal.1 cutoff hc t before)
  have oldTime : t ∈ oldTimes ∨ t = oldTimes := by
    rcases bound with equal | before
    · exact equal.symm ▸ oldCutoff
    · exact Or.inl (oldCutoff.elim
        (fun member => ordinal.2 oldTimes hOldTimes cutoff member t before) (fun equal => equal ▸ before))
  have layer := (prior.layer cutoff hc t ht bound).congr_sources_below
    (fun s hs => (births.chronology_sources_eq_below heights prior oldTime hs).1.symm)
    (fun s hs => (births.chronology_sources_eq_below heights prior oldTime hs).2.1.symm)
    (fun s hs => (births.chronology_sources_eq_below heights prior oldTime hs).2.2.symm)
  have values := births.chronologyFields_old heights prior oldCutoff
  simpa only [values.1, values.2.1, values.2.2.1, values.2.2.2.1] using layer

theorem chronology_sources_ground_below {t : ZFSet.{u}}
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) : ∀ s ∈ t, (fields).space s ∈ M.sets := by
  intro s hs
  rw [(births.chronology_sources_eq_below heights prior oldTime hs).1]
  have ht : t ∈ T0 := oldTime.elim
    (fun member => ordinal.1 oldTimes hOldTimes t member) (fun equal => equal.symm ▸ hOldTimes)
  exact prior.space_mem s (ordinal.1 t ht s hs)

variable (priorSpace : prior.space oldTimes = completion.algebra.union.fields 0)
variable (priorOrder : prior.order oldTimes = completion.algebra.union.fields 1)
variable (priorMeet : prior.meetGraph oldTimes = completion.algebra.union.fields 2)
variable (priorBirth : prior.birth oldTimes = oldBirth)
include priorSpace priorOrder priorMeet priorBirth

noncomputable def chronology_base_layer (t : ZFSet.{u}) (oldTime : t ∈ oldTimes ∨ t = oldTimes) :
    CodedGrowthLayer M (fields).space (fields).order (fields).meetGraph U
      (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) oldBirth t := by
  have layer := births.chronology_old_layer heights prior ordinal hOldTimes
    (Or.inr rfl : oldTimes ∈ oldTimes ∨ oldTimes = oldTimes) oldTime.symm
  have values := births.chronologyFields_old heights prior (Or.inr rfl : oldTimes ∈ oldTimes ∨ oldTimes = oldTimes)
  simpa only [values.1, values.2.1, values.2.2.1, values.2.2.2.1,
    priorSpace, priorOrder, priorMeet, priorBirth] using layer

variable {inv : ZFSet.{u}}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (oldFunction : ZFSet.IsFunc (completion.algebra.union.fields 0) oldTimes oldBirth)
include data group action pairing unions powers separation infinite hG hP0 oldFunction

noncomputable def chronology_finite_layers (n : Nat) (t : ZFSet.{u})
    (bound : t = compressionStamp oldTimes n ∨ t ∈ compressionStamp oldTimes n) :
    CodedGrowthLayer M (fields).space (fields).order (fields).meetGraph
      ((fields).space (compressionStamp oldTimes n)) ((fields).order (compressionStamp oldTimes n))
      ((fields).meetGraph (compressionStamp oldTimes n)) ((fields).birth (compressionStamp oldTimes n)) t := by
  have values := births.chronologyFields_stamp heights prior n
  rw [values.1, values.2.1, values.2.2.1, values.2.2.2.1]
  have atBase := births.chronologyFields_old heights prior (Or.inr rfl : oldTimes ∈ oldTimes ∨ oldTimes = oldTimes)
  have fresh (k : Nat) (before : k ≤ n) := data.externalBirth_cutoff_fresh_layer group action
    pairing unions powers separation infinite hG hP0 births (fields).space (fields).order (fields).meetGraph
    (atBase.1.trans priorSpace) (atBase.2.1.trans priorOrder) (atBase.2.2.1.trans priorMeet) k n before
  have original (s : ZFSet.{u}) (oldTime : s ∈ oldTimes ∨ s = oldTimes) :=
    data.externalBirth_cutoff_prior_layer group action pairing unions powers separation infinite hG hP0 births
      (births.chronology_base_layer heights prior ordinal hOldTimes priorSpace priorOrder priorMeet priorBirth s oldTime)
      (births.chronology_sources_ground_below heights prior ordinal hOldTimes oldTime) oldFunction oldTime n
  apply Classical.choice
  rcases bound with rfl | before
  · exact ⟨fresh n (Nat.le_refl n)⟩
  · rcases (mem_compressionStamp_iff oldTimes t n).1 before with old | same | ⟨k, earlier, rfl⟩
    · exact ⟨original t (Or.inl old)⟩
    · exact ⟨original t (Or.inr same)⟩
    · exact ⟨fresh k (Nat.le_of_lt earlier)⟩

noncomputable def chronology_union_layers (t : ZFSet.{u}) (bound : t = births.limit ∨ t ∈ births.limit) :
    CodedGrowthLayer M (fields).space (fields).order (fields).meetGraph
      ((fields).space births.limit) ((fields).order births.limit)
      ((fields).meetGraph births.limit) ((fields).birth births.limit) t := by
  have values := births.chronologyFields_limit heights prior
  rw [values.1, values.2.1, values.2.2.1, values.2.2.2.1]
  have atBase := births.chronologyFields_old heights prior (Or.inr rfl : oldTimes ∈ oldTimes ∨ oldTimes = oldTimes)
  have original (s : ZFSet.{u}) (oldTime : s ∈ oldTimes ∨ s = oldTimes) :=
    data.externalBirth_prior_layer group action pairing unions powers separation infinite hG hP0 births
      (births.chronology_base_layer heights prior ordinal hOldTimes priorSpace priorOrder priorMeet priorBirth s oldTime)
      (births.chronology_sources_ground_below heights prior ordinal hOldTimes oldTime) oldFunction oldTime
  apply Classical.choice
  rcases bound with rfl | before
  · exact ⟨.empty_of_no_birth ⟨births.limit, births.limit_ground⟩ (fun x _ => births.no_limit_birth x)⟩
  · rcases (births.times.mem_limit_iff t).1 before with old | same | ⟨k, rfl⟩
    · exact ⟨original t (Or.inl old)⟩
    · exact ⟨original t (Or.inr same)⟩
    · exact ⟨data.externalBirth_fresh_layer group action pairing unions powers separation infinite hG hP0 births
        (fields).space (fields).order (fields).meetGraph (atBase.1.trans priorSpace)
        (atBase.2.1.trans priorOrder) (atBase.2.2.1.trans priorMeet) k⟩

noncomputable def chronology_all_layers :
    ∀ cutoff ∈ insert births.limit births.limit, ∀ t ∈ insert births.limit births.limit,
      t = cutoff ∨ t ∈ cutoff → CodedGrowthLayer M (fields).space (fields).order (fields).meetGraph
        ((fields).space cutoff) ((fields).order cutoff) ((fields).meetGraph cutoff) ((fields).birth cutoff) t := by
  intro cutoff hc t _ bound
  apply Classical.choice
  rcases ZFSet.mem_insert_iff.1 hc with rfl | before
  · exact ⟨births.chronology_union_layers heights prior ordinal hOldTimes priorSpace priorOrder priorMeet priorBirth
      data group action pairing unions powers separation infinite hG hP0 oldFunction t bound⟩
  · rcases (births.times.mem_limit_iff cutoff).1 before with old | same | ⟨n, rfl⟩
    · exact ⟨births.chronology_old_layer heights prior ordinal hOldTimes (Or.inl old) bound⟩
    · exact ⟨births.chronology_old_layer heights prior ordinal hOldTimes (Or.inr same) bound⟩
    · exact ⟨births.chronology_finite_layers heights prior ordinal hOldTimes priorSpace priorOrder priorMeet priorBirth
        data group action pairing unions powers separation infinite hG hP0 oldFunction n t bound⟩

end PartitionPilot.Forcing.GroundExternalBirthData



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundChronologicalHistory M T0 C D rD)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (ordinal : ordinalSetProperty T0) (hOldTimes : oldTimes ∈ T0)
variable (priorSpace : prior.space oldTimes = completion.algebra.union.fields 0)
variable (priorOrder : prior.order oldTimes = completion.algebra.union.fields 1)
variable (priorMeet : prior.meetGraph oldTimes = completion.algebra.union.fields 2)
variable (priorBirth : prior.birth oldTimes = oldBirth)
variable (oldFunction : ZFSet.IsFunc (completion.algebra.union.fields 0) oldTimes oldBirth)

noncomputable def chronologyHistory :
    GroundChronologicalHistory M (insert births.limit births.limit) C D rD where
  space := (births.chronologyFields heights prior).space
  order := (births.chronologyFields heights prior).order
  meetGraph := (births.chronologyFields heights prior).meetGraph
  birth := (births.chronologyFields heights prior).birth
  height := (births.chronologyFields heights prior).height
  space_mem := fun _ hs => (births.chronologyFields_ground heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).1
  order_mem := fun _ hs => (births.chronologyFields_ground heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.1
  meet_mem := fun _ hs => (births.chronologyFields_ground heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.2.1
  birth_mem := fun _ hs => (births.chronologyFields_ground heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.2.2.1
  height_mem := fun _ hs => (births.chronologyFields_ground heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.2.2.2
  meet_order := fun _ hs => (births.chronologyFields_stage_laws heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).1
  birth_function := fun _ hs => (births.chronologyFields_stage_laws heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.1
  birth_bound := fun _ hs => (births.chronologyFields_stage_laws heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.2.1
  old_meet := fun _ hs => (births.chronologyFields_stage_laws heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.2.2.1
  strict_height := fun _ hs => (births.chronologyFields_stage_laws heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes hs).2.2.2.2
  layer := births.chronology_all_layers heights prior ordinal hOldTimes priorSpace priorOrder priorMeet priorBirth
    data group action pairing unions powers separation infinite hG hP0 oldFunction

end PartitionPilot.Forcing.GroundExternalBirthData



namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundChronologicalHistory M T0 C D rD)

noncomputable def chronologicalData
    (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
    (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
    (ordinal : ordinalSetProperty T0) (hOldTimes : oldTimes ∈ T0)
    (priorSpace : prior.space oldTimes = completion.algebra.union.fields 0)
    (priorOrder : prior.order oldTimes = completion.algebra.union.fields 1)
    (priorMeet : prior.meetGraph oldTimes = completion.algebra.union.fields 2)
    (priorBirth : prior.birth oldTimes = oldBirth)
    (oldFunction : ZFSet.IsFunc (completion.algebra.union.fields 0) oldTimes oldBirth)
    (boundedHeights : GroundBoundedExternalHeightData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 C D rD lo hi seed completion heights) :
    GroundChronologicalExternal M initial I Sources Reps G m inv one T τ
      P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 completion births heights prior := by
  let history := births.chronologyHistory heights prior data group action
    pairing unions powers separation infinite hG hP0 ordinal hOldTimes
    priorSpace priorOrder priorMeet priorBirth oldFunction
  have terminal := births.chronologyFields_limit heights prior
  have space : history.space births.limit = completion.externalPointCarrier P0 r0 μ0 A0 := terminal.1
  have order : history.order births.limit = completion.externalPointOrder P0 r0 μ0 A0 := terminal.2.1
  have birth : history.birth births.limit = births.birth := terminal.2.2.2.1
  have earlier : ∀ x t, ZFSet.pair x t ∈ history.birth births.limit → t ∈ births.limit := by
    intro x t entry
    rw [birth] at entry
    exact (ZFSet.pair_mem_prod.1 (births.function.1 entry)).2
  have heightCode : StrictLexHeightCode (fixedTopCarrier (history.space births.limit)) C D
      (fixedTopOrder (history.space births.limit) (history.order births.limit)) heights.boundedHeight rD := by
    rw [space, order]
    exact boundedHeights.code
  let bounded := history.replaceTerminalFixedTop pairing unions powers separation births.times.ordinal
    births.limit_ground earlier heights.boundedHeight boundedHeights.height_ground heightCode
  refine ⟨data, history, (fun _ before => births.chronologyFields_old heights prior before),
    (fun n => births.chronologyFields_stamp heights prior n), terminal, bounded, ?_, ?_⟩
  · intro s hs
    exact history.replaceTerminalFixedTop_old pairing unions powers separation births.times.ordinal
      births.limit_ground earlier heights.boundedHeight boundedHeights.height_ground heightCode hs
  · have values := history.replaceTerminalFixedTop_terminal pairing unions powers separation births.times.ordinal
      births.limit_ground earlier heights.boundedHeight boundedHeights.height_ground heightCode
    rw [space, order, birth] at values
    exact values

end PartitionPilot.Forcing.GroundExternalBirthData



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

section
universe u

structure GroundInitialMainSuccessorData (M : TransitiveGround.{u}) (C D rD : ZFSet.{u})
    (source : GroundChronologicalMainStage M C D rD) (Labels : ZFSet.{u}) where
  indices_ground : (source.stage.compressionTasks Labels) ∈ M.sets
  sources_ground : (source.stage.compressionSources Labels) ∈ M.sets
  filters_ground : (source.stage.compressionFilters Labels) ∈ M.sets
  task_action_ground : (source.stage.compressionTaskAction Labels) ∈ M.sets
  Reps : ZFSet.{u}
  representatives_ground : Reps ∈ M.sets
  origin : GroundCompressionOrigin M (source.stage.compressionInitial Labels)
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action source.stage.top
    (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.inverse source.stage.identity (source.stage.compressionTaskAction Labels) (source.stage.compressionFilters Labels)
  compression : GroundChronologicalCompression M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier C D rD source.stage.height (source.stage.compressionTargets Labels) (source.stage.compressionSeparators Labels) (source.stage.compressionFilters Labels)
    source.cutoff source.birth (insert source.cutoff source.cutoff) source.history
  geometry : GroundExternalGeometryData M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action compression.born.profiled.heighted.completion
  boundedGeometry : GroundExternalBoundedGeometryData M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action compression.born.profiled.heighted.completion
  lo : ZFSet.{u}
  hi : ZFSet.{u}
  lo_mem : lo ∈ D
  hi_mem : hi ∈ D
  interval : ZFSet.pair lo hi ∈ rD
  heights : GroundExternalHeightData M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action C D rD lo hi
    compression.born.profiled.heighted.heights.height compression.born.profiled.heighted.completion
  boundedHeights : GroundBoundedExternalHeightData M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action C D rD lo hi
    compression.born.profiled.heighted.heights.height compression.born.profiled.heighted.completion heights
  births : GroundExternalBirthData M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action
    compression.born.births.limit compression.born.births.birth compression.born.profiled.heighted.completion
  boundedBirths : GroundBoundedExternalBirthData M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action
    compression.born.births.limit compression.born.births.birth compression.born.profiled.heighted.completion births
  external : GroundChronologicalExternal M (source.stage.compressionInitial Labels) (source.stage.compressionTasks Labels) (source.stage.compressionSources Labels) Reps source.stage.actors source.stage.multiplication source.stage.inverse source.stage.identity (source.stage.compressionTaskAction Labels) source.stage.top
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action compression.born.births.limit compression.born.births.birth
    C D rD lo hi compression.born.profiled.heighted.heights.height (insert compression.born.births.limit compression.born.births.limit)
    compression.born.profiled.heighted.completion births heights compression.history
  bottomImage : ZFSet.{u}
  bottom_ground : bottomImage ∈ M.sets
  bottom_entry : ZFSet.pair source.stage.bottom bottomImage ∈
    compression.born.profiled.heighted.completion.externalOriginalEmbedding source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action
  target : GroundChronologicalMainStage M C D rD
  transition : GroundChronologicalMainTransition source target
  cutoff_strict : source.cutoff ∈ target.cutoff
  target_cutoff : target.cutoff = births.limit
  target_history : HEq target.history external.bounded_history
  target_fields :
    target.stage.carrier = compression.born.profiled.heighted.completion.externalBoundedCarrier source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action ∧
    target.stage.order = compression.born.profiled.heighted.completion.externalBoundedOrder source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action ∧
    target.stage.meetGraph = compression.born.profiled.heighted.completion.externalBoundedMeet source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action ∧
    target.stage.actors = M.externalGroupCarrier source.stage.actors (externalChildLetters (source.stage.compressionTasks Labels) source.stage.carrier (externalRectangles source.stage.carrier source.stage.actors source.stage.order source.stage.meetGraph source.stage.action)) source.stage.multiplication source.stage.identity ∧
    target.stage.multiplication = M.externalGroupMultiplication source.stage.actors (externalChildLetters (source.stage.compressionTasks Labels) source.stage.carrier (externalRectangles source.stage.carrier source.stage.actors source.stage.order source.stage.meetGraph source.stage.action)) source.stage.multiplication source.stage.identity ∧
    target.stage.inverse = M.externalGroupInverse source.stage.actors (externalChildLetters (source.stage.compressionTasks Labels) source.stage.carrier (externalRectangles source.stage.carrier source.stage.actors source.stage.order source.stage.meetGraph source.stage.action)) source.stage.multiplication source.stage.inverse source.stage.identity ∧
    target.stage.identity = M.externalGroupIdentity source.stage.actors (externalChildLetters (source.stage.compressionTasks Labels) source.stage.carrier (externalRectangles source.stage.carrier source.stage.actors source.stage.order source.stage.meetGraph source.stage.action)) source.stage.multiplication source.stage.identity ∧
    target.stage.action = compression.born.profiled.heighted.completion.externalBoundedAction source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action ∧
    target.stage.bottom = bottomImage ∧
    target.stage.top = compression.born.profiled.heighted.completion.externalPointCarrier source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action ∧
    target.stage.height = heights.boundedHeight
  target_birth : target.birth = births.boundedBirth
  point_graph : transition.map.points = compression.born.profiled.heighted.completion.externalOriginalEmbedding
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action
  actor_graph : transition.map.actors = M.externalOldInclusion source.stage.actors
    (externalChildLetters (source.stage.compressionTasks Labels) source.stage.carrier (externalRectangles source.stage.carrier source.stage.actors source.stage.order source.stage.meetGraph source.stage.action)) source.stage.multiplication source.stage.identity
  strict_new_top : ∀ x y, ZFSet.pair x y ∈ transition.map.points →
    ZFSet.pair y target.stage.top ∈ target.stage.order ∧
      ZFSet.pair target.stage.top y ∉ target.stage.order

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundInitialSeedSerializationRanks
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

structure GroundInitialMainSeedData (M : TransitiveGround.{u}) (K C : ZFSet.{u}) where
  fractionCode : ZFSet.{u}
  fraction_ground : fractionCode ∈ M.sets
  fraction_injection : InjectionCode fractionCarrier ZFSet.omega fractionCode
  coordinateInjection : ZFSet.{u}
  injection_ground : coordinateInjection ∈ M.sets
  injection_code : InjectionCode (rationalCarrier fractionCode) ZFSet.omega coordinateInjection
  dense : DenseOrderCode (rationalCarrier fractionCode) (rationalLtGraph fractionCode)
  no_endpoints : ∀ x ∈ rationalCarrier fractionCode,
    (∃ y ∈ rationalCarrier fractionCode, ZFSet.pair y x ∈ rationalLtGraph fractionCode) ∧
    (∃ y ∈ rationalCarrier fractionCode, ZFSet.pair x y ∈ rationalLtGraph fractionCode)
  lo : ZFSet.{u}
  hi : ZFSet.{u}
  lo_mem : lo ∈ rationalCarrier fractionCode
  hi_mem : hi ∈ rationalCarrier fractionCode
  gap : ZFSet.pair lo hi ∈ rationalLtGraph fractionCode
  source : GroundChronologicalMainStage M C (rationalCarrier fractionCode) (rationalLtGraph fractionCode)
  points_eq : source.stage.carrier = natSetCode 2
  actors_eq : source.stage.actors = natSetCode 1
  bottom_eq : source.stage.bottom = natSetCode 0
  top_eq : source.stage.top = natSetCode 1
  stage_code : source.stage.code = mainStageCode InitialMainAlgebra.carrier InitialMainAlgebra.order
    InitialMainAlgebra.meetGraph InitialMainAlgebra.actors InitialMainAlgebra.multiplication
    InitialMainAlgebra.inverse InitialMainAlgebra.identity InitialMainAlgebra.action
    InitialMainAlgebra.bottom InitialMainAlgebra.top
    (twoPointHeight InitialMainAlgebra.bottom InitialMainAlgebra.top ∅ lo hi)
  cutoff_zero : source.cutoff = ∅
  birth_eq : source.birth = constantFamilyGraph (natSetCode 2) ∅
  invariant : source.Invariant K C

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
universe u

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (priorFields : GroundChronologyFields M T0)

noncomputable def chronologyGraph (j : Fin 5) : ZFSet.{u} :=
  compressionPrefixGraph oldTimes births.limit (priorFields.graph j)
    (births.cutoffFieldFamily heights j) births.stamps (births.terminalField heights j)

variable {inv : ZFSet.{u}}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (ordinal : ordinalSetProperty T0) (hOld : oldTimes ∈ T0)
include data group action pairing unions powers separation infinite hG hP0

theorem chronologyGraph_ground (j : Fin 5) : births.chronologyGraph heights priorFields j ∈ M.sets :=
  M.compressionPrefixGraph_mem pairing unions powers separation
    (M.omega_mem separation infinite)
    (M.transitive births.limit_ground births.times.base_mem_limit) births.limit_ground
    (priorFields.graph_ground j)
    (births.cutoffFieldFamily_spec heights data group action pairing unions powers separation infinite hG hP0 j).1
    births.stamps_ground
    (births.terminalField_ground heights data group action pairing unions powers separation infinite hG hP0 j)

include ordinal hOld in
theorem chronologyGraph_function (j : Fin 5) :
    FunctionGraphOn (insert births.limit births.limit) (births.chronologyGraph heights priorFields j) := by
  apply compressionPrefixGraph_function births.times (priorFields.value j) (births.cutoffField heights j)
  · intro s before y
    have hs : s ∈ T0 := before.elim (fun h => ordinal.1 oldTimes hOld s h) (fun h => h.symm ▸ hOld)
    exact ⟨fun entry => (priorFields.value_eq_of_entry j entry).symm,
      fun equal => equal.symm ▸ priorFields.value_entry j hs⟩
  · exact (births.cutoffFieldFamily_spec heights data group action pairing unions powers separation infinite hG hP0 j).2.2

noncomputable def groundChronologyFields : GroundChronologyFields M (insert births.limit births.limit) :=
  GroundChronologyFields.ofGraphs pairing unions (M.insert_mem pairing unions births.limit_ground births.limit_ground)
    (births.chronologyGraph heights priorFields)
    (births.chronologyGraph_ground heights priorFields data group action pairing unions powers separation infinite hG hP0)
    (births.chronologyGraph_function heights priorFields data group action pairing unions powers separation infinite hG hP0 ordinal hOld)

end GroundExternalBirthData




end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (linked : GroundLinkedMainStage M K Labels C D rD)

theorem code_ground (pairing : Realize M.sets SetFormula.pairing Fin.elim0) : linked.code ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 2 _ (Fin.cases (linked.main.stage.code_mem pairing)
    (Fin.cases linked.main.cutoff_ground (fun _ => linked.serial.code_ground pairing)))

end GroundLinkedMainStage

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u v

structure GroundMainPrefix (M : TransitiveGround.{u}) (K Labels C D rD : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (I : Type v) [Small.{u} I] [Preorder I] where
  key : I → ZFSet.{u}
  key_injective : Function.Injective key
  key_order : ∀ i j, i ≤ j ↔ key i = key j ∨ key i ∈ key j
  indices_ground : ZFSet.range key ∈ M.sets
  indices_ordinal : ordinalSetProperty (ZFSet.range key)
  diagram : GroundChronologicalMainDiagram M C D rD pairing unions powers separation I
  linked : I → GroundLinkedMainStage M K Labels C D rD
  linked_main : ∀ i, (linked i).main = diagram.stage i
  coverage : diagram.CoversOldBirths
  stages_ground : familyCodeGraph key (fun i => (linked i).code) ∈ M.sets
  transitions_ground : familyCodeGraph (mainTransitionIndexKey key)
    (fun p => (diagram.transition p.property).map.code) ∈ M.sets

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def indices : ZFSet.{u} := ZFSet.range run.key

noncomputable def stageGraph : ZFSet.{u} := familyCodeGraph run.key (fun i => (run.linked i).code)

noncomputable def transitionGraph : ZFSet.{u} := familyCodeGraph (mainTransitionIndexKey run.key)
  (fun p => (run.diagram.transition p.property).map.code)

noncomputable def code : ZFSet.{u} := nonemptyTupleCode 2
  (Fin.cases run.indices (Fin.cases run.stageGraph (fun _ => run.transitionGraph)))

end GroundMainPrefix

end PartitionPilot.Forcing



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

include run in
theorem common_upper (i j : I) : ∃ k, i ≤ k ∧ j ≤ k := by
  let first := SetMembers.ofMem (run.key i) (ZFSet.mem_range.2 ⟨i, rfl⟩ : run.key i ∈ run.indices)
  let second := SetMembers.ofMem (run.key j) (ZFSet.mem_range.2 ⟨j, rfl⟩ : run.key j ∈ run.indices)
  have total := ordinalMainIndex_total run.indices_ordinal first second
  change (SetMembers.raw first = SetMembers.raw second ∨ SetMembers.raw first ∈ SetMembers.raw second) ∨
    (SetMembers.raw second = SetMembers.raw first ∨ SetMembers.raw second ∈ SetMembers.raw first) at total
  simp only [first, second, SetMembers.raw_ofMem] at total
  rcases total with before | after
  · exact ⟨j, (run.key_order i j).2 before, le_rfl⟩
  · exact ⟨i, le_rfl, (run.key_order j i).2 after⟩

noncomputable def pointSystem : CodedDirectSystem.{u} I :=
  run.diagram.pointSystem run.common_upper

noncomputable def actorSystem : CodedDirectSystem.{u} I :=
  run.diagram.actorSystem run.common_upper

end GroundMainPrefix
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

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

noncomputable def serializedChronologyCandidates (B C D rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ T, ∃ serial : GroundSerializedChronology M T C D rD, serial.code = z) B

end TransitiveGround

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LinkedMainTransitionRawCodes
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

def LinkedMainTransitionRawCode (M : TransitiveGround.{u})
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : ZFSet.{u})
    (source target : Fin 24 → ZFSet.{u}) : Prop :=
  LinkedMainStageRawCode M K Labels C D rD N sourceCode source ∧
  LinkedMainStageRawCode M K Labels C D rD N targetCode target ∧
  LinkedTransitionLawsCode z points actors sourceBirth targetBirth source target

end PartitionPilot.Forcing

end

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

noncomputable def stageFieldFamily (j : Fin 11) : ZFSet.{u} :=
  familyCodeGraph run.key (fun i => (run.diagram.stage i).stage.field j)

noncomputable def carrierFamily : ZFSet.{u} := run.stageFieldFamily 0

noncomputable def actorFamily : ZFSet.{u} := run.stageFieldFamily 3

noncomputable def pointMapFamily : ZFSet.{u} :=
  familyCodeGraph (mainTransitionIndexKey run.key) (fun p => (run.diagram.transition p.property).map.points)

noncomputable def actorMapFamily : ZFSet.{u} :=
  familyCodeGraph (mainTransitionIndexKey run.key) (fun p => (run.diagram.transition p.property).map.actors)

theorem stageFieldFamily_ground (j : Fin 11) : run.stageFieldFamily j ∈ M.sets := by
  have stageCodes := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).main.stage.code)
    (fun i => ZFSet.pair (run.linked i).main.cutoff (run.linked i).serial.code)
    run.key_injective run.indices_ground run.stages_ground).1
  have codes : familyCodeGraph run.key (fun i => (run.diagram.stage i).stage.code) ∈ M.sets := by
    simpa only [run.linked_main] using stageCodes
  exact M.familyCodeGraph_tuple_fields pairing unions powers separation run.key run.key_injective
    run.indices_ground 10 (fun i => (run.diagram.stage i).stage.field) codes j

theorem carrierFamily_ground : run.carrierFamily ∈ M.sets := run.stageFieldFamily_ground 0

theorem actorFamily_ground : run.actorFamily ∈ M.sets := run.stageFieldFamily_ground 3

theorem mapFamilies_ground : run.pointMapFamily ∈ M.sets ∧ run.actorMapFamily ∈ M.sets := by
  have domain : ZFSet.range (mainTransitionIndexKey run.key) ∈ M.sets := by
    rw [mainTransitionIndex_range run.key run.key_order]
    exact M.chronologyPairs_mem pairing unions powers separation run.indices_ground
  exact M.familyCodeGraph_pair_projections pairing unions powers separation
    (mainTransitionIndexKey run.key) _ _ (mainTransitionIndexKey_injective run.key run.key_injective)
    domain run.transitions_ground

theorem pointMapFamily_ground : run.pointMapFamily ∈ M.sets := run.mapFamilies_ground.1

theorem stageFieldFamily_function (j : Fin 11) : FunctionGraphOn run.indices (run.stageFieldFamily j) :=
  familyCodeGraph_function run.key _ run.key_injective

theorem carrierFamily_function : FunctionGraphOn run.indices run.carrierFamily :=
  run.stageFieldFamily_function 0

theorem actorFamily_function : FunctionGraphOn run.indices run.actorFamily :=
  run.stageFieldFamily_function 3

theorem actorMapFamily_function : FunctionGraphOn (chronologyPairs run.indices) run.actorMapFamily := by
  have function := familyCodeGraph_function (mainTransitionIndexKey run.key)
    (fun p => (run.diagram.transition p.property).map.actors)
    (mainTransitionIndexKey_injective run.key run.key_injective)
  rw [mainTransitionIndex_range run.key run.key_order] at function
  exact function

theorem stageFieldFamily_entry (j : Fin 11) (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.stageFieldFamily j ↔ z = (run.diagram.stage i).stage.field j :=
  pair_mem_familyCodeGraph run.key _ run.key_injective i z

theorem carrierFamily_entry (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.carrierFamily ↔ z = (run.diagram.stage i).stage.carrier :=
  run.stageFieldFamily_entry 0 i z

theorem actorFamily_entry (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.actorFamily ↔ z = (run.diagram.stage i).stage.actors :=
  run.stageFieldFamily_entry 3 i z

theorem actorMapFamily_entry {i j : I} (before : i ≤ j) (z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (run.key j) (run.key i)) z ∈ run.actorMapFamily ↔
      z = (run.diagram.transition before).map.actors :=
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

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u v

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}

theorem field_rank_le_linkedCode (target : GroundLinkedMainStage M K Labels C D rD) (j : Fin 11) :
    ZFSet.rank (target.main.stage.field j) ≤ ZFSet.rank target.code := by
  have stageBound : ZFSet.rank target.main.stage.code ≤ ZFSet.rank target.code := by
    simpa only [code, linkedMainStageCode, Fin.cases_zero] using
      (rank_nonemptyTupleCode_field_le 2 (Fin.cases target.main.stage.code
        (Fin.cases target.main.cutoff (fun _ => target.serial.code))) 0)
  exact (rank_nonemptyTupleCode_field_le 10 target.main.stage.field j).trans stageBound

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

section
open SetFormula
universe u

def LinkedMainTransitionCode (M : TransitiveGround.{u})
    (K Labels C D rD sourceCode targetCode z : ZFSet.{u}) : Prop :=
  ∃ source target : GroundLinkedMainStage M K Labels C D rD,
    source.code = sourceCode ∧ target.code = targetCode ∧
    ∃ transition : GroundChronologicalMainTransition source.main target.main,
      transition.map.code = z ∧ transition.CoversOldBirths

end

universe u

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

section
universe u

structure MainPrefixGraphCode (M : TransitiveGround.{u})
    (K Labels C D rD T S E : ZFSet.{u}) : Prop where
  ordinal : ordinalSetProperty T
  stages : FunctionGraphOn T S
  transitions : FunctionGraphOn (chronologyPairs T) E
  stage_valid : ∀ i a, ZFSet.pair i a ∈ S →
    ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = a
  transition_valid : ∀ i j a b z, ZFSet.pair i a ∈ S → ZFSet.pair j b ∈ S →
    ZFSet.pair (ZFSet.pair j i) z ∈ E → LinkedMainTransitionCode M K Labels C D rD a b z
  identity : ∀ i p a, ZFSet.pair (ZFSet.pair i i) (ZFSet.pair p a) ∈ E →
    GraphDiagonalCode p ∧ GraphDiagonalCode a
  composition : ∀ i j k p₁ a₁ p₂ a₂ p₃ a₃,
    ZFSet.pair (ZFSet.pair j i) (ZFSet.pair p₁ a₁) ∈ E →
    ZFSet.pair (ZFSet.pair k j) (ZFSet.pair p₂ a₂) ∈ E →
    ZFSet.pair (ZFSet.pair k i) (ZFSet.pair p₃ a₃) ∈ E →
    GraphCompositionCode p₁ p₂ p₃ ∧ GraphCompositionCode a₁ a₂ a₃

end

section
open SetFormula
universe u

def MainPrefixCode (M : TransitiveGround.{u}) (K Labels C D rD z : ZFSet.{u}) : Prop :=
  ∃ T S E, z = mainPrefixCode T S E ∧ MainPrefixGraphCode M K Labels C D rD T S E

end

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





noncomputable def stageFieldUnion (j : Fin 11) : ZFSet.{u} :=
  ⋃₀ ZFSet.range (fun i => (run.diagram.stage i).stage.field j)

noncomputable def carrierUnion : ZFSet.{u} := run.stageFieldUnion 0

noncomputable def actorUnion : ZFSet.{u} := run.stageFieldUnion 3

theorem stageFieldValues_ground (j : Fin 11) :
    ZFSet.range (fun i => (run.diagram.stage i).stage.field j) ∈ M.sets :=
  M.familyCodeGraph_valueRange_mem unions separation run.key _ run.indices_ground
    (run.stageFieldFamily_ground j)

theorem stageFieldUnion_ground (j : Fin 11) : run.stageFieldUnion j ∈ M.sets :=
  M.union_mem unions (run.stageFieldValues_ground j)

theorem carrierUnion_ground : run.carrierUnion ∈ M.sets := run.stageFieldUnion_ground 0

theorem stageFieldFamily_subset_union (j : Fin 11) {i X : ZFSet.{u}}
    (entry : ZFSet.pair i X ∈ run.stageFieldFamily j) : X ⊆ run.stageFieldUnion j :=
  familyCodeGraph_value_subset_union run.key _ entry

theorem actorFamily_subset_union {i X : ZFSet.{u}}
    (entry : ZFSet.pair i X ∈ run.actorFamily) : X ⊆ run.actorUnion :=
  run.stageFieldFamily_subset_union 3 entry





noncomputable def cutoffFamily : ZFSet.{u} :=
  familyCodeGraph run.key (fun i => (run.diagram.stage i).cutoff)

noncomputable def serialFieldFamily (j : Fin 5) : ZFSet.{u} :=
  familyCodeGraph run.key (fun i => (run.linked i).serial.fields.graph j)

noncomputable def birthFamily : ZFSet.{u} :=
  familyCodeGraph run.key (fun i => (run.diagram.stage i).birth)

theorem cutoffFamily_ground : run.cutoffFamily ∈ M.sets := by
  have tails := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).main.stage.code)
    (fun i => ZFSet.pair (run.linked i).main.cutoff (run.linked i).serial.code)
    run.key_injective run.indices_ground run.stages_ground).2
  have cutoffs := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).main.cutoff) (fun i => (run.linked i).serial.code)
    run.key_injective run.indices_ground tails).1
  simpa only [cutoffFamily, run.linked_main] using cutoffs

theorem serialFieldFamily_ground (j : Fin 5) : run.serialFieldFamily j ∈ M.sets := by
  have tails := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).main.stage.code)
    (fun i => ZFSet.pair (run.linked i).main.cutoff (run.linked i).serial.code)
    run.key_injective run.indices_ground run.stages_ground).2
  have serialCodes := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).main.cutoff) (fun i => (run.linked i).serial.code)
    run.key_injective run.indices_ground tails).2
  have fieldCodes := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).serial.fields.code)
    (fun i => ZFSet.pair (run.linked i).serial.layerBound (run.linked i).serial.layers)
    run.key_injective run.indices_ground serialCodes).1
  exact M.familyCodeGraph_tuple_fields pairing unions powers separation run.key run.key_injective
    run.indices_ground 6 (fun i => (run.linked i).serial.fields.codeFields) fieldCodes j.succ.succ

theorem serialBirth_entry (i : I) :
    ZFSet.pair (run.diagram.stage i).cutoff (run.diagram.stage i).birth ∈
      (run.linked i).serial.fields.graph 3 := by
  have entry := (run.linked i).serial.fields.value_entry 3 (ZFSet.mem_insert _ _)
  rw [(run.linked i).terminal_values.2.2.2.1] at entry
  simpa only [run.linked_main] using entry

theorem birthFamily_ground : run.birthFamily ∈ M.sets := by
  apply M.familyCodeGraph_evaluation_ground pairing unions powers separation run.key
    (fun i => (run.diagram.stage i).cutoff) (fun i => (run.linked i).serial.fields.graph 3)
    (fun i => (run.diagram.stage i).birth) run.key_injective run.indices_ground
    run.cutoffFamily_ground (run.serialFieldFamily_ground 3)
  intro i y
  exact ⟨fun entry => ((run.linked i).serial.fields.graphFunction 3).unique entry (run.serialBirth_entry i),
    fun equal => equal.symm ▸ run.serialBirth_entry i⟩

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

noncomputable def cutoffSuccessorFamily : ZFSet.{u} :=
  familyCodeGraph run.key (fun i => insert (run.diagram.stage i).cutoff (run.diagram.stage i).cutoff)

noncomputable def cutoffLimit : ZFSet.{u} :=
  ⋃₀ ZFSet.range (fun i => insert (run.diagram.stage i).cutoff (run.diagram.stage i).cutoff)

theorem cutoffSuccessorFamily_ground : run.cutoffSuccessorFamily ∈ M.sets := by
  have tails := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).main.stage.code)
    (fun i => ZFSet.pair (run.linked i).main.cutoff (run.linked i).serial.code)
    run.key_injective run.indices_ground run.stages_ground).2
  have serialCodes := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).main.cutoff) (fun i => (run.linked i).serial.code)
    run.key_injective run.indices_ground tails).2
  have fieldCodes := (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    (fun i => (run.linked i).serial.fields.code)
    (fun i => ZFSet.pair (run.linked i).serial.layerBound (run.linked i).serial.layers)
    run.key_injective run.indices_ground serialCodes).1
  have times := M.familyCodeGraph_tuple_fields pairing unions powers separation run.key run.key_injective
    run.indices_ground 6 (fun i => (run.linked i).serial.fields.codeFields) fieldCodes 0
  simpa only [cutoffSuccessorFamily, GroundChronologyFields.codeFields, Fin.cases_zero,
    run.linked_main] using times

theorem cutoffSuccessorValues_ground :
    ZFSet.range (fun i => insert (run.diagram.stage i).cutoff (run.diagram.stage i).cutoff) ∈ M.sets :=
  M.familyCodeGraph_valueRange_mem unions separation run.key _ run.indices_ground run.cutoffSuccessorFamily_ground

theorem cutoffLimit_ground : run.cutoffLimit ∈ M.sets := M.union_mem unions run.cutoffSuccessorValues_ground

theorem cutoffLimit_mem (t : ZFSet.{u}) :
    t ∈ run.cutoffLimit ↔ ∃ i, t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff := by
  rw [cutoffLimit, familyCodeGraph_valueUnion_mem_iff]
  exact exists_congr (fun i => ZFSet.mem_insert_iff)

theorem cutoffLimit_ordinal : ordinalSetProperty run.cutoffLimit := by
  apply ordinalSetProperty_sUnion
  intro a ha
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 ha
  exact ordinalSetProperty_succ (run.diagram.stage i).cutoff_ordinal

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing
universe u v

def MainPrefixLimitStepRawCode (M : TransitiveGround.{u})
    (K Labels C D rD N old next : ZFSet.{u}) (w : Fin 32 → ZFSet.{u}) : Prop :=
  let v := mainPrefixLimitTargetFields w
  w 7 = insert (w 0) (w 0) ∧
  old = mainPrefixCode (w 0) (w 1) (w 2) ∧
  next = mainPrefixCode (w 7) (w 3) (w 4) ∧
  MainPrefixExtends old next ∧
  ZFSet.pair (w 0) (w 5) ∈ w 3 ∧
  LinkedMainStageRawCode M K Labels C D rD N (w 5) v ∧
  ZFSet.pair (v 11) (w 6) ∈ v 17 ∧
  MainLimitCoverageGraphCode (w 0) (w 1) (w 4) (v 0) (v 3) (v 1) (v 9) (v 11) (w 6)

def MainPrefixLimitStepCode (M : TransitiveGround.{u})
    (K Labels C D rD N old next : ZFSet.{u}) : Prop :=
  ∃ w : Fin 32 → ZFSet.{u}, (∀ j, w j ∈ M.sets) ∧
    MainPrefixLimitStepRawCode M K Labels C D rD N old next w

end PartitionPilot.Forcing



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

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem directLimitRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T U F L : ZFSet.{u}} (hT : T ∈ M.sets) (hU : U ∈ M.sets)
    (hF : F ∈ M.sets) (hL : L ∈ M.sets) : directLimitRelation T U F L ∈ M.sets := by
  have hB := M.union_mem unions (M.union_mem unions hF)
  let params := extend T (extend U (extend (⋃₀ ⋃₀ F) (extend F Fin.elim0)))
  have selected := M.bounded_separation_mem separation BoundedFormula.directLimitRelationEntryFormula
    params (Fin.cases hT (Fin.cases hU (Fin.cases hB (Fin.cases hF (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation hL hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.directLimitRelationEntryFormula
      (extend z params)) (ZFSet.prod L L) = directLimitRelation T U F L := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, directLimitRelation, ZFSet.mem_sep,
      BoundedFormula.truth_directLimitRelationEntryFormula]
    rfl
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def limitPointLabels : ZFSet.{u} :=
  indexedCarrierLabels run.indices run.carrierUnion run.carrierFamily

noncomputable def limitPointRelation : ZFSet.{u} :=
  directLimitRelation run.indices run.carrierUnion run.pointMapFamily run.limitPointLabels

noncomputable def limitPoints : ZFSet.{u} :=
  directLimitCarrier run.indices run.carrierUnion run.carrierFamily run.pointMapFamily

noncomputable def limitPointInclusions : ZFSet.{u} :=
  M.indexedClassInclusions run.indices run.carrierUnion run.limitPointLabels run.limitPointRelation

theorem limitPointLabels_ground : run.limitPointLabels ∈ M.sets :=
  M.indexedCarrierLabels_mem pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.carrierFamily_ground

theorem limitPointRelation_ground : run.limitPointRelation ∈ M.sets :=
  M.directLimitRelation_mem pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.pointMapFamily_ground run.limitPointLabels_ground

theorem limitPoints_ground : run.limitPoints ∈ M.sets :=
  M.equivalenceClasses_mem powers separation run.limitPointLabels_ground run.limitPointRelation_ground

theorem limitPointInclusions_ground : run.limitPointInclusions ∈ M.sets :=
  M.indexedClassInclusions_mem pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.limitPointLabels_ground run.limitPointRelation_ground

noncomputable def limitActorLabels : ZFSet.{u} :=
  indexedCarrierLabels run.indices run.actorUnion run.actorFamily

noncomputable def limitActorRelation : ZFSet.{u} :=
  directLimitRelation run.indices run.actorUnion run.actorMapFamily run.limitActorLabels

noncomputable def limitActors : ZFSet.{u} :=
  directLimitCarrier run.indices run.actorUnion run.actorFamily run.actorMapFamily

noncomputable def limitActorInclusions : ZFSet.{u} :=
  M.indexedClassInclusions run.indices run.actorUnion run.limitActorLabels run.limitActorRelation

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

open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def limitOrder : ZFSet.{u} :=
  indexedRelationLift run.indices run.carrierUnion run.limitPoints
    (run.stageFieldFamily 1) run.limitPointInclusions

noncomputable def limitMeetGraph : ZFSet.{u} :=
  indexedBinaryLift run.indices run.carrierUnion run.limitPoints
    (run.stageFieldFamily 2) run.limitPointInclusions

theorem limitOrder_ground : run.limitOrder ∈ M.sets :=
  M.indexedRelationLift_mem pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.limitPoints_ground (run.stageFieldFamily_ground 1)
    run.limitPointInclusions_ground

theorem limitMeetGraph_ground : run.limitMeetGraph ∈ M.sets :=
  M.indexedBinaryLift_mem pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.limitPoints_ground (run.stageFieldFamily_ground 2)
    run.limitPointInclusions_ground

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

noncomputable def limitAction : ZFSet.{u} :=
  indexedMixedBinaryLift run.indices run.actorUnion run.carrierUnion run.limitActors run.limitPoints
    (run.stageFieldFamily 7) run.limitActorInclusions run.limitPointInclusions

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_ExternalBirthLayerSeparation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth completion)
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "V" => M.externalStarVertices G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0))
  (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)) m one
local notation "owner" => completion.externalStarOwner P0 r0 μ0 A0

noncomputable def layerFiber (k : Nat) : ZFSet.{u} := layerBirthFiber B births.birth (compressionStamp oldTimes k)
noncomputable def layerOwners (k : Nat) : ZFSet.{u} := relationImage (births.layerFiber k) V owner
noncomputable def layerComponents (k : Nat) : ZFSet.{u} := graphRestriction (births.layerFiber k) owner
noncomputable def layerIndices (k : Nat) : ZFSet.{u} := constantFamilyGraph (births.layerOwners k) oldTimes
noncomputable def layerMaps (k : Nat) : ZFSet.{u} :=
  completion.externalSlotCopyMaps P0 r0 μ0 A0 (births.layerOwners k) (natSetCode (k % 3))
noncomputable def layerWitness (k : Nat) : ZFSet.{u} :=
  separatedLayerWitness (births.layerOwners k) (births.layerIndices k) (births.layerMaps k)
    (M.groundRelations U B) (births.layerComponents k) (births.layerFiber k)

end GroundExternalBirthData
end PartitionPilot.Forcing




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

noncomputable def serialFieldUnion (j : Fin 5) : ZFSet.{u} :=
  ⋃₀ ZFSet.range (fun i => (run.linked i).serial.fields.graph j)

theorem serialFieldUnion_ground (j : Fin 5) : run.serialFieldUnion j ∈ M.sets :=
  M.union_mem unions (M.familyCodeGraph_valueRange_mem unions separation run.key _
    run.indices_ground (run.serialFieldFamily_ground j))

theorem serialFieldUnion_mem (j : Fin 5) (z : ZFSet.{u}) :
    z ∈ run.serialFieldUnion j ↔ ∃ i, z ∈ (run.linked i).serial.fields.graph j :=
  familyCodeGraph_valueUnion_mem_iff _ z

theorem historyFieldValue_transition {i k : I} (before : i ≤ k) (j : Fin 5) {s : ZFSet.{u}}
    (time : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) :
    (run.diagram.stage k).history.fieldValue j s = (run.diagram.stage i).history.fieldValue j s := by
  have equal := (run.diagram.transition before).history_prefix s time
  exact Fin.cases equal.1 (Fin.cases equal.2.1 (Fin.cases equal.2.2.1
    (Fin.cases equal.2.2.2.1 (fun _ => equal.2.2.2.2)))) j

theorem historyFieldValue_compatible (i k : I) (j : Fin 5) {s : ZFSet.{u}}
    (first : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff)
    (second : s = (run.diagram.stage k).cutoff ∨ s ∈ (run.diagram.stage k).cutoff) :
    (run.diagram.stage i).history.fieldValue j s = (run.diagram.stage k).history.fieldValue j s := by
  obtain ⟨m, im, km⟩ := run.common_upper i k
  exact (run.historyFieldValue_transition im j first).symm.trans
    (run.historyFieldValue_transition km j second)

theorem serialFieldGraph_entry (i : I) (j : Fin 5) (s y : ZFSet.{u}) :
    ZFSet.pair s y ∈ (run.linked i).serial.fields.graph j ↔
      (s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) ∧
      y = (run.diagram.stage i).history.fieldValue j s := by
  have historyEqual : (run.linked i).main.history.fieldValue j s =
      (run.diagram.stage i).history.fieldValue j s :=
    congrArg (fun stage : GroundChronologicalMainStage M C D rD => stage.history.fieldValue j s) (run.linked_main i)
  constructor
  · intro entry
    have hs := (ZFSet.pair_mem_prod.1 (((run.linked i).serial.fields.function j).1 entry)).1
    have agreement := (run.linked i).agreement j s hs
    have value := ((run.linked i).serial.fields.value_eq_of_entry j entry).symm.trans agreement
    exact ⟨by simpa only [run.linked_main, ZFSet.mem_insert_iff] using hs,
      value.trans historyEqual⟩
  · rintro ⟨time, equal⟩
    have hs : s ∈ insert (run.linked i).main.cutoff (run.linked i).main.cutoff := by
      simpa only [run.linked_main, ZFSet.mem_insert_iff] using time
    have entry := (run.linked i).serial.fields.value_entry j hs
    have agreement := (run.linked i).agreement j s hs
    rw [agreement] at entry
    have value : ZFSet.pair s ((run.diagram.stage i).history.fieldValue j s) ∈
        (run.linked i).serial.fields.graph j := by rw [← historyEqual]; exact entry
    exact equal.symm ▸ value

theorem serialFieldUnion_entry (j : Fin 5) (s y : ZFSet.{u}) :
    ZFSet.pair s y ∈ run.serialFieldUnion j ↔
      ∃ i, (s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) ∧
        y = (run.diagram.stage i).history.fieldValue j s := by
  rw [run.serialFieldUnion_mem]
  exact exists_congr (fun i => run.serialFieldGraph_entry i j s y)

theorem serialFieldUnion_at (i : I) (j : Fin 5) {s : ZFSet.{u}}
    (time : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) (y : ZFSet.{u}) :
    ZFSet.pair s y ∈ run.serialFieldUnion j ↔ y = (run.diagram.stage i).history.fieldValue j s := by
  rw [run.serialFieldUnion_entry]
  constructor
  · intro h
    obtain ⟨k, before, equal⟩ := h
    exact equal.trans (run.historyFieldValue_compatible k i j before time)
  · intro equal
    exact ⟨i, time, equal⟩

theorem serialFieldUnion_function (j : Fin 5) : FunctionGraphOn run.cutoffLimit (run.serialFieldUnion j) := by
  refine ⟨⋃₀ ⋃₀ run.serialFieldUnion j, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, entry⟩ := (run.serialFieldUnion_mem j z).1 hz
    obtain ⟨s, _, y, _, rfl⟩ := ZFSet.mem_prod.1 (((run.linked i).serial.fields.function j).1 entry)
    have before := ((run.serialFieldGraph_entry i j s y).1 entry).1
    exact ZFSet.pair_mem_prod.2 ⟨(run.cutoffLimit_mem s).2 ⟨i, before⟩, pair_second_mem_doubleUnion hz⟩
  · intro s hs
    obtain ⟨i, before⟩ := (run.cutoffLimit_mem s).1 hs
    exact ⟨(run.diagram.stage i).history.fieldValue j s, (run.serialFieldUnion_at i j before _).2 rfl,
      fun y entry => (run.serialFieldUnion_at i j before y).1 entry⟩

noncomputable def limitPriorFields : GroundChronologyFields M run.cutoffLimit :=
  GroundChronologyFields.ofGraphs pairing unions run.cutoffLimit_ground
    run.serialFieldUnion run.serialFieldUnion_ground run.serialFieldUnion_function

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





noncomputable def limitValueGraph (F V : ZFSet.{u}) : ZFSet.{u} :=
  indexedValueLift run.indices run.carrierUnion run.limitPoints V F run.limitPointInclusions

theorem limitValueGraph_ground {F V : ZFSet.{u}} (hF : F ∈ M.sets) (hV : V ∈ M.sets) :
    run.limitValueGraph F V ∈ M.sets :=
  M.indexedValueLift_mem pairing unions powers separation run.indices_ground run.carrierUnion_ground
    run.limitPoints_ground hV hF run.limitPointInclusions_ground





noncomputable def heightValueBound : ZFSet.{u} := ZFSet.sUnion (ZFSet.sUnion (run.stageFieldUnion 10))

theorem heightValueBound_ground : run.heightValueBound ∈ M.sets :=
  M.union_mem unions (M.union_mem unions (run.stageFieldUnion_ground 10))

noncomputable def limitHeight : ZFSet.{u} :=
  run.limitValueGraph (run.stageFieldFamily 10) run.heightValueBound

theorem limitHeight_ground : run.limitHeight ∈ M.sets :=
  run.limitValueGraph_ground (run.stageFieldFamily_ground 10) run.heightValueBound_ground





noncomputable def limitBirth : ZFSet.{u} :=
  run.limitValueGraph run.birthFamily run.cutoffLimit

theorem limitBirth_ground : run.limitBirth ∈ M.sets :=
  run.limitValueGraph_ground run.birthFamily_ground run.cutoffLimit_ground





noncomputable def limitTerminalFields : Fin 5 → ZFSet.{u} :=
  Fin.cases run.limitPoints (Fin.cases run.limitOrder (Fin.cases run.limitMeetGraph
    (Fin.cases run.limitBirth (Fin.cases run.limitHeight Fin.elim0))))

theorem limitTerminalFields_ground : ∀ j, run.limitTerminalFields j ∈ M.sets :=
  Fin.cases run.limitPoints_ground (Fin.cases run.limitOrder_ground (Fin.cases run.limitMeetGraph_ground
    (Fin.cases run.limitBirth_ground (Fin.cases run.limitHeight_ground (fun i => Fin.elim0 i)))))





noncomputable def limitChronologyFields :
    GroundChronologyFields M (insert run.cutoffLimit run.cutoffLimit) :=
  run.limitPriorFields.appendTime pairing unions run.limitTerminalFields run.limitTerminalFields_ground

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalSerializedCore
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
open scoped ZFSet
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)
variable (prior : GroundSerializedChronology M T0 C D rD)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
variable (hOld : oldTimes ∈ T0)

noncomputable abbrev serializedFields : GroundChronologyFields M (insert births.limit births.limit) :=
  births.groundChronologyFields heights prior.fields data group action
    pairing unions powers separation infinite hG hP0 prior.ordinal hOld

end PartitionPilot.Forcing.GroundExternalBirthData

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundSerializedCandidateLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

structure GroundMainCandidateLevel (M : TransitiveGround.{u}) (K : ZFSet.{u}) where
  trace : ZFSet.{u}
  trace_ground : trace ∈ M.sets
  carrier : ZFSet.{u}
  carrier_ground : carrier ∈ M.sets
  hierarchy : GroundCumulativeHierarchyCode M (insert K K) trace
  entry : ZFSet.pair K carrier ∈ trace
  membership : ∀ x, x ∈ carrier ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank K





namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

noncomputable def validChronologies (C D rD : ZFSet.{u}) : ZFSet.{u} :=
  M.serializedChronologyCandidates level.carrier C D rD

end GroundMainCandidateLevel

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundLinkedMainStageLevels
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
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

noncomputable def linkedMainStageCandidates (B K Labels C D rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = z) B

end TransitiveGround

end PartitionPilot.Forcing



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

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

noncomputable def compressionCapImages : ZFSet.{u} :=
  certificate.compression.born.profiled.heighted.completion.boundedCapImages
    source.stage.carrier source.stage.order source.stage.meetGraph source.stage.action

end GroundInitialMainSuccessorData

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundTaskBearingSuccessorDecoding
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

def MainSuccessorTaskBindingsCode (M : TransitiveGround.{u}) (Labels : ZFSet.{u})
    (f : Fin 30 → ZFSet.{u}) : Prop :=
  f 21 = M.groundEligibleTasks (f 0) (f 6) (f 2) (f 4) (f 12) Labels ∧
  f 22 = literalTaskFieldGraph (f 21) (f 0) (M.groundRelations (f 0) (f 0))
    (M.groundMeetFilters (f 0) (f 2) (f 4)) Labels 0 ∧
  f 23 = literalTaskFieldGraph (f 21) (f 0) (M.groundRelations (f 0) (f 0))
    (M.groundMeetFilters (f 0) (f 2) (f 4)) Labels 1 ∧
  f 24 = literalTaskFieldGraph (f 21) (f 0) (M.groundRelations (f 0) (f 0))
    (M.groundMeetFilters (f 0) (f 2) (f 4)) Labels 3 ∧
  f 25 = literalTaskFieldGraph (f 21) (f 0) (M.groundRelations (f 0) (f 0))
    (M.groundMeetFilters (f 0) (f 2) (f 4)) Labels 4 ∧
  f 26 = M.groundPower (f 0) ∧
  TaskRepresentativesCode (f 27)
    (M.groundEligibleTasks (f 0) (f 6) (f 2) (f 4) (f 12) Labels)
    (f 0) (f 6) (f 2) (f 12) (M.groundRelations (f 0) (f 0))
    (M.groundMeetFilters (f 0) (f 2) (f 4)) Labels

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)





noncomputable def successorOutputValues : Fin 30 → ZFSet.{u} :=
  extend (source.stage.carrier)
    (extend (certificate.target.stage.carrier)
    (extend (source.stage.order)
    (extend (certificate.target.stage.order)
    (extend (source.stage.meetGraph)
    (extend (certificate.target.stage.meetGraph)
    (extend (source.stage.actors)
    (extend (certificate.target.stage.actors)
    (extend (source.stage.multiplication)
    (extend (certificate.target.stage.multiplication)
    (extend (source.stage.identity)
    (extend (certificate.target.stage.identity)
    (extend (source.stage.action)
    (extend (certificate.target.stage.action)
    (extend (source.stage.bottom)
    (extend (certificate.target.stage.bottom)
    (extend (source.stage.height)
    (extend (certificate.target.stage.height)
    (extend (certificate.transition.map.points)
    (extend (certificate.transition.map.actors)
    (extend (source.stage.top)
    (extend (source.stage.compressionTasks Labels)
    (extend (source.stage.compressionSources Labels)
    (extend (source.stage.compressionTargets Labels)
    (extend (source.stage.compressionSeparators Labels)
    (extend (source.stage.compressionFilters Labels)
    (extend (M.groundPower source.stage.carrier)
    (extend (certificate.Reps)
    (extend (certificate.compressionCapImages)
    (extend (certificate.target.stage.top)
    (Fin.elim0))))))))))))))))))))))))))))))

end PartitionPilot.Forcing.GroundInitialMainSuccessorData



namespace PartitionPilot.Forcing
open SetFormula
universe u v w

def TaskBearingMainSuccessorRawCode (M : TransitiveGround.{u})
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : ZFSet.{u})
    (source target : Fin 24 → ZFSet.{u}) (extra : Fin 8 → ZFSet.{u}) : Prop :=
  LinkedMainTransitionRawCode M K Labels C D rD N sourceCode targetCode z points actors
    sourceBirth targetBirth source target ∧
  source 11 ∈ target 11 ∧
  MainSuccessorOutputCode (linkedSuccessorOutputFields source target points actors extra) ∧
  MainSuccessorTaskBindingsCode M Labels (linkedSuccessorOutputFields source target points actors extra)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

def TaskBearingMainSuccessorCode (M : TransitiveGround.{u})
    (K Labels C D rD N sourceCode targetCode z : ZFSet.{u}) : Prop :=
  ∃ fields : Fin 60 → ZFSet.{u}, (∀ j, fields j ∈ M.sets) ∧
    TaskBearingMainSuccessorRawCode M K Labels C D rD N sourceCode targetCode z
      (fields 48) (fields 49) (fields 50) (fields 51)
      (fun j => fields (j.castAdd 36))
      (fun j => fields (Fin.natAdd 24 (j.castAdd 12)))
      (fun j => fields (Fin.natAdd 52 j))

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundOmegaOneTaskBearingSuccessorFunction
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

noncomputable def taskBearingSuccessorRelation (S V K Labels C D rD : ZFSet.{u}) : ZFSet.{u} :=
  M.definableRelation (taskBearingSuccessorPairFormula 2 3 4 5 6 7 8 9 (0 : Fin 10) 1)
    (taskBearingSuccessorParams S V K Labels C D rD) S (ZFSet.prod V V)

end TransitiveGround
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



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

def PreservesOldProfiles : Prop :=
  ∀ (i j : I) (before : i ≤ j), (run.diagram.transition before).PreservesOldProfiles

end PartitionPilot.Forcing.GroundMainPrefix



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundLinkedProfilePreservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

def LinkedProfilePreservingTransitionCode (M : TransitiveGround.{u})
    (K Labels C D rD a b z : ZFSet.{u}) : Prop :=
  ∃ source target : GroundLinkedMainStage M K Labels C D rD,
    source.code = a ∧ target.code = b ∧
    ∃ transition : GroundChronologicalMainTransition source.main target.main,
      transition.map.code = z ∧ transition.CoversOldBirths ∧ transition.PreservesOldProfiles

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
open SetFormula
universe u v

def MainPrefixProfileGraphCode (M : TransitiveGround.{u})
    (K Labels C D rD S E : ZFSet.{u}) : Prop :=
  ∀ i j a b z, ZFSet.pair i a ∈ S → ZFSet.pair j b ∈ S →
    ZFSet.pair (ZFSet.pair j i) z ∈ E →
    LinkedProfilePreservingTransitionCode M K Labels C D rD a b z

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u v

def PreservedMainPrefixCode (M : TransitiveGround.{u}) (K Labels C D rD z : ZFSet.{u}) : Prop :=
  ∃ T S E, z = mainPrefixCode T S E ∧ MainPrefixGraphCode M K Labels C D rD T S E ∧
    MainPrefixProfileGraphCode M K Labels C D rD S E

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialPreservedMainPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetFormula
universe u v

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def mainPrefixCandidates (B K Labels C D rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (MainPrefixCode M K Labels C D rD) B

end TransitiveGround

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

noncomputable def validMainPrefixes (Labels C D rD : ZFSet.{u}) : ZFSet.{u} :=
  M.mainPrefixCandidates level.carrier K Labels C D rD

end GroundMainCandidateLevel
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

structure FinalChronology
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (level : GroundMainCandidateLevel M K) where
  serial : GroundSerializedChronology M (insert run.cutoffLimit run.cutoffLimit) C D rD
  code_rank : ZFSet.rank serial.code < ZFSet.rank K
  candidate : serial.code ∈ level.validChronologies C D rD
  graphs : serial.fields.graph = run.limitChronologyFields.graph
  values : ∀ j s, serial.fields.value j s = run.limitChronologyFields.value j s
  attained_layer_bound : serial.layerBound = functionGraphRange
    (chronologyPairs (insert run.cutoffLimit run.cutoffLimit)) serial.layers

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

structure GroundMainFinalInclusions
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (geometry : GroundMainFinalGeometry M C D rD) where
  pointMap : I → ZFSet.{u}
  actorMap : I → ZFSet.{u}
  pointFamily : ZFSet.{u}
  actorFamily : ZFSet.{u}
  pointMap_ground : ∀ i, pointMap i ∈ M.sets
  actorMap_ground : ∀ i, actorMap i ∈ M.sets
  pointFamily_ground : pointFamily ∈ M.sets
  actorFamily_ground : actorFamily ∈ M.sets
  pointFamily_function : FunctionGraphOn run.indices pointFamily
  actorFamily_function : FunctionGraphOn run.indices actorFamily
  pointFamily_entry : ∀ i f, ZFSet.pair (run.key i) f ∈ pointFamily ↔ f = pointMap i
  actorFamily_entry : ∀ i f, ZFSet.pair (run.key i) f ∈ actorFamily ↔ f = actorMap i
  point_embedding : ∀ i, MeetEmbeddingCode (run.diagram.stage i).stage.carrier geometry.carrier
    (run.diagram.stage i).stage.order geometry.order (run.diagram.stage i).stage.meetGraph
    geometry.meetGraph (pointMap i)
  order_iff : ∀ i x y p q, ZFSet.pair x p ∈ pointMap i → ZFSet.pair y q ∈ pointMap i →
    (ZFSet.pair p q ∈ geometry.order ↔ ZFSet.pair x y ∈ (run.diagram.stage i).stage.order)
  actor_embedding : ∀ i, GroupEmbeddingCode (run.diagram.stage i).stage.actors geometry.actors
    (run.diagram.stage i).stage.multiplication geometry.multiplication
    (run.diagram.stage i).stage.identity geometry.identity (actorMap i)
  inverse_iff : ∀ i a b g h, ZFSet.pair a g ∈ actorMap i → ZFSet.pair b h ∈ actorMap i →
    (ZFSet.pair g h ∈ geometry.inverse ↔ ZFSet.pair a b ∈ (run.diagram.stage i).stage.inverse)
  action_iff : ∀ i a g x y p q, ZFSet.pair a g ∈ actorMap i →
    ZFSet.pair x p ∈ pointMap i → ZFSet.pair y q ∈ pointMap i →
    (ZFSet.pair (ZFSet.pair g p) q ∈ geometry.action ↔
      ZFSet.pair (ZFSet.pair a x) y ∈ (run.diagram.stage i).stage.action)
  bottom : ∀ i, ZFSet.pair (run.diagram.stage i).stage.bottom geometry.bottom ∈ pointMap i
  height : ∀ i x p, ZFSet.pair x p ∈ pointMap i → ∀ t,
    (ZFSet.pair p t ∈ geometry.height ↔ ZFSet.pair x t ∈ (run.diagram.stage i).stage.height)
  birth : ∀ i x p t, ZFSet.pair x p ∈ pointMap i →
    (ZFSet.pair p t ∈ geometry.birth ↔ ZFSet.pair x t ∈ (run.diagram.stage i).birth)
  old_fiber : ∀ i p t, (t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff) →
    (ZFSet.pair p t ∈ geometry.birth ↔ ∃ x ∈ (run.diagram.stage i).stage.carrier,
      ZFSet.pair x t ∈ (run.diagram.stage i).birth ∧ ZFSet.pair x p ∈ pointMap i)
  point_comp : ∀ {i j} (before : i ≤ j), relationCompose (run.diagram.stage i).stage.carrier
    (run.diagram.stage j).stage.carrier geometry.carrier (run.diagram.transition before).map.points
    (pointMap j) = pointMap i
  actor_comp : ∀ {i j} (before : i ≤ j), relationCompose (run.diagram.stage i).stage.actors
    (run.diagram.stage j).stage.actors geometry.actors (run.diagram.transition before).map.actors
    (actorMap j) = actorMap i
  point_coverage : ∀ p ∈ geometry.carrier, ∃ i x, x ∈ (run.diagram.stage i).stage.carrier ∧
    ZFSet.pair x p ∈ pointMap i
  actor_coverage : ∀ g ∈ geometry.actors, ∃ i a, a ∈ (run.diagram.stage i).stage.actors ∧
    ZFSet.pair a g ∈ actorMap i
  agreement : ∀ i g h g' h' x x', ZFSet.pair g g' ∈ actorMap i →
    ZFSet.pair h h' ∈ actorMap i → ZFSet.pair x x' ∈ pointMap i →
    ActionAgreementBelow (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.order
      (run.diagram.stage i).stage.action g h x →
    ActionAgreementBelow geometry.carrier geometry.order geometry.action g' h' x'

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixRawCoveredAppend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula SetRealization
universe u v

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def preservedMainPrefixCandidates (B K Labels C D rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (PreservedMainPrefixCode M K Labels C D rD) B

end TransitiveGround

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

noncomputable def preservedMainPrefixes (Labels C D rD : ZFSet.{u}) : ZFSet.{u} :=
  M.preservedMainPrefixCandidates level.carrier K Labels C D rD

end GroundMainCandidateLevel
end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixSelectedStepTotality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula SetRealization
universe u v

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

noncomputable def recursionPrefixes (Omega Labels C D rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (MainPrefixRecursionIndexCode Omega) (level.preservedMainPrefixes Labels C D rD)

end GroundMainCandidateLevel
end

open SetFormula SetRealization
universe u v w

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_MainPrefixConditionalStepCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

def MainPrefixConditionalStepCode (M : TransitiveGround.{u})
    (K Labels C D rD N f old next : ZFSet.{u}) : Prop :=
  MainPrefixSelectedStepCode f old next ∨
    ∃ T S E, old = mainPrefixCode T S E ∧ NonzeroLimitOrdinalCode T ∧
      MainPrefixLimitStepCode M K Labels C D rD N old next

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainConditionalTotality
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

noncomputable def mainPrefixConditionalRelation (S K Labels C D rD N f : ZFSet.{u}) : ZFSet.{u} :=
  M.definableRelation (mainPrefixConditionalStepFormula 2 3 4 5 6 7 8 (0 : Fin 9) 1)
    (mainPrefixConditionalParams K Labels C D rD N f) S S

end TransitiveGround
end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainOrdinalConstructionData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

structure GroundMainOrdinalConstructionData (M : TransitiveGround.{u}) (K C : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) where
  level : GroundMainCandidateLevel M K
  seed : GroundInitialMainSeedData M K C
  seedRun : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
    (rationalLtGraph seed.fractionCode) pairing unions powers separation (Fin 2)
  initial : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
    (rationalLtGraph seed.fractionCode) pairing unions powers separation
    {i : Fin 2 // seedRun.key i ∈ natSetCode 1}
  domain : ZFSet.{u}
  domain_eq : domain = level.recursionPrefixes C C C (rationalCarrier seed.fractionCode)
    (rationalLtGraph seed.fractionCode)
  domain_ground : domain ∈ M.sets
  initial_member : initial.code ∈ domain
  initial_indices : initial.indices = natSetCode 1
  initial_profiles : initial.PreservesOldProfiles
  initial_rank : ZFSet.rank initial.code < ZFSet.rank K
  initial_stages : initial.stageGraph = graphRestriction (natSetCode 1) seedRun.stageGraph
  initial_transitions : initial.transitionGraph =
    graphRestriction (chronologyPairs (natSetCode 1)) seedRun.transitionGraph
  initial_source : ∃ i, initial.key i = natSetCode 0 ∧ initial.diagram.stage i = seed.source
  successors : ZFSet.{u}
  successors_ground : successors ∈ M.sets
  successors_function : ZFSet.IsFunc
    (M.linkedMainStageCandidates level.carrier K C C (rationalCarrier seed.fractionCode)
      (rationalLtGraph seed.fractionCode)) (ZFSet.prod level.carrier level.carrier) successors
  successors_selected : successors ⊆ M.taskBearingSuccessorRelation
    (M.linkedMainStageCandidates level.carrier K C C (rationalCarrier seed.fractionCode)
      (rationalLtGraph seed.fractionCode)) level.carrier K C C
      (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode)
  successors_entries : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ successors →
    target ∈ M.linkedMainStageCandidates level.carrier K C C (rationalCarrier seed.fractionCode)
      (rationalLtGraph seed.fractionCode) ∧ z ∈ level.carrier ∧
      TaskBearingMainSuccessorCode M K C C (rationalCarrier seed.fractionCode)
        (rationalLtGraph seed.fractionCode) ZFSet.omega source target z
  steps : ZFSet.{u}
  steps_ground : steps ∈ M.sets
  steps_function : ZFSet.IsFunc domain domain steps
  steps_selected : steps ⊆ M.mainPrefixConditionalRelation domain K C C
    (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) ZFSet.omega successors
  steps_entries : ∀ old next, ZFSet.pair old next ∈ steps → next ∈ domain ∧
    MainPrefixConditionalStepCode M K C C (rationalCarrier seed.fractionCode)
      (rationalLtGraph seed.fractionCode) ZFSet.omega successors old next
  history : ZFSet.{u}
  history_ground : history ∈ M.sets
  trace : OrdinalRecursionTrace (MainPrefixTraceStepCode domain initial.code steps) C history
  trace_unique : ∀ q, OrdinalRecursionTrace (MainPrefixTraceStepCode domain initial.code steps) C q →
    q = history

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalRowOrdinaryZF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainFinalGeometry
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

theorem decoded_directed
    (directed : ∀ x ∈ geometry.carrier, ∀ y ∈ geometry.carrier,
      ∃ z ∈ geometry.carrier, ZFSet.pair x z ∈ geometry.order ∧
        ZFSet.pair y z ∈ geometry.order) :
    letI := geometry.meet.order.toPartialOrder
    ∀ x y : SetMembers geometry.carrier, ∃ z, x ≤ z ∧ y ≤ z := by
  let := geometry.meet.order.toPartialOrder
  intro x y
  obtain ⟨z, hz, xz, yz⟩ := directed _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y)
  refine ⟨SetMembers.ofMem z hz, ?_, ?_⟩
  · change ZFSet.pair (SetMembers.raw x) (SetMembers.raw (SetMembers.ofMem z hz)) ∈ geometry.order
    simpa only [SetMembers.raw_ofMem] using xz
  · change ZFSet.pair (SetMembers.raw y) (SetMembers.raw (SetMembers.ofMem z hz)) ∈ geometry.order
    simpa only [SetMembers.raw_ofMem] using yz

end GroundMainFinalGeometry

end PartitionPilot.Forcing

end OAI
end


