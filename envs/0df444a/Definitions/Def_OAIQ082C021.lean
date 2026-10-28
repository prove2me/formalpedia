-- Prove2me | Definitions.Def_OAIQ082C021
-- name    : OAIQ082C021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:45:46.021998+00:00
-- url     : https://prove2.me/theorems/2dbc5c0b-b3ed-4da3-ac25-208a0d766f70
-- title:
--   Definitions bundle OAIQ082C021 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 241 declarations of OpenAI's Lean: 77 definitions, 1 instance and 163 theorems. The definitions and types are `OAI.BinPackingGap.GraphPackingJobStream.rawPair`, `OAI.BinPackingGap.InventoryData.allGlobalRequests`, `OAI.BinPackingGap.InventoryData.constructedLocalState`, `OAI.BinPackingGap.InventoryData.deadlineShiftData`, `OAI.BinPackingGap.InventoryData.designated`, `OAI.BinPackingGap.InventoryData.earlierGoodKeyTuples`, `OAI.BinPackingGap.InventoryData.earlierKeyItems`, `OAI.BinPackingGap.InventoryData.earlierKeys`, `OAI.BinPackingGap.InventoryData.edgeLongTuples`, `OAI.BinPackingGap.InventoryData.edgeLongTuplesAt`, `OAI.BinPackingGap.InventoryData.integralFlagAllocation`, `OAI.BinPackingGap.InventoryData.integralGlobalAllocation`, `OAI.BinPackingGap.InventoryData.integralRoleEquiv`, `OAI.BinPackingGap.InventoryData.longMatchesAt`, `OAI.BinPackingGap.InventoryData.minusPoint`, `OAI.BinPackingGap.InventoryData.plusPoint`, `OAI.BinPackingGap.InventoryData.rawItemListReindexing`, `OAI.BinPackingGap.InventoryData.remainingEarlierW`, `OAI.BinPackingGap.InventoryData.stateMainPattern`, `OAI.BinPackingGap.InventoryData.statePoolTemplates`, `OAI.BinPackingGap.InventoryData.taggedAddress`, `OAI.BinPackingGap.InventoryData.taggedNodeCell`, `OAI.BinPackingGap.InventoryData.taggedNodeDepth`, `OAI.BinPackingGap.InventoryData.templateAnchorCopy`, `OAI.BinPackingGap.InventoryData.templateBase`, `OAI.BinPackingGap.InventoryData.templateCopyEquiv`, `OAI.BinPackingGap.InventoryData.templateFlagSpecies`, `OAI.BinPackingGap.InventoryData.templateGlobalSpecies`, `OAI.BinPackingGap.InventoryData.templateLocalCopy`, `OAI.BinPackingGap.InventoryData.templateRowCopy`, `OAI.BinPackingGap.InventoryData.testCell`, `OAI.BinPackingGap.InventoryData.testInterval`, `OAI.BinPackingGap.InventoryData.testLeft`, `OAI.BinPackingGap.InventoryData.testRight`, `OAI.BinPackingGap.LiteralSlotGraphMachine.copy`, `OAI.BinPackingGap.LiteralSlotGraphMachine.drain`, `OAI.BinPackingGap.LiteralSlotGraphMachine.graphInput`, `OAI.BinPackingGap.LiteralSlotGraphMachine.innerBody`, `OAI.BinPackingGap.LiteralSlotGraphMachine.innerLoop`, `OAI.BinPackingGap.LiteralSlotGraphMachine.inputBits` and 37 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Arithmetic_NatExpressionBranch`, `BinPacking_Configurations_CoverageSoundness`, `BinPacking_Configurations_ReductionCompleteness`, `BinPacking_Configurations_ReductionFractional`, `BinPacking_Hardness_LiteralSlotGraphComputation`, `BinPacking_Hardness_LiteralSlotGraphEnumeration`, `BinPacking_Hardness_PCPPackingGap`, `BinPacking_Inventory_EdgeLongConsumption`, `BinPacking_Inventory_IntegralSpeciesCounts`, `BinPacking_Inventory_InventoryScores`, `BinPacking_Inventory_LocalCompletionCoverage`, `BinPacking_Machines_GraphPackingJobList`, `BinPacking_Machines_GraphPackingOutput`, `BinPacking_Machines_GraphPackingStockStreams`, `BinPacking_Machines_MachineBoundedIteration`, `BinPacking_Machines_PackingCountedProgram`, `BinPacking_Machines_PackingPowerProgram`, `BinPacking_Packing_ConstructLocalState`, `BinPacking_Packing_ExtractedCover`, `BinPacking_Packing_LocalTemplateBases`, `BinPacking_Packing_PackingCoordinates`, `BinPacking_Packing_PackingGapDefinitions`, `BinPacking_Packing_PackingScalarExpression`, `BinPacking_Search_SearchFinalizeMachine`, `BinPacking_Search_SearchInitialItemsMachine`, `BinPacking_Search_SearchInitializeEncoding`, `BinPacking_Search_SearchStageMachines`, `BinPacking_Search_SearchUpdateMachine`, `BinPacking_Trees_TestGeometry`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C010`, `OAIQ082C011`, `OAIQ082C013`, `OAIQ082C014` and `OAIQ082C015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C024`, `OAIQ082C025` and `OAIQ082C026`; the statements `OAI_BinPackingGap_InventoryData_edge_long_matches_capacity`, `OAI.BinPackingGap.InventoryData.edge_long_matches_capacity_oaiq082`, `OAI_BinPackingGap_InventoryData_long_matches_at_nonexcluded`, `OAI.BinPackingGap.InventoryData.long_matches_at_nonexcluded_oaiq082`, `OAI_BinPackingGap_PCPFoundation_packingOutput_sound` and `OAI.BinPackingGap.PCPFoundation.packingOutput_sound_oaiq082`; the proofs of `OAI_BinPackingGap_InventoryData_edge_long_matches_capacity`, `OAI.BinPackingGap.InventoryData.edge_long_matches_capacity_oaiq082`, `OAI_BinPackingGap_InventoryData_long_matches_at_nonexcluded`, `OAI.BinPackingGap.InventoryData.long_matches_at_nonexcluded_oaiq082`, `OAI_BinPackingGap_extractedCover_card_le` and `OAI.BinPackingGap.extractedCover_card_le_oaiq082`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C010
import Definitions.Def_OAIQ082C011
import Definitions.Def_OAIQ082C013
import Definitions.Def_OAIQ082C014
import Definitions.Def_OAIQ082C015

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_NatExpressionBranch
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.NatExpressionCompiler

open BinaryRegisterProgram

instance instFintypeBinaryOp : Fintype BinaryOp where
  elems := {.add, .mul, .monus}
  complete op := by cases op <;> simp

end BinPackingGap.NatExpressionCompiler

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryScores
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeDescriptor _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeTreeDescriptor _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace InventoryData

variable (D : InventoryData)

def designated {v : D.Vertex} : D.TestAt v × Fin D.d → D.MBase v
  | ⟨.inl leaf, j⟩ => .inl (.inl (leaf.val, j))
  | ⟨.inr (.inl leaf), j⟩ => .inl (.inr (.inl (leaf.val, j)))
  | ⟨.inr (.inr r), j⟩ => .inr (r, j)

end InventoryData

end BinPackingGap

noncomputable section

namespace BinPackingGap
namespace InventoryData

variable (D : InventoryData)

def earlierKeys (h : ℕ) (hle : h ≤ D.graph.edges.length) : Finset D.Item := by
  classical
  exact Finset.univ.image fun j => D.keyItem (D.allJobEquiv.symm (D.prefixJobIndex h hle j))

end InventoryData
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_TestGeometry
attribute [-instance] _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeDescriptor _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeTreeDescriptor _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

theorem incidencePosition_injective (v : D.Vertex) :
    Function.Injective (D.incidencePosition (v := v)) := by
  rintro ⟨⟨⟨e, s⟩, hes⟩, i⟩ ⟨⟨⟨f, t⟩, hft⟩, j⟩ h
  change (e, i) = (f, j) at h
  have he : e = f := congrArg Prod.fst h
  have hij : i = j := congrArg Prod.snd h
  subst f
  subst j
  have hst : s = t := D.graph.endpoint_injective e (hes.trans hft.symm)
  subst t
  rfl

def testLeft {v : D.Vertex} : D.TestAt v → ℚ
  | .inl p => TreeGeometry.left D.graph.edges.length D.R D.geometryBound .plus p.val.val
  | .inr (.inl p) =>
      TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus p.val.val
  | .inr (.inr j) =>
      Geometry.jobLeft D.graph.edges.length D.R D.geometryBound D.L (D.incidencePosition j)

def testRight {v : D.Vertex} : D.TestAt v → ℚ
  | .inl p => TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus p.val.val
  | .inr (.inl p) =>
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound .minus p.val.val
  | .inr (.inr j) => Geometry.baseline D.graph.edges.length D.R (D.incidencePosition j)

def testCell {v : D.Vertex} (t : D.TestAt v) : Set ℚ :=
  Set.Icc (D.testLeft t) (D.testRight t)

def testInterval {v : D.Vertex} (t : D.TestAt v) : Set ℚ :=
  Set.Ico (D.testLeft t) (D.testRight t)

theorem testLeft_lt_testRight {v : D.Vertex} (t : D.TestAt v) :
    D.testLeft t < D.testRight t := by
  rcases t with p | p | j
  · exact TreeGeometry.left_lt_right _ _ _ .plus p.val.val
  · exact TreeGeometry.left_lt_right _ _ _ .minus p.val.val
  · exact Geometry.jobLeft_lt_baseline _ _ _ _ (D.incidencePosition j)

theorem testInterval_subset_testCell {v : D.Vertex} (t : D.TestAt v) :
    D.testInterval t ⊆ D.testCell t := fun _ hx => ⟨hx.1, hx.2.le⟩

theorem plusLeaf_right_lt_tenth (hplusheight : D.plus.height = D.L)
    (hL : 1 ≤ D.L) (p : D.PlusLeaf) :
    TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus p.val.val < 1 / 10 := by
  have hlength : p.val.val.length = D.L := (D.plus.length_leaf _ p.property).trans hplusheight
  have hn : p.val.val ≠ [] := by
    intro h
    rw [h] at hlength
    simp only [List.length_nil] at hlength
    omega
  have hb := TreeGeometry.nonroot_endpoints D.graph.edges.length D.R D.geometryBound .plus
    hn (TreeGeometry.boundedAddress_node p.val D.plus_branch_le_geometryBound)
  simpa only [TreeGeometry.rootOffset, zero_add] using hb.2

theorem plusLeaf_job_disjoint (hplusheight : D.plus.height = D.L)
    (hL : 1 ≤ D.L) {v : D.Vertex} (p : D.PlusLeaf) (j : D.IncidencePosition v) :
    Disjoint (D.testCell (.inl p : D.TestAt v)) (D.testCell (.inr (.inr j))) := by
  have hp := D.plusLeaf_right_lt_tenth hplusheight hL p
  have hj := Geometry.one_tenth_lt_jobLeft D.graph.edges.length D.R D.geometryBound D.L
    (D.incidencePosition j)
  exact disjoint_of_endpoint_lt (hp.trans hj)

theorem minusLeaf_job_disjoint {v : D.Vertex} (p : D.MinusLeaf)
    (j : D.IncidencePosition v) :
    Disjoint (D.testCell (.inr (.inl p) : D.TestAt v)) (D.testCell (.inr (.inr j))) := by
  have hp := D.tree_endpoints_in_root p.val .minus D.minus_branch_le_geometryBound
  have hj := Geometry.job_baseline_lt_one D.graph.edges.length D.R (D.incidencePosition j)
  norm_num only [TreeGeometry.rootOffset] at hp
  change 4 ≤ TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus p.val.val ∧
    _ ≤ 5 at hp
  have hgap : Geometry.baseline D.graph.edges.length D.R (D.incidencePosition j) <
      TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus p.val.val := by
    linarith [hp.1]
  exact (disjoint_of_endpoint_lt hgap).symm

theorem testCell_disjoint (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    {v : D.Vertex} {s t : D.TestAt v} (hne : s ≠ t) :
    Disjoint (D.testCell s) (D.testCell t) := by
  rcases s with p | p | j <;> rcases t with q | q | k
  · apply D.same_depth_cells_disjoint
      ((D.plus.length_leaf _ p.property).trans hplusheight)
      ((D.plus.length_leaf _ q.property).trans hplusheight)
      (TreeGeometry.boundedAddress_node p.val D.plus_branch_le_geometryBound)
      (TreeGeometry.boundedAddress_node q.val D.plus_branch_le_geometryBound)
    intro h
    have hpq : p = q := Subtype.ext (Subtype.ext (congrArg Prod.snd h))
    exact hne (congrArg Sum.inl hpq)
  · apply D.same_depth_cells_disjoint
      ((D.plus.length_leaf _ p.property).trans hplusheight)
      ((D.minus.length_leaf _ q.property).trans hminusheight)
      (TreeGeometry.boundedAddress_node p.val D.plus_branch_le_geometryBound)
      (TreeGeometry.boundedAddress_node q.val D.minus_branch_le_geometryBound)
    intro h
    have hs := congrArg Prod.fst h
    cases hs
  · exact D.plusLeaf_job_disjoint hplusheight hL p k
  · apply D.same_depth_cells_disjoint
      ((D.minus.length_leaf _ p.property).trans hminusheight)
      ((D.plus.length_leaf _ q.property).trans hplusheight)
      (TreeGeometry.boundedAddress_node p.val D.minus_branch_le_geometryBound)
      (TreeGeometry.boundedAddress_node q.val D.plus_branch_le_geometryBound)
    intro h
    have hs := congrArg Prod.fst h
    cases hs
  · apply D.same_depth_cells_disjoint
      ((D.minus.length_leaf _ p.property).trans hminusheight)
      ((D.minus.length_leaf _ q.property).trans hminusheight)
      (TreeGeometry.boundedAddress_node p.val D.minus_branch_le_geometryBound)
      (TreeGeometry.boundedAddress_node q.val D.minus_branch_le_geometryBound)
    intro h
    have hpq : p = q := Subtype.ext (Subtype.ext (congrArg Prod.snd h))
    exact hne (congrArg (fun l => Sum.inr (Sum.inl l)) hpq)
  · exact D.minusLeaf_job_disjoint p k
  · exact (D.plusLeaf_job_disjoint hplusheight hL q j).symm
  · exact (D.minusLeaf_job_disjoint q j).symm
  · apply Geometry.closedJobCell_disjoint
    intro h
    have hjk := D.incidencePosition_injective v h
    exact hne (congrArg (fun r => Sum.inr (Sum.inr r)) hjk)

theorem testInterval_disjoint (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    {v : D.Vertex} {s t : D.TestAt v} (hne : s ≠ t) :
    Disjoint (D.testInterval s) (D.testInterval t) :=
  (D.testCell_disjoint hplusheight hminusheight hL hne).mono
    (D.testInterval_subset_testCell s) (D.testInterval_subset_testCell t)

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingCoordinates
attribute [-instance] _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeDescriptor _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeTreeDescriptor _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

theorem mainBaseline_designated {v : D.Vertex} (q : D.TestAt v × Fin D.d) :
    D.mainBaseline (D.designated q) = D.testRight q.1 := by
  rcases q with ⟨t, j⟩
  rcases t with p | p | r <;> rfl

theorem deadline_designated {v : D.Vertex} (q : D.TestAt v × Fin D.d) :
    D.deadline (D.designated q) = D.testLeft q.1 := by
  rcases q with ⟨t, j⟩
  rcases t with p | p | r
  · simp [designated, deadline, treeDeadline, p.property, testLeft]
  · simp [designated, deadline, treeDeadline, p.property, testLeft]
  · rfl

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_LocalCompletionCoverage
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeDescriptor _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeTreeDescriptor _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

open IntervalCoverage

variable (D : InventoryData)

theorem designated_injective (v : D.Vertex) :
    Function.Injective (D.designated (v := v)) := by
  rintro ⟨(p | p | j), a⟩ ⟨(q | q | k), b⟩ h <;>
    simp_all [designated, Subtype.val_inj]

theorem deadline_undesignated {v : D.Vertex} (i : D.MBase v)
    (hi : ∀ q : D.TestAt v × Fin D.d, D.designated q ≠ i) :
    D.deadline i = D.mainBaseline i := by
  rcases i with (⟨node, j⟩ | ⟨node, j⟩ | padding) | job
  · have hn : node.val ∉ D.plus.leaves := by
      intro hn
      exact hi (.inl ⟨node, hn⟩, j) rfl
    simp only [deadline, treeDeadline, hn, ite_false, mainBaseline, treeBaseline]
  · have hn : node.val ∉ D.minus.leaves := by
      intro hn
      exact hi (.inr (.inl ⟨node, hn⟩), j) rfl
    simp only [deadline, treeDeadline, hn, ite_false, mainBaseline, treeBaseline]
  · rfl
  · exact False.elim (hi (.inr (.inr job.1), job.2) rfl)

def deadlineShiftData (v : D.Vertex) :
    ShiftData (D.MBase v) (D.TestAt v) D.d ℚ where
  baseline := D.mainBaseline
  left := D.testLeft
  right := D.testRight
  designated := ⟨D.designated, D.designated_injective v⟩
  baseline_designated := D.mainBaseline_designated
  left_le_right := fun t => (D.testLeft_lt_testRight t).le

theorem deadline_prefix_active (v : D.Vertex) (a : ℚ) :
    prefixCount (D.deadline (v := v)) a =
      prefixCount (D.mainBaseline (v := v)) a +
        D.d * ((D.deadlineShiftData v).activeTests a).card := by
  exact (D.deadlineShiftData v).deadline_prefix_of_agrees
    (D.deadline (v := v)) D.deadline_designated D.deadline_undesignated a

theorem deadline_active_card (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    (v : D.Vertex) (a : ℚ) :
    ((D.deadlineShiftData v).activeTests a).card =
      @ite ℕ (∃ t : D.TestAt v, a ∈ D.testInterval t)
        (Classical.propDecidable _) 1 0 := by
  classical
  have hdisjoint : ∀ s t : D.TestAt v, s ≠ t →
      Disjoint (Set.Ico ((D.deadlineShiftData v).left s)
        ((D.deadlineShiftData v).right s))
        (Set.Ico ((D.deadlineShiftData v).left t)
        ((D.deadlineShiftData v).right t)) := by
    intro s t hst
    exact D.testInterval_disjoint hplusheight hminusheight hL hst
  have hc := (D.deadlineShiftData v).activeTests_card hdisjoint a
  by_cases ht : ∃ t : D.TestAt v, a ∈ D.testInterval t
  · rw [ite_eq_left ht]
    have ht' : ∃ t : D.TestAt v,
        (D.deadlineShiftData v).left t ≤ a ∧
          a < (D.deadlineShiftData v).right t := ht
    rw [ite_eq_left ht'] at hc
    exact hc
  · rw [ite_eq_right ht]
    have ht' : ¬ ∃ t : D.TestAt v,
        (D.deadlineShiftData v).left t ≤ a ∧
          a < (D.deadlineShiftData v).right t := ht
    rw [ite_eq_right ht'] at hc
    exact hc

theorem deadline_prefix (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    (v : D.Vertex) (a : ℚ) :
    prefixCount (D.deadline (v := v)) a =
      prefixCount (D.mainBaseline (v := v)) a +
        D.d * (@ite ℕ (∃ t : D.TestAt v, a ∈ D.testInterval t)
          (Classical.propDecidable _) 1 0) := by
  rw [D.deadline_prefix_active, D.deadline_active_card hplusheight hminusheight hL]

theorem exists_deadline_matching (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    (v : D.Vertex) (h : D.MBase v → ℚ)
    (hle : ∀ b, h b ≤ D.mainBaseline b)
    (hcover : ∀ (t : D.TestAt v) (a : ℚ), a ∈ D.testInterval t →
      D.d ≤ coverageCount h D.mainBaseline a) :
    ∃ e : D.MBase v ≃ D.MBase v, ∀ b, h b ≤ D.deadline (e b) := by
  classical
  apply exists_equiv_of_prefix_dominance h D.deadline rfl
  intro a
  rw [D.deadline_prefix hplusheight hminusheight hL,
    completion_prefix_identity h D.mainBaseline hle]
  by_cases ht : ∃ t : D.TestAt v, a ∈ D.testInterval t
  · rw [ite_eq_left ht, Nat.mul_one]
    obtain ⟨t, ht⟩ := ht
    exact Nat.add_le_add_left (hcover t a ht) _
  · rw [ite_eq_right ht, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_add_right _ _

end BinPackingGap.InventoryData

namespace BinPackingGap.LocalResourceAllocation

open UniformTree

variable (G : GraphInput) {d : ℕ} (T : CompetingTrees d) (hd : 0 < d) (R k : ℕ)

local notation "D" => InventoryData.ofCompetingTrees G T R k

def markedRow (v : G.Vertex) :
    (selected : Bool) → OppositeMarked T selected → (D).MBase v
  | false, a => .inl (.inl (a.val, ⟨0, hd⟩))
  | true, a => .inl (.inr (.inl (a.val, ⟨0, hd⟩)))

theorem markedRow_injective (v : G.Vertex) (selected : Bool) :
    Function.Injective (markedRow G T hd R k v selected) := by
  cases selected
  · intro a b hab
    apply Subtype.ext
    exact congrArg Prod.fst (Sum.inl.inj (Sum.inl.inj hab))
  · intro a b hab
    apply Subtype.ext
    exact congrArg Prod.fst (Sum.inl.inj (Sum.inr.inj (Sum.inl.inj hab)))

theorem fundedRoot_ne_markedRow (v : G.Vertex) (selected : Bool) (j : Fin d)
    (a : OppositeMarked T selected) :
    (D).fundedRoot selected j ≠ markedRow G T hd R k v selected a := by
  cases selected <;> intro h <;> cases Sum.inl.inj h

def seedRows (v : G.Vertex) (selected : Bool) :
    (Fin d ⊕ OppositeMarked T selected) ↪ (D).MBase v := by
  refine ⟨Sum.elim ((D).fundedRoot selected) (markedRow G T hd R k v selected), ?_⟩
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl ((D).fundedRoot_injective v selected hab)
  · exact False.elim (fundedRoot_ne_markedRow G T hd R k v selected a b hab)
  · exact False.elim (fundedRoot_ne_markedRow G T hd R k v selected b a hab.symm)
  · exact congrArg Sum.inr (markedRow_injective G T hd R k v selected hab)

def seedResources (v : G.Vertex) (selected : Bool) :
    (Fin d ⊕ OppositeMarked T selected) ↪ (D).DMAt v := by
  refine ⟨Sum.elim (zeroResource G T R k v)
    (fun a => .inl (markedResource G T R k selected a)), ?_⟩
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl ((zeroResource G T R k v).injective hab)
  · have hbad : Sum.inr _ = Sum.inl _ := hab
    cases hbad
  · have hbad : Sum.inl _ = Sum.inr _ := hab
    cases hbad
  · exact congrArg Sum.inr ((markedResource G T R k selected).injective (Sum.inl.inj hab))

theorem exists_localEquiv (v : G.Vertex) (selected : Bool) :
    ∃ e : (D).MBase v ≃ (D).DMAt v,
      ∀ s : Fin d ⊕ OppositeMarked T selected,
        e (seedRows G T hd R k v selected s) = seedResources G T R k v selected s := by
  let : Fintype ((D).MBase v) := by
    dsimp [InventoryData.MBase, InventoryData.TreeRow, InventoryData.JobCopy,
      InventoryData.ofCompetingTrees]
    infer_instance
  let : Fintype ((D).DMAt v) := by
    dsimp [InventoryData.DMAt, InventoryData.PositiveLocal, InventoryData.ZeroLocalAt,
      InventoryData.Depth, InventoryData.JobCopy, InventoryData.ofCompetingTrees]
    infer_instance
  apply PartialAllocation.exists_equiv_extending_embeddings
    (seedRows G T hd R k v selected) (seedResources G T R k v selected)
  exact ((D).card_mBase v).trans ((D).card_dmAt v).symm

def localEquiv (v : G.Vertex) (selected : Bool) : (D).MBase v ≃ (D).DMAt v :=
  Classical.choose (exists_localEquiv G T hd R k v selected)

theorem localEquiv_seed (v : G.Vertex) (selected : Bool)
    (s : Fin d ⊕ OppositeMarked T selected) :
    localEquiv G T hd R k v selected (seedRows G T hd R k v selected s) =
      seedResources G T R k v selected s :=
  Classical.choose_spec (exists_localEquiv G T hd R k v selected) s

theorem localEquiv_fundedRoot (v : G.Vertex) (selected : Bool) (j : Fin d) :
    localEquiv G T hd R k v selected ((D).fundedRoot selected j) =
      zeroResource G T R k v j :=
  localEquiv_seed G T hd R k v selected (.inl j)

theorem localEquiv_markedRow (v : G.Vertex) (selected : Bool)
    (a : OppositeMarked T selected) :
    localEquiv G T hd R k v selected (markedRow G T hd R k v selected a) =
      .inl (markedResource G T R k selected a) :=
  localEquiv_seed G T hd R k v selected (.inr a)

theorem fundedRoot_local_zero (v : G.Vertex) (selected : Bool) (j : Fin d) :
    (D).localLength (.inl (localEquiv G T hd R k v selected ((D).fundedRoot selected j))) =
      0 := by
  rw [localEquiv_fundedRoot, zeroResource_local_length]

theorem markedRow_local_length (v : G.Vertex) (selected : Bool)
    (a : OppositeMarked T selected) :
    (D).localLength (.inl (localEquiv G T hd R k v selected
      (markedRow G T hd R k v selected a))) =
      Geometry.lambda G.edges.length R (D).geometryBound (depth a.val) := by
  rw [localEquiv_markedRow]
  change Geometry.lambda G.edges.length R (D).geometryBound
    (markedResource G T R k selected a).1.val = _
  rw [markedResource_depth]

theorem plusMarked_local_length (v : G.Vertex) (node : T.plus.Node)
    (hnode : node ∈ T.markingPlus) :
    (D).localLength (.inl (localEquiv G T hd R k v false
      (.inl (.inl (node, ⟨0, hd⟩))))) =
      Geometry.lambda G.edges.length R (D).geometryBound (depth node) :=
  markedRow_local_length G T hd R k v false ⟨node, hnode⟩

theorem minusMarked_local_length (v : G.Vertex) (node : T.minus.Node)
    (hnode : node ∈ T.markingMinus) :
    (D).localLength (.inl (localEquiv G T hd R k v true
      (.inl (.inr (.inl (node, ⟨0, hd⟩)))))) =
      Geometry.lambda G.edges.length R (D).geometryBound (depth node) :=
  markedRow_local_length G T hd R k v true ⟨node, hnode⟩

end BinPackingGap.LocalResourceAllocation

namespace BinPackingGap.LocalCompletionCoverage

open InventoryData IntervalCoverage

theorem nodeInterval_subset_root {U : UniformTree} (node : U.Node)
    (m R B : ℕ) (side : TreeGeometry.Side) (hB : U.branchBound ≤ B)
    {a : ℚ}
    (ha : a ∈ Set.Ico (TreeGeometry.left m R B side node.val)
      (TreeGeometry.right m R B side node.val)) :
    a ∈ Set.Ico (TreeGeometry.rootOffset side) (TreeGeometry.rootOffset side + 1) := by
  have he := TreeGeometry.prefix_endpoints m R B side
    (u := []) (v := node.val) List.nil_prefix (TreeGeometry.boundedAddress_node node hB)
  simp only [TreeGeometry.left_nil, TreeGeometry.right_nil] at he
  exact ⟨he.1.trans ha.1, ha.2.trans_le he.2⟩

variable (G : GraphInput) {d : ℕ} (T : CompetingTrees d) (hd : 0 < d) (R k : ℕ)

local notation "D" => InventoryData.ofCompetingTrees G T R k

local instance mainFintype (v : G.Vertex) : Fintype ((D).MBase v) := by
  dsimp [InventoryData.MBase, InventoryData.TreeRow, InventoryData.JobCopy,
    InventoryData.ofCompetingTrees]
  infer_instance

def localCompletion (v : G.Vertex) (selected : Bool) (b : (D).MBase v) : ℚ :=
  (D).rowCoordinate ((D).stateMainRow v selected b) - (D).stateMainLength selected b -
    (D).localLength (.inl (LocalResourceAllocation.localEquiv G T hd R k v selected b))

theorem localCompletion_le_baseline (v : G.Vertex) (selected : Bool) (b : (D).MBase v) :
    localCompletion G T hd R k v selected b ≤ (D).mainBaseline b := by
  have hg := (D).stateMainLength_nonneg selected b
  have hl := (D).localLength_nonneg
    (.inl (LocalResourceAllocation.localEquiv G T hd R k v selected b))
  have hdelta := Geometry.delta_nonneg G.edges.length R (D).geometryBound (D).L
  have hshort : (0 : ℚ) ≤
      if (D).rowShort ((D).stateMainRow v selected b) then
        Geometry.delta G.edges.length R (D).geometryBound (D).L else 0 := by
    split_ifs
    · exact hdelta
    · exact le_rfl
  have hbase := (D).stateMainRow_baseline v selected b
  unfold localCompletion rowCoordinate
  dsimp only [InventoryData.ofCompetingTrees] at *
  rw [hbase]
  linarith

theorem fundedRoot_covers (v : G.Vertex) (selected : Bool) (j : Fin d)
    {a : ℚ} (ha : a ∈ Set.Ico (if selected then 0 else 4) (if selected then 1 else 5)) :
    localCompletion G T hd R k v selected ((D).fundedRoot selected j) ≤ a ∧
      a < (D).mainBaseline ((D).fundedRoot (v := v) selected j) := by
  have hzero := LocalResourceAllocation.fundedRoot_local_zero G T hd R k v selected j
  have hglobal := (D).stateMainLength_fundedRoot (v := v) selected j
  unfold localCompletion
  rw [hzero, hglobal]
  cases selected <;>
    norm_num [fundedRoot, stateMainRow, stateRowEquiv, rowCoordinate, rowBaseline,
      rowShort, mainBaseline, treeBaseline, UniformTree.root, TreeGeometry.right_nil,
      TreeGeometry.rootOffset] at ha ⊢ <;> exact ha

theorem fundedRoot_coverage (v : G.Vertex) (selected : Bool) {a : ℚ}
    (ha : a ∈ Set.Ico (if selected then 0 else 4) (if selected then 1 else 5)) :
    d ≤ coverageCount (localCompletion G T hd R k v selected) (D).mainBaseline a := by
  classical
  have hc := card_le_coverage (localCompletion G T hd R k v selected)
    (D).mainBaseline a (Finset.univ : Finset (Fin d)) ((D).fundedRoot selected)
    ((D).fundedRoot_injective v selected)
    (fun j _ => fundedRoot_covers G T hd R k v selected j ha)
  simpa only [Finset.card_univ, Fintype.card_fin] using hc

theorem plusMarked_completion_le (v : G.Vertex) (node : T.plus.Node)
    (hnode : node ∈ T.markingPlus) :
    localCompletion G T hd R k v false (.inl (.inl (node, ⟨0, hd⟩))) ≤
      TreeGeometry.left G.edges.length R (D).geometryBound .plus node.val := by
  have hlocal := LocalResourceAllocation.plusMarked_local_length G T hd R k v node hnode
  have hglobal := (D).stateMainLength_nonneg false
    (.inl (.inl (node, ⟨0, hd⟩))) (v := v)
  have hn : node.val ≠ [] := by
    intro hn
    have hp := T.markingPlus_depth_pos node hnode
    simp [UniformTree.depth, hn] at hp
  have hcoord : (D).rowCoordinate
      ((D).stateMainRow v false (.inl (.inl (node, ⟨0, hd⟩)))) =
      TreeGeometry.right G.edges.length R (D).geometryBound .plus node.val := by
    change TreeGeometry.right G.edges.length R (D).geometryBound .plus node.val - 0 = _
    exact sub_zero _
  have hwidth : TreeGeometry.right G.edges.length R (D).geometryBound .plus node.val =
      TreeGeometry.left G.edges.length R (D).geometryBound .plus node.val +
        Geometry.lambda G.edges.length R (D).geometryBound (UniformTree.depth node) := by
    rw [TreeGeometry.right, TreeGeometry.width_of_ne_nil _ _ _ hn]
    rfl
  unfold localCompletion
  dsimp only [InventoryData.ofCompetingTrees] at *
  rw [hcoord, hlocal, hwidth]
  linarith

theorem minusMarked_completion_le (v : G.Vertex) (node : T.minus.Node)
    (hnode : node ∈ T.markingMinus) :
    localCompletion G T hd R k v true (.inl (.inr (.inl (node, ⟨0, hd⟩)))) ≤
      TreeGeometry.left G.edges.length R (D).geometryBound .minus node.val := by
  have hlocal := LocalResourceAllocation.minusMarked_local_length G T hd R k v node hnode
  have hglobal := (D).stateMainLength_nonneg true
    (.inl (.inr (.inl (node, ⟨0, hd⟩)))) (v := v)
  have hn : node.val ≠ [] := by
    intro hn
    have hp := T.markingMinus_depth_pos node hnode
    simp [UniformTree.depth, hn] at hp
  have hcoord : (D).rowCoordinate
      ((D).stateMainRow v true (.inl (.inr (.inl (node, ⟨0, hd⟩))))) =
      TreeGeometry.right G.edges.length R (D).geometryBound .minus node.val := by
    change TreeGeometry.right G.edges.length R (D).geometryBound .minus node.val - 0 = _
    exact sub_zero _
  have hwidth : TreeGeometry.right G.edges.length R (D).geometryBound .minus node.val =
      TreeGeometry.left G.edges.length R (D).geometryBound .minus node.val +
        Geometry.lambda G.edges.length R (D).geometryBound (UniformTree.depth node) := by
    rw [TreeGeometry.right, TreeGeometry.width_of_ne_nil _ _ _ hn]
    rfl
  unfold localCompletion
  dsimp only [InventoryData.ofCompetingTrees] at *
  rw [hcoord, hlocal, hwidth]
  linarith

theorem plusMarked_coverage (v : G.Vertex) (leaf : (D).PlusLeaf) {a : ℚ}
    (ha : a ∈ (D).testInterval (.inl leaf : (D).TestAt v)) :
    d ≤ coverageCount (localCompletion G T hd R k v false) (D).mainBaseline a := by
  classical
  apply (T.plus_rich leaf.val leaf.property).trans
  apply card_le_coverage (localCompletion G T hd R k v false) (D).mainBaseline a
    (T.markingPlus.filter (fun node => UniformTree.ancestor node leaf.val))
    (fun node => .inl (.inl (node, ⟨0, hd⟩)))
  · intro x y hxy
    exact congrArg Prod.fst (Sum.inl.inj (Sum.inl.inj hxy))
  · intro node hnode
    obtain ⟨hmark, hancestor⟩ := Finset.mem_filter.mp hnode
    have he := TreeGeometry.prefix_endpoints G.edges.length R (D).geometryBound .plus
      hancestor (TreeGeometry.boundedAddress_node leaf.val (D).plus_branch_le_geometryBound)
    exact ⟨(plusMarked_completion_le G T hd R k v node hmark).trans (he.1.trans ha.1),
      ha.2.trans_le he.2⟩

theorem minusMarked_coverage (v : G.Vertex) (leaf : (D).MinusLeaf) {a : ℚ}
    (ha : a ∈ (D).testInterval (.inr (.inl leaf) : (D).TestAt v)) :
    d ≤ coverageCount (localCompletion G T hd R k v true) (D).mainBaseline a := by
  classical
  apply (T.minus_rich leaf.val leaf.property).trans
  apply card_le_coverage (localCompletion G T hd R k v true) (D).mainBaseline a
    (T.markingMinus.filter (fun node => UniformTree.ancestor node leaf.val))
    (fun node => .inl (.inr (.inl (node, ⟨0, hd⟩))))
  · intro x y hxy
    exact congrArg Prod.fst (Sum.inl.inj (Sum.inr.inj (Sum.inl.inj hxy)))
  · intro node hnode
    obtain ⟨hmark, hancestor⟩ := Finset.mem_filter.mp hnode
    have he := TreeGeometry.prefix_endpoints G.edges.length R (D).geometryBound .minus
      hancestor (TreeGeometry.boundedAddress_node leaf.val (D).minus_branch_le_geometryBound)
    exact ⟨(minusMarked_completion_le G T hd R k v node hmark).trans (he.1.trans ha.1),
      ha.2.trans_le he.2⟩

theorem shortJob_coverage (v : G.Vertex) (job : (D).IncidencePosition v) {a : ℚ}
    (ha : a ∈ (D).testInterval (.inr (.inr job) : (D).TestAt v)) :
    d ≤ coverageCount (localCompletion G T hd R k v false) (D).mainBaseline a := by
  classical
  have hc := card_le_coverage (localCompletion G T hd R k v false)
    (D).mainBaseline a (Finset.univ : Finset (Fin d))
    (fun j => .inr (job, j))
    (by intro i j hij; exact congrArg Prod.snd (Sum.inr.inj hij)) (by
      intro j _
      have hl := (D).localLength_nonneg
        (.inl (LocalResourceAllocation.localEquiv G T hd R k v false (.inr (job, j))))
      change Geometry.baseline G.edges.length R ((D).incidencePosition job) -
        Geometry.delta G.edges.length R (D).geometryBound (D).L - 0 -
        (D).localLength (.inl (LocalResourceAllocation.localEquiv G T hd R k v false
          (.inr (job, j)))) ≤ a ∧
        a < Geometry.baseline G.edges.length R ((D).incidencePosition job)
      change Geometry.baseline G.edges.length R ((D).incidencePosition job) -
          Geometry.delta G.edges.length R (D).geometryBound (D).L ≤ a ∧
        a < Geometry.baseline G.edges.length R ((D).incidencePosition job) at ha
      exact ⟨by linarith [ha.1], ha.2⟩)
  simpa only [Finset.card_univ, Fintype.card_fin] using hc

theorem localCompletion_coverage (v : G.Vertex) (selected : Bool)
    (test : (D).TestAt v) (a : ℚ) (ha : a ∈ (D).testInterval test) :
    d ≤ coverageCount (localCompletion G T hd R k v selected) (D).mainBaseline a := by
  cases selected
  · rcases test with leaf | leaf | job
    · exact plusMarked_coverage G T hd R k v leaf ha
    · apply fundedRoot_coverage G T hd R k v false
      have hroot := nodeInterval_subset_root leaf.val G.edges.length R (D).geometryBound .minus
        (D).minus_branch_le_geometryBound ha
      norm_num [TreeGeometry.rootOffset] at hroot ⊢
      exact hroot
    · exact shortJob_coverage G T hd R k v job ha
  · rcases test with leaf | leaf | job
    · apply fundedRoot_coverage G T hd R k v true
      have hroot := nodeInterval_subset_root leaf.val G.edges.length R (D).geometryBound .plus
        (D).plus_branch_le_geometryBound ha
      norm_num [TreeGeometry.rootOffset] at hroot ⊢
      exact hroot
    · exact minusMarked_coverage G T hd R k v leaf ha
    · apply fundedRoot_coverage G T hd R k v true
      have hj := Geometry.closedJobCell_bounds
        (Geometry.jobTestInterval_subset_closedJobCell G.edges.length R (D).geometryBound
          (D).L ((D).incidencePosition job) ha)
      exact ⟨by dsimp; linarith [hj.1], hj.2⟩

theorem exists_anchorEquiv (v : G.Vertex) (selected : Bool) :
    ∃ e : (D).MBase v ≃ (D).MBase v, ∀ b,
      (D).rowCoordinate ((D).stateMainRow v selected b) - (D).stateMainLength selected b -
        (D).localLength (.inl (LocalResourceAllocation.localEquiv G T hd R k v selected b)) ≤
          (D).deadline (e b) := by
  exact (D).exists_deadline_matching T.plus_height T.minus_height T.height_pos v
    (localCompletion G T hd R k v selected)
    (localCompletion_le_baseline G T hd R k v selected)
    (localCompletion_coverage G T hd R k v selected)

end BinPackingGap.LocalCompletionCoverage

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Configurations_CoverageSoundness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

namespace InventoryData

variable (D : InventoryData)

def longMatchesAt {b : ℕ} (p : Packing D.packingInstance b)
    (v : D.Vertex) (r : D.IncidencePosition v) : ℕ :=
  (Coverage.currentLongEdgeAt p D.encodedSubclass D.encodedLabel v
    (InventoryCoverage.rowBaseline D.itemEquiv) (InventoryCoverage.keyBaseline D.itemEquiv)
    (InventoryCoverage.rowShort D.itemEquiv)
    (Geometry.baseline D.graph.edges.length D.R (D.incidencePosition r))).card

end InventoryData
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_IntegralSpeciesCounts
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

theorem stateGlobalSpecies_up_true_count (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .up true)).card =
        if selected then D.d else 0 := by
  classical
  cases selected <;>
    simp [-Finset.sum_boole, Finset.card_filter, LocalBin, MBase, TreeRow,
      Fintype.sum_sum_type, Fintype.sum_prod_type, stateGlobalSpecies,
      stateMainGlobalSpecies]
  exact root_copy_indicator_sum D.plus D.d

theorem stateGlobalSpecies_up_total (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .up true)).card +
      (Finset.univ.filter (fun b : D.LocalBin v =>
        D.stateGlobalSpecies selected b = .up false)).card = D.tPlus + D.J v := by
  classical
  simp only [Finset.card_filter, ← Finset.sum_add_distrib, D.up_indicator_add]
  simp [LocalBin, MBase, TreeRow, Fintype.sum_sum_type,
    stateGlobalSpecies, stateMainGlobalSpecies, D.card_jobCopy, tPlus,
    Nat.mul_comm, Nat.add_assoc]

theorem stateGlobalSpecies_edge_count (v : D.Vertex) (selected : Bool)
    (e : D.Edge) (permit : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .edge e permit)).card =
        if permit = !selected ∧ (D.graph.left e = v ∨ D.graph.right e = v)
        then D.d * D.R else 0 := by
  classical
  simp only [Finset.card_filter, Fintype.sum_sum_type]
  by_cases hp : permit = !selected
  · subst permit
    simpa [-Finset.sum_boole, Finset.card_filter, stateGlobalSpecies, stateMainGlobalSpecies,
      Fintype.sum_prod_type] using D.card_jobCopy_edge v e
  · have hp' : (!selected) ≠ permit := Ne.symm hp
    simp [-Finset.sum_boole, stateGlobalSpecies, stateMainGlobalSpecies, hp, hp']

def allGlobalRequests (g : GlobalSpecies D.graph) : ℕ :=
  ∑ v : D.Vertex, ∑ selected : Bool,
    (Finset.univ.filter (fun b : D.LocalBin v => D.stateGlobalSpecies selected b = g)).card

theorem allGlobalRequests_up_true : D.allGlobalRequests (.up true) = D.graph.n * D.d := by
  classical
  simp [allGlobalRequests, D.stateGlobalSpecies_up_true_count]

theorem allGlobalRequests_um_true : D.allGlobalRequests (.um true) = D.graph.n * D.d := by
  classical
  simp [allGlobalRequests, D.stateGlobalSpecies_um_true_count]

theorem allGlobalRequests_up_total :
    D.allGlobalRequests (.up true) + D.allGlobalRequests (.up false) = 2 * D.plusSlots := by
  classical
  calc
    _ = ∑ v : D.Vertex, ∑ selected : Bool,
        ((Finset.univ.filter (fun b : D.LocalBin v =>
          D.stateGlobalSpecies selected b = .up true)).card +
          (Finset.univ.filter (fun b : D.LocalBin v =>
            D.stateGlobalSpecies selected b = .up false)).card) := by
        simp only [allGlobalRequests, Finset.sum_add_distrib]
    _ = ∑ v : D.Vertex, ∑ _selected : Bool, (D.tPlus + D.J v) := by
        simp_rw [D.stateGlobalSpecies_up_total]
    _ = _ := by simp [plusSlots, Finset.sum_add_distrib, two_mul]

theorem allGlobalRequests_um_total :
    D.allGlobalRequests (.um true) + D.allGlobalRequests (.um false) = 2 * D.minusSlots := by
  classical
  calc
    _ = ∑ v : D.Vertex, ∑ selected : Bool,
        ((Finset.univ.filter (fun b : D.LocalBin v =>
          D.stateGlobalSpecies selected b = .um true)).card +
          (Finset.univ.filter (fun b : D.LocalBin v =>
            D.stateGlobalSpecies selected b = .um false)).card) := by
        simp only [allGlobalRequests, Finset.sum_add_distrib]
    _ = ∑ v : D.Vertex, ∑ _selected : Bool, D.tMinus := by
        simp_rw [D.stateGlobalSpecies_um_total]
    _ = _ := by simp [minusSlots, two_mul, Nat.mul_add]

theorem allGlobalRequests_edge (e : D.Edge) (permit : Bool) :
    D.allGlobalRequests (.edge e permit) = 2 * D.d * D.R := by
  classical
  have hpair (v : D.Vertex) :
      (Finset.univ.filter (fun b : D.LocalBin v =>
        D.stateGlobalSpecies true b = .edge e permit)).card +
        (Finset.univ.filter (fun b : D.LocalBin v =>
          D.stateGlobalSpecies false b = .edge e permit)).card =
        (Finset.univ.filter (fun j : D.JobCopy v => (D.jobPosition j).1 = e)).card := by
    cases permit <;> simp [D.stateGlobalSpecies_edge_count, D.card_jobCopy_edge]
  unfold allGlobalRequests
  simp only [Fintype.sum_bool, hpair]
  exact D.sum_card_jobCopy_edge e

theorem allGlobalRequests_eq_twice_stock (hn : D.graph.n = 2 * D.k)
    (g : GlobalSpecies D.graph) : D.allGlobalRequests g = 2 * D.globalStock g := by
  have hk : D.k ≤ D.graph.n := by omega
  have hdiff : D.graph.n - D.k = D.k := by omega
  have hup : D.allGlobalRequests (.up true) = 2 * (D.d * D.k) := by
    rw [D.allGlobalRequests_up_true, hn]
    ring
  have hum : D.allGlobalRequests (.um true) = 2 * (D.d * (D.graph.n - D.k)) := by
    rw [D.allGlobalRequests_um_true, hdiff, hn]
    ring
  cases g with
  | up b =>
      cases b
      · have ht := D.allGlobalRequests_up_total
        have hs := D.unitPlus_le_stock hk
        rw [hup] at ht
        dsimp [globalStock]
        omega
      · exact hup
  | um b =>
      cases b
      · have ht := D.allGlobalRequests_um_total
        have hs := D.unitMinus_le_stock
        rw [hum] at ht
        dsimp [globalStock]
        omega
      · exact hum
  | edge e permit =>
      simpa [globalStock, Nat.mul_assoc] using D.allGlobalRequests_edge e permit

theorem doubled_stateGlobalSpecies_count (hn : D.graph.n = 2 * D.k)
    (g : GlobalSpecies D.graph) :
    (Finset.univ.filter (fun q : (Σ v : D.Vertex, Bool × D.LocalBin v) =>
      D.stateGlobalSpecies q.2.1 q.2.2 = g)).card = 2 * D.globalStock g := by
  classical
  have hsum :
      (Finset.univ.filter (fun q : (Σ v : D.Vertex, Bool × D.LocalBin v) =>
        D.stateGlobalSpecies q.2.1 q.2.2 = g)).card = D.allGlobalRequests g := by
    simp only [Finset.card_filter, Fintype.sum_sigma, Fintype.sum_prod_type,
      allGlobalRequests]
  rw [hsum]
  exact D.allGlobalRequests_eq_twice_stock hn g

theorem doubled_stateFlagSpecies_count (f : FlagSpecies) :
    (Finset.univ.filter (fun q : (Σ v : D.Vertex, Bool × D.LocalBin v) =>
      D.stateFlagSpecies q.2.2 = f)).card = 2 * D.flagStock f := by
  classical
  have hsum :
      (Finset.univ.filter (fun q : (Σ v : D.Vertex, Bool × D.LocalBin v) =>
        D.stateFlagSpecies q.2.2 = f)).card =
        ∑ v : D.Vertex, ∑ _selected : Bool,
          (Finset.univ.filter (fun b : D.LocalBin v => D.stateFlagSpecies b = f)).card := by
    simp only [Finset.card_filter, Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [hsum]
  cases f <;>
    simp [D.stateFlagSpecies_count, flagStock, treeFlags,
      jobFlags, Finset.sum_add_distrib, two_mul, Nat.mul_add]

end BinPackingGap.InventoryData

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

theorem integral_up_count_eq_sum (C : Finset D.Vertex) (one : Bool) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .up one)).card =
      ∑ v : D.Vertex, (Finset.univ.filter (fun b : D.LocalBin v =>
        D.stateGlobalSpecies (D.coverSelected C v) b = .up one)).card := by
  classical
  simp only [Finset.card_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro b _
  rcases b with b | j
  · rfl
  · simp [integralGlobalSpecies, stateGlobalSpecies]

theorem sum_coverSelected (C : Finset D.Vertex) :
    (∑ v : D.Vertex, if D.coverSelected C v then D.d else 0) = D.d * C.card := by
  classical
  simp [coverSelected, Nat.mul_comm]

theorem sum_coverUnselected (C : Finset D.Vertex) :
    (∑ v : D.Vertex, if D.coverSelected C v then 0 else D.d) =
      D.d * (D.graph.n - C.card) := by
  classical
  calc
    _ = ∑ v : D.Vertex, if v ∈ Cᶜ then D.d else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ C <;> simp [coverSelected, hv]
    _ = D.d * (Cᶜ).card := by
      rw [Fintype.sum_ite_mem]
      simp [Nat.mul_comm]
    _ = _ := by simp [Finset.card_compl]

theorem integral_up_true_count (C : Finset D.Vertex) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .up true)).card = D.d * C.card := by
  rw [D.integral_up_count_eq_sum]
  simp_rw [D.stateGlobalSpecies_up_true_count]
  exact D.sum_coverSelected C

theorem integral_um_true_count (C : Finset D.Vertex) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .um true)).card =
      D.d * (D.graph.n - C.card) := by
  rw [D.integral_um_count_eq_sum]
  simp_rw [D.stateGlobalSpecies_um_true_count]
  exact D.sum_coverUnselected C

theorem integral_up_total (C : Finset D.Vertex) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .up true)).card +
      (Finset.univ.filter (fun b : D.PhysicalBins =>
        D.integralGlobalSpecies C b = .up false)).card = D.plusSlots := by
  rw [D.integral_up_count_eq_sum, D.integral_up_count_eq_sum,
    ← Finset.sum_add_distrib]
  simp_rw [D.stateGlobalSpecies_up_total]
  rfl

theorem card_integralGlobalSpecies (C : Finset D.Vertex) (hC : C.card = D.k)
    (s : GlobalSpecies D.graph) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = s)).card = D.globalStock s := by
  classical
  cases s with
  | up one =>
      cases one
      · have ht := D.integral_up_total C
        have hu := D.integral_up_true_count C
        rw [hC] at hu
        dsimp [globalStock]
        omega
      · simpa [globalStock, hC] using D.integral_up_true_count C
  | um one =>
      cases one
      · have ht := D.integral_um_total C
        have hu := D.integral_um_true_count C
        rw [hC] at hu
        dsimp [globalStock]
        omega
      · simpa [globalStock, hC] using D.integral_um_true_count C
  | edge e permit =>
      rw [Finset.card_filter, Fintype.sum_sigma]
      have hj := D.card_integralEdgeJobs C e permit
      rw [Finset.card_filter, Fintype.sum_sigma] at hj
      refine Eq.trans ?_ hj
      apply Finset.sum_congr rfl
      intro vertex _
      have hmain (base : D.MBase vertex) :
          D.stateMainGlobalSpecies (D.coverSelected C vertex) base ≠ .edge e permit := by
        rcases base with (⟨node, copy⟩ | (⟨node, copy⟩ | zero)) | job <;>
          simp [stateMainGlobalSpecies]
      rw [Fintype.sum_sum_type]
      simp only [integralGlobalSpecies, hmain, ite_false, Finset.sum_const_zero, zero_add]
      rfl

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_ConstructLocalState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

def constructedLocalState (G : GraphInput) {d : ℕ} (T : CompetingTrees d)
    (hd : 0 < d) (R k : ℕ) (v : G.Vertex) (selected : Bool) :
    (ofCompetingTrees G T R k).LocalState v selected where
  localEquiv := LocalResourceAllocation.localEquiv G T hd R k v selected
  anchorEquiv := Classical.choose
    (LocalCompletionCoverage.exists_anchorEquiv G T hd R k v selected)
  completion_le_deadline := Classical.choose_spec
    (LocalCompletionCoverage.exists_anchorEquiv G T hd R k v selected)

end BinPackingGap.InventoryData

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_ExtractedCover
attribute [-instance] _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeDescriptor _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeTreeDescriptor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

section

theorem reductionInventory_plus_height (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).plus.height = (reductionInventory c ρ G k).L :=
  (reductionTrees c ρ).plus_height

theorem reductionInventory_minus_height (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).minus.height = (reductionInventory c ρ G k).L :=
  (reductionTrees c ρ).minus_height

open UniformTree

namespace InventoryData

variable (D : InventoryData)

def plusPoint (v : D.plus.Node) : ℚ :=
  (TreeGeometry.left D.graph.edges.length D.R D.geometryBound .plus v.val +
    TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus v.val) / 2

def minusPoint (v : D.minus.Node) : ℚ :=
  (TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus v.val +
    TreeGeometry.right D.graph.edges.length D.R D.geometryBound .minus v.val) / 2

def taggedAddress : D.plus.Node ⊕ D.minus.Node → TreeGeometry.Side × List ℕ
  | .inl v => (.plus, v.val)
  | .inr v => (.minus, v.val)

def taggedNodeDepth (v : D.plus.Node ⊕ D.minus.Node) : ℕ :=
  (D.taggedAddress v).2.length

def taggedNodeCell (v : D.plus.Node ⊕ D.minus.Node) : Set ℚ :=
  TreeGeometry.cell D.graph.edges.length D.R D.geometryBound
    (D.taggedAddress v).1 (D.taggedAddress v).2

end InventoryData

namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def tupleHits (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (v : D.plus.Node ⊕ D.minus.Node) : Prop :=
  D.taggedNodeDepth v = tupleLocalDepth p e t ∧
    (tupleClosedInterval p e t ∩ D.taggedNodeCell v).Nonempty

end PackingCounts

end

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_LocalTemplateBases
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace InventoryData

variable (D : InventoryData)

theorem localTemplateItems_injective {v : D.Vertex}
    (row : D.RowAt v) (anchor : D.AnchorAt v) (u : D.GlobalCopy)
    (l : D.LocalAt v) (flag : D.FlagCopy) :
    Function.Injective (D.localTemplateItems row anchor u l flag) := by
  intro r s h
  simpa only [localTemplateItems_role] using congrArg D.itemRole h

theorem localTemplate_coordinate_sum {v : D.Vertex}
    (row : D.RowAt v) (anchor : D.AnchorAt v) (u : D.GlobalCopy)
    (l : D.LocalAt v) (flag : D.FlagCopy) :
    (∑ r, D.itemCoordinate (D.localTemplateItems row anchor u l flag r)) =
      D.rowCoordinate row + D.anchorCoordinate anchor + D.globalCoordinate u -
        D.localLength l := by
  rw [Role.sum_univ]
  simp only [localTemplateItems, itemCoordinate, localCoordinate, add_zero]
  ring

theorem localTemplate_size_sum {v : D.Vertex}
    (row : D.RowAt v) (anchor : D.AnchorAt v) (u : D.GlobalCopy)
    (l : D.LocalAt v) (flag : D.FlagCopy) (p : Pattern)
    (hpattern : ∀ r, D.itemSubclass (D.localTemplateItems row anchor u l flag r) =
      patternSubclass p r) :
    (∑ r, D.itemSize (D.localTemplateItems row anchor u l flag r)) =
      1 + nu D.graph.n * ∑ r,
        D.itemCoordinate (D.localTemplateItems row anchor u l flag r) := by
  simp only [itemSize, hpattern, localTemplateItems_label]
  exact encoded_pattern_role_sum p v _

def stateMainPattern {v : D.Vertex} : D.MBase v → Pattern
  | .inl (.inl _) => .plusTree
  | .inl (.inr (.inl _)) => .minusTree
  | .inl (.inr (.inr _)) => .plusTree
  | .inr _ => .mainJob

theorem stateMainTemplate_pattern {v : D.Vertex} (selected : Bool)
    (b z : D.MBase v) (l : D.DMAt v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = D.stateMainGlobalSpecies selected b)
    (hf : f.1 = D.stateFlagSpecies (.inl b)) (r : Role) :
    D.itemSubclass (D.localTemplateItems (D.stateMainRow v selected b)
      (.inl z) u (.inl l) f r) = patternSubclass (D.stateMainPattern b) r := by
  rcases u with ⟨us, ui⟩
  rcases f with ⟨fs, fi⟩
  change us = D.stateMainGlobalSpecies selected b at hu
  change fs = D.stateFlagSpecies (.inl b) at hf
  subst us
  subst fs
  rcases b with (⟨node, copy⟩ | (⟨node, copy⟩ | padding)) | job
  all_goals cases r <;> rfl

theorem stateMainGlobal_coordinate {v : D.Vertex} (selected : Bool)
    (b : D.MBase v) (u : D.GlobalCopy)
    (hu : u.1 = D.stateMainGlobalSpecies selected b) :
    D.globalCoordinate u = -D.stateMainLength selected b := by
  rcases u with ⟨us, ui⟩
  change us = D.stateMainGlobalSpecies selected b at hu
  subst us
  rcases b with (⟨node, copy⟩ | (⟨node, copy⟩ | padding)) | job <;> rfl

theorem stateMainTemplate_size_eq {v : D.Vertex} (selected : Bool)
    (b z : D.MBase v) (l : D.DMAt v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = D.stateMainGlobalSpecies selected b)
    (hf : f.1 = D.stateFlagSpecies (.inl b)) :
    (∑ r, D.itemSize (D.localTemplateItems (D.stateMainRow v selected b)
      (.inl z) u (.inl l) f r)) =
      1 + nu D.graph.n * (D.rowCoordinate (D.stateMainRow v selected b) -
        D.stateMainLength selected b - D.localLength (.inl l) - D.deadline z) := by
  rw [D.localTemplate_size_sum _ _ _ _ _ (D.stateMainPattern b)
    (D.stateMainTemplate_pattern selected b z l u f hu hf)]
  rw [D.localTemplate_coordinate_sum, D.stateMainGlobal_coordinate selected b u hu]
  simp only [anchorCoordinate]
  ring

theorem stateMainTemplate_feasible_iff {v : D.Vertex} (selected : Bool)
    (b z : D.MBase v) (l : D.DMAt v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = D.stateMainGlobalSpecies selected b)
    (hf : f.1 = D.stateFlagSpecies (.inl b)) :
    ((∑ r, D.itemSize (D.localTemplateItems (D.stateMainRow v selected b)
      (.inl z) u (.inl l) f r)) ≤ 1) ↔
      D.rowCoordinate (D.stateMainRow v selected b) - D.stateMainLength selected b -
        D.localLength (.inl l) ≤ D.deadline z := by
  rw [D.stateMainTemplate_size_eq selected b z l u f hu hf]
  have hnu := nu_pos D.graph.n
  constructor
  · intro h
    have hmul : nu D.graph.n *
        (D.rowCoordinate (D.stateMainRow v selected b) - D.stateMainLength selected b -
          D.localLength (.inl l) - D.deadline z) ≤ nu D.graph.n * 0 := by linarith
    exact sub_nonpos.mp (le_of_mul_le_mul_left hmul hnu)
  · intro h
    have hmul := mul_nonpos_of_nonneg_of_nonpos hnu.le (sub_nonpos.mpr h)
    linarith

theorem edgeTemplate_size_eq {v : D.Vertex} (short permit : Bool)
    (j : D.JobCopy v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = .edge (D.jobPosition j).1 permit) (hf : f.1 = .edge) :
    (∑ r, D.itemSize (D.localTemplateItems (.inr (short, j))
      (.inr j) u (.inr j) f r)) =
      1 + nu D.graph.n *
        ((if permit then 0 else Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) -
          (if short then Geometry.delta D.graph.edges.length D.R D.geometryBound D.L else 0)) := by
  rcases u with ⟨us, ui⟩
  rcases f with ⟨fs, fi⟩
  change us = .edge (D.jobPosition j).1 permit at hu
  change fs = .edge at hf
  subst us
  subst fs
  rw [D.localTemplate_size_sum _ _ _ _ _ .edgeJob (by intro r; cases r <;> rfl)]
  rw [D.localTemplate_coordinate_sum]
  simp only [rowCoordinate, rowBaseline, rowShort, anchorCoordinate,
    globalCoordinate, localLength]
  cases short <;> cases permit <;> simp <;> ring_nf <;> simp

theorem stateEdgeTemplate_size_eq_one {v : D.Vertex} (selected : Bool)
    (j : D.JobCopy v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = .edge (D.jobPosition j).1 (!selected)) (hf : f.1 = .edge) :
    (∑ r, D.itemSize (D.localTemplateItems (.inr (selected, j))
      (.inr j) u (.inr j) f r)) = 1 := by
  rw [D.edgeTemplate_size_eq selected (!selected) j u f hu hf]
  cases selected <;> simp

end InventoryData

end BinPackingGap

noncomputable section

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

def templateGlobalSpecies (t : D.Template) : GlobalSpecies D.graph :=
  D.stateGlobalSpecies t.2.1 t.2.2

def templateFlagSpecies (t : D.Template) : FlagSpecies :=
  D.stateFlagSpecies t.2.2

def templateRowCopy (t : D.Template) : Σ v : D.Vertex, D.RowAt v :=
  ⟨t.1, D.stateRowEquiv t.1 t.2.1 t.2.2⟩

def templateAnchorCopy (S : ∀ v s, D.LocalState v s) (t : D.Template) :
    Σ v : D.Vertex, D.AnchorAt v :=
  ⟨t.1, (S t.1 t.2.1).anchorAtEquiv t.2.2⟩

def templateLocalCopy (S : ∀ v s, D.LocalState v s) (t : D.Template) :
    Σ v : D.Vertex, D.LocalAt v :=
  ⟨t.1, (S t.1 t.2.1).localAtEquiv t.2.2⟩

def templateBase (S : ∀ v s, D.LocalState v s) (t : D.Template) :
    Finset D.packingInstance.Item :=
  {D.itemEquiv ⟨.x, D.templateRowCopy t⟩,
   D.itemEquiv ⟨.anchor, D.templateAnchorCopy S t⟩,
   D.itemEquiv ⟨.«local», D.templateLocalCopy S t⟩}

theorem templateBase_subset_labeledItems (S : ∀ v s, D.LocalState v s)
    (t : D.Template) : D.templateBase S t ⊆ D.labeledItems := by
  intro i hi
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> simp

def templateCopyEquiv {C : D.Vertex → Type*}
    (e : ∀ v (_s : Bool), D.LocalBin v ≃ C v) : D.Template ≃ Bool × (Σ v, C v) where
  toFun t := (t.2.1, ⟨t.1, e t.1 t.2.1 t.2.2⟩)
  invFun t := ⟨t.2.1, t.1, (e t.2.1 t.1).symm t.2.2⟩
  left_inv := by
    rintro ⟨v, s, b⟩
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨s, v, c⟩
    simp only [Equiv.apply_symm_apply]

@[simp] theorem templateCopyEquiv_apply {C : D.Vertex → Type*}
    (e : ∀ v (_s : Bool), D.LocalBin v ≃ C v) (t : D.Template) :
    D.templateCopyEquiv e t = (t.2.1, ⟨t.1, e t.1 t.2.1 t.2.2⟩) := rfl

@[simp] theorem packingInstance_size_itemEquiv (i : D.Item) :
    D.packingInstance.size (D.itemEquiv i) = D.itemSize i := by
  change D.itemSize (D.itemEquiv.symm (D.itemEquiv i)) = D.itemSize i
  rw [Equiv.symm_apply_apply]

theorem templateBase_complete_eq_image (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (u : D.GlobalCopy) (f : D.FlagCopy) :
    D.templateBase S t ∪ {D.itemEquiv ⟨.«global», u⟩, D.itemEquiv ⟨.flag, f⟩} =
      Finset.univ.image (fun r => D.itemEquiv
        (D.localTemplateItems (D.stateRowEquiv t.1 t.2.1 t.2.2)
          ((S t.1 t.2.1).anchorAtEquiv t.2.2) u
          ((S t.1 t.2.1).localAtEquiv t.2.2) f r)) := by
  apply Finset.ext
  intro i
  constructor
  · intro hi
    simp only [Finset.mem_union, templateBase, Finset.mem_insert,
      Finset.mem_singleton] at hi
    rcases hi with (rfl | rfl | rfl) | (rfl | rfl)
    · exact Finset.mem_image.mpr ⟨.x, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.anchor, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.«local», Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.«global», Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.flag, Finset.mem_univ _, rfl⟩
  · intro hi
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
    cases r with
    | x =>
      apply Finset.mem_union_left
      exact Finset.mem_insert_self _ _
    | anchor =>
      apply Finset.mem_union_left
      apply Finset.mem_insert_of_mem
      exact Finset.mem_insert_self _ _
    | «global» =>
      apply Finset.mem_union_right
      exact Finset.mem_insert_self _ _
    | «local» =>
      apply Finset.mem_union_left
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact Finset.mem_singleton_self _
    | flag =>
      apply Finset.mem_union_right
      apply Finset.mem_insert_of_mem
      exact Finset.mem_singleton_self _

theorem templateBase_size_sum (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (u : D.GlobalCopy) (f : D.FlagCopy) :
    (∑ i ∈ D.templateBase S t ∪
      {D.itemEquiv ⟨.«global», u⟩, D.itemEquiv ⟨.flag, f⟩}, D.packingInstance.size i) =
    ∑ r, D.itemSize (D.localTemplateItems (D.stateRowEquiv t.1 t.2.1 t.2.2)
      ((S t.1 t.2.1).anchorAtEquiv t.2.2) u
      ((S t.1 t.2.1).localAtEquiv t.2.2) f r) := by
  rw [D.templateBase_complete_eq_image S t u f, Finset.sum_image]
  · simp only [packingInstance_size_itemEquiv]
  · intro r _ r' _ h
    exact D.localTemplateItems_injective _ _ _ _ _ (D.itemEquiv.injective h)

theorem templateBase_capacity (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = D.templateGlobalSpecies t) (hf : f.1 = D.templateFlagSpecies t) :
    (∑ i ∈ D.templateBase S t ∪
      {D.itemEquiv ⟨.«global», u⟩, D.itemEquiv ⟨.flag, f⟩}, D.packingInstance.size i) ≤ 1 := by
  rw [D.templateBase_size_sum S t u f]
  rcases t with ⟨v, selected, b⟩
  rcases b with b | j
  · exact (D.stateMainTemplate_feasible_iff selected b ((S v selected).anchorEquiv b)
      ((S v selected).localEquiv b) u f hu hf).mpr
        ((S v selected).completion_le_deadline b)
  · exact (D.stateEdgeTemplate_size_eq_one selected j u f hu hf).le

end BinPackingGap.InventoryData

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Configurations_ReductionCompleteness
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

def integralGlobalAllocation (C : Finset D.Vertex) (hC : C.card = D.k) :
    D.PhysicalBins ≃ D.GlobalCopy := by
  classical
  exact SpeciesAllocation.allocation (D.integralGlobalSpecies C) D.globalStock
    (fun s => by rw [Fintype.card_subtype]; exact D.card_integralGlobalSpecies C hC s)

def integralFlagAllocation : D.PhysicalBins ≃ D.FlagCopy := by
  classical
  exact SpeciesAllocation.allocation D.integralFlagSpecies D.flagStock
    (fun s => by rw [Fintype.card_subtype]; exact D.card_integralFlagSpecies s)

@[simp] theorem integralGlobalAllocation_species (C : Finset D.Vertex)
    (hC : C.card = D.k) (b : D.PhysicalBins) :
    (D.integralGlobalAllocation C hC b).1 = D.integralGlobalSpecies C b :=
  SpeciesAllocation.allocation_species _ _ _ b

@[simp] theorem integralFlagAllocation_species (b : D.PhysicalBins) :
    (D.integralFlagAllocation b).1 = D.integralFlagSpecies b :=
  SpeciesAllocation.allocation_species _ _ _ b

def integralRoleEquiv (C : Finset D.Vertex) (hC : C.card = D.k)
    (S : ∀ v, D.LocalState v (D.coverSelected C v)) :
    ∀ r : Role, D.PhysicalBins ≃ D.RoleCopies r
  | .x => Equiv.sigmaCongrRight fun v => D.stateRowEquiv v (D.coverSelected C v)
  | .anchor => Equiv.sigmaCongrRight fun v => (S v).anchorAtEquiv
  | .«global» => D.integralGlobalAllocation C hC
  | .«local» => Equiv.sigmaCongrRight fun v => (S v).localAtEquiv
  | .flag => D.integralFlagAllocation

end BinPackingGap.InventoryData

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Configurations_ReductionFractional
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

def statePoolTemplates (hn : D.graph.n = 2 * D.k)
    (S : ∀ v s, D.LocalState v s) :
    PoolTemplates D.packingInstance D.Template (GlobalSpecies D.graph) FlagSpecies where
  base := D.templateBase S
  globalPool := D.physicalGlobalPool
  flagPool := D.physicalFlagPool
  globalSpecies := D.templateGlobalSpecies
  flagSpecies := D.templateFlagSpecies
  global_nonempty := by
    intro t
    apply (D.physicalGlobalPool_nonempty_iff _).mpr
    have hc := D.doubled_stateGlobalSpecies_count hn (D.templateGlobalSpecies t)
    have hp : 0 < (Finset.univ.filter (fun q : D.Template =>
        D.templateGlobalSpecies q = D.templateGlobalSpecies t)).card := by
      exact Finset.card_pos.mpr ⟨t, by simp⟩
    change (Finset.univ.filter (fun q : D.Template =>
      D.templateGlobalSpecies q = D.templateGlobalSpecies t)).card = _ at hc
    omega
  flag_nonempty := by
    intro t
    apply (D.physicalFlagPool_nonempty_iff _).mpr
    have hc := D.doubled_stateFlagSpecies_count (D.templateFlagSpecies t)
    have hp : 0 < (Finset.univ.filter (fun q : D.Template =>
        D.templateFlagSpecies q = D.templateFlagSpecies t)).card := by
      exact Finset.card_pos.mpr ⟨t, by simp⟩
    change (Finset.univ.filter (fun q : D.Template =>
      D.templateFlagSpecies q = D.templateFlagSpecies t)).card = _ at hc
    omega
  base_global := fun t =>
    (D.labeledItems_disjoint_physicalGlobalPool (D.templateGlobalSpecies t)).mono_left
      (D.templateBase_subset_labeledItems S t)
  base_flag := fun t =>
    (D.labeledItems_disjoint_physicalFlagPool (D.templateFlagSpecies t)).mono_left
      (D.templateBase_subset_labeledItems S t)
  global_flag := fun t => D.physicalGlobalPool_disjoint_physicalFlagPool
    (D.templateGlobalSpecies t) (D.templateFlagSpecies t)
  capacity := by
    intro t u f
    obtain ⟨j, hj⟩ := (D.mem_physicalGlobalPool (D.templateGlobalSpecies t) u.val).mp
      u.property
    obtain ⟨l, hl⟩ := (D.mem_physicalFlagPool (D.templateFlagSpecies t) f.val).mp
      f.property
    rw [← hj, ← hl]
    exact D.templateBase_capacity S t ⟨D.templateGlobalSpecies t, j⟩
      ⟨D.templateFlagSpecies t, l⟩ rfl rfl

end BinPackingGap.InventoryData

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_MachineBoundedIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.MachineBoundedIteration

open Turing BinPackingGames.Foundations.Complexity

theorem computation_finiteAlphabet {α : Type} (encode : α → List Bool) (step : α → α)
    (body : TM2ComputableInPolyTime encode encode step)
    (growth : Polynomial Nat) (bounded : GrowthBound encode step growth)
    (finite : MachineFiniteAlphabet.FiniteAlphabet body.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (computation encode step body growth bounded).tm :=
  MachineFiniteAlphabet.repeat_machine body.tm body.inputAlphabet body.outputAlphabet finite

end BinPackingGap.MachineBoundedIteration

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingGapDefinitions
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.PairFirstProjection

open Turing BinPackingGames.Foundations.Complexity MachineComposition

def program : MachineCanonicalOutput.Program Tape Label State where
  input := .input
  output := .output
  main := .scan
  initial := none
  code := code

abbrev machine := MachineCanonicalOutput.sourceMachine program

def cfg (label : Option Label) (state : State)
    (input counter reversed output : List Bool) : machine.Cfg :=
  ⟨label, state, tapes input counter reversed output⟩

theorem scan_true (r : State) (a b c d : List Bool) :
    machine.step (cfg (some .scan) r (true :: a) b c d) =
      some (cfg (some .scan) (some true) a (true :: b) c d) := by
  simp [FinTM2.step, TM2.step, machine, MachineCanonicalOutput.sourceMachine,
    program, code, cfg, TM2.stepAux]
  apply congrArg (fun stk => some (⟨some .scan, some true, stk⟩ : machine.Cfg))
  funext k
  cases k <;> rfl

theorem scan_false (r : State) (a b c d : List Bool) :
    machine.step (cfg (some .scan) r (false :: a) b c d) =
      some (cfg (some .copy) (some false) a b c d) := by
  simp [FinTM2.step, TM2.step, machine, MachineCanonicalOutput.sourceMachine,
    program, code, cfg, TM2.stepAux]
  apply congrArg (fun stk => some (⟨some .copy, some false, stk⟩ : machine.Cfg))
  funext k
  cases k <;> rfl

theorem copy_cons (r : State) (bit : Bool) (a b c d : List Bool) :
    machine.step (cfg (some .copy) r (bit :: a) (true :: b) c d) =
      some (cfg (some .copy) (some bit) a b (bit :: c) d) := by
  simp [FinTM2.step, TM2.step, machine, MachineCanonicalOutput.sourceMachine,
    program, code, cfg, TM2.stepAux]
  apply congrArg (fun stk => some (⟨some .copy, some bit, stk⟩ : machine.Cfg))
  funext k
  cases k <;> rfl

theorem copy_nil (r : State) (a c d : List Bool) :
    machine.step (cfg (some .copy) r a [] c d) =
      some (cfg (some .reverse) none a [] c d) := by
  simp [FinTM2.step, TM2.step, machine, MachineCanonicalOutput.sourceMachine,
    program, code, cfg, TM2.stepAux]
  apply congrArg (fun stk => some (⟨some .reverse, none, stk⟩ : machine.Cfg))
  funext k
  cases k <;> rfl

theorem reverse_cons (r : State) (bit : Bool) (a b c d : List Bool) :
    machine.step (cfg (some .reverse) r a b (bit :: c) d) =
      some (cfg (some .reverse) (some bit) a b c (bit :: d)) := by
  simp [FinTM2.step, TM2.step, machine, MachineCanonicalOutput.sourceMachine,
    program, code, cfg, TM2.stepAux]
  apply congrArg (fun stk => some (⟨some .reverse, some bit, stk⟩ : machine.Cfg))
  funext k
  cases k <;> rfl

theorem reverse_nil (r : State) (a b d : List Bool) :
    machine.step (cfg (some .reverse) r a b [] d) =
      some (cfg none none a b [] d) := by
  simp [FinTM2.step, TM2.step, machine, MachineCanonicalOutput.sourceMachine,
    program, code, cfg, TM2.stepAux]
  apply congrArg (fun stk => some (⟨none, none, stk⟩ : machine.Cfg))
  funext k
  cases k <;> rfl

theorem scan_trace (n m : Nat) (r : State) (rest c d : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some .scan) r (encodeWord n ++ rest)
        (List.replicate m true) c d)) =
    some (cfg (some .copy) (some false) rest
      (List.replicate (m + n) true) c d) := by
  induction n generalizing m r with
  | zero =>
      simpa [encodeWord, advance, Option.bind_some] using!
        scan_false r rest (List.replicate m true) c d
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp only [encodeWord, List.replicate_succ, List.cons_append, advance_some,
        scan_true]
      have h := ih (m + 1) (some true)
      simpa [encodeWord, List.replicate_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h

theorem copy_trace (word rest acc out : List Bool) (r : State) :
    (advance machine.step)^[word.length + 1]
      (some (cfg (some .copy) r (word ++ rest)
        (List.replicate word.length true) acc out)) =
    some (cfg (some .reverse) none rest [] (word.reverse ++ acc) out) := by
  induction word generalizing acc r with
  | nil => simpa [advance, Option.bind_some] using! copy_nil r rest acc out
  | cons bit word ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [List.cons_append, List.replicate_succ, advance_some, copy_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (bit :: acc) (some bit)

theorem reverse_trace (word rest counter out : List Bool) (r : State) :
    (advance machine.step)^[word.length + 1]
      (some (cfg (some .reverse) r rest counter word out)) =
    some (cfg none none rest counter [] (word.reverse ++ out)) := by
  induction word generalizing out r with
  | nil => simpa [advance, Option.bind_some] using! reverse_nil r rest counter out
  | cons bit word ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some, reverse_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (bit :: out) (some bit)

theorem init_eq (input : List Bool) :
    initList machine input = cfg (some .scan) none input [] [] [] := by
  unfold initList cfg
  congr 1
  funext k
  cases k <;> rfl

theorem projection_trace (x witness : List Bool) :
    (advance machine.step)^[3 * x.length + 3]
      (some (initList machine (CookLevin.pairBits (x, witness)))) =
    some (cfg none none witness [] [] x) := by
  have hs := scan_trace x.length 0 none (x ++ witness) [] []
  have hc := copy_trace x witness [] [] (some false)
  have hr := reverse_trace x.reverse witness [] [] none
  simp only [Nat.zero_add, List.replicate_zero] at hs
  simp only [List.append_nil] at hc
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  rw [init_eq]
  have hn : 3 * x.length + 3 = (x.length + 1) + ((x.length + 1) + (x.length + 1)) := by omega
  rw [hn]
  simpa only [CookLevin.pairBits, List.append_assoc, Function.iterate_add_apply] using
    (show (advance machine.step)^[x.length + 1]
      ((advance machine.step)^[x.length + 1]
        ((advance machine.step)^[x.length + 1]
          (some (cfg (some .scan) none (encodeWord x.length ++ (x ++ witness)) [] [] [])))) =
        some (cfg none none witness [] [] x) from by rw [hs, hc, hr])

def rawRun (p : List Bool × List Bool) :
    MachineCanonicalOutput.TerminalRun program (CookLevin.pairBits p) p.1
      (rawTime.eval (CookLevin.pairBits p).length) where
  state := none
  tapes := tapes p.2 [] [] p.1
  execution := {
    steps := 3 * p.1.length + 3
    evals_in_steps := projection_trace p.1 p.2
    steps_le_m := by
      simp [rawTime, CookLevin.pairBits_length]
      omega }
  output_eq := rfl

theorem cleanup_complete (k : Tape) : k ∈ cleanupTapes ↔ k ≠ program.output := by
  cases k <;> simp [cleanupTapes, program]

noncomputable def computation :
    TM2ComputableInPolyTime CookLevin.pairBits (id : List Bool → List Bool)
      (fun p : List Bool × List Bool => p.1) :=
  MachineCanonicalOutput.computableInPolyTime program cleanupTapes cleanup_complete
    CookLevin.pairBits id (fun p => p.1) rawTime rawRun

end BinPackingGap.PairFirstProjection

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitializeEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchSemantics

open ExtensionQuery

def DecidesExtension (D : List Bool → Bool) : Prop :=
  ∀ b r fixed, D (BinaryEncoding.extensionBits b r fixed) = true ↔ Ext b r fixed

end BinPackingGap.SearchSemantics

namespace BinPackingGap.SearchEncoding

open SearchSemantics BinaryEncoding BinPackingGames.Foundations.Complexity

theorem label_le_stateBits_length (s : State) : s.label ≤ (stateBits s).length := by
  rw [stateBits_length]
  omega

theorem fixedBits_set_length_le (fixed : List (Option Nat)) (i j : Nat) :
    (fixedBits (fixed.set i (some j))).length ≤
      (fixedBits fixed).length + 2 * j + 2 := by
  have bound := listBits_set_length_le (optionBits natBits) fixed i (some j)
  have width := size_le_self j
  simp only [optionBits, List.length_cons, natBits_length] at bound
  change (listBits (optionBits natBits) (fixed.set i (some j))).length ≤
    (listBits (optionBits natBits) fixed).length + 2 * j + 2
  omega

theorem update_label_le (s : State) (answer : Bool) :
    (update s answer).label ≤ s.label + 1 := by
  cases h : s.phase <;> cases answer <;> simp [update, h]

theorem update_length_le (s : State) (answer : Bool) :
    (stateBits (update s answer)).length ≤ (stateBits s).length + 2 * s.label + 5 := by
  have fixedBound := fixedBits_set_length_le s.fixed s.item s.label
  simp only [stateBits_length]
  cases h : s.phase <;> cases answer <;> simp [update, h] <;> omega

theorem step_label_le (D : List Bool → Bool) (s : State) :
    (step D s).label ≤ s.label + 1 := update_label_le s _

theorem step_length_le (D : List Bool → Bool) (s : State) :
    (stateBits (step D s)).length ≤ (stateBits s).length + 2 * s.label + 5 :=
  update_length_le s _

theorem iterate_label_le (D : List Bool → Bool) (s : State) (t : Nat) :
    ((step D)^[t] s).label ≤ s.label + t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have bound := step_label_le D ((step D)^[t] s)
    omega

theorem iterate_length_le (D : List Bool → Bool) (s : State) (t : Nat) :
    (stateBits ((step D)^[t] s)).length ≤
      (stateBits s).length + t * (2 * s.label + 2 * t + 5) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have bound := step_length_le D ((step D)^[t] s)
    have labelBound := iterate_label_le D s t
    nlinarith

theorem growthBound (D : List Bool → Bool) :
    MachineBoundedIteration.GrowthBound stateBits (step D) growthPolynomial := by
  intro p i hi
  let L := (MachineBoundedIteration.inputBits stateBits p).length
  have startBound : (stateBits p.2).length ≤ L := by
    dsimp [L]
    rw [MachineBoundedIteration.inputBits_length]
    omega
  have countBound : p.1 ≤ L := by
    dsimp [L]
    rw [MachineBoundedIteration.inputBits_length]
    omega
  have iBound : i ≤ L := hi.trans countBound
  have labelBound : p.2.label ≤ L := (label_le_stateBits_length p.2).trans startBound
  have coefficientBound : 2 * p.2.label + 2 * i + 5 ≤ 4 * L + 5 := by omega
  have productBound := Nat.mul_le_mul iBound coefficientBound
  have lengthBound := iterate_length_le D p.2 i
  change (stateBits ((step D)^[i] p.2)).length ≤ growthPolynomial.eval L
  simp only [growthPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

end BinPackingGap.SearchEncoding

namespace BinPackingGap.SearchOptimalConstruction

open Turing BinPackingGames.Foundations.Complexity

theorem decidesExtension_of_language {D : List Bool → Bool}
    (correct : ∀ input, ExtensionCertificate.language input ↔ D input = true) :
    SearchSemantics.DecidesExtension D := by
  intro bins items fixed
  exact (correct (BinaryEncoding.extensionBits bins items fixed)).symm.trans
    (ExtensionCertificate.language_extensionBits bins items fixed)

end BinPackingGap.SearchOptimalConstruction

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitialItemsMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchInitialItemsMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer

def loopTime : RawInstance → Nat
  | [] => 1
  | (a, d) :: items => rowTime a d + loopTime items

end BinPackingGap.SearchInitialItemsMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingPowerProgram
attribute [-instance] _root_.OAI.BinPackingCompleteness.PCPSource.clauseCount_neZero _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.LiteralSlotGraphMachine.instDecidableBodyEdge _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype _root_.OAI.BinPackingGap.instFintypeGlobalSpecies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.LiteralSlotGraphMachine

open Turing BinPackingGames.Foundations BinPackingGames.Foundations.Target
open FiniteTapeProgram

def inputBits (F : NonemptyFormula) : List Bool := Complexity.formulaBits F.val

def graphInput (F : NonemptyFormula) : GraphReductionInput where
  graph := LiteralSlotGraph.graph F.val
  k := 2 * F.val.clauses.length
  k_le := by simp [LiteralSlotGraph.graph, LiteralSlotGraph.vertexCount]; omega
  nonempty := LiteralSlotGraph.graph_edges_nonempty F.val F.property

def copy (source destination scratchTape : Tape) : Program :=
  BooleanTapeCode.copy source destination scratchTape
def drain (source : Tape) : Program := BooleanTapeCode.drain source

def innerBody : Program := sequence [
  readVariable .innerSource .innerVariable,
  readSign .innerSource (fun a b => {a with innerSign := b}),
  copy .outerVariable .comparison .scratch,
  compareVariables,
  .branch isEdge emitPair skip,
  increment .innerIndex,
  changeControl nextRemaining]

def innerLoop : Program :=
  .loop (.peek .innerSource saveHead .done) (fun s => s.2.isSome) innerBody

def outerBody : Program := sequence [
  readVariable .input .outerVariable,
  readSign .input (fun a b => {a with outerSign := b}),
  copy .input .innerSource .scratch,
  copy .outerIndex .innerIndex .scratch,
  increment .innerIndex,
  changeControl startRow,
  innerLoop,
  drain .innerIndex,
  drain .outerVariable,
  increment .outerIndex,
  changeControl nextSlot]

def outerLoop : Program :=
  .loop (.peek .input saveHead .done) (fun s => s.2.isSome) outerBody

def program : Program := sequence [
  skipField .input,
  pushBit .unary false,
  countHeader,
  .atom (.load resetHead .done),
  BooleanTapeCode.convert .unary .outerIndex .scratch,
  frame .outerIndex .scratch .accumulator,
  drain .outerIndex,
  vertices,
  pushBit .accumulator false,
  drain .outerIndex,
  outerLoop,
  pushBit .accumulator false,
  drain .outerIndex,
  transfer .accumulator .output,
  .atom (.load (fun _ => initialState) .done)]

def machine : FinTM2 := program.machine .input .output initialState

end BinPackingGap.LiteralSlotGraphMachine

namespace BinPackingGap.PackingFieldDecodeMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open FiniteTapeProgram

variable {K A : Type} [DecidableEq K]

theorem decodeNat_exec (slots : Fin 3 ↪ K) (base : K → List Bool)
    (ambient : A) (n : Nat) (suffix : List Bool)
    (sourceWord : base (slots 0) = BinaryEncoding.natBits n ++ suffix)
    (scratchEmpty : base (slots 1) = []) :
    Exec (code slots) ⟨BinaryAddMachine.clean ambient, base⟩ (2 * n.size + 2)
      ⟨BinaryAddMachine.clean ambient, decodedTapes slots base n.bits suffix⟩ := by
  apply Exec.routine
  have run := ExtensionNatMachine.natTrace (decoderSlots slots) id none none
    (ExtensionNatMachine.statement (decoderSlots slots) id none none) (fun _ => rfl)
    base n suffix (by simpa using sourceWord) (by simpa using scratchEmpty) ambient
  simpa only [ExtensionNatMachine.resultTapes, decodedTapes, decoderSlots_zero,
    decoderSlots_one, id_eq] using run

end BinPackingGap.PackingFieldDecodeMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Hardness_LiteralSlotGraphEnumeration
attribute [-instance] _root_.OAI.BinPackingCompleteness.PCPSource.clauseCount_neZero _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.LiteralSlotGraphMachine

section

open FiniteTapeProgram BinPackingGames.Foundations.Complexity

theorem vertexBodyCost_le (i : Nat) : vertexBodyCost i ≤ 5 * i + 12 := by
  have hs := UnaryToBinaryMachine.steps_le 1 i
  have hb := bits_length_le i
  simp only [vertexBodyCost]
  nlinarith

theorem vertexLoopCost_le (n i : Nat) :
    vertexLoopCost n i ≤ n * (5 * (i + n) + 13) + 1 := by
  induction n generalizing i with
  | zero => simp [vertexLoopCost]
  | succ n ih =>
      have hs := vertexBodyCost_le i
      have ht := ih (i + 1)
      simp only [vertexLoopCost]
      nlinarith

theorem innerBodyCost_le (a : Control) (left right : RawLiteral) (u v B : Nat)
    (hL : left.1 ≤ B) (hR : right.1 ≤ B) (hU : u ≤ B) (hV : v ≤ B) :
    innerBodyCost a left right u v ≤ 14 * B + 25 := by
  have hp := pairCost_le u v
  have hi := UnaryToBinaryMachine.steps_le 1 v
  have hb : branchCost a left right u v ≤ 3 * u + 3 * v + 9 := by
    unfold branchCost
    split_ifs <;> omega
  have hm : max left.1 right.1 ≤ B := max_le hL hR
  simp only [innerBodyCost]
  omega

theorem innerLoopCost_le (a : Control) (left : RawLiteral) (u v B : Nat)
    (rest : List RawLiteral) (hL : left.1 ≤ B) (hU : u ≤ B)
    (hV : v + rest.length ≤ B) (hR : ∀ right ∈ rest, right.1 ≤ B) :
    innerLoopCost a left u v rest ≤ rest.length * (14 * B + 26) + 1 := by
  induction rest generalizing a v with
  | nil => simp [innerLoopCost]
  | cons right rest ih =>
      have hb := innerBodyCost_le a left right u v B hL (hR right (by simp)) hU (by simp_all; omega)
      have ht := ih (bodyControl a left right) (v + 1) (by simp_all; omega)
        (fun x hx => hR x (by simp [hx]))
      simp only [innerLoopCost, List.length_cons]
      nlinarith

theorem outerBodyCost_le (a : Control) (left : RawLiteral) (u B : Nat) (rest : List RawLiteral)
    (hL : left.1 ≤ B) (hU : u + 1 + rest.length ≤ B)
    (hS : (literalsBits rest).length ≤ B) (hR : ∀ right ∈ rest, right.1 ≤ B) :
    outerBodyCost a left u rest ≤ 40 * (B + 1) ^ 2 := by
  have hu : u ≤ B := by omega
  have hcount : rest.length ≤ B := by omega
  have huBits := bits_length_le u
  have hvBits := bits_length_le (u + 1 + rest.length)
  have inc := UnaryToBinaryMachine.steps_le 1 u
  have row := innerLoopCost_le (rowStartControl a left) left u (u + 1) B rest hL hu hU hR
  have rowBound := Nat.mul_le_mul_right (14 * B + 26) hcount
  simp only [outerBodyCost]
  nlinarith

theorem outerLoopCost_le (a : Control) (u B : Nat) (literals : List RawLiteral)
    (hU : u + literals.length ≤ B) (hS : (literalsBits literals).length ≤ B)
    (hL : ∀ left ∈ literals, left.1 ≤ B) :
    outerLoopCost a u literals ≤ literals.length * (40 * (B + 1) ^ 2 + 1) + 1 := by
  induction literals generalizing a u with
  | nil => simp [outerLoopCost]
  | cons left rest ih =>
      have tailSize : (literalsBits rest).length ≤ B := by
        rw [literalsBits_cons, List.length_append] at hS
        omega
      have hu : u + 1 + rest.length ≤ B := by simpa [List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hU
      have hb := outerBodyCost_le a left u B rest (hL left (by simp)) hu tailSize
        (fun x hx => hL x (by simp [hx]))
      have ht := ih (outerBodyControl a left rest) (u + 1) hu tailSize
        (fun x hx => hL x (by simp [hx]))
      simp only [outerLoopCost, List.length_cons]
      nlinarith

end

open BinPackingGames.Foundations.Target BinPackingGames.Foundations.Complexity

theorem suffixEdges_formulaLiterals (F : Formula) :
    suffixEdges 0 (formulaLiterals F) = (LiteralSlotGraph.graph F).endpointPairs := by
  have tagged : indexFrom 0 (formulaLiterals F) =
      (List.finRange (LiteralSlotGraph.vertexCount F)).map (tagVertex F) := by
    rw [formulaLiterals_eq_ofFn, indexFrom_ofFn]
    simp only [Nat.zero_add]
    change List.ofFn (tagVertex F) = _
    exact List.ofFn_eq_map
  have sorted : ((List.finRange (LiteralSlotGraph.vertexCount F)).map
      (tagVertex F)).Pairwise (fun a b => a.1 < b.1) := by
    rw [← List.ofFn_eq_map, List.pairwise_ofFn]
    intro i j hij
    exact hij
  rw [suffixEdges_eq_forwardRows, tagged, forwardRows_eq_allPairs _ sorted]
  simp only [List.flatMap_map, List.filterMap_map, Function.comp_def]
  have pairEq (u v : LiteralSlotGraph.Vertex F) :
      pairEntry (tagVertex F u) (tagVertex F v) =
        if decide (u < v ∧ LiteralSlotGraph.Conflict F u v)
        then some (u.val, v.val) else none := by
    change (if u.val < v.val ∧ taggedConflict (tagVertex F u) (tagVertex F v)
        then some (u.val, v.val) else none) = _
    simp only [tagVertex_conflict, decide_eq_true_eq, Fin.lt_def]
  simp_rw [pairEq]
  rw [filtered_product]
  rfl

end BinPackingGap.LiteralSlotGraphMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Hardness_LiteralSlotGraphComputation
attribute [-instance] _root_.OAI.BinPackingCompleteness.PCPSource.clauseCount_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.LiteralSlotGraphMachine

open Turing FiniteTapeProgram BinPackingGames.Foundations.Target
open BinPackingGames.Foundations.Complexity

theorem rawGraphWord_graphBits (F : NonemptyFormula) :
    rawGraphWord F.val.clauses.length (formulaLiterals F.val) = graphBits (graphInput F) := by
  have vertices : vertexRecords 0 (3 * F.val.clauses.length) ++ [false] =
      BinaryEncoding.listBits BinaryEncoding.natBits (List.range (3 * F.val.clauses.length)) := by
    simpa only [← List.range_eq_range'] using
      vertexRecords_listBits 0 (3 * F.val.clauses.length)
  have edges := edgeRecords_listBits (suffixEdges 0 (formulaLiterals F.val))
  rw [suffixEdges_formulaLiterals] at edges
  change BinaryEncoding.natBits (2 * F.val.clauses.length) ++
      vertexRecords 0 (3 * F.val.clauses.length) ++ [false] ++
      edgeRecords (suffixEdges 0 (formulaLiterals F.val)) ++ [false] = _
  rw [show BinaryEncoding.natBits (2 * F.val.clauses.length) ++
      vertexRecords 0 (3 * F.val.clauses.length) ++ [false] ++
      edgeRecords (suffixEdges 0 (formulaLiterals F.val)) ++ [false] =
      BinaryEncoding.natBits (2 * F.val.clauses.length) ++
        (vertexRecords 0 (3 * F.val.clauses.length) ++ [false]) ++
        (edgeRecords (suffixEdges 0 (formulaLiterals F.val)) ++ [false]) by
      simp only [List.append_assoc]]
  rw [vertices, edgeRecords_listBits, suffixEdges_formulaLiterals]
  rfl

theorem rawCost_formula_le (F : Formula) :
    rawCost F.variables F.clauses.length (formulaLiterals F) ≤
      100 * ((formulaBits F).length + 1) ^ 3 := by
  let s := (formulaBits F).length
  have hcount : 3 * F.clauses.length ≤ s := literalSlots_le_formulaBits_length F
  have hlits : (formulaLiterals F).length ≤ s := by
    rw [formulaLiterals_length]
    exact hcount
  have htwo : 2 * F.clauses.length ≤ s := by omega
  have hvar : F.variables ≤ s := by
    have h := congrArg List.length (formulaBits_eq_formulaLiterals F)
    simp only [List.length_append, encodeWord_length] at h
    change s = _ at h
    omega
  have hqbits := (bits_length_le (2 * F.clauses.length)).trans htwo
  have hnbits := (bits_length_le (3 * F.clauses.length)).trans hcount
  have hlbits := (bits_length_le (formulaLiterals F).length).trans hlits
  have convert := UnaryToBinaryMachine.steps_le (2 * F.clauses.length) 0
  have convertMul := Nat.mul_le_mul htwo
    (show 2 * (0 + 2 * F.clauses.length) + 3 ≤ 2 * s + 3 by omega)
  have vertices := vertexLoopCost_le (3 * F.clauses.length) 0
  have verticesMul := Nat.mul_le_mul hcount
    (show 5 * (0 + 3 * F.clauses.length) + 13 ≤ 5 * s + 13 by omega)
  have outer := outerLoopCost_le initialControl 0 s (formulaLiterals F)
    (by simpa using hlits) (literalsBits_formula_length_le F)
    (fun literal h => formula_literal_variable_le_input F h)
  have outerMul := Nat.mul_le_mul_right (40 * (s + 1) ^ 2 + 1) hlits
  have output := formulaGraphWord_length_le F
  change (rawGraphWord F.clauses.length (formulaLiterals F)).length ≤
    4 * s ^ 3 + 5 * s ^ 2 + 4 * s + 3 at output
  have coarse : rawCost F.variables F.clauses.length (formulaLiterals F) ≤
      44 * s ^ 3 + 92 * s ^ 2 + 70 * s + 21 := by
    simp only [rawCost, phaseCosts, List.sum_cons, List.sum_nil]
    nlinarith
  change _ ≤ 100 * (s + 1) ^ 3
  nlinarith [Nat.zero_le (s ^ 3), Nat.zero_le (s ^ 2)]

end BinPackingGap.LiteralSlotGraphMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_EdgeLongConsumption
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace InventoryData

section

variable (D : InventoryData) {b : ℕ}

def earlierKeyItems (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Finset D.packingInstance.Item := (D.earlierKeys h hle).image D.itemEquiv

def earlierGoodKeyTuples (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) : Finset (p.TableBin D.encodedSubclass) := by
  classical
  exact Finset.univ.filter fun t => p.IsGoodTableBin D.encodedSubclass D.encodedLabel t ∧
    p.itemAtRole D.encodedSubclass t .anchor ∈ D.earlierKeyItems h hle

@[simp] theorem mem_earlierGoodKeyTuples (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) (t : p.TableBin D.encodedSubclass) :
    t ∈ D.earlierGoodKeyTuples p h hle ↔
      p.IsGoodTableBin D.encodedSubclass D.encodedLabel t ∧
        p.itemAtRole D.encodedSubclass t .anchor ∈ D.earlierKeyItems h hle := by
  classical
  simp [earlierGoodKeyTuples]

def remainingEarlierW (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) : Finset D.packingInstance.Item :=
  D.earlierWItems h hle \
    Coverage.roleItems p D.encodedSubclass (D.earlierGoodKeyTuples p h hle) .«global»

end

open scoped BigOperators
open PackingCounts

variable (D : InventoryData) {b : ℕ}

def edgeLongTuplesAt (p : Packing D.packingInstance b) (edge : D.Edge)
    (q : Fin 2 × Fin D.R) : Finset (p.TableBin D.encodedSubclass) :=
  Coverage.currentLongEdgeAt p D.encodedSubclass D.encodedLabel
    (D.graph.endpoint edge q.1)
    (InventoryCoverage.rowBaseline D.itemEquiv)
    (InventoryCoverage.keyBaseline D.itemEquiv)
    (InventoryCoverage.rowShort D.itemEquiv)
    (Geometry.baseline D.graph.edges.length D.R (edge, q.2))

@[simp] theorem mem_edgeLongTuplesAt (p : Packing D.packingInstance b) (edge : D.Edge)
    (q : Fin 2 × Fin D.R) (t : p.TableBin D.encodedSubclass) :
    t ∈ D.edgeLongTuplesAt p edge q ↔
      t ∈ Coverage.edgeTuplesAt p D.encodedSubclass D.encodedLabel
        (D.graph.endpoint edge q.1) ∧
      InventoryCoverage.keyBaseline D.itemEquiv
        (p.itemAtRole D.encodedSubclass t .anchor) =
          Geometry.baseline D.graph.edges.length D.R (edge, q.2) ∧
      InventoryCoverage.rowBaseline D.itemEquiv
        (p.itemAtRole D.encodedSubclass t .x) =
          Geometry.baseline D.graph.edges.length D.R (edge, q.2) ∧
      InventoryCoverage.rowShort D.itemEquiv
        (p.itemAtRole D.encodedSubclass t .x) ≠ true := by
  classical
  simp [edgeLongTuplesAt, Coverage.currentLongEdgeAt, Coverage.currentEdgeTuplesAt,
    and_assoc]

def edgeLongTuples (p : Packing D.packingInstance b) (edge : D.Edge)
    (J : Finset (Fin D.R)) : Finset (p.TableBin D.encodedSubclass) := by
  classical
  exact ((Finset.univ : Finset (Fin 2)).product J).biUnion (D.edgeLongTuplesAt p edge)

end InventoryData
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingScalarExpression
attribute [-instance] _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

open IntegerPackingArithmetic

variable (D : InventoryData)

variable (hplus : D.plus.height ≤ D.L) (hminus : D.minus.height ≤ D.L)

include hplus hminus in
theorem coordinateDenominator_mul_treeBaseline (r : D.TreeRow) :
    (D.coordinateDenominator : ℚ) * D.treeBaseline r =
      (D.treeBaselineInteger r : ℚ) := by
  rcases r with ⟨node, j⟩ | (⟨node, j⟩ | j)
  · simpa only [treeBaseline, treeBaselineInteger, Int.cast_natCast,
      coordinateDenominator] using
      geomDenominator_mul_treeRight D.graph.edges.length D.R D.geometryBound D.L
        .plus node.val ((D.plus.length_le_height node.property).trans hplus)
  · simpa only [treeBaseline, treeBaselineInteger, Int.cast_natCast,
      coordinateDenominator] using
      geomDenominator_mul_treeRight D.graph.edges.length D.R D.geometryBound D.L
        .minus node.val ((D.minus.length_le_height node.property).trans hminus)
  · simp [treeBaseline, treeBaselineInteger]

include hplus hminus in
theorem coordinateDenominator_mul_rowBaseline {v : D.Vertex} (r : D.RowAt v) :
    (D.coordinateDenominator : ℚ) * D.rowBaseline r =
      (D.rowBaselineInteger r : ℚ) := by
  rcases r with r | ⟨b, j⟩
  · exact D.coordinateDenominator_mul_treeBaseline hplus hminus r
  · exact geomDenominator_mul_baseline _ _ _ _ _

include hplus hminus in
theorem coordinateDenominator_mul_treeDeadline (r : D.TreeRow) :
    (D.coordinateDenominator : ℚ) * D.treeDeadline r =
      (D.treeDeadlineInteger r : ℚ) := by
  rcases r with ⟨node, j⟩ | (⟨node, j⟩ | j)
  · have hn := (D.plus.length_le_height node.property).trans hplus
    by_cases hl : node.val ∈ D.plus.leaves
    · simpa only [treeDeadline, treeDeadlineInteger, hl, ite_true, if_true, Int.cast_natCast,
        coordinateDenominator] using
        geomDenominator_mul_treeLeft D.graph.edges.length D.R D.geometryBound D.L
          .plus node.val hn
    · simpa only [treeDeadline, treeDeadlineInteger, hl, ite_false, Int.cast_natCast,
        coordinateDenominator] using
        geomDenominator_mul_treeRight D.graph.edges.length D.R D.geometryBound D.L
          .plus node.val hn
  · have hn := (D.minus.length_le_height node.property).trans hminus
    by_cases hl : node.val ∈ D.minus.leaves
    · simpa only [treeDeadline, treeDeadlineInteger, hl, ite_true, if_true, Int.cast_natCast,
        coordinateDenominator] using
        geomDenominator_mul_treeLeft D.graph.edges.length D.R D.geometryBound D.L
          .minus node.val hn
    · simpa only [treeDeadline, treeDeadlineInteger, hl, ite_false, Int.cast_natCast,
        coordinateDenominator] using
        geomDenominator_mul_treeRight D.graph.edges.length D.R D.geometryBound D.L
          .minus node.val hn
  · simp [treeDeadline, treeDeadlineInteger]

include hplus hminus in
theorem coordinateDenominator_mul_deadline {v : D.Vertex} (r : D.MBase v) :
    (D.coordinateDenominator : ℚ) * D.deadline r =
      (D.deadlineInteger r : ℚ) := by
  rcases r with r | j
  · exact D.coordinateDenominator_mul_treeDeadline hplus hminus r
  · simp only [deadline, deadlineInteger, Geometry.jobLeft, mul_sub, Int.cast_sub,
      Int.cast_one, coordinateDenominator, geomDenominator_mul_baseline,
      geomDenominator_mul_delta]

include hplus hminus in
theorem coordinateDenominator_mul_rowCoordinate {v : D.Vertex} (r : D.RowAt v) :
    (D.coordinateDenominator : ℚ) * D.rowCoordinate r =
      (D.rowIntegerCoordinate r : ℚ) := by
  have hb := D.coordinateDenominator_mul_rowBaseline hplus hminus r
  simp only [coordinateDenominator] at hb
  have hd := geomDenominator_mul_delta D.graph.edges.length D.R D.geometryBound D.L
  cases hs : D.rowShort r <;>
    simp [rowCoordinate, rowIntegerCoordinate, hs, mul_sub, hb,
      coordinateDenominator, hd]

include hplus hminus in
theorem coordinateDenominator_mul_anchorCoordinate {v : D.Vertex} (r : D.AnchorAt v) :
    (D.coordinateDenominator : ℚ) * D.anchorCoordinate r =
      (D.anchorIntegerCoordinate r : ℚ) := by
  rcases r with r | j
  · simp only [anchorCoordinate, anchorIntegerCoordinate, mul_neg, Int.cast_neg,
      D.coordinateDenominator_mul_deadline hplus hminus r]
  · simp only [anchorCoordinate, anchorIntegerCoordinate, mul_sub, mul_neg,
      Int.cast_sub, Int.cast_neg, coordinateDenominator, geomDenominator_mul_baseline,
      geomDenominator_mul_beta]

include hplus hminus in
theorem coordinateDenominator_mul_itemCoordinate (i : D.Item) :
    (D.coordinateDenominator : ℚ) * D.itemCoordinate i =
      (D.itemIntegerCoordinate i : ℚ) := by
  rcases i with ⟨r, i⟩
  cases r with
  | x => exact D.coordinateDenominator_mul_rowCoordinate hplus hminus i.2
  | anchor => exact D.coordinateDenominator_mul_anchorCoordinate hplus hminus i.2
  | «global» => exact D.coordinateDenominator_mul_globalCoordinate i
  | «local» => exact D.coordinateDenominator_mul_localCoordinate i.2
  | flag => simp [itemCoordinate, itemIntegerCoordinate]

include hplus hminus in
theorem itemIntegerCoordinate_ratio (i : D.Item) :
    (D.itemIntegerCoordinate i : ℚ) / D.coordinateDenominator = D.itemCoordinate i := by
  have hd : (D.coordinateDenominator : ℚ) ≠ 0 := by
    exact_mod_cast D.coordinateDenominator_pos.ne'
  apply (div_eq_iff hd).mpr
  simpa only [mul_comm] using
    (D.coordinateDenominator_mul_itemCoordinate hplus hminus i).symm

include hplus hminus in
theorem itemRawPair_valid (i : D.Item) :
    0 < (D.itemRawPair i).1 ∧ (D.itemRawPair i).1 < (D.itemRawPair i).2 := by
  apply rawItem_valid D.coordinateDenominator D.coordinateDenominator_pos
  rw [D.itemIntegerCoordinate_ratio hplus hminus i]
  exact D.itemCoordinate_abs_le_six i

include hplus hminus in
theorem itemRawPair_ratio (i : D.Item) :
    ((D.itemRawPair i).1 : ℚ) / (D.itemRawPair i).2 = D.itemSize i := by
  have hW : |(D.itemIntegerCoordinate i : ℚ) / D.coordinateDenominator| ≤ 6 := by
    rw [D.itemIntegerCoordinate_ratio hplus hminus i]
    exact D.itemCoordinate_abs_le_six i
  change ((rawItem _ _ _ _).1 : ℚ) / (rawItem _ _ _ _).2 = _
  rw [rawItem_ratio D.coordinateDenominator D.coordinateDenominator_pos _ _ _ hW,
    D.itemIntegerCoordinate_ratio hplus hminus i]
  rfl

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

theorem rawItemList_valid (hplus : D.plus.height ≤ D.L)
    (hminus : D.minus.height ≤ D.L) : D.rawItemList.Valid := by
  intro q hq
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  have hi := D.itemRawPair_valid hplus hminus i
  exact ⟨hi.1, hi.2.le⟩

theorem rawItemList_get (i : Fin D.rawItemList.length) :
    D.rawItemList.get i =
      D.itemRawPair (D.itemList.get (Fin.cast D.rawItemList_length_items i)) := by
  rcases i with ⟨i, hi⟩
  change i < (D.itemList.map D.itemRawPair).length at hi
  change (D.itemList.map D.itemRawPair)[i]'hi =
    D.itemRawPair (D.itemList[i]'(by simpa [rawItemList] using hi))
  simp only [List.getElem_map]

theorem rawItemList_get_ratio (hplus : D.plus.height ≤ D.L)
    (hminus : D.minus.height ≤ D.L) (i : Fin D.rawItemList.length) :
    RawInstance.ratValue (D.rawItemList.get i) =
      D.itemSize (D.itemList.get (Fin.cast D.rawItemList_length_items i)) := by
  rw [D.rawItemList_get]
  exact D.itemRawPair_ratio hplus hminus _

def rawItemListReindexing (hk : D.k ≤ D.graph.n)
    (hplus : D.plus.height ≤ D.L) (hminus : D.minus.height ≤ D.L) :
    Instance.Reindexing (D.rawItemList.toInstance (D.rawItemList_valid hplus hminus))
      D.packingInstance where
  equiv := (D.rawItemListEquiv hk).trans D.itemEquiv
  size_eq i := by
    change Fin D.rawItemList.length at i
    change RawInstance.ratValue (D.rawItemList.get i) =
      D.itemSize (D.itemEquiv.symm (D.itemEquiv (D.rawItemListEquiv hk i)))
    rw [Equiv.symm_apply_apply, D.rawItemListEquiv_apply]
    exact D.rawItemList_get_ratio hplus hminus i

theorem rawOutput_valid (hplus : D.plus.height ≤ D.L)
    (hminus : D.minus.height ≤ D.L) : D.rawOutput.2.Valid :=
  D.rawItemList_valid hplus hminus

end BinPackingGap.InventoryData

namespace BinPackingGap

theorem graphPackingOutput_valid (c : ℕ) (ρ : ℝ) (x : GraphReductionInput) :
    (graphPackingOutput c ρ x).2.Valid :=
  (reductionInventory c ρ x.graph x.k).rawOutput_valid
    (reductionInventory_plus_height c ρ x.graph x.k).le
    (reductionInventory_minus_height c ρ x.graph x.k).le

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Hardness_PCPPackingGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PCPFoundation

section

open BinPackingGames.Foundations
open Target
open BinPackingCompleteness

def formula (F : Formula) : Formula := PCPSource.normalizedFormula F

def graph (F : Formula) : GraphInput := LiteralSlotGraph.graph (formula F)

def target (F : Formula) : ℕ := 2 * (formula F).clauses.length

theorem formula_nonempty (F : Formula) : (formula F).clauses ≠ [] :=
  PCPSource.normalizedFormula_nonempty F

theorem edges_nonempty (F : Formula) : (graph F).edges ≠ [] :=
  LiteralSlotGraph.graph_edges_nonempty (formula F) (formula_nonempty F)

theorem target_le_vertices (F : Formula) : target F ≤ (graph F).n := by
  change 2 * (formula F).clauses.length ≤ 3 * (formula F).clauses.length
  omega

end

open BinPackingGames.Foundations.Target

def graphInput (F : Formula) : GraphReductionInput where
  graph := graph F
  k := target F
  k_le := target_le_vertices F
  nonempty := edges_nonempty F

def packingOutput (c : Nat) (F : Formula) : RawReductionOutput :=
  graphPackingOutput c rho (graphInput F)

theorem packingOutput_valid (c : Nat) (F : Formula) :
    (packingOutput c F).2.Valid :=
  graphPackingOutput_valid c rho (graphInput F)

end BinPackingGap.PCPFoundation

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingCountedProgram
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.GraphTokenMachine

open Turing
open BinaryEncoding
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction
open GraphTallyMachine (Mode Slot afterName initial transition)

variable {K Λ σ : Type} [DecidableEq K]

theorem tokensTrace (field : Field) (slots : Fin 3 ↪ K) (labels : Label → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = instruction field slots labels exit label)
    (base : K → List Bool) (input : GraphReductionInput)
    (sourceWord : base (slots 0) = graphBits input) (scratchEmpty : base (slots 1) = [])
    (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[3 * (graphBits input).length + 2]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨exit, clean ambient, resultTapes field slots base input⟩ := by
  have hd (i j : Fin 3) (hne : i ≠ j) : slots i ≠ slots j := slots.injective.ne hne
  have run := MachineTransducerCopy.transduceCopyTrace (slots 0) (slots 1) (slots 2)
    (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide))
    initial transition (emit field) (labels .scan) (labels .restore)
    (fun mode bit => labels (.emitter mode bit)) exit program
    (atLabels .scan) (fun mode bit => atLabels (.emitter mode bit))
    (atLabels .restore) base scratchEmpty ambient initial none
  have hout : MachineTransducer.output transition (emit field) initial (base (slots 0)) =
      tokenBits field input := by
    change scanOutput field initial (base (slots 0)) = _
    rw [sourceWord, output_graphBits]
  rw [hout] at run
  simpa only [sourceWord, tokenBits_reverse, clean, resultTapes] using run

end BinPackingGap.GraphTokenMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingJobList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingJobStream

open PackingDescriptorExpression PackingInventoryDescriptors

def rawPair (D : InventoryData) (edge : D.Edge) (rep : Nat) : RawInstance :=
  (List.finRange 2).flatMap fun side =>
    (jobDescriptors D).map
      (rawOfDescriptor D (some (D.graph.endpoint edge side)) edge.val rep)

end BinPackingGap.GraphPackingJobStream

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingStockStreams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingStockStreams

open PackingConstantPool PackingInventoryDescriptors PackingDescriptorExpression

theorem globalPoolStream_eq_replicate (D : InventoryData) (species : GlobalSpecies D.graph) :
    globalPoolStream D species =
      List.replicate (D.globalStock species)
        (rawOfDescriptor D none (globalEdgeIndex D species) 0 (globalDescriptor D species)) := by
  simp only [globalPoolStream, List.map_const', List.length_finRange]

theorem flagPoolStream_eq_replicate (D : InventoryData) (species : FlagSpecies) :
    flagPoolStream D species =
      List.replicate (D.flagStock species)
        (rawOfDescriptor D none 0 0 (flagDescriptor D species)) := by
  simp only [flagPoolStream, List.map_const', List.length_finRange]

end BinPackingGap.GraphPackingStockStreams

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchFinalizeMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchFinalizeMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open SearchSemantics SearchEncoding BinaryEncoding
open BinPackingGames.Reduction.MachineTransfer

def program : MachineCanonicalOutput.Program Tape Label Register where
  input := .input
  output := .output
  main := .start
  initial := ((), none)
  code := code

abbrev machine := MachineCanonicalOutput.sourceMachine program

def cfg (label : Option Label) (input binary scratch reversed output : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, ((), register), tapes input binary scratch reversed output⟩

theorem oneStepTrace {a b : machine.Cfg} (h : machine.step a = some b) :
    (advance machine.step)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

theorem transferNext (dst : Tape) : nextAt dst code = advance machine.step := by
  funext state
  rfl

theorem skipStep (again next current : Label) (h : code current = skipUnary again next)
    (bit : Bool) (a b c d e : List Bool) :
    machine.step (cfg (some current) (bit :: a) b c d e) =
      some (cfg (some (if bit then again else next)) a b c d e) := by
  change some (TM2.stepAux (code current) _ _) = _
  rw [h]
  cases bit <;> simp [skipUnary, go, TM2.stepAux, cfg]
  all_goals rfl

theorem digitStep (next current : Label) (h : code current = skipDigit next)
    (bit : Bool) (a b c d e : List Bool) :
    machine.step (cfg (some current) (bit :: a) b c d e) =
      some (cfg (some next) a b c d e) := by
  change some (TM2.stepAux (code current) _ _) = _
  rw [h]
  simp [skipDigit, go, TM2.stepAux, cfg]
  all_goals rfl

theorem skipUnaryTrace (current next : Label) (h : code current = skipUnary current next)
    (n : Nat) (a b c d e : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some current) (encodeWord n ++ a) b c d e)) =
      some (cfg (some next) a b c d e) := by
  induction n with
  | zero =>
      simpa only [encodeWord, List.replicate_zero, List.nil_append, List.singleton_append,
        Nat.zero_add, Function.iterate_one, advance_some, Bool.false_eq_true, ↓reduceIte]
        using skipStep current next current h false a b c d e
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp only [encodeWord, List.replicate_succ, List.cons_append, advance_some]
      rw [skipStep current next current h true]
      simpa only [encodeWord, Bool.true_eq, ↓reduceIte] using ih

theorem skipNameTrace (current digit next : Label)
    (hc : code current = skipUnary digit next) (hd : code digit = skipDigit current)
    (bits a b c d e : List Bool) :
    (advance machine.step)^[(BinPackingCompleteness.BinaryEncoding.frame bits).length]
      (some (cfg (some current) (BinPackingCompleteness.BinaryEncoding.frame bits ++ a) b c d e)) =
      some (cfg (some next) a b c d e) := by
  induction bits with
  | nil =>
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.length_singleton,
        List.singleton_append, Function.iterate_one, advance_some,
        Bool.false_eq_true, ↓reduceIte] using skipStep digit next current hc false a b c d e
  | cons bit bits ih =>
      have first := skipStep digit next current hc true
        (bit :: (BinPackingCompleteness.BinaryEncoding.frame bits ++ a)) b c d e
      have second := digitStep current digit hd bit
        (BinPackingCompleteness.BinaryEncoding.frame bits ++ a) b c d e
      simp only [↓reduceIte] at first
      have full := joinTrace (joinTrace
        (oneStepTrace first)
        (oneStepTrace second)) ih
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.length_cons,
        List.cons_append, Nat.add_comm, Nat.add_assoc] using full

theorem skipItemsTrace (r : RawInstance) (a b c d e : List Bool) :
    (advance machine.step)^[(rawInstanceBits r).length]
      (some (cfg (some .items) (rawInstanceBits r ++ a) b c d e)) =
      some (cfg (some .fixed) a b c d e) := by
  induction r with
  | nil =>
      simpa only [rawInstanceBits, listBits, List.length_singleton, List.singleton_append,
        Function.iterate_one, advance_some, Bool.false_eq_true, ↓reduceIte]
        using skipStep .numerator .fixed .items rfl false a b c d e
  | cons q r ih =>
      have first := skipStep .numerator .fixed .items rfl true
        (natBits q.1 ++ natBits q.2 ++ rawInstanceBits r ++ a) b c d e
      have second := skipNameTrace .numerator .numeratorDigit .denominator rfl rfl q.1.bits
        (natBits q.2 ++ rawInstanceBits r ++ a) b c d e
      have third := skipNameTrace .denominator .denominatorDigit .items rfl rfl q.2.bits
        (rawInstanceBits r ++ a) b c d e
      simp only [↓reduceIte] at first
      simp only [natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
        List.append_assoc] at first second third
      have full := joinTrace (joinTrace (joinTrace
        (oneStepTrace first) second) third) ih
      have clock : 1 + (BinPackingCompleteness.BinaryEncoding.frame q.1.bits).length +
          (BinPackingCompleteness.BinaryEncoding.frame q.2.bits).length +
          (rawInstanceBits r).length = (rawInstanceBits (q :: r)).length := by
        simp only [rawInstanceBits, listBits, pairBits, natBits,
          BinPackingCompleteness.BinaryEncoding.nameBits, List.length_cons, List.length_append]
        omega
      rw [clock] at full
      simpa only [rawInstanceBits, listBits, pairBits, natBits,
        BinPackingCompleteness.BinaryEncoding.nameBits, List.length_cons,
        List.length_append, List.cons_append, List.append_assoc, Nat.add_assoc] using full

theorem emitBinaryStep_nil (a c d e : List Bool) :
    machine.step (cfg (some .emitBinary) a [] c d e) =
      some (cfg (some .skipItem) a [] c (false :: d) e) := by
  change some (TM2.stepAux (code .emitBinary) _ _) = _
  simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem emitBinaryStep_cons (bit : Bool) (a b c d e : List Bool) :
    machine.step (cfg (some .emitBinary) a (bit :: b) c d e) =
      some (cfg (some .emitBinary) a b c (bit :: true :: d) e) := by
  change some (TM2.stepAux (code .emitBinary) _ _) = _
  simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem emitBinaryTrace (a bits c d e : List Bool) :
    (advance machine.step)^[bits.length + 1]
      (some (cfg (some .emitBinary) a bits c d e)) =
      some (cfg (some .skipItem) a [] c
        ((BinPackingCompleteness.BinaryEncoding.frame bits).reverse ++ d) e) := by
  induction bits generalizing d with
  | nil => simpa [advance, BinPackingCompleteness.BinaryEncoding.frame] using!
      emitBinaryStep_nil a c d e
  | cons bit bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some, emitBinaryStep_cons]
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.reverse_cons,
        List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] using ih (bit :: true :: d)

theorem fixedStep (bit : Bool) (a b c d e : List Bool) :
    machine.step (cfg (some .fixed) (bit :: a) b c d e) =
      some (cfg (some (if bit then .option else .reverse)) a b c (bit :: d) e) := by
  change some (TM2.stepAux (code .fixed) _ _) = _
  cases bit <;> simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem optionStep (bit : Bool) (a b c d e : List Bool) :
    machine.step (cfg (some .option) (bit :: a) b c d e) =
      some (cfg (some (if bit then .name else .fixed)) a b c
        (if bit then d else false :: d) e) := by
  change some (TM2.stepAux (code .option) _ _) = _
  cases bit <;> simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem nameStep (bit : Bool) (a b c d e : List Bool) :
    machine.step (cfg (some .name) (bit :: a) b c d e) =
      some (cfg (some (if bit then .nameDigit else .fixed)) a b c (bit :: d) e) := by
  change some (TM2.stepAux (code .name) _ _) = _
  cases bit <;> simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem nameDigitStep (bit : Bool) (a b c d e : List Bool) :
    machine.step (cfg (some .nameDigit) (bit :: a) b c d e) =
      some (cfg (some .name) a b c (bit :: d) e) := by
  change some (TM2.stepAux (code .nameDigit) _ _) = _
  simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem nameTrace (bits a b c d e : List Bool) :
    (advance machine.step)^[(BinPackingCompleteness.BinaryEncoding.frame bits).length]
      (some (cfg (some .name) (BinPackingCompleteness.BinaryEncoding.frame bits ++ a) b c d e)) =
      some (cfg (some .fixed) a b c
        ((BinPackingCompleteness.BinaryEncoding.frame bits).reverse ++ d) e) := by
  induction bits generalizing d with
  | nil =>
      simpa [BinPackingCompleteness.BinaryEncoding.frame, advance] using! nameStep false a b c d e
  | cons bit bits ih =>
      have first := nameStep true (bit :: (BinPackingCompleteness.BinaryEncoding.frame bits ++ a))
        b c d e
      have second := nameDigitStep bit (BinPackingCompleteness.BinaryEncoding.frame bits ++ a)
        b c (true :: d) e
      simp only [↓reduceIte] at first
      have full := joinTrace (joinTrace
        (oneStepTrace first)
        (oneStepTrace second)) (ih (bit :: true :: d))
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.length_cons,
        List.cons_append, List.reverse_cons, List.append_assoc, List.singleton_append,
        List.nil_append, Nat.add_comm, Nat.add_assoc] using full

theorem fixedTrace (fixed : List (Option Nat)) (a b c d e : List Bool) :
    (advance machine.step)^[(fixedBits fixed).length]
      (some (cfg (some .fixed) (fixedBits fixed ++ a) b c d e)) =
      some (cfg (some .reverse) a b c ((assignmentBits (labels fixed)).reverse ++ d) e) := by
  induction fixed generalizing d with
  | nil =>
      simpa [fixedBits, listBits, labels, assignmentBits, advance] using!
        fixedStep false a b c d e
  | cons value fixed ih =>
      cases value with
      | none =>
          have first := fixedStep true (false :: (fixedBits fixed ++ a)) b c d e
          have second := optionStep false (fixedBits fixed ++ a) b c (true :: d) e
          simp only [Bool.false_eq_true, ↓reduceIte] at first second
          have full := joinTrace (joinTrace
            (oneStepTrace first)
            (oneStepTrace second)) (ih (false :: true :: d))
          have clock : 1 + 1 + (fixedBits fixed).length =
              (fixedBits (none :: fixed)).length := by
            simp only [fixedBits, listBits, optionBits, List.length_cons,
              List.length_append, List.length_nil]
            omega
          rw [clock] at full
          simpa only [fixedBits, listBits, optionBits, labels, List.map_cons,
            Option.getD_none, assignmentBits, natBits,
            BinPackingCompleteness.BinaryEncoding.nameBits, Nat.zero_bits,
            BinPackingCompleteness.BinaryEncoding.frame, List.reverse_cons,
            List.reverse_append, List.reverse_nil, List.cons_append,
            List.nil_append, List.append_nil, List.append_assoc] using full
      | some n =>
          have first := fixedStep true (true :: (natBits n ++ fixedBits fixed ++ a)) b c d e
          have second := optionStep true (natBits n ++ fixedBits fixed ++ a) b c (true :: d) e
          have third := nameTrace n.bits (fixedBits fixed ++ a) b c (true :: d) e
          simp only [↓reduceIte] at first second
          simp only [natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
            List.append_assoc] at first second third
          have full := joinTrace (joinTrace (joinTrace
            (oneStepTrace first)
            (oneStepTrace second)) third)
              (ih ((natBits n).reverse ++ true :: d))
          have clock : 1 + 1 + (BinPackingCompleteness.BinaryEncoding.frame n.bits).length +
              (fixedBits fixed).length = (fixedBits (some n :: fixed)).length := by
            simp only [fixedBits, listBits, optionBits, natBits,
              BinPackingCompleteness.BinaryEncoding.nameBits, List.length_cons, List.length_append]
            omega
          rw [clock] at full
          simpa only [fixedBits, listBits, optionBits, labels, List.map_cons,
            Option.getD_some, assignmentBits, natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
            List.length_cons, List.length_append, List.cons_append, List.reverse_cons,
            List.reverse_append, List.append_assoc, List.singleton_append,
            List.nil_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem convertTrace (n : Nat) (a d e : List Bool) :
    (advance machine.step)^[UnaryToBinaryMachine.steps n 0]
      (some (cfg (some (.convert .scan)) (encodeWord n ++ a) [] [] d e)) =
      some (cfg (some .emitBinary) a n.bits [] d e) := by
  have h := UnaryToBinaryMachine.convertTrace
    (K := Tape) (A := Unit) .input .binary .scratch (by decide) (by decide) (by decide)
    Label.convert (some .emitBinary) code (fun _ => rfl)
    (tapes [] [] [] d e) () n 0 a
  have step_eq : TM2.step code = machine.step := rfl
  rw [step_eq] at h
  simpa [UnaryToBinaryMachine.tapes, cfg] using! h

theorem reverseTrace (a b c d e : List Bool) :
    (advance machine.step)^[d.length + 1]
      (some (cfg (some .reverse) a b c d e)) =
      some (cfg none a b c [] (d.reverse ++ e)) := by
  have h := transferAt_fromTapes (Γ := fun _ : Tape => Bool) .reversed .output
    (by decide) id false .reverse none code rfl (tapes a b c d e) () none
  simpa only [transferNext, cfg, tapes_reversed, tapes_output, tapesAt,
    update_reversed, update_output, List.map_id_fun, id_eq] using! h

theorem startDone (a : List Bool) :
    machine.step (cfg (some .start) (true :: false :: a) [] [] [] []) =
      some (cfg (some (.convert .scan)) a [] [] [true] []) := by
  change some (TM2.stepAux (code .start) _ _) = _
  simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem startFalse (a : List Bool) :
    machine.step (cfg (some .start) (false :: a) [] [] [] []) =
      some (cfg none a [] [] [] [false]) := by
  change some (TM2.stepAux (code .start) _ _) = _
  simp [code, reject, TM2.stepAux, cfg]
  all_goals rfl

theorem startInvalid (a : List Bool) :
    machine.step (cfg (some .start) (true :: true :: a) [] [] [] []) =
      some (cfg none a [] [] [] [false]) := by
  change some (TM2.stepAux (code .start) _ _) = _
  simp [code, reject, TM2.stepAux, cfg]
  all_goals rfl

def bodyBits (s : State) : List Bool :=
  encodeWord s.bins ++ encodeWord s.item ++ encodeWord s.label ++
    rawInstanceBits s.items ++ fixedBits s.fixed

def resultBits (bins : Nat) (fixed : List (Option Nat)) : List Bool :=
  packingResultBits (some ⟨bins, labels fixed⟩)

def doneSteps (s : State) : Nat :=
  1 + UnaryToBinaryMachine.steps s.bins 0 + (s.bins.bits.length + 1) +
    (s.item + 1) + (s.label + 1) + (rawInstanceBits s.items).length +
    (fixedBits s.fixed).length + ((resultBits s.bins s.fixed).length + 1)

theorem doneTrace (s : State) :
    (advance machine.step)^[doneSteps s]
      (some (cfg (some .start) (true :: false :: bodyBits s) [] [] [] [])) =
      some (cfg none [] [] [] [] (resultBits s.bins s.fixed)) := by
  let rest := encodeWord s.item ++ (encodeWord s.label ++
    (rawInstanceBits s.items ++ fixedBits s.fixed))
  let reverseHeader := (natBits s.bins).reverse ++ [true]
  have first := startDone (bodyBits s)
  have second := convertTrace s.bins rest [true] []
  have third := emitBinaryTrace rest s.bins.bits [] [true] []
  have fourth := skipUnaryTrace .skipItem .skipLabel rfl s.item
    (encodeWord s.label ++ (rawInstanceBits s.items ++ fixedBits s.fixed))
    [] [] reverseHeader []
  have fifth := skipUnaryTrace .skipLabel .items rfl s.label
    (rawInstanceBits s.items ++ fixedBits s.fixed) [] [] reverseHeader []
  have sixth := skipItemsTrace s.items (fixedBits s.fixed) [] [] reverseHeader []
  have seventh := fixedTrace s.fixed [] [] [] reverseHeader []
  simp only [List.append_nil] at seventh
  have finalWord :
      ((assignmentBits (labels s.fixed)).reverse ++ reverseHeader).reverse =
        resultBits s.bins s.fixed := by
    simp only [reverseHeader, resultBits, packingResultBits, optionBits, rawPackingBits,
      List.reverse_append, List.reverse_reverse, List.reverse_singleton,
      List.cons_append, List.nil_append]
  have finalLength :
      ((assignmentBits (labels s.fixed)).reverse ++ reverseHeader).length =
        (resultBits s.bins s.fixed).length := by
    simpa only [List.length_reverse] using congrArg List.length finalWord
  have eighth := reverseTrace [] [] []
    ((assignmentBits (labels s.fixed)).reverse ++ reverseHeader) []
  rw [finalLength, finalWord] at eighth
  simp only [List.append_nil] at eighth
  have headerEq :
      (BinPackingCompleteness.BinaryEncoding.frame s.bins.bits).reverse ++ [true] = reverseHeader := rfl
  rw [headerEq] at third
  have firstSecond := joinTrace
    (oneStepTrace first)
    (show (advance machine.step)^[UnaryToBinaryMachine.steps s.bins 0]
      (some (cfg (some (.convert .scan)) (bodyBits s) [] [] [true] [])) = _ from by
        simpa only [bodyBits, rest, List.append_assoc] using second)
  have full := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace firstSecond third) fourth) fifth) sixth) seventh) eighth
  simpa only [doneSteps] using full

theorem labelsBits_le (fixed : List (Option Nat)) :
    (assignmentBits (labels fixed)).length ≤ (fixedBits fixed).length := by
  induction fixed with
  | nil => simp [assignmentBits, labels, fixedBits, listBits]
  | cons value fixed ih =>
      cases value <;>
        simp only [assignmentBits, labels, List.map_cons, fixedBits, listBits,
          optionBits, Option.getD_none, Option.getD_some, List.length_cons,
          List.length_append] at ih ⊢
      · simpa using ih
      · omega

theorem resultBits_length_le (bins : Nat) (fixed : List (Option Nat)) :
    (resultBits bins fixed).length ≤ 2 * bins + (fixedBits fixed).length + 2 := by
  have hf := labelsBits_le fixed
  have hn : bins.size ≤ bins := Nat.size_le.mpr bins.lt_two_pow_self
  simp only [resultBits, packingResultBits, optionBits, rawPackingBits,
    List.length_cons, List.length_append, natBits_length]
  omega

theorem doneSteps_le (s : State) : doneSteps s ≤ rawTime.eval (stateBits s).length := by
  have ht := UnaryToBinaryMachine.steps_le s.bins 0
  have hr := resultBits_length_le s.bins s.fixed
  have hn : s.bins.bits.length ≤ s.bins := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr s.bins.lt_two_pow_self
  have hlen := stateBits_length s
  have hbins : s.bins ≤ (stateBits s).length := by omega
  have hsq : s.bins * s.bins ≤ (stateBits s).length * (stateBits s).length :=
    Nat.mul_le_mul hbins hbins
  simp only [doneSteps, rawTime, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  simp only [Nat.zero_add] at ht
  nlinarith

theorem init_eq (input : List Bool) :
    initList machine input = cfg (some .start) input [] [] [] [] := by
  unfold initList cfg
  congr 1
  funext k
  cases k <;> rfl

def rejectedRun (s : State) (rest : List Bool)
    (h : machine.step (cfg (some .start) (stateBits s) [] [] [] []) =
      some (cfg none rest [] [] [] [false]))
    (hout : packingResultBits (SearchSemantics.output s) = [false]) :
    MachineCanonicalOutput.TerminalRun program (stateBits s)
      (packingResultBits (SearchSemantics.output s)) (rawTime.eval (stateBits s).length) where
  state := ((), none)
  tapes := tapes rest [] [] [] [false]
  execution := {
    steps := 1
    evals_in_steps := by
      change machine.step (initList machine (stateBits s)) = _
      rw [init_eq]
      exact h
    steps_le_m := by
      simp only [rawTime, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      have positive : 1 ≤ (stateBits s).length + 1 := by omega
      have square := Nat.mul_le_mul positive positive
      nlinarith only [square] }
  output_eq := hout.symm

theorem cleanup_complete (k : Tape) : k ∈ cleanupTapes ↔ k ≠ program.output := by
  cases k <;> simp [cleanupTapes, program]

end BinPackingGap.SearchFinalizeMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchUpdateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchUpdateMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open SearchSemantics SearchEncoding BinaryEncoding

def ambient (phase : Phase) (flag : Bool := false) : Ambient :=
  match phase with
  | .find => ⟨false, false, flag⟩
  | .fill => ⟨false, true, flag⟩
  | .done => ⟨true, false, flag⟩
  | .invalid => ⟨true, true, flag⟩

@[simp] theorem phaseWord_ambient (phase : Phase) (flag : Bool) :
    phaseWord (ambient phase flag) = phaseBits phase := by cases phase <;> rfl

def bodyBits (s : State) : List Bool :=
  encodeWord s.bins ++ encodeWord s.item ++ encodeWord s.label ++
    rawInstanceBits s.items ++ fixedBits s.fixed

@[simp] theorem stateBits_eq (s : State) : stateBits s = phaseBits s.phase ++ bodyBits s := by
  simp [stateBits, bodyBits, List.append_assoc]

@[simp] theorem bodyBits_length (s : State) :
    (bodyBits s).length = 3 + s.bins + s.item + s.label +
      (rawInstanceBits s.items).length + (fixedBits s.fixed).length := by
  simp only [bodyBits, List.length_append, encodeWord_length]
  omega

end BinPackingGap.SearchUpdateMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchStageMachines
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchInitialEmitMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinPackingGames.Reduction.MachineSubstitution

def fixedWord (n : Nat) : List Bool := SearchEncoding.fixedBits (List.replicate n none)

@[simp] theorem fixedWord_zero : fixedWord 0 = [false] := rfl

@[simp] theorem fixedWord_succ (n : Nat) :
    fixedWord (n + 1) = true :: false :: fixedWord n := rfl

def selectedFixed (valid : Bool) (n : Nat) : List Bool :=
  if valid then fixedWord n else fixedWord 0

def bodyWord (valid : Bool) (n : Nat) (input : List Bool) : List Bool :=
  header (initialFlags valid n) ++ (input ++ selectedFixed valid n)

def outputWord (valid : Bool) (n : Nat) (input : List Bool) : List Bool :=
  encodeWord (fuelValue valid n) ++ bodyWord valid n input

def finishTapes (valid : Bool) (n : Nat) (input : List Bool) : Tape → List Bool :=
  tapes [] (outputWord valid n input) (encodeWord n) (encodeWord (n + 1))
    [] (residualFixed valid n) []

end BinPackingGap.SearchInitialEmitMachine

end OAI
end


