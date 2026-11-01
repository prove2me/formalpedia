-- Prove2me | Definitions.Def_OAIQ053K070
-- name    : OAIQ053K070
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:21:10.539833+00:00
-- url     : https://prove2.me/theorems/5d67dee6-db9b-4457-a51b-8e9a12df8c8d
-- title:
--   Definitions bundle OAIQ053K070 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 104 declarations of OpenAI's Lean: 50 definitions, 1 inductive type or structure and 53 theorems. The definitions and types are `OAI.MetricKMedian.Complexity.firstProjectionProgram`, `OAI.MetricKMedian.Complexity.firstWordProgram`, `OAI.MetricKMedian.Coverage.HasSeparator`, `OAI.MetricKMedian.Coverage.Input.inputRawProgram`, `OAI.MetricKMedian.Coverage.Input.rawContextProgram`, `OAI.MetricKMedian.Coverage.Input.verdictProgram`, `OAI.MetricKMedian.Coverage.ProjectionGapNPReductions`, `OAI.MetricKMedian.Coverage.ProjectionInput.coverageProgram`, `OAI.MetricKMedian.Coverage.ProjectionInput.encode`, `OAI.MetricKMedian.Coverage.ProjectionInput.raw`, `OAI.MetricKMedian.Coverage.ProjectionRaw.blocks`, `OAI.MetricKMedian.Coverage.ProjectionRaw.bytes`, `OAI.MetricKMedian.Coverage.ProjectionRaw.program`, `OAI.MetricKMedian.Coverage.ProjectionRaw.table`, `OAI.MetricKMedian.Coverage.ProjectionReduction`, `OAI.MetricKMedian.Coverage.Raw.accepts`, `OAI.MetricKMedian.Coverage.Raw.coveredCount`, `OAI.MetricKMedian.Coverage.Raw.isCovered`, `OAI.MetricKMedian.FixedBatch.RationalParameters.GridDataProgram.Input`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.Input.candidates`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.Input.encode`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.Input.encode`, `OAI.MetricKMedian.Reduction.Enumeration.arcpairs`, `OAI.MetricKMedian.Reduction.Enumeration.branchesData`, `OAI.MetricKMedian.Reduction.Enumeration.choicesRaw`, `OAI.MetricKMedian.Reduction.Enumeration.restrictData`, `OAI.MetricKMedian.Reduction.Program.Branch.restrictedData`, `OAI.MetricKMedian.Reduction.Program.LocalRaw`, `OAI.MetricKMedian.Reduction.Program.annotateData`, `OAI.MetricKMedian.Reduction.Program.candidatesData`, `OAI.MetricKMedian.Reduction.Program.completionData`, `OAI.MetricKMedian.Reduction.Program.completionsData`, `OAI.MetricKMedian.Reduction.Program.costData`, `OAI.MetricKMedian.Reduction.Program.deleteData`, `OAI.MetricKMedian.Reduction.Program.diff`, `OAI.MetricKMedian.Reduction.Program.eligibleData`, `OAI.MetricKMedian.Reduction.Program.endpointsData`, `OAI.MetricKMedian.Reduction.Program.feasibleData`, `OAI.MetricKMedian.Reduction.Program.getDist`, `OAI.MetricKMedian.Reduction.Program.historyData` and 11 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Hardness_Classes`, `KMedian_Hardness_ProjectionEncoding`, `KMedian_Hardness_ProjectionReduction`, `KMedian_Hardness_Reduction`, `KMedian_Hardness_Verdict`, `KMedian_Preparation_PreparedScanProgram`, `KMedian_Process_RoundCountsProgram`, `KMedian_Programs_BoundedEnumerationProgram`, `KMedian_Programs_BranchProgram`, `KMedian_Programs_FinalSelectionProgram`, `KMedian_Programs_RestrictionProgram`, `KMedian_Reduction_DeletionProgram`, `KMedian_Reduction_LocalCompletionProgram`, `KMedian_Reduction_ReductionCostProgram`, `KMedian_Reduction_ReductionOutcomesProgram`, `KMedian_Rounding_GridDataProgram`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundle `OAIQ053K063` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K075`, `OAIQ053K076`, `OAIQ053K077`, `OAIQ053K078` and `OAIQ053K079`; the statements `OAI.MetricKMedian.Coverage.projection_gap_np_reductions_s53` and `OAI.MetricKMedian.Coverage.reduction_from_projections_s53`; the proofs of `OAI.MetricKMedian.Coverage.reduction_from_projections_s53` and `OAI.MetricKMedian.below_threshold_impossible_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K063

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_GridDataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.FixedBatch.RationalParameters.GridDataProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open RationalPhysicalKernel CopyList CopyNearestProgram
variable {τ : ℝ} (q : RationalParameters τ)

local instance instLinearOrderCopyFin_r103194_1 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
structure Input where
  f : ℕ
  j : ℕ
  d₀ : Fin f → Fin f → ℚ
  d : Fin j → Fin f → ℚ
  A : Finset (CopyState.Copy (F:=Fin f) q.Δ)
  enough : q.Δ≤A.card
end MetricKMedian.FixedBatch.RationalParameters.GridDataProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundCountsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open RationalPhysicalKernel CopyList
variable {τ : ℝ} (q : RationalParameters τ)
abbrev Input.encode (x : Input) := enc x.raw

end MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedScanProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
variable {τ : ℝ} (q : RationalParameters τ)
abbrev Input.encode (x : Input) := enc x.raw

def Input.candidates (x : Input) := q.countCandidates x.df x.dc x.orig x.ns

end MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BoundedEnumerationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Reduction.Enumeration
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)

def choicesRaw (c : ℕ) (T : Row) : Table :=
  (words c (Preparation.RationalUnitInput.Program.ranks T)).map (fun ys => maskWord (T,ys))
@[fun_prop] theorem choicesRaw_poly (c : ℕ) : Poly (choicesRaw c) := by unfold choicesRaw; apply list_map <;> fun_prop
end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_RestrictionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Reduction.Enumeration
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw )
open MetricKMedian.MaskProgram

def arcpairs (T : Row) : List (ℕ × ℕ) :=
  (Preparation.RationalUnitInput.Program.ranks T).flatMap (fun i =>
    (Preparation.RationalUnitInput.Program.ranks T).map (fun j => (i,j)))
@[fun_prop] theorem arcpairs_poly : Poly arcpairs := by unfold arcpairs; apply list_flatMap; apply list_map <;> fun_prop; fun_prop

def restrictData (x : Raw × (Row × List (ℕ × ℕ))) : Row :=
  (indices x.2.1).map (fun i => get x.2.1 i &&
    (x.2.2.map (fun p => decide ((x.1.2.2[p.1]?.getD [])[p.2]?.getD 0 ≤
      (x.1.2.2[p.1]?.getD [])[i]?.getD 0))).all id)
@[fun_prop] theorem restrictData_poly : Poly restrictData := by
  unfold restrictData
  have h : Poly (fun x : (Raw × (Row × List (ℕ × ℕ))) × ℕ =>
    (x.1.2.2.map (fun p => decide ((x.1.1.2.2[p.1]?.getD [])[p.2]?.getD 0 ≤
      (x.1.1.2.2[p.1]?.getD [])[x.2]?.getD 0))).all id) := by apply comp bool_all; apply list_map <;> fun_prop
  apply list_map <;> fun_prop

def branchesData (a : ℕ) (x : Raw × Row) : Table :=
  (words a (arcpairs x.2)).map (fun ps => restrictData (x.1,(x.2,ps)))
@[fun_prop] theorem branchesData_poly (a : ℕ) : Poly (branchesData a) := by unfold branchesData; apply list_map <;> fun_prop
end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_ReductionCostProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw )
open MaskProgram

def nearestData (x : List ℚ × Row) : ℚ := LPBinary.minimum (selectedValues x)
@[fun_prop] theorem nearestData_poly : Poly nearestData := by
  have h : Poly LPBinary.minimum := ⟨LPBinary.Program.minimumProgram⟩
  unfold nearestData; fun_prop

def costData (x : Raw × Row) : ℚ :=
  ((indices x.1.1.1).map (fun j => if get x.1.1.1 j then nearestData (x.1.2.2[j]?.getD [],x.2) else 0)).sum
@[fun_prop] theorem costData_poly : Poly costData := by
  unfold costData
  apply comp rat_sum
  apply list_map <;> fun_prop

def diff (x : Row × Row) : Row := (x.1.zip x.2).map (fun z => z.1 && !z.2)
def union (x : Row × Row) : Row := (x.1.zip x.2).map (fun z => z.1 || z.2)
@[fun_prop] theorem diff_poly : Poly diff := by unfold diff; apply list_map <;> fun_prop
@[fun_prop] theorem union_poly : Poly union := by unfold union; apply list_map <;> fun_prop
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_DeletionProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw )
open MetricKMedian.MaskProgram
open Preparation.RationalNearest.MaskProgram (erase )
open Completion.Rational.BestProgram (card card_view)
open Enumeration

def eligibleData (x : (Raw × ℚ) × Row) : Row :=
  (indices x.2).map (fun i => get x.2 i && decide (costData (x.1.1,erase (i,x.2))-costData (x.1.1,x.2)≤x.1.2))
@[fun_prop] theorem eligibleData_poly : Poly eligibleData := by unfold eligibleData; apply list_map <;> fun_prop
def deleteData (x : (Raw × ℚ) × Row) : Row :=
  if x.1.1.2.1 < card x.2 then
    let E := eligibleData x
    if E.any id then erase (InstanceProgram.first E,x.2) else x.2
  else x.2
@[fun_prop] theorem deleteData_poly : Poly deleteData := by unfold deleteData; fun_prop

def historyData : ℕ → (Raw × ℚ) × Row → Row
  | 0,x => x.2
  | c+1,x => deleteData (x.1,historyData c x)
@[fun_prop] theorem historyData_poly (c : ℕ) : Poly (historyData c) := by
  induction c with
  | zero => exact snd
  | succ c ih => change Poly (fun x => deleteData (x.1,historyData c x)); fun_prop
def valuesData (c : ℕ) (x : Raw × Row) : List ℚ :=
  (choicesRaw c x.2).flatMap (fun D => (Preparation.RationalUnitInput.Program.ranks x.2).map (fun i =>
    costData (x.1,erase (i,diff (x.2,D)))-costData (x.1,diff (x.2,D))))
@[fun_prop] theorem valuesData_poly (c : ℕ) : Poly (valuesData c) := by unfold valuesData; apply list_flatMap; apply list_map <;> fun_prop; fun_prop
def endpointsData (c : ℕ) (x : Raw × Row) : Table :=
  (0::valuesData c x).map (fun B => historyData c ((x.1,B),x.2))
@[fun_prop] theorem endpointsData_poly (c : ℕ) : Poly (endpointsData c) := by
  unfold endpointsData
  apply list_map
  · fun_prop
  · have h := comp (list_cons (α := ℚ)) (pair (const 0 : Poly (fun _ : Raw × Row => (0:ℚ))) (valuesData_poly c))
    exact h
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_LocalCompletionProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw )
open MetricKMedian.MaskProgram
open Preparation.RationalNearest.MaskProgram (erase insert )
open Enumeration

def getDist (x : Raw × (ℕ × ℕ)) : ℚ := (x.1.2.2[x.2.1]?.getD [])[x.2.2]?.getD 0
@[fun_prop] theorem getDist_poly : Poly getDist := by unfold getDist; fun_prop

def radiiData (x : Raw × Row) : List ℚ := (indices x.2).map (fun t => nearestData (x.1.2.2[t]?.getD [],erase (t,x.2)))
@[fun_prop] theorem radiiData_poly : Poly radiiData := by unfold radiiData; apply list_map <;> fun_prop

abbrev LocalRaw := (Raw × (Row × Row)) × (List ℚ × ℚ)
def candidatesData (x : LocalRaw × ℕ) : Row :=
  (indices x.1.1.2.1).map (fun a => get x.1.1.2.1 a &&
    decide (getDist (x.1.1.1,(x.2,a))≤x.1.2.2*(x.1.2.1[x.2]?.getD 0)))
@[fun_prop] theorem candidatesData_poly : Poly candidatesData := by unfold candidatesData; apply list_map <;> fun_prop

def weightData (x : LocalRaw × (ℕ × ℕ)) : ℚ :=
  ((indices x.1.1.1.1.1).map (fun j => if get x.1.1.1.1.1 j &&
    decide (3*getDist (x.1.1.1,(j,x.2.1))≤x.1.2.1[x.2.1]?.getD 0) then
      nearestData (x.1.1.1.2.2[j]?.getD [],insert (x.2.2,x.1.1.2.2)) else 0)).sum
@[fun_prop] theorem weightData_poly : Poly weightData := by unfold weightData; apply comp rat_sum; apply list_map <;> fun_prop

def pickData (x : List ℚ × Row) : Row :=
  if x.2.any id then InstanceProgram.singletonRaw (x.2,MetricKMedian.MaskProgram.nearest x) else x.2.map (fun _ => false)
@[fun_prop] theorem pickData_poly : Poly pickData := by unfold pickData; fun_prop

def localData (x : LocalRaw × ℕ) : Row :=
  pickData ((indices x.1.1.2.1).map (fun a => weightData (x.1,(x.2,a))),candidatesData x)
@[fun_prop] theorem localData_poly : Poly localData := by unfold localData; apply comp pickData_poly; apply pair; apply list_map <;> fun_prop; fun_prop

def unionData (x : Row × Table) : Row := (indices x.1).map (fun i => (x.2.map (fun S => get S i)).any id)
@[fun_prop] theorem unionData_poly : Poly unionData := by unfold unionData; apply list_map; apply comp bool_any; apply list_map <;> fun_prop; fun_prop

def completionData (x : LocalRaw × Row) : Row := union (x.1.1.2.2,unionData (x.2,
  (Preparation.RationalUnitInput.Program.ranks x.2).map (fun t => localData (x.1,t))))
@[fun_prop] theorem completionData_poly : Poly completionData := by
  unfold completionData
  have hm : Poly (fun x : LocalRaw × Row => (Preparation.RationalUnitInput.Program.ranks x.2).map (fun t => localData (x.1,t))) := by apply list_map <;> fun_prop
  fun_prop
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_ReductionOutcomesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw )
open Enumeration
def completionsData (δ : ℚ) (b : ℕ) (x : Raw × (Row × Row)) : Table :=
  (choicesRaw b x.2.2).flatMap (fun H => (choicesRaw b x.2.1).map (fun B =>
    completionData (((x.1,(x.2.1,B)),(radiiData (x.1,x.2.2),δ)),diff (x.2.2,H))))
@[fun_prop] theorem completionsData_poly (δ : ℚ) (b : ℕ) : Poly (completionsData δ b) := by
  unfold completionsData; apply list_flatMap; apply list_map <;> fun_prop; fun_prop
def outcomesData (δ : ℚ) (c b : ℕ) (x : Raw × (Row × Row)) : Table :=
  x.2.2::(endpointsData c (x.1,x.2.2)).flatMap (fun U => U::completionsData δ b (x.1,(x.2.1,U)))
@[fun_prop] theorem outcomesData_poly (δ : ℚ) (c b : ℕ) : Poly (outcomesData δ c b) := by
  unfold outcomesData
  have h : Poly (fun x : (Raw × (Row × Row)) × Row => x.2::completionsData δ b (x.1.1,(x.1.2.1,x.2))) := by
    have hh := comp (list_cons (α := Row)) (pair (snd : Poly (fun x : (Raw × (Row × Row)) × Row =>x.2))
      (show Poly (fun x : (Raw × (Row × Row)) × Row => completionsData δ b (x.1.1,(x.1.2.1,x.2))) from by fun_prop))
    exact hh
  have hh : Poly (fun x : Raw × (Row × Row) => (endpointsData c (x.1,x.2.2)).flatMap (fun U => U::completionsData δ b (x.1,(x.2.1,U)))) := by
    apply list_flatMap <;> fun_prop
  have hhh := comp (list_cons (α := Row)) (pair (show Poly (fun x : Raw × (Row × Row) => x.2.2) from by fun_prop) hh)
  exact hhh
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw )
open Completion.Rational.BestProgram (card card_view)
open Enumeration
namespace Branch
def restrictedData (x : Raw × Row) : Raw := ((x.1.1.1,x.2),x.1.2)
@[fun_prop] theorem restrictedData_poly : Poly restrictedData := by unfold restrictedData; fun_prop
end Branch
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_FinalSelectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw )
open Completion.Rational.BestProgram (card card_view)
def feasibleData (x : Raw × Row) : Bool := InstanceProgram.subsetRaw (x.2,x.1.1.2) && x.2.any id && decide (card x.2≤x.1.2.1)
@[fun_prop] theorem feasibleData_poly : Poly feasibleData := by unfold feasibleData; fun_prop
def annotateData (x : Raw × Table) : List SparseSelect.TaggedProgram.Tag :=
  x.2.map (fun S => (feasibleData (x.1,S),(costData (x.1,S),S)))
@[fun_prop] theorem annotateData_poly : Poly annotateData := by unfold annotateData; apply list_map <;> fun_prop
def selectRaw (x : Raw × Table) : Table := SparseSelect.TaggedProgram.raw (annotateData x)
@[fun_prop] theorem selectRaw_poly : Poly selectRaw := by unfold selectRaw; fun_prop
def selectData (x : Raw × Table) : Row := InstanceProgram.fallbackData (x.1,selectRaw x)
@[fun_prop] theorem selectData_poly : Poly selectData := by unfold selectData; fun_prop
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Classes
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Complexity
open Binary.Automatic Binary.Automatic.Poly

@[fun_prop] theorem firstWord_poly : Poly firstWord := by
  unfold firstWord
  exact Poly.comp InputParser.take_poly
    (pair (Poly.comp snd InputParser.natRead_poly) (Poly.comp fst InputParser.natRead_poly))

 theorem firstWord_encodePair (x : Word × Word) : firstWord (encodePair x) = x.1 := by
  simp only [firstWord, encodePair, List.append_assoc, InputParser.natRead_append]
  simp

noncomputable def firstWordProgram : Binary.PolyProgram id id firstWord :=
  (Binary.BooleanLists.packProgram.comp firstWord_poly.program).comp
    Binary.BooleanLists.unpackProgram

noncomputable def firstProjectionProgram : Binary.PolyProgram encodePair id Prod.fst :=
  firstWordProgram.recode encodePair (fun _ => rfl) firstWord_encodePair

end MetricKMedian.Complexity

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_ProjectionEncoding
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Binary Binary.Automatic Binary.Automatic.Poly

namespace ProjectionRaw

@[fun_prop] theorem edge_poly : Poly (fun x : ProjectionRaw × ℕ × ℕ => x.1.edge x.2.1 x.2.2) := by
  unfold edge; fun_prop
@[fun_prop] theorem test_poly : Poly (fun x : ProjectionRaw × ℕ × BlockCode × ℕ × ℕ × ℕ =>
    x.1.test x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) := by
  unfold test; fun_prop
@[fun_prop] theorem incident_poly (D : ℕ) : Poly (fun x : ProjectionRaw × ℕ × BlockCode × ℕ × ℕ =>
    incident D x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  unfold incident
  have ht : Poly (fun x : (ProjectionRaw × ℕ × BlockCode × ℕ × ℕ) × ℕ =>
      x.1.1.test x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.1.2.2.2.2 x.2) :=
    Poly.comp (g := fun x : (ProjectionRaw × ℕ × BlockCode × ℕ × ℕ) × ℕ =>
      (x.1.1,x.1.2.1,x.1.2.2.1,x.1.2.2.2.1,x.1.2.2.2.2,x.2)) test_poly (by fun_prop)
  fun_prop

noncomputable def blocks (r b D : ℕ) : List BlockCode :=
  List.ofFn (fun x : Fin (ProjectionInput.width r b D) =>
    let sw := (ProjectionInput.blockEquiv r b D).symm x
    (List.ofFn (fun j => (sw.1 j).val),List.ofFn (fun c => (sw.2 c).val)))

def table (a D : ℕ) (cs : List BlockCode) (R : ProjectionRaw) : List Bool :=
  R.rights.flatMap (fun v => cs.flatMap (fun sw =>
    R.lefts.flatMap (fun u => (List.range a).map (fun c => incident D R v sw u c))))

@[fun_prop] theorem table_poly (a D : ℕ) (cs : List BlockCode) : Poly (table a D cs) := by
  have hentry : Poly (fun x : ((ProjectionRaw × ℕ × BlockCode) × ℕ) × ℕ =>
      incident D x.1.1.1 x.1.1.2.1 x.1.1.2.2 x.1.2 x.2) :=
    Poly.comp (g := fun x : ((ProjectionRaw × ℕ × BlockCode) × ℕ) × ℕ =>
      (x.1.1.1,x.1.1.2.1,x.1.1.2.2,x.1.2,x.2)) (incident_poly D) (by fun_prop)
  have hlabel : Poly (fun x : (ProjectionRaw × ℕ × BlockCode) × ℕ =>
      (List.range a).map (fun c => incident D x.1.1 x.1.2.1 x.1.2.2 x.2 c)) :=
    Poly.list_map hentry (by fun_prop)
  have hu : Poly (fun x : ProjectionRaw × ℕ × BlockCode =>
      x.1.lefts.flatMap (fun u => (List.range a).map (fun c => incident D x.1 x.2.1 x.2.2 u c))) :=
    Poly.list_flatMap hlabel (Poly.comp lefts_poly Poly.fst)
  have hsw : Poly (fun x : (ProjectionRaw × ℕ) × BlockCode =>
      x.1.1.lefts.flatMap (fun u => (List.range a).map (fun c =>
        incident D x.1.1 x.1.2 x.2 u c))) :=
    Poly.comp (g := fun x : (ProjectionRaw × ℕ) × BlockCode =>
      (x.1.1,x.1.2,x.2)) hu (by fun_prop)
  have hv : Poly (fun x : ProjectionRaw × ℕ => cs.flatMap (fun sw =>
      x.1.lefts.flatMap (fun u => (List.range a).map (fun c => incident D x.1 x.2 sw u c)))) :=
    Poly.list_flatMap hsw (by fun_prop)
  exact Poly.list_flatMap hv rights_poly

noncomputable def bytes (r a b D : ℕ) (R : ProjectionRaw) : List Bool :=
  encodeNat (R.2.length * ProjectionInput.width r b D) ++
  encodeNat (R.1.length * a) ++ encodeNat R.1.length ++
  table a D (blocks r b D) R

@[fun_prop] theorem bytes_poly (r a b D : ℕ) : Poly (bytes r a b D) := by
  have ht : Poly (table a D (blocks r b D)) := table_poly a D _
  unfold bytes
  fun_prop

noncomputable def program (r a b D : ℕ) :
    PolyProgram enc id (bytes r a b D) :=
  PolyProgram.comp (f := bytes r a b D) (g := id)
    (bytes_poly r a b D).program BooleanLists.unpackProgram

end ProjectionRaw

namespace ProjectionInput
variable {r a b : ℕ} (G : ProjectionInput r a b)

def raw : ProjectionRaw :=
  (List.replicate G.u false,
    List.ofFn (fun v => List.ofFn (fun i =>
      ((G.system.neighbor v i).val,List.ofFn (fun c => (G.system.project v i c).val)))))

def encode : List Bool := enc G.raw

@[simp] theorem raw_lefts : G.raw.lefts = List.range G.u := by
  simp [raw,ProjectionRaw.lefts]
@[simp] theorem raw_rights : G.raw.rights = List.range G.v := by
  simp [raw,ProjectionRaw.rights]

@[simp] theorem raw_edge (v : Fin G.v) (i : Fin r) :
    G.raw.edge v.val i.val =
      ((G.system.neighbor v i).val,List.ofFn (fun c => (G.system.project v i c).val)) := by
  simp only [raw,ProjectionRaw.edge,List.getElem?_ofFn,dite_eq_left v.isLt,
    dite_eq_left i.isLt,Option.getD_some]

theorem raw_test (D : ℕ) (v : Fin G.v)
    (s : Fin D → Fin r) (w : Fin b → Fin D) (u : Fin G.u) (c : Fin a) (j : Fin D) :
    G.raw.test v.val (List.ofFn (fun i => (s i).val),List.ofFn (fun e => (w e).val))
      u.val c.val j.val =
      decide (G.system.neighbor v (s j) = u ∧ w (G.system.project v (s j) c) = j) := by
  simp only [ProjectionRaw.test,List.getElem?_ofFn,dite_eq_left j.isLt,Option.getD_some,
    G.raw_edge,dite_eq_left c.isLt,dite_eq_left (G.system.project v (s j) c).isLt,
    Fin.val_inj]
  exact (Bool.decide_and _ _).symm

theorem raw_incident (D : ℕ) (hD : 0 < D) (v : Fin G.v)
    (s : Fin D → Fin r) (w : Fin b → Fin D) (u : Fin G.u) (c : Fin a) :
    ProjectionRaw.incident D G.raw v.val
      (List.ofFn (fun i => (s i).val),List.ofFn (fun e => (w e).val)) u.val c.val =
      (G.toCoverage D hD).incident (G.clientEquiv D ((v,s),w)) (G.facilityEquiv (u,c)) := by
  apply Bool.eq_iff_iff.mpr
  rw [G.incident_equiv]
  simp only [ProjectionRaw.incident,Bool.not_eq_true',List.isEmpty_eq_false_iff_exists_mem,
    List.mem_filter,List.mem_range]
  constructor
  · rintro ⟨j,hj,ht⟩
    have hh := G.raw_test D v s w u c ⟨j,hj⟩
    rw [hh,decide_eq_true_eq] at ht
    exact ⟨⟨j,hj⟩,ht⟩
  · rintro ⟨j,hj⟩
    refine ⟨j.val,j.isLt,?_⟩
    rw [G.raw_test,decide_eq_true_eq]
    exact hj

@[simp] theorem client_block (D : ℕ) (v : Fin G.v) (x : Fin (width r b D)) :
    G.clientEquiv D ((v,((blockEquiv r b D).symm x).1),
      ((blockEquiv r b D).symm x).2) = finProdFinEquiv (v,x) := by
  simp [clientEquiv]

theorem table_correct (D : ℕ) (hD : 0 < D) :
    ProjectionRaw.table a D (ProjectionRaw.blocks r b D) G.raw =
      (List.ofFn (fun x => List.ofFn ((G.toCoverage D hD).incident x))).flatten := by
  have hp (x : Fin (G.v * width r b D)) :
      List.ofFn ((G.toCoverage D hD).incident x) =
      (List.finRange G.u).flatMap (fun u => (List.finRange a).map
        (fun c => (G.toCoverage D hD).incident x (G.facilityEquiv (u,c)))) :=
    ofFn_product _
  rw [ofFn_product]
  simp only [hp,List.flatten_eq_flatMap,List.flatMap_assoc,List.flatMap_map,Function.id_def]
  unfold ProjectionRaw.table ProjectionRaw.blocks
  rw [G.raw_lefts,G.raw_rights]
  simp only [RoundingList.range_finRange,List.ofFn_eq_map,List.flatMap_map,List.map_map,
    Function.comp_def]
  congr 1
  funext v
  congr 1
  funext x
  congr 1
  funext u
  congr 1
  funext c
  simpa only [G.client_block,List.ofFn_eq_map] using G.raw_incident D hD v
    ((blockEquiv r b D).symm x).1 ((blockEquiv r b D).symm x).2 u c

theorem bytes_correct (D : ℕ) (hD : 0 < D) :
    ProjectionRaw.bytes r a b D G.raw = (G.toCoverage D hD).encode := by
  unfold ProjectionRaw.bytes
  rw [G.table_correct D hD]
  simp only [raw,List.length_replicate,List.length_ofFn,Input.encode]

noncomputable def coverageProgram (D : ℕ) (hD : 0 < D) :
    PolyProgram (encode (r:=r) (a:=a) (b:=b)) Input.encode (fun G => G.toCoverage D hD) :=
  (ProjectionRaw.program r a b D).recode raw (fun _ => rfl)
    (fun G => by exact G.bytes_correct D hD)

end ProjectionInput
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Verdict
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.ProjectionInput.incident_equiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Binary Binary.Automatic Binary.Automatic.Poly

namespace Raw

@[fun_prop] theorem clients_poly : Poly clients := by
  unfold clients
  apply Poly.comp Poly.list_indices
  dsimp only [m, table]
  fun_prop

@[fun_prop] theorem sets_poly : Poly sets := by
  unfold sets
  apply Poly.comp Poly.list_indices
  dsimp only [n, table]
  fun_prop

def isCovered (r : Raw) (out : List Bool) (j : ℕ) : Bool :=
  !((r.sets.filter (fun i => (out[r.m+i]?).getD false &&
    (r.table[j*r.n+i]?).getD false)).isEmpty)

@[fun_prop] theorem isCovered_poly : Poly (fun x : (Raw × List Bool) × ℕ =>
    x.1.1.isCovered x.1.2 x.2) := by
  unfold isCovered
  apply Poly.comp Poly.bool_not
  apply Poly.comp Poly.list_empty
  apply Poly.list_filter
  · dsimp only [m, n, table]
    fun_prop
  · exact Poly.comp sets_poly (by fun_prop)

def coveredCount (r : Raw) (out : List Bool) : ℕ :=
  (r.clients.filter (r.isCovered out)).length

@[fun_prop] theorem coveredCount_poly : Poly (fun x : Raw × List Bool =>
    x.1.coveredCount x.2) := by
  unfold coveredCount
  apply Poly.comp Poly.list_length
  exact Poly.list_filter isCovered_poly (Poly.comp clients_poly Poly.fst)

def accepts (q : ℚ) (r : Raw) (out : List Bool) : Bool :=
  decide (3*(r.m : ℚ)-2*(r.coveredCount out : ℚ) < q*r.m)

@[fun_prop] theorem accepts_poly (q : ℚ) : Poly (fun x : Raw × List Bool =>
    accepts q x.1 x.2) := by
  unfold accepts
  dsimp only [m]
  fun_prop

end Raw

namespace Input

theorem clients_raw (C : Input) : C.raw.clients = List.range C.m := by
  have hm : C.m ≤ C.raw.table.length := by
    rw [C.table_length]; exact Nat.le_mul_of_pos_right _ C.n_pos
  simp only [Raw.clients, List.length_take, raw_m, Nat.min_eq_left hm]

theorem sets_raw (C : Input) : C.raw.sets = List.range C.n := by
  have hn : C.n ≤ C.raw.table.length := by
    rw [C.table_length]; exact Nat.le_mul_of_pos_left _ C.m_pos
  simp only [Raw.sets, List.length_take, raw_n, Nat.min_eq_left hn]

theorem isCovered_raw (C : Input) (out : List Bool) (j : Fin C.m) :
    C.raw.isCovered out j.val = decide (j ∈ C.covered (C.selectedMask out)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Raw.isCovered, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem,
    List.mem_filter, C.sets_raw, List.mem_range, Bool.and_eq_true, raw_m, raw_n,
    decide_eq_true_eq, mem_covered, mem_selectedMask_iff]
  constructor
  · rintro ⟨i, hi, hs, hc⟩
    exact ⟨⟨i,hi⟩, hs, by simpa only [← C.table_get j ⟨i,hi⟩] using hc⟩
  · rintro ⟨i,hs,hc⟩
    exact ⟨i.val,i.isLt,hs,by simpa only [C.table_get] using hc⟩

theorem coveredCount_raw (C : Input) (out : List Bool) :
    C.raw.coveredCount out = (C.covered (C.selectedMask out)).card := by
  unfold Raw.coveredCount
  rw [C.clients_raw, RoundingList.range_finRange]
  rw [List.filter_map]
  simp only [Function.comp_def, C.isCovered_raw]
  rw [List.length_map]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange C.m).filter _)]
  congr 1
  ext j
  simp

theorem accepts_raw (C : Input) (q : ℚ) (out : List Bool) :
    Raw.accepts q C.raw out = C.accepts q out := by
  simp only [Raw.accepts, C.coveredCount_raw, raw_m, accepts, comparisonCost]
  rfl

noncomputable def inputRawProgram : Binary.PolyProgram encode enc raw :=
  Raw.parsedProgram.recode encode (fun _ => rfl) (fun C => by rw [C.parse_encode])
attribute [irreducible] inputRawProgram

noncomputable def rawContextProgram :
    Binary.PolyProgram (Binary.encodePair id encode) (Binary.encodePair enc enc)
      (fun x : List Bool × Input => (x.2.raw,x.1)) := by
  let a : Binary.PolyProgram (Binary.encodePair id encode) enc
      (fun x : List Bool × Input => x.2.raw) :=
    (Binary.PolyProgram.snd id encode).comp inputRawProgram
  let b : Binary.PolyProgram (Binary.encodePair id encode) enc
      (fun x : List Bool × Input => x.1) :=
    (Binary.PolyProgram.fst id encode).comp BooleanLists.packProgram
  exact a.fanout b
attribute [irreducible] rawContextProgram

noncomputable def verdictProgram (q : ℚ) :
    Binary.PolyProgram (Binary.encodePair id encode) Complexity.encodeBit
      (fun x : List Bool × Input => x.2.accepts q x.1) :=
  (rawContextProgram.comp (Raw.accepts_poly q).program).congr _
    (fun x => x.2.accepts_raw q x.1)

end Input
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Reduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Complexity

def HasSeparator (δ : ℝ) : Prop :=
  ∃ d : Input → Bool, FinitePolyTime Input.encode encodeBit d ∧
    (∀ C, C.Perfect → d C = true) ∧
    (∀ C, C.Sound δ → d C = false)

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_ProjectionReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Complexity

def ProjectionReduction (ε : ℚ) (L : Language) : Prop :=
  ∃ r a b : ℕ, ∃ reduce : Word → ProjectionInput r a b,
    FinitePolyTime id ProjectionInput.encode reduce ∧
    (∀ x, x ∈ L → (reduce x).Perfect) ∧
    (∀ x, x ∉ L → (reduce x).Sound (ε : ℝ))

def ProjectionGapNPReductions : Prop :=
  ∀ ε : ℚ, 0 < ε → ∀ L ∈ NP, ProjectionReduction ε L

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end


