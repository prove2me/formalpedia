-- Prove2me | Definitions.Def_OAIQ053K063
-- name    : OAIQ053K063
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:16:20.0302+00:00
-- url     : https://prove2.me/theorems/88cc8fd7-702a-4d18-b9ea-e400b276afab
-- title:
--   Definitions bundle OAIQ053K063 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 153 declarations of OpenAI's Lean: 79 definitions and 74 theorems. The definitions and types are `OAI.MetricKMedian.FixedBatch.RationalParameters.GridDataProgram.Raw`, `OAI.MetricKMedian.FixedBatch.RationalParameters.GridDataProgram.prepare`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.images`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.metadata`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.prepare`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.dummy`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.finish`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.prepare`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.valid`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.Input.raw`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.attach`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.ctxRaw`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.metadata`, `OAI.MetricKMedian.InputParser.Header`, `OAI.MetricKMedian.InputParser.header`, `OAI.MetricKMedian.InputParser.reshape`, `OAI.MetricKMedian.InputParser.squareUnits`, `OAI.MetricKMedian.InstanceProgram.Raw`, `OAI.MetricKMedian.InstanceProgram.dcData`, `OAI.MetricKMedian.InstanceProgram.ddData`, `OAI.MetricKMedian.InstanceProgram.dfData`, `OAI.MetricKMedian.InstanceProgram.fallbackData`, `OAI.MetricKMedian.InstanceProgram.first`, `OAI.MetricKMedian.InstanceProgram.fractionalData`, `OAI.MetricKMedian.InstanceProgram.imageData`, `OAI.MetricKMedian.InstanceProgram.lpData`, `OAI.MetricKMedian.InstanceProgram.singletonData`, `OAI.MetricKMedian.InstanceProgram.singletonRaw`, `OAI.MetricKMedian.InstanceProgram.subsetRaw`, `OAI.MetricKMedian.InstanceProgram.zeroOutputData`, `OAI.MetricKMedian.InstanceProgram.zeroTestData`, `OAI.MetricKMedian.Preparation.FractionalRefinement.Program.splitData`, `OAI.MetricKMedian.Preparation.FractionalRefinement.Program.unitData`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.Input.result`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.imageData`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.stepRaw`, `OAI.MetricKMedian.Preparation.RationalSplitting.Program.assignedData`, `OAI.MetricKMedian.Preparation.RationalSplitting.Program.originalData`, `OAI.MetricKMedian.Preparation.RationalSplitting.Program.piecesData`, `OAI.MetricKMedian.Preparation.RationalSplitting.Program.previousData` and 39 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_InstanceParserProgram`, `KMedian_Hardness_ProjectionEncoding`, `KMedian_Optimization_FractionalInputProgram`, `KMedian_Optimization_FractionalScanProgram`, `KMedian_Preparation_PreparedDataOperations`, `KMedian_Preparation_PreparedKernelProgram`, `KMedian_Preparation_PreparedLawProgram`, `KMedian_Preparation_PreparedScanProgram`, `KMedian_Preparation_RepresentativeProgram`, `KMedian_Preparation_SupplierPreparationProgram`, `KMedian_Preparation_SupplierScanProgram`, `KMedian_Process_PhysicalHistoriesProgram`, `KMedian_Process_RoundCountsProgram`, `KMedian_Programs_BoundedEnumerationProgram`, `KMedian_Programs_HistorySelectionProgram`, `KMedian_Programs_InstanceDataProgram`, `KMedian_Programs_InstanceRoundProgram`, `KMedian_Programs_InstanceZeroProgram`, `KMedian_Programs_OuterLawProgram`, `KMedian_Programs_SplitListProgram`, `KMedian_Programs_StarActivationProgram`, `KMedian_Programs_UnitGeometryProgram`, `KMedian_Programs_UnitRepresentativeProgram`, `KMedian_Programs_UnitScanProgram`, `KMedian_Rounding_GridDataProgram`, `KMedian_Rounding_GridRoundingProgram`, `KMedian_Rounding_SignedPreparationProgram`, `KMedian_Rounding_TargetSubsetProgram`.
--
--   **Imports.** It imports the bundles `OAIQ053K054` and `OAIQ053K055` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K070`, `OAIQ053K071`, `OAIQ053K072`, `OAIQ053K073` and `OAIQ053K074`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K054
import Definitions.Def_OAIQ053K055

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_SplitListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Preparation.RationalSplitting.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
@[fun_prop] theorem cutsData_poly : Poly cutsData := by
  unfold cutsData
  apply comp RationalSortProgram.sort_poly
  apply list_filter
  · fun_prop
  · have h : Poly (fun x : Raw × ℕ => x.1.2.map (fun r => r[x.2]?.getD 0)) := by apply list_map <;> fun_prop
    have g : Poly (fun x : Raw × ℕ => x.1.1[x.2]?.getD (0:ℚ)) := by fun_prop
    exact Poly.comp list_cons (pair g h)

def piecesData (x : Raw) : List (ℕ × ℚ) :=
  (indices x.1).flatMap (fun i => (cutsData (x,i)).map (fun q => (i,q)))
@[fun_prop] theorem piecesData_poly : Poly piecesData := by
  unfold piecesData
  apply list_flatMap
  · apply list_map <;> fun_prop
  · fun_prop

def originalData (x : Raw) : List ℕ := (piecesData x).map Prod.fst
@[fun_prop] theorem originalData_poly : Poly originalData := by unfold originalData; apply list_map <;> fun_prop

def previousData (x : List ℚ × ℚ) : ℚ := maximum (0::x.1.filter (fun q => decide (q<x.2)))
@[fun_prop] theorem previousData_poly : Poly previousData := by
  unfold previousData
  have h : Poly (fun x : List ℚ × ℚ => x.1.filter (fun q => decide (q<x.2))) := by apply list_filter <;> fun_prop
  have h2 : Poly (fun x : List ℚ × ℚ => (0:ℚ)::x.1.filter (fun q => decide (q<x.2))) :=
    Poly.comp (f:=fun t : ℚ × List ℚ => t.1::t.2) (list_cons (α:=ℚ)) (pair (const (α:=List ℚ × ℚ) (0:ℚ)) h)
  exact Poly.comp maximum_poly h2

def weightsData (x : Raw) : List ℚ := (piecesData x).map (fun a => a.2-previousData (cutsData (x,a.1),a.2))
@[fun_prop] theorem weightsData_poly : Poly weightsData := by unfold weightsData; apply list_map <;> fun_prop

def assignedData (x : Raw) : Table := x.2.map (fun row => (piecesData x).map (fun a => decide (a.2 ≤ row[a.1]?.getD 0)))
@[fun_prop] theorem assignedData_poly : Poly assignedData := by
  unfold assignedData
  apply list_map
  · apply list_map <;> fun_prop
  · fun_prop
end MetricKMedian.Preparation.RationalSplitting.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RepresentativeProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalRepresentatives.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram

def stepRaw (x : Raw × (Row × Row)) : Raw × (Row × Row) :=
  if x.2.1.any id then
    let c := MaskProgram.nearest (x.1.1.1,x.2.1)
    (x.1,((indices x.2.1).map (fun i => MaskProgram.get x.2.1 i &&
      decide (x.1.1.2.2*(x.1.1.1[i]?.getD 0) < (x.1.1.2.1[i]?.getD [])[c]?.getD 0)),
      (indices x.2.2).map (fun i => MaskProgram.get x.2.2 i || decide (i=c))))
  else x
@[fun_prop] theorem stepRaw_poly : Poly stepRaw := by
  unfold stepRaw
  apply Poly.ite
  · fun_prop
  · apply pair
    · fun_prop
    · apply pair <;> apply list_map <;> fun_prop
  · fun_prop
end MetricKMedian.Preparation.RationalRepresentatives.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_UnitRepresentativeProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Preparation.RationalUnitInput.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram

def values (x : Raw) : List ℚ := (indices x.1.2).map (fun c =>
  ((indices x.1.1).map (fun a => if MetricKMedian.MaskProgram.get (x.1.2[c]?.getD []) a then
    x.1.1[a]?.getD 0*(x.2.1[c]?.getD [])[a]?.getD 0 else 0)).sum)
@[fun_prop] theorem values_poly : Poly values := by
  unfold values; apply list_map
  · apply comp rat_sum
    apply list_map <;> fun_prop
  · fun_prop
def repData (M : ℚ) (x : Raw) : RationalRepresentatives.Program.Raw :=
  ((values x,(x.2.2.1,M)),x.1.2.map (fun _ => true))
@[fun_prop] theorem repData_poly (M : ℚ) : Poly (repData M) := by
  unfold repData
  have : Poly (fun x : Raw => x.1.2.map (fun _ => true)) := by apply list_map <;> fun_prop
  fun_prop

def ranks (x : Row) : List ℕ := (indices x).filter (fun i => MetricKMedian.MaskProgram.get x i)
@[fun_prop] theorem ranks_poly : Poly ranks := by unfold ranks; apply list_filter <;> fun_prop

end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.FractionalRefinement.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
@[fun_prop] theorem assignmentData_poly : Poly assignmentData := by
  have h : Poly (fun z : Raw => (z.1,z.2.1)) := by fun_prop
  exact ⟨(h.program.comp (LPBinary.Nearest.fillingProgram.listMapWith [] [])).congr _ (fun _ => rfl)⟩

def splitData (z : Raw) : RationalSplitting.Program.Raw := (z.1,assignmentData z)
@[fun_prop] theorem splitData_poly : Poly splitData := by unfold splitData; fun_prop

def unitData (z : Raw) : RationalUnitInput.Program.Raw :=
  ((RationalSplitting.Program.weightsData (splitData z),RationalSplitting.Program.assignedData (splitData z)),
    (z.2.1.map (fun d => pullback (d,RationalSplitting.Program.originalData (splitData z))),
      (z.2.2.1,pullbackMatrix (z.2.2.2,RationalSplitting.Program.originalData (splitData z)))))
@[fun_prop] theorem unitData_poly : Poly unitData := by
  unfold unitData
  have h : Poly (fun z : Raw => z.2.1.map (fun d => pullback (d,RationalSplitting.Program.originalData (splitData z)))) := by
    apply list_map <;> fun_prop
  fun_prop

end MetricKMedian.Preparation.FractionalRefinement.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_UnitGeometryProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Preparation.RationalUnitInput.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram

@[fun_prop] theorem pickRows_poly {α : Type} [Coding α] [Inhabited α] : Poly (pickRows (α:=α)) := by
  unfold pickRows; apply list_map <;> fun_prop

def geometryData (x : Raw × Row) : RationalBundles.Program.Raw :=
  ((pullbackMatrix (x.1.2.2.1,ranks x.2),pickRows (x.1.2.1,ranks x.2)),
    (pickRows (x.1.1.2,ranks x.2),x.1.1.1))
@[fun_prop] theorem geometryData_poly : Poly geometryData := by unfold geometryData; fun_prop

def suppliersData (δ γ : ℚ) (x : RationalBundles.Program.Raw) : RationalSuppliers.Program.SupplierRaw :=
  (x.2.2,(RationalBundles.Program.bundlesData δ x,(RationalBundles.Program.missingData δ x,
    (RationalBundles.Program.massData (x.2.2,RationalBundles.Program.bundlesData δ x),
      (RationalBundles.Program.massData (x.2.2,RationalBundles.Program.missingData δ x),γ)))))
@[fun_prop] theorem suppliersData_poly (δ γ : ℚ) : Poly (suppliersData δ γ) := by unfold suppliersData; fun_prop
end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceDataProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.InstanceProgram
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram
open RationalUnitInput.Program (ranks pickRows)
abbrev Raw := (Row × Row) × (ℕ × Matrix)
def dcData (x : Raw) : Matrix := (pickRows (x.2.2,ranks x.1.1)).map (fun d => pullback (d,ranks x.1.2))
@[fun_prop] theorem dcData_poly : Poly dcData := by unfold dcData; apply list_map <;> fun_prop
def ddData (x : Raw) : Matrix := pullbackMatrix (x.2.2,ranks x.1.1)
def dfData (x : Raw) : Matrix := pullbackMatrix (x.2.2,ranks x.1.2)
@[fun_prop] theorem ddData_poly : Poly ddData := by unfold ddData; fun_prop
@[fun_prop] theorem dfData_poly : Poly dfData := by unfold dfData; fun_prop
def lpData (x : Raw) : Matrix × ℕ := (dcData x,x.2.1)
@[fun_prop] theorem lpData_poly : Poly lpData := by unfold lpData; fun_prop
def fractionalData (x : Raw × LPBinary.Repair.Output) : FractionalRefinement.Program.Raw :=
  (x.2.1,(dcData x.1,(ddData x.1,dfData x.1)))
@[fun_prop] theorem fractionalData_poly : Poly fractionalData := by unfold fractionalData; fun_prop
end MetricKMedian.InstanceProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_InstanceParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.InputParser
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw )
@[fun_prop] theorem take_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → ℕ} {g : α → List β} (hf : Poly f) (hg : Poly g) : Poly (fun x => (g x).take (f x)) :=
  comp list_take (pair hg hf)
@[fun_prop] theorem drop_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → ℕ} {g : α → List β} (hf : Poly f) (hg : Poly g) : Poly (fun x => (g x).drop (f x)) :=
  comp list_drop (pair hg hf)
def squareUnits (xs : Row) : List Unit := xs.flatMap (fun _ => xs.map (fun _ => ()))
@[fun_prop] theorem squareUnits_poly : Poly squareUnits := by unfold squareUnits; apply list_flatMap; apply list_map <;> fun_prop; fun_prop
def reshape (x : Row × List ℚ) : InstanceProgram.Matrix :=
  (indices x.1).map (fun i => (indices x.1).map (fun j => x.2[i*x.1.length+j]?.getD 0))
@[fun_prop] theorem reshape_poly : Poly reshape := by unfold reshape; apply list_map; apply list_map <;> fun_prop; fun_prop
abbrev Header := (Row × Row) × ℕ
def header (xs : List Bool) : Header × List Bool :=
  let a := natRead xs
  let b := natRead a.2
  (((b.2.take a.1,(b.2.drop a.1).take a.1),b.1),b.2.drop (a.1+a.1))
@[fun_prop] theorem header_poly : Poly header := by unfold header; fun_prop
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_ProjectionEncoding
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Binary Binary.Automatic Binary.Automatic.Poly

namespace ProjectionRaw

@[fun_prop] theorem rights_poly : Poly rights := by
  unfold rights; apply Poly.comp Poly.list_indices; fun_prop

end ProjectionRaw

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalHistoriesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.RationalPhysicalKernel.HistoryProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table)
open CopyList UpdateProgram
@[fun_prop] theorem nextRaw_poly (P : ℚ) : Poly (nextRaw P) := by unfold nextRaw; fun_prop

def attach (P : ℚ) (x : RoundProgram.Raw × Data Row) : LawData × List RoundProgram.Raw :=
  (x.2.1,x.2.2.map (fun A => nextRaw P (x.1,A)))
@[fun_prop] theorem attach_poly (P : ℚ) : Poly (attach P) := by
  unfold attach
  apply pair
  · fun_prop
  · apply list_map <;> fun_prop

end MetricKMedian.RationalPhysicalKernel.HistoryProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_HistorySelectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open RationalPhysicalKernel
variable {τ : ℝ} (q : RationalParameters τ)
def Input.raw (x : Input q) : Raw := (List.ofFn (fun i => List.ofFn (x.d₀ i)),x.toInput.raw)

def ctxRaw (x : Raw) : RoundProgram.Raw := (((((q.g,1),q.Δ),x.1),x.2.2.2.2),(q.β,(q.probabilityQ,q.φ)))
@[fun_prop] theorem ctxRaw_poly : Poly (ctxRaw q) := by unfold ctxRaw; fun_prop
def attach (x : Raw × Data Row) : List Completion.Rational.Program.Raw :=
  x.2.2.map (fun A => (x.1.2.1,(x.1.2.2.1,(x.1.2.2.2.1,A))))
@[fun_prop] theorem attach_poly : Poly attach := by unfold attach; apply list_map <;> fun_prop

def metadata (x : Raw) : ℚ × List (List ℚ) :=
  (q.g*Completion.Rational.BestProgram.card x.2.2.2.2+q.allowance,x.2.2.1.1)
@[fun_prop] theorem metadata_poly : Poly (metadata q) := by unfold metadata; fun_prop
end MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
end

end OAI
end

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
abbrev Raw := List Unit × ((List (List ℚ) × List (List ℚ)) × Row)

def prepare (Δ : ℕ) (x : Raw) : SelectionProgram.Raw :=
  (x.2.1.1,(x.1,((x.2.1.2,x.2.1.2.map (fun ds => radiusRaw Δ (ds,x.2.2))),
    (x.2.1.2.map (fun ds => nearestRaw Δ (ds,x.2.2)),x.2.2))))
@[fun_prop] theorem prepare_poly (Δ : ℕ) : Poly (prepare Δ) := by
  unfold prepare
  have hr : Poly (fun x : Raw => x.2.1.2.map (fun ds => radiusRaw Δ (ds,x.2.2))) := by apply list_map <;> fun_prop
  have hn : Poly (fun x : Raw => x.2.1.2.map (fun ds => nearestRaw Δ (ds,x.2.2))) := by apply list_map <;> fun_prop
  fun_prop
end MetricKMedian.FixedBatch.RationalParameters.GridDataProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundCountsProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
@[fun_prop] theorem cap_poly (Δ : ℕ) : Poly (cap Δ) := by unfold cap; apply comp bool_all; apply list_map <;> fun_prop

def valid (Δ : ℕ) (x : Raw) : Bool := cap Δ x.2.2 && decide (Δ≤Completion.Rational.BestProgram.card (CopyState.CountsProgram.mask Δ x.2.2))
@[fun_prop] theorem valid_poly (Δ : ℕ) : Poly (valid Δ) := by unfold valid; fun_prop

local instance instLinearOrderCopyFin_rf4c062_1 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
def dummy : SelectionProgram.Input q where
  f := 0
  j := 0
  d := fun c => Fin.elim0 c
  R := fun c => Fin.elim0 c
  A := ∅
  B := fun c => Fin.elim0 c
  hB := fun c => Fin.elim0 c
  d₀ := fun i => Fin.elim0 i

def prepare (x : Raw) : SelectionProgram.Raw :=
  if valid q.Δ x then GridDataProgram.prepare q.Δ (x.1,(x.2.1,CopyState.CountsProgram.mask q.Δ x.2.2))
  else (dummy q).raw
@[fun_prop] theorem prepare_poly : Poly (prepare q) := by unfold prepare; fun_prop

def finish (x : Raw × Table) : Table := if valid q.Δ x.1 then x.2 else []
@[fun_prop] theorem finish_poly : Poly (finish q) := by unfold finish; fun_prop
end MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedScanProgram
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

def prepare (x : Raw) : List RoundCountsProgram.Raw := x.2.2.1.map (fun ns =>
  (x.1.2.map (fun _ => ()),((MaskProgram.pullbackMatrix (x.2.1.1,x.1.2),
    x.2.1.2.map (fun ds => MaskProgram.pullback (ds,x.1.2))),ns)))
@[fun_prop] theorem prepare_poly : Poly prepare := by
  unfold prepare
  apply list_map
  · have hd : Poly (fun x : Raw × List ℕ => x.1.2.1.2.map (fun ds => MaskProgram.pullback (ds,x.1.1.2))) := by
      apply list_map <;> fun_prop
    have hu : Poly (fun x : Raw × List ℕ => x.1.1.2.map (fun _ => ())) := by apply list_map <;> fun_prop
    fun_prop
  · fun_prop

def images (x : Raw × List Table) : Table := x.2.flatten.map (fun O => MaskProgram.imageRaw (x.1.1,O))
@[fun_prop] theorem images_poly : Poly images := by
  unfold images
  apply list_map
  · fun_prop
  · exact comp (⟨listFlatten (enc : Row → List Bool) []⟩ : Poly (List.flatten : List Table → Table)) (by fun_prop)

def metadata (x : Raw) : ℚ × List (List ℚ) := (x.2.2.2,x.2.1.2)
@[fun_prop] theorem metadata_poly : Poly metadata := by unfold metadata; fun_prop

end MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_TargetSubsetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseTargetSubset.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
@[fun_prop] theorem prepare_poly : Poly prepare := by
  unfold prepare
  apply pair <;> apply list_map <;> fun_prop
end MetricKMedian.SparseTargetSubset.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_StarActivationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparseStarActivation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView indices)

def prepare (x : Raw) : List SparseTargetSubset.Program.Raw :=
  (indices x.2.2).map (fun e => (x.2.1[e]?.getD [],x.2.2[e]?.getD 0))
@[fun_prop] theorem prepare_poly : Poly prepare := by unfold prepare; apply list_map <;> fun_prop
end MetricKMedian.SparseStarActivation.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedPreparationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparseSignedPreparation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
abbrev StateRaw := QRow × (Table × Row)
abbrev KernelRaw := List Unit × (Table × QRow)

def attach (x : QRow × Data (Table × Row)) : Data StateRaw := (x.2.1,x.2.2.map (fun s => (x.1,s)))
@[fun_prop] theorem attach_poly : Poly attach := by
  unfold attach; apply pair
  · fun_prop
  · apply list_map <;> fun_prop

abbrev Raw := List Unit × (Table × (QRow × QRow))
def beta (x : Raw) : QRow :=
  (SparseGraph.ListOperation.indices x.2.2.1).map (fun e => x.2.2.1[e]?.getD 0-
    (Completion.Rational.BestProgram.card (x.2.1[e]?.getD []):ℚ))
@[fun_prop] theorem beta_poly : Poly beta := by unfold beta; apply list_map <;> fun_prop

def inputRows (x : Raw × QRow × Data QRow) : List KernelRaw :=
  x.2.2.2.map (fun p => (x.1.1,(x.1.2.1,p)))
@[fun_prop] theorem inputRows_poly : Poly inputRows := by unfold inputRows; apply list_map <;> fun_prop

end MetricKMedian.SparseSignedPreparation.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedDataOperations
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView indices)
abbrev StateRaw := SparseSignedPreparation.Program.StateRaw

abbrev KernelRaw := BaseRaw × StateRaw

def activationData (x : KernelRaw) (e j : ℕ) : ℕ :=
  (if (x.1.1[e]?.getD [])[j]?.getD false then ⌊x.1.2.1[e]?.getD 0⌋₊ else 0)+
    if (x.2.2.1[e]?.getD [])[j]?.getD false then 1 else 0
def totalData (x : KernelRaw) (j : ℕ) : ℕ :=
  x.1.2.2.2.2.2-min ((indices x.1.2.1).map (fun e => activationData x e j)).sum (x.1.2.2.2.2.2/2)
def pieces (x : KernelRaw) : List (List ℚ) :=
  (indices x.1.2.2.2.2.1).map (fun j => (indices x.1.2.2.2.1).map (fun i =>
    if (x.1.2.2.1[j]?.getD [])[i]?.getD false then
      (totalData x j:ℚ)*x.1.2.2.2.1[i]?.getD 0/x.1.2.2.2.2.1[j]?.getD 0 else 0))
@[fun_prop] theorem activationData_poly : Poly (fun x : KernelRaw × (ℕ × ℕ) => activationData x.1 x.2.1 x.2.2) := by
  unfold activationData; fun_prop
@[fun_prop] theorem totalData_poly : Poly (fun x : KernelRaw × ℕ => totalData x.1 x.2) := by
  unfold totalData
  have h : Poly (fun x : KernelRaw × ℕ => ((indices x.1.1.2.1).map (fun e => activationData x.1 e x.2)).sum) := by
    apply comp nat_list_sum
    apply list_map <;> fun_prop
  fun_prop
@[fun_prop] theorem pieces_poly : Poly pieces := by
  unfold pieces
  apply list_map
  · apply list_map <;> fun_prop
  · fun_prop

end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_GridRoundingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGridRounding.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
@[fun_prop] theorem fractionRow_poly : Poly fractionRow := by unfold fractionRow; apply list_map <;> fun_prop
@[fun_prop] theorem counts_poly : Poly counts := by unfold counts; apply list_map <;> fun_prop
def post (x : List ℚ × Data (List Bool)) : Data (List ℕ) := (x.2.1,x.2.2.map (fun b => counts (x.1,b)))
@[fun_prop] theorem post_poly : Poly post := by
  unfold post; apply pair
  · fun_prop
  · apply list_map <;> fun_prop

end MetricKMedian.SparseGridRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedKernelProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

def bundleData (x : KernelRaw) : List Unit × List (List ℚ) := (x.1.2.2.2.1.map (fun _ => ()),pieces x)
@[fun_prop] theorem bundleData_poly : Poly bundleData := by
  unfold bundleData; apply Binary.Automatic.Poly.pair
  · apply list_map <;> fun_prop
  · exact pieces_poly
abbrev PreparedRaw := StateRaw × SparseCounts.ListOperation.Table
def attach (x : StateRaw × Data SparseCounts.ListOperation.Table) : Data PreparedRaw :=
  (x.2.1,x.2.2.map (fun G => (x.1,G)))
@[fun_prop] theorem attach_poly : Poly attach := by
  unfold attach; apply Binary.Automatic.Poly.pair
  · fun_prop
  · apply list_map <;> fun_prop

end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_OuterLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Table setView)
abbrev Raw := SparseSignedPreparation.Program.Raw
def post (x : Raw) : Raw := (x.1,(x.2.1,(x.2.2.1,SparseGridRounding.Program.fractionRow x.2.2.2)))
@[fun_prop] theorem post_poly : Poly post := by unfold post; fun_prop
end MetricKMedian.SparseOuterLaw.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView)
abbrev Raw := BaseRaw × QRow
def outerData (x : Raw) : SparseOuterLaw.Program.Raw :=
  (x.1.2.2.2.2.1.map (fun _ => ()),(x.1.1,(x.2,x.1.2.1)))
@[fun_prop] theorem outerData_poly : Poly outerData := by
  unfold outerData; apply Binary.Automatic.Poly.pair
  · apply list_map <;> fun_prop
  · fun_prop

def kernelRows (x : Raw × Data StateRaw) : List KernelRaw := x.2.2.map (fun z => (x.1.1,z))
@[fun_prop] theorem kernelRows_poly : Poly kernelRows := by unfold kernelRows; apply list_map <;> fun_prop
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierPreparationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)
open SparseIntegerLaw.BinarySparse
variable {τ : ℝ} (qR : FixedBatch.RationalParameters τ)
@[fun_prop] theorem qData_poly : Poly (qData qR) := by unfold qData; apply list_map <;> fun_prop
def prepareData (x : SupplierRaw) : SparsePrepared.Program.Raw :=
  ((targetsData x,(qData qR x,(x.2.1,(x.1,(x.2.2.2.1,qR.Δ))))),flagsData x)
@[fun_prop] theorem prepareData_poly : Poly (prepareData qR) := by unfold prepareData; fun_prop

abbrev PreparedRaw := SparsePrepared.Program.PreparedRaw

def countsData (x : SupplierRaw × PreparedRaw) : List ℕ :=
  ((indices x.1.1).map (fun i => ⌊(qData qR x.1)[i]?.getD 0⌋₊+
    if 0 < x.2.1.1[i]?.getD 0 then 1 else 0)) ++ x.2.2.flatten
@[fun_prop] theorem countsData_poly : Poly (countsData qR) := by
  unfold countsData
  apply append_poly
  · apply list_map <;> fun_prop
  · exact comp (⟨listFlatten (enc : ℕ → List Bool) 0⟩ : Poly (List.flatten : List (List ℕ) → List ℕ)) (by fun_prop)

def tablesData (x : SupplierRaw × List PreparedRaw) : List (List ℕ) := x.2.map (fun z => countsData qR (x.1,z))
@[fun_prop] theorem tablesData_poly : Poly (tablesData qR) := by unfold tablesData; apply list_map <;> fun_prop
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
variable {τ : ℝ} (qR : FixedBatch.RationalParameters τ)
abbrev ScanRaw := SupplierRaw × ((List (List ℚ) × List (List ℚ)) × ℚ)
def originals (x : SupplierRaw) : List ℕ := indices x.1 ++ x.2.2.2.1.flatMap (fun _ => indices x.1)
@[fun_prop] theorem originals_poly : Poly originals := by
  unfold originals
  apply append_poly
  · fun_prop
  · apply list_flatMap <;> fun_prop

def scanData (x : ScanRaw × List (List ℕ)) : FixedBatch.RationalParameters.PreparedScanProgram.Raw :=
  ((x.1.1.1.map (fun _ => ()),originals x.1.1),(x.1.2.1,(x.2,x.1.2.2)))
@[fun_prop] theorem scanData_poly : Poly scanData := by
  unfold scanData
  have : Poly (fun x : ScanRaw × List (List ℕ) => x.1.1.1.map (fun _ => ())) := by apply list_map <;> fun_prop
  fun_prop
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_UnitScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Preparation.RationalUnitInput.ScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open Program
abbrev Raw := Program.Raw × ℚ
variable {η τ : ℝ} (p : RationalAllParameters η τ)
def postData (x : Raw × RationalSuppliers.Program.SupplierRaw) : RationalSuppliers.Program.ScanRaw :=
  (x.2,((x.1.1.2.2.2,x.1.1.2.1),x.1.2))
@[fun_prop] theorem postData_poly : Poly postData := by unfold postData; fun_prop
def Input.result (x : Input) : Table :=
  letI := x.metric
  ((x.U.scan x.R p x.B).map setView).toList
end MetricKMedian.Preparation.RationalUnitInput.ScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.FractionalRefinement.ScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
attribute [local irreducible] RationalUnitInput.ScanProgram.Input.result
variable {η τ : ℝ} (p : RationalAllParameters η τ)
def imageData (x : Program.Raw × Table) : Table := x.2.map (fun row => imageRaw
  ((x.1.1.map (fun _ => ()),RationalSplitting.Program.originalData (Program.splitData x.1)),row))
@[fun_prop] theorem imageData_poly : Poly imageData := by
  unfold imageData
  have h : Poly (fun x : (Program.Raw × Table) × Row => x.1.1.1.map (fun _ => ())) := by apply list_map <;> fun_prop
  apply list_map
  · fun_prop
  · fun_prop
def Input.result (z : Input) : Table :=
  letI := z.metric
  ((scan z.a z.k z.ha z.hj z.dc z.dd z.df z.hdc z.hdd z.hds z.facility z.client z.hdf z.hc z.hcc p z.B).map setView).toList
attribute [irreducible] Input.result
end MetricKMedian.Preparation.FractionalRefinement.ScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BoundedEnumerationProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Reduction.Enumeration
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
@[fun_prop] theorem words_poly {α : Type} [Coding α] [Inhabited α] (c : ℕ) : Poly (@words α c) := by
  induction c with
  | zero => exact const [[]]
  | succ c ih =>
    change Poly (fun xs : List α => []::xs.flatMap (fun a => (words c xs).map (List.cons a)))
    have h : Poly (fun xs : List α => xs.flatMap (fun a => (words c xs).map (List.cons a))) := by
      apply list_flatMap
      · apply list_map
        · exact comp list_cons (pair (comp snd fst) snd)
        · exact comp ih fst
      · fun_prop
    have hh := comp (list_cons (α := List α)) (pair (const ([] : List α) : Poly (fun _ : List α => ([] : List α))) h)
    exact hh

def maskWord (x : Row × List ℕ) : Row := (indices x.1).map (fun i => (x.2.map (fun a => decide (a=i))).any id)
@[fun_prop] theorem maskWord_poly : Poly maskWord := by
  unfold maskWord
  apply list_map
  · apply comp bool_any
    apply list_map <;> fun_prop
  · fun_prop
end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceZeroProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.InstanceProgram
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram
open Completion.Rational.BestProgram (card card_view)
def subsetRaw (x : Row × Row) : Bool := (x.1.zip x.2).all (fun p => !p.1 || p.2)
@[fun_prop] theorem subsetRaw_poly : Poly subsetRaw := by
  unfold subsetRaw
  have h : Poly (fun x : Row × Row => (x.1.zip x.2).map (fun p => !p.1 || p.2)) := by apply list_map <;> fun_prop
  simpa only [List.all_map,Function.comp_def,id_eq] using (comp bool_all h)

def zeroTestData (x : Raw) : Bool := subsetRaw x.1 && decide (card x.1.1≤x.2.1)
@[fun_prop] theorem zeroTestData_poly : Poly zeroTestData := by unfold zeroTestData; fun_prop

def first (O : Row) : ℕ := O.findIdx id
@[fun_prop] theorem first_poly : Poly first := by unfold first; apply list_findIdx <;> fun_prop
def singletonRaw (x : Row × ℕ) : Row := (indices x.1).map (fun i => decide (i=x.2))
@[fun_prop] theorem singletonRaw_poly : Poly singletonRaw := by unfold singletonRaw; apply list_map <;> fun_prop
def singletonData (x : Raw) : Row := singletonRaw (x.1.2,first x.1.2)
@[fun_prop] theorem singletonData_poly : Poly singletonData := by unfold singletonData; fun_prop
def zeroOutputData (x : Raw) : Row := if x.1.1.any id then x.1.1 else singletonData x
@[fun_prop] theorem zeroOutputData_poly : Poly zeroOutputData := by unfold zeroOutputData; fun_prop
end MetricKMedian.InstanceProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceRoundProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.InstanceProgram
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (C : ℕ)
def imageData (x : Raw × Table) : Table := x.2.map (fun row => imageRaw
  ((x.1.1.2.map (fun _ => ()),RationalUnitInput.Program.ranks x.1.1.2),row))
@[fun_prop] theorem imageData_poly : Poly imageData := by unfold imageData; apply list_map <;> fun_prop
attribute [local irreducible] FractionalRefinement.scan Instance.computedFractional

def fallbackData (x : Raw × Table) : Row := if x.2.isEmpty then singletonData x.1 else x.2.head?.getD []
@[fun_prop] theorem fallbackData_poly : Poly fallbackData := by unfold fallbackData; fun_prop
end MetricKMedian.InstanceProgram
end

end OAI
end


