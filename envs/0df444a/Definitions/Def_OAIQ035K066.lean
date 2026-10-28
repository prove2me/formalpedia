-- Prove2me | Definitions.Def_OAIQ035K066
-- name    : OAIQ035K066
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:18:00.994374+00:00
-- url     : https://prove2.me/theorems/3ee3cbad-f6ba-443e-b9e5-7f66f77531b0
-- title:
--   Definitions bundle OAIQ035K066 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 101 declarations of OpenAI's Lean: 46 definitions and 55 theorems. The definitions and types are `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.metadata`, `OAI.MetricKMedian.InputParser.instanceProgram`, `OAI.MetricKMedian.InstanceProgram.budgetProgram`, `OAI.MetricKMedian.InstanceProgram.fallbackData`, `OAI.MetricKMedian.InstanceProgram.first`, `OAI.MetricKMedian.InstanceProgram.imageData`, `OAI.MetricKMedian.InstanceProgram.lpProgram`, `OAI.MetricKMedian.InstanceProgram.scanInput`, `OAI.MetricKMedian.InstanceProgram.singletonData`, `OAI.MetricKMedian.InstanceProgram.singletonRaw`, `OAI.MetricKMedian.InstanceProgram.zeroOutputData`, `OAI.MetricKMedian.InstanceProgram.zeroTestData`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.Input.encode`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.Input.raw`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.Input.result`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.Input.unit`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.Raw`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.budgetProgram`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.imageData`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.Input.encode`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.Input.prepared`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.Input.raw`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.PreparedRaw`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.ScanInput.encode`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.ScanInput.raw`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.ScanInput.scan`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.ScanRaw`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.countsData`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.originals`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.prepareData`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.qData`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.scanData`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.scanPrepProgram`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.tablesData`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.Input.encode`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.Input.raw`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.Input.result`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.Raw`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.postData`, `OAI.MetricKMedian.SparseGridRounding.Program.post` and 6 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Binary_InstanceParserProgram`, `KMedian_Optimization_FractionalInputProgram`, `KMedian_Optimization_FractionalScanProgram`, `KMedian_Preparation_PreparedKernelProgram`, `KMedian_Preparation_PreparedLawProgram`, `KMedian_Preparation_PreparedScanProgram`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Preparation_SupplierPreparationProgram`, `KMedian_Preparation_SupplierScanProgram`, `KMedian_Programs_HistorySelectionProgram`, `KMedian_Programs_InstanceDataProgram`, `KMedian_Programs_InstanceRoundProgram`, `KMedian_Programs_InstanceZeroProgram`, `KMedian_Programs_OuterLawProgram`, `KMedian_Programs_RationalSortProgram`, `KMedian_Programs_SplitListProgram`, `KMedian_Programs_UnitGeometryProgram`, `KMedian_Programs_UnitRepresentativeProgram`, `KMedian_Programs_UnitScanProgram`, `KMedian_Rounding_GridRoundingProgram`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K059`, `OAIQ035K061` and `OAIQ035K062` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K069`, `OAIQ035K070`, `OAIQ035K071` and `OAIQ035K072`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K059
import Definitions.Def_OAIQ035K061
import Definitions.Def_OAIQ035K062

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)

 theorem pairWeight_view {f n : ℕ} (S : Data f n) (s t : Fin n) :
    pairWeight (supplierView S) s.val t.val=∑ i∈S.A s∩S.P t,S.y i := by
  simp only [pairWeight,supplierView,indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),
    Option.getD_some,setView,Fin.eta,← Bool.decide_and,decide_eq_true_eq,List.sum_ofFn]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

 theorem weightsData_view {f n : ℕ} (S : Data f n) :
    weightsData (supplierView S)=List.ofFn (fun e => weightQ S.y S.P S.A S.c S.γ (index e)) := by
  rw [ofFn_star]
  simp only [weightsData,supplierView,indices,List.length_ofFn,RoundingList.range_finRange,
    List.flatMap_def,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,
    List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]
  change (List.ofFn (fun i => if outsideData (supplierView S) i.val then S.y i else 0) ++
     ((List.ofFn (fun s => List.ofFn (fun t => pairWeight (supplierView S) s.val t.val))).flatten ++
       List.ofFn (fun t => S.γ*S.c t)))=_
  simp only [outsideData_view,pairWeight_view,decide_eq_true_eq,weightQ]
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_RationalSortProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.RationalSortProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly

 theorem insertData_sorted (xs : List ℚ) (hx : xs.SortedLT) (a : ℚ) : (insertData (xs,a)).SortedLT := by
  rw [List.sortedLT_iff_pairwise]
  rw [insertData,List.pairwise_append,List.pairwise_cons]
  refine ⟨hx.pairwise.filter _,⟨?_,hx.pairwise.filter _⟩,?_⟩
  · intro b hb
    exact of_decide_eq_true (List.mem_filter.mp hb).2
  · intro b hb c hc
    have hb' : b<a := of_decide_eq_true (List.mem_filter.mp hb).2
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hb'
    · exact hb'.trans (of_decide_eq_true (List.mem_filter.mp hc).2)
 theorem insertData_mem (xs : List ℚ) (a q : ℚ) : q∈insertData (xs,a) ↔ q=a ∨ q∈xs := by
  simp only [insertData,List.mem_append,List.mem_filter,List.mem_cons,decide_eq_true_eq]
  constructor
  · tauto
  · rintro (rfl | hq)
    · tauto
    · rcases lt_trichotomy q a with h | h | h <;> tauto
 theorem insertData_sort (Q : Finset ℚ) (a : ℚ) : insertData (Q.sort,a) = (insert a Q).sort := by
  apply List.SortedLT.eq_of_mem_iff
  · exact insertData_sorted Q.sort Q.sortedLT_sort a
  · exact (insert a Q).sortedLT_sort
  · intro q
    simp only [insertData_mem,mem_sort,mem_insert]
 theorem fold_sort (xs : List ℚ) (Q : Finset ℚ) :
     xs.foldl (fun s a => insertData (s,a)) Q.sort=(xs.toFinset ∪ Q).sort := by
  induction xs generalizing Q with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons,insertData_sort,ih]
    congr 1
    ext q
    simp only [List.toFinset_cons,mem_union,mem_insert]
    tauto
 theorem sort_eq (xs : List ℚ) : sort xs=xs.toFinset.sort := by
  have h := fold_sort xs ∅
  simpa only [sort,Finset.sort_empty,union_empty] using h
end MetricKMedian.RationalSortProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_SplitListProgram
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
 theorem cutsData_view {f j : ℕ} (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) (i : Fin f) :
    cutsData (view y x,i.val)=(cuts y x i).sort := by
  simp only [cutsData,view,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,
    List.map_ofFn,Function.comp_def,RationalSortProgram.sort_eq,List.toFinset_filter,List.toFinset_cons]
  congr 1
  ext q
  simp only [Finset.mem_filter,Finset.mem_insert,List.mem_toFinset,List.mem_ofFn,cuts,Finset.mem_image,
    Finset.mem_univ,true_and,decide_eq_true_eq]

 theorem piecesData_view {f j : ℕ} (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) :
    piecesData (view y x)=List.ofFn (fun a => ((index y x a).1.val,(index y x a).2.val)) := by
  simp only [piecesData,view,indices,List.length_ofFn,RoundingList.range_finRange,List.flatMap_map]
  change ((List.finRange f).flatMap (fun i => (cutsData (view y x,i.val)).map (fun q => (i.val,q))))=_
  simp only [cutsData_view]
  have hs (i : Fin f) : (cuts y x i).sort=List.ofFn (fun t => ((cuts y x i).orderIsoOfFin rfl t).val) := by
    exact (EncodingLists.sorted_enum (cuts y x i)).symm
  simp only [hs,List.map_ofFn,Function.comp_def,List.flatMap_def,← List.ofFn_eq_map]
  rw [ListSigma.ofFn_sigma]
  rfl

 theorem originalData_view {f j : ℕ} (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) :
    originalData (view y x)=List.ofFn (fun a => (original y x a).val) := by
  simp only [originalData,piecesData_view,List.map_ofFn,Function.comp_def,original]

 theorem previousData_view (s : Finset ℚ) (q : ℚ) : previousData (s.sort,q)=RationalIntervals.previous s q := by
  apply maximum_eq_finset
  · exact insert_nonempty _ _
  intro a
  simp only [List.mem_cons,List.mem_filter,mem_sort,decide_eq_true_eq,mem_insert,mem_filter]

 theorem weightsData_view {f j : ℕ} (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) :
    weightsData (view y x)=List.ofFn (weights y x) := by
  rw [weightsData,piecesData_view,List.map_ofFn]
  simp only [Function.comp_def,cutsData_view,previousData_view]
  rfl

 theorem assignedData_view {f j : ℕ} (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ) :
    assignedData (view y x)=List.ofFn (fun c => setView (assigned y x c)) := by
  unfold assignedData
  rw [piecesData_view]
  simp only [view,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    Fin.eta,setView,mem_assigned,assignment,mem_filter,mem_univ,true_and]
end MetricKMedian.Preparation.RationalSplitting.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_UnitRepresentativeProgram
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
 theorem ranks_view {n : ℕ} (s : Finset (Fin n)) :
    ranks (setView s)=List.ofFn (fun i : Fin s.card => (s.orderEmbOfFin rfl i).val) := by
  have h : ((List.finRange n).filter (fun i => decide (i∈s))).map Fin.val =
      List.ofFn (fun i : Fin s.card => (s.orderEmbOfFin rfl i).val) := by
    rw [EncodingLists.filter_range,Finset.filter_mem_eq_inter,Finset.univ_inter,
      ← EncodingLists.sorted_enum,List.map_ofFn]
    rfl
  rw [← h]
  simp only [ranks,indices,setView,List.length_ofFn,RoundingList.range_finRange,List.filter_map]
  congr 1
  apply List.filter_congr
  intro i hi
  simp only [Function.comp_def,MetricKMedian.MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta]

end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalInputProgram
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
 theorem assignmentData_view (z : Input) : assignmentData z.raw=List.ofFn (fun c => List.ofFn (x z.a z.k z.ha z.hj z.dc c)) := by
  simp only [assignmentData,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext c
  exact LPBinary.Nearest.filling_ofFn _ _ (fun i => (z.ha.1 i).1) (mass_one z.a z.k z.ha z.hj)

 theorem splitData_view (z : Input) : splitData z.raw=RationalSplitting.Program.view (y z.a) (x z.a z.k z.ha z.hj z.dc) := by
  unfold splitData
  rw [assignmentData_view]
  rfl

 theorem unitData_view (z : Input) : unitData z.raw=z.unit.raw := by
  unfold unitData
  rw [splitData_view,RationalSplitting.Program.weightsData_view,RationalSplitting.Program.assignedData_view,
    RationalSplitting.Program.originalData_view]
  simp only [List.map_ofFn,Function.comp_def,pullback_view,pullbackMatrix_view]
  rfl
end MetricKMedian.Preparation.FractionalRefinement.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_UnitGeometryProgram
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

 theorem pickRows_view {m n k : ℕ} {α : Type} [Inhabited α] (r : Fin k → Fin n) (v : Fin n → Fin m → α) :
    pickRows (List.ofFn (fun i => List.ofFn (v i)),List.ofFn (fun i => (r i).val))=
      List.ofFn (fun i => List.ofFn (v (r i))) := by
  simp only [pickRows,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]

end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_InstanceDataProgram
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
 theorem dcData_view (I : Instance) : dcData (view I)=List.ofFn (fun c => List.ofFn (I.indexedDistance c)) := by
  simp only [dcData,view,RationalUnitInput.Program.ranks_view,RationalUnitInput.Program.pickRows_view,
    List.map_ofFn,Function.comp_def,pullback_view]
  rfl
 theorem ddData_view (I : Instance) : ddData (view I)=List.ofFn (fun c => List.ofFn (I.clientDistance c)) := by
  simp only [ddData,view,RationalUnitInput.Program.ranks_view,pullbackMatrix_view]; rfl
 theorem dfData_view (I : Instance) : dfData (view I)=List.ofFn (fun c => List.ofFn (I.facilityDistance c)) := by
  simp only [dfData,view,RationalUnitInput.Program.ranks_view,pullbackMatrix_view]; rfl
noncomputable def lpProgram : PolyProgram nzEncode LPBinary.Input.encode lpInput :=
  lpData_poly.program.recode (fun I => view I.val) (fun _ => rfl) (fun I => congrArg enc (by
    unfold lpData; rw [dcData_view]; rfl))
variable (r : ℕ) (hr : 0 < r)
 theorem fractionalData_view (I : Nonzero) : fractionalData (view I.val,LPBinary.Scale.selected r (lpInput I))=(fractionalInput r hr I).raw := by
  unfold fractionalData
  rw [LPBinary.Scale.selected_eq r hr (lpInput I) I.val.indexedDistance_nonneg,dcData_view,ddData_view,dfData_view]
  rfl
end MetricKMedian.InstanceProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_InstanceParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.InputParser
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
 theorem raw_encoded (I : Instance) : raw (encodeInstance I)=view I := by
  unfold raw
  rw [header_encoded]
  have he : (List.ofFn (fun i => (List.ofFn (fun j => encodeRat (I.distance i j))).flatten)).flatten=
      ((List.ofFn (fun i => List.ofFn (I.distance i))).flatten.map encodeRat).flatten := by
    simp only [List.map_flatten,List.map_ofFn,Function.comp_def]
    rw [List.flatten_flatten]
    simp only [List.map_ofFn,Function.comp_def]
  rw [he]
  dsimp only
  have hm := matrix_encoded I.clients I.distance []
  simp only [List.append_nil] at hm
  rw [hm]
  rfl
noncomputable def instanceProgram : PolyProgram encodeInstance InstanceProgram.encode (id : Instance → Instance) :=
  (BooleanLists.packProgram.comp rawProgram).recode encodeInstance (fun _ => rfl) (fun I => congrArg enc (raw_encoded I))
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_HistorySelectionProgram
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
 theorem metadata_input (x : Input q) : metadata q x.raw=(q.g*x.A.card+q.allowance,List.ofFn (fun c => List.ofFn (x.d c))) := by
  unfold metadata Input.raw Completion.Rational.Program.Input.raw
  dsimp only
  rw [CopyList.view,Completion.Rational.BestProgram.card_view,card_map]

end MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparedScanProgram
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

def metadata (x : Raw) : ℚ × List (List ℚ) := (x.2.2.2,x.2.1.2)
@[fun_prop] theorem metadata_poly : Poly metadata := by unfold metadata; fun_prop

end MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_GridRoundingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGridRounding.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
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
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparedKernelProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

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
-- module Solutions.OAIQ035_KM.KMedian_Programs_OuterLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Table setView)
def post (x : Raw) : Raw := (x.1,(x.2.1,(x.2.2.1,SparseGridRounding.Program.fractionRow x.2.2.2)))
@[fun_prop] theorem post_poly : Poly post := by unfold post; fun_prop
end MetricKMedian.SparseOuterLaw.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparedLawProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierPreparationProgram
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
abbrev Input.raw (x : Input) := supplierView x.S
abbrev Input.encode (x : Input) := enc x.raw

def qData (x : SupplierRaw) : QRow := (weightsData x).map (fun w => w/qR.g)
@[fun_prop] theorem qData_poly : Poly (qData qR) := by unfold qData; apply list_map <;> fun_prop
 theorem qData_view (x : Input) : qData qR x.raw=List.ofFn (q x.S.y x.S.P x.S.A x.S.c x.S.γ qR.g) := by
  unfold qData Input.raw
  rw [weightsData_view,List.map_ofFn]
  rfl

def Input.prepared (x : Input) : SparsePrepared.Program.Input :=
  ⟨x.n,size x.f x.n,x.f,D x.S.A,a,q x.S.y x.S.P x.S.A x.S.c x.S.γ qR.g,
    x.S.P,x.S.y,x.S.p,qR.Δ,x.S.hy,x.S.hp,a_bounds,
    q_nonneg _ _ _ _ _ _ x.S.hy x.S.hc0 x.S.hγ.le (FixedParameters.positive qR).le⟩
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
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierScanProgram
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
def ScanInput.raw (x : ScanInput) : ScanRaw := (supplierView x.S,((List.ofFn (fun i => List.ofFn (x.df i)),List.ofFn (fun c => List.ofFn (x.dc c))),x.budget))
abbrev ScanInput.encode (x : ScanInput) := enc x.raw
def ScanInput.scan (x : ScanInput) : FixedBatch.RationalParameters.PreparedScanProgram.Input :=
  ⟨x.f+x.n*x.f,x.f,x.j,x.df,x.dc,original,x.S.tables qR,x.budget⟩
def originals (x : SupplierRaw) : List ℕ := indices x.1 ++ x.2.2.2.1.flatMap (fun _ => indices x.1)
@[fun_prop] theorem originals_poly : Poly originals := by
  unfold originals
  apply append_poly
  · fun_prop
  · apply list_flatMap <;> fun_prop
 theorem originals_view {f n : ℕ} (S : Data f n) : originals (supplierView S)=List.ofFn (fun i => (original (f:=f) (n:=n) i).val) := by
  rw [show (fun e => (original (f:=f) (n:=n) e).val)=(fun e => Sum.elim (fun i : Fin f => i.val) (fun ti : Fin n × Fin f => ti.2.val) (physicalIndex e)) by
    funext e; unfold original; cases physicalIndex e <;> rfl]
  rw [ofFn_physical]
  simp only [originals,supplierView,indices,List.length_ofFn,RoundingList.range_finRange,List.flatMap_def,List.map_ofFn]
  rw [← List.ofFn_eq_map]
  simp [Function.comp_def]

def scanData (x : ScanRaw × List (List ℕ)) : FixedBatch.RationalParameters.PreparedScanProgram.Raw :=
  ((x.1.1.1.map (fun _ => ()),originals x.1.1),(x.1.2.1,(x.2,x.1.2.2)))
@[fun_prop] theorem scanData_poly : Poly scanData := by
  unfold scanData
  have : Poly (fun x : ScanRaw × List (List ℕ) => x.1.1.1.map (fun _ => ())) := by apply list_map <;> fun_prop
  fun_prop
 theorem scanData_view (x : ScanInput) : scanData (x.raw,(x.S.tables qR).map List.ofFn)=(x.scan qR).raw := by
  unfold scanData ScanInput.raw
  rw [originals_view]
  simp only [supplierView,List.map_ofFn,ScanInput.scan,FixedBatch.RationalParameters.PreparedScanProgram.Input.raw]
  simp only [Function.comp_def,List.ofFn_const]
noncomputable def scanPrepProgram : PolyProgram ScanInput.encode Input.encode ScanInput.prep :=
  (fst enc enc).recode ScanInput.raw (fun _ => rfl) (fun _ => rfl)
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_UnitScanProgram
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
def Input.raw (x : Input) : Raw := (view x.U,x.B)
abbrev Input.encode (x : Input) := enc x.raw
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
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalScanProgram
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
abbrev Raw := Program.Raw × ℚ
def Input.raw (z : Input) : Raw := (z.toInput.raw,z.B)
abbrev Input.encode (z : Input) := enc z.raw

def Input.unit (z : Input) : RationalUnitInput.ScanProgram.Input :=
  letI := z.metric
  ⟨count z.a z.k z.ha z.hj z.dc,z.j,z.m,z.toInput.unit.U,z.metric,
    realization z.a z.k z.ha z.hj z.dc z.dd z.df z.hdc z.hdd z.hds z.facility z.client z.hdf z.hc z.hcc,z.B⟩
noncomputable def budgetProgram : PolyProgram Input.encode enc Input.B :=
  (snd enc enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
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
 theorem imageRaw_option {f n : ℕ} (g : Fin n → Fin f) (O : Option (Finset (Fin n))) :
    (O.map setView).toList.map (fun row => imageRaw ((List.replicate f (),List.ofFn (fun b => (g b).val)),row))=
    ((O.map (fun S => S.image g)).map setView).toList := by
  cases O with
  | none => rfl
  | some S => simp only [Option.map_some,Option.toList_some,List.map_cons,List.map_nil,imageRaw_view]
 theorem imageData_view (z : Input) : imageData (z.toInput.raw,RationalUnitInput.ScanProgram.Input.result p z.unit)=z.result p := by
  let := z.metric
  unfold imageData
  rw [Program.splitData_view,RationalSplitting.Program.originalData_view]
  have hu : z.toInput.raw.1.map (fun _ => ())=List.replicate z.f () := by
    simp only [List.map_ofFn,Function.comp_def,List.ofFn_const]
  rw [hu]
  simp only [RationalUnitInput.ScanProgram.Input.result,Input.unit,Program.Input.unit]
  simp only [Input.result,scan]
  convert (imageRaw_option (original z.a z.k z.ha z.hj z.dc)
      ((unitInput z.a z.k z.ha z.hj z.dc z.dd z.df z.hdc z.hdd z.hds).scan
        (realization z.a z.k z.ha z.hj z.dc z.dd z.df z.hdc z.hdd z.hds z.facility z.client z.hdf z.hc z.hcc) p z.B)) using 1
  all_goals try with_reducible_and_instances rfl
  rfl
attribute [irreducible] Input.result
end MetricKMedian.Preparation.FractionalRefinement.ScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_InstanceZeroProgram
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
@[fun_prop] theorem subsetRaw_poly : Poly subsetRaw := by
  unfold subsetRaw
  have h : Poly (fun x : Row × Row => (x.1.zip x.2).map (fun p => !p.1 || p.2)) := by apply list_map <;> fun_prop
  simpa only [List.all_map,Function.comp_def,id_eq] using (comp bool_all h)

def zeroTestData (x : Raw) : Bool := subsetRaw x.1 && decide (card x.1.1≤x.2.1)
@[fun_prop] theorem zeroTestData_poly : Poly zeroTestData := by unfold zeroTestData; fun_prop

def first (O : Row) : ℕ := O.findIdx id
@[fun_prop] theorem first_poly : Poly first := by unfold first; apply list_findIdx <;> fun_prop
 theorem first_view {n : ℕ} (O : Finset (Fin n)) (hO : O.Nonempty) : first (setView O)=(O.min' hO).val := by
  unfold first
  apply (List.findIdx_eq (by simp only [setView,List.length_ofFn]; exact (O.min' hO).isLt)).mpr
  constructor
  · simp only [setView,List.getElem_ofFn,id_eq,Fin.eta,decide_eq_true_eq]; exact min'_mem _ _
  · intro k hk
    have hkn : k<n := hk.trans (O.min' hO).isLt
    simp only [setView,List.getElem_ofFn,id_eq,decide_eq_false_iff_not]
    intro hm
    exact (not_le_of_gt hk) (O.min'_le ⟨k,hkn⟩ hm)
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
-- module Solutions.OAIQ035_KM.KMedian_Programs_InstanceRoundProgram
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
def scanInput (I : Nonzero) : FractionalRefinement.ScanProgram.Input :=
  { fractionalInput r hr I with
    m := I.val.n
    metric := I.val.pseudoMetric
    facility := I.val.facilities.orderEmbOfFin rfl
    client := I.val.clients.orderEmbOfFin rfl
    hdf := fun _ _ => rfl
    hc := fun _ _ => rfl
    hcc := fun _ _ => rfl
    B := I.val.k+C }
noncomputable def budgetProgram : PolyProgram nzEncode (enc : ℚ → List Bool) (fun I => (I.val.k:ℚ)+C) :=
  (by fun_prop : Poly (fun x : Raw => (x.2.1:ℚ)+C)).program.recode (fun I => view I.val) (fun _ => rfl) (fun _ => rfl)
def imageData (x : Raw × Table) : Table := x.2.map (fun row => imageRaw
  ((x.1.1.2.map (fun _ => ()),RationalUnitInput.Program.ranks x.1.1.2),row))
@[fun_prop] theorem imageData_poly : Poly imageData := by unfold imageData; apply list_map <;> fun_prop
attribute [local irreducible] FractionalRefinement.scan Instance.computedFractional
 theorem imageData_view (I : Nonzero) :
    imageData (view I.val,(scanInput r hr C I).result p)=((I.val.nonzeroRound I.property r hr p C).map setView).toList := by
  let := I.val.pseudoMetric
  unfold imageData
  simp only [view]
  rw [RationalUnitInput.Program.ranks_view]
  simp only [setView,List.map_ofFn,Function.comp_def,List.ofFn_const]
  convert FractionalRefinement.ScanProgram.imageRaw_option (I.val.facilities.orderEmbOfFin rfl)
    (FractionalRefinement.scan (I.val.computedFractional r hr (I.val.nonzero_clients I.property)) I.val.k
      (I.val.nonzeroFractional_spec I.property r hr).1 (card_pos.mpr (I.val.nonzero_clients I.property))
      I.val.indexedDistance I.val.clientDistance I.val.facilityDistance
      I.val.indexedDistance_nonneg I.val.clientDistance_self I.val.clientDistance_comm
      (I.val.facilities.orderEmbOfFin rfl) (I.val.clients.orderEmbOfFin rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) p (I.val.k+C)) using 1
  all_goals try with_reducible_and_instances rfl
  unfold FractionalRefinement.ScanProgram.Input.result
  rfl
  rfl

def fallbackData (x : Raw × Table) : Row := if x.2.isEmpty then singletonData x.1 else x.2.head?.getD []
@[fun_prop] theorem fallbackData_poly : Poly fallbackData := by unfold fallbackData; fun_prop
end MetricKMedian.InstanceProgram
end

end OAI
end


