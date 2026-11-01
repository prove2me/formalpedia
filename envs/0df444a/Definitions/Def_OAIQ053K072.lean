-- Prove2me | Definitions.Def_OAIQ053K072
-- name    : OAIQ053K072
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:18:57.500981+00:00
-- url     : https://prove2.me/theorems/87bc66d6-593c-41fa-bdd3-1b95dcf35779
-- title:
--   Definitions bundle OAIQ053K072 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 64 declarations of OpenAI's Lean: 32 definitions and 32 theorems. The definitions and types are `OAI.MetricKMedian.InstanceProgram.budgetProgram`, `OAI.MetricKMedian.InstanceProgram.encode`, `OAI.MetricKMedian.InstanceProgram.fractionalProgram`, `OAI.MetricKMedian.InstanceProgram.lpProgram`, `OAI.MetricKMedian.InstanceProgram.nzEncode`, `OAI.MetricKMedian.InstanceProgram.scanInput`, `OAI.MetricKMedian.InstanceProgram.view`, `OAI.MetricKMedian.Preparation.FractionalRefinement.Program.Input.encode`, `OAI.MetricKMedian.Preparation.FractionalRefinement.Program.unitProgram`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.Input.unit`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.Input.encode`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.Input.prepared`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.ScanInput.encode`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.ScanInput.raw`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.ScanInput.scan`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.preparedInputProgram`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.scanPrepProgram`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.Input.encode`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.Input.raw`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.view`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.Input.encode`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.Input.raw`, `OAI.MetricKMedian.SparseGridRounding.Program.Input.result`, `OAI.MetricKMedian.SparsePrepared.Program.Input.base`, `OAI.MetricKMedian.SparsePrepared.Program.Input.encode`, `OAI.MetricKMedian.SparsePrepared.Program.Input.raw`, `OAI.MetricKMedian.SparsePrepared.Program.Input.result`, `OAI.MetricKMedian.SparsePrepared.Program.KernelInput.encode`, `OAI.MetricKMedian.SparsePrepared.Program.KernelInput.raw`, `OAI.MetricKMedian.SparsePrepared.Program.view`, `OAI.MetricKMedian.SparseSignedPreparation.Program.Input.raw`, `OAI.MetricKMedian.SparseSignedPreparation.Program.view`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_InstanceParserProgram`, `KMedian_Optimization_FractionalInputProgram`, `KMedian_Optimization_FractionalScanProgram`, `KMedian_Preparation_PreparedDataOperations`, `KMedian_Preparation_PreparedKernelProgram`, `KMedian_Preparation_PreparedLawProgram`, `KMedian_Preparation_SupplierPreparationProgram`, `KMedian_Preparation_SupplierScanProgram`, `KMedian_Process_CopyNextProgram`, `KMedian_Process_PhysicalBatchUpdateProgram`, `KMedian_Programs_HistorySelectionProgram`, `KMedian_Programs_InstanceDataProgram`, `KMedian_Programs_InstanceRoundProgram`, `KMedian_Programs_InstanceZeroProgram`, `KMedian_Programs_SplitListProgram`, `KMedian_Programs_UnitGeometryProgram`, `KMedian_Programs_UnitRepresentativeProgram`, `KMedian_Programs_UnitScanProgram`, `KMedian_Rounding_GridRoundingProgram`, `KMedian_Rounding_SignedPreparationProgram`, `KMedian_Sparse_SparseTable`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K063`, `OAIQ053K064`, `OAIQ053K065` and `OAIQ053K066` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K075`, `OAIQ053K076`, `OAIQ053K077`, `OAIQ053K078` and `OAIQ053K079`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K063
import Definitions.Def_OAIQ053K064
import Definitions.Def_OAIQ053K065
import Definitions.Def_OAIQ053K066

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_SplitListProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
-- module Solutions.OAIQ053_KM.KMedian_Programs_UnitRepresentativeProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
def view {f j : ℕ} (U : RationalUnitInput f j) : Raw :=
  ((List.ofFn U.y,List.ofFn (fun c => setView (U.F c))),
    (List.ofFn (fun c => List.ofFn (U.dc c)),(List.ofFn (fun c => List.ofFn (U.dd c)),List.ofFn (fun a => List.ofFn (U.df a)))))
abbrev Input.raw (x : Input) := view x.U
abbrev Input.encode (x : Input) := enc x.raw

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
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalInputProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
abbrev Input.encode (z : Input) := enc z.raw

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
noncomputable def unitProgram : PolyProgram Input.encode RationalUnitInput.Program.Input.encode Input.unit :=
  unitData_poly.program.recode Input.raw (fun _ => rfl) (fun z => congrArg enc (unitData_view z))
end MetricKMedian.Preparation.FractionalRefinement.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_UnitGeometryProgram
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
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceDataProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
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
def view (I : Instance) : Raw :=
  ((setView I.clients,setView I.facilities),(I.k,List.ofFn (fun i => List.ofFn (I.distance i))))
abbrev encode (I : Instance) := enc (view I)
 theorem dcData_view (I : Instance) : dcData (view I)=List.ofFn (fun c => List.ofFn (I.indexedDistance c)) := by
  simp only [dcData,view,RationalUnitInput.Program.ranks_view,RationalUnitInput.Program.pickRows_view,
    List.map_ofFn,Function.comp_def,pullback_view]
  rfl
 theorem ddData_view (I : Instance) : ddData (view I)=List.ofFn (fun c => List.ofFn (I.clientDistance c)) := by
  simp only [ddData,view,RationalUnitInput.Program.ranks_view,pullbackMatrix_view]; rfl
 theorem dfData_view (I : Instance) : dfData (view I)=List.ofFn (fun c => List.ofFn (I.facilityDistance c)) := by
  simp only [dfData,view,RationalUnitInput.Program.ranks_view,pullbackMatrix_view]; rfl
abbrev nzEncode (I : Nonzero) := encode I.val
noncomputable def lpProgram : PolyProgram nzEncode LPBinary.Input.encode lpInput :=
  lpData_poly.program.recode (fun I => view I.val) (fun _ => rfl) (fun I => congrArg enc (by
    unfold lpData; rw [dcData_view]; rfl))
variable (r : ℕ) (hr : 0 < r)
 theorem fractionalData_view (I : Nonzero) : fractionalData (view I.val,LPBinary.Scale.selected r (lpInput I))=(fractionalInput r hr I).raw := by
  unfold fractionalData
  rw [LPBinary.Scale.selected_eq r hr (lpInput I) I.val.indexedDistance_nonneg,dcData_view,ddData_view,dfData_view]
  rfl
noncomputable def fractionalProgram : PolyProgram nzEncode FractionalRefinement.Program.Input.encode (fractionalInput r hr) :=
  (((identity enc).recode (fun I : Nonzero => view I.val) (fun _ => rfl) (fun _ => rfl) |>.fanout
    (lpProgram.comp (LPBinary.Scale.selectedProgram r hr))).comp fractionalData_poly.program).recode
      id (fun _ => rfl) (fun I => congrArg enc (fractionalData_view r hr I))
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
open InstanceProgram (Raw view)
 theorem squareUnits_length (xs : Row) : (squareUnits xs).length=xs.length*xs.length := by
  simp only [squareUnits,List.length_flatMap,List.length_map]
  rw [List.map_const',List.sum_replicate]
  simp only [smul_eq_mul]
 theorem reshape_flatten {n : ℕ} (S : Finset (Fin n)) (d : Fin n → Fin n → ℚ) :
    reshape (setView S,(List.ofFn (fun i => List.ofFn (d i))).flatten)=List.ofFn (fun i => List.ofFn (d i)) := by
  rw [flatten_ofFn]
  simp only [reshape,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hij : i.val*n+j.val<n*n := by
    calc
      i.val*n+j.val < i.val*n+n := Nat.add_lt_add_left j.isLt _
      _ = (i.val+1)*n := by simp only [Nat.add_mul,Nat.one_mul]
      _ ≤ n*n := Nat.mul_le_mul_right n i.isLt
  simp only [List.getElem?_ofFn,dite_eq_left hij,Option.getD_some]
  have he : (⟨i.val*n+j.val, hij⟩ : Fin (n*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext; change _=j.val+n*i.val; ac_rfl
  rw [he]
  exact congrArg (fun p : Fin n × Fin n => d p.1 p.2) (finProdFinEquiv.symm_apply_apply (i,j))
 theorem header_encoded (I : Instance) : header (encodeInstance I)=
    (((setView I.clients,setView I.facilities),I.k),
      (List.ofFn (fun i => (List.ofFn (fun j => encodeRat (I.distance i j))).flatten)).flatten) := by
  unfold header encodeInstance
  simp only [List.append_assoc,natRead_append]
  have hc : (setView I.clients).length=I.n := by simp only [setView,List.length_ofFn]
  have hf : (setView I.facilities).length=I.n := by simp only [setView,List.length_ofFn]
  change (((((setView I.clients)++(setView I.facilities++_)).take I.n,
    (((setView I.clients)++(setView I.facilities++_)).drop I.n).take I.n),I.k),
    ((setView I.clients)++(setView I.facilities++_)).drop (I.n+I.n))=_
  have htC (xs : Row) : (setView I.clients++xs).take I.n=setView I.clients := by simpa only [hc] using List.take_left (l₁ := setView I.clients) (l₂ := xs)
  have hdC (xs : Row) : (setView I.clients++xs).drop I.n=xs := by simpa only [hc] using List.drop_left (l₁ := setView I.clients) (l₂ := xs)
  have htF (xs : Row) : (setView I.facilities++xs).take I.n=setView I.facilities := by simpa only [hf] using List.take_left (l₁ := setView I.facilities) (l₂ := xs)
  have hdF (xs : Row) : (setView I.facilities++xs).drop I.n=xs := by simpa only [hf] using List.drop_left (l₁ := setView I.facilities) (l₂ := xs)
  simp only [htC,hdC,htF,← List.drop_drop,hdF]

end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyNextProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.RationalPhysicalKernel.CopyNext
open Binary Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open CopyList
open CopyGraphProgram (rank_owner)
open SparseGraph.ListOperation (Row Table setView indices)
open RationalBatchData.Ordinal (sets)

 local instance instLinearOrderCopyFin_r5bc0f2_1 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.CopyNext.instLinearOrderSubtypeCopyFinMemFinset
theorem pick_mem {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) (S : Finset A) (k : ℕ) :
    k∈pick (active (view A),sets (ordinal A) S) ↔ ∃a∈S,(rank a.val).val=k := by
  simp only [pick,active_view,RationalBatchData.Ordinal.sets_eq,Gaussian.ListOperation.zip_ofFn,
    List.mem_map,List.mem_filter,List.mem_ofFn]
  constructor
  · rintro ⟨z,⟨⟨i,rfl⟩,hi⟩,hk⟩
    exact ⟨enumeration A i,of_decide_eq_true hi,hk⟩
  · rintro ⟨a,ha,rfl⟩
    refine ⟨_,⟨⟨(enumeration A).symm a,rfl⟩,?_⟩,?_⟩
    · change decide (enumeration A ((enumeration A).symm a)∈S)=true
      rw [Equiv.apply_symm_apply]
      exact decide_eq_true ha
    · simp only [Equiv.apply_symm_apply]

 theorem next_view {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) (E O : Finset A) :
    next ((Δ,view A),(sets (ordinal A) E,sets (ordinal A) O))=
    view (CopyState.next Δ A (E.image Subtype.val) (O.image (fun a => a.val.1))) := by
  unfold next
  have hl : (view A).length=f*Δ := by simp only [view,setView,List.length_ofFn]
  simp only [indices,hl,RoundingList.range_finRange,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn]
  change List.ofFn (fun k : Fin (f*Δ) => _)=_
  conv_rhs => rw [view_eq]
  apply congrArg List.ofFn
  funext k
  let a := finProdFinEquiv.symm k
  have ha : rank a=k := finProdFinEquiv.apply_symm_apply k
  have hdiv : k.val/Δ=a.1.val := by rw [← ha,rank_owner]
  apply Bool.eq_iff_iff.mpr
  simp only [view_get,Bool.or_eq_true,
    Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,Bool.eq_false_iff,decide_eq_true_eq,natMember_true,
    CopyState.next,mem_union,mem_sdiff,CopyState.mem_resets]
  simp only [ne_eq,natMember_true]
  rw [pick_mem]
  apply or_congr
  · apply and_congr Iff.rfl
    apply not_congr
    simp only [mem_image]
    constructor
    · rintro ⟨b,hb,hk⟩
      exact ⟨b,hb,finProdFinEquiv.injective ((Fin.ext hk).trans ha.symm)⟩
    · rintro ⟨b,hb,hba⟩
      refine ⟨b,hb,?_⟩
      change b.val=a at hba
      rw [hba,ha]
  · rw [List.mem_map]
    simp only [mem_image]
    constructor
    · rintro ⟨j,hj,hjk⟩
      obtain ⟨b,hb,rfl⟩ := (pick_mem A O j).mp hj
      rw [rank_owner,hdiv] at hjk
      exact ⟨b,hb,Fin.ext hjk⟩
    · rintro ⟨b,hb,hba⟩
      refine ⟨(rank b.val).val,(pick_mem A O _).mpr ⟨b,hb,rfl⟩,?_⟩
      rw [rank_owner,hdiv]
      exact congrArg Fin.val hba

end MetricKMedian.RationalPhysicalKernel.CopyNext
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchUpdateProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section
namespace MetricKMedian.RationalPhysicalKernel.UpdateProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open CopyList

 local instance instLinearOrderCopyFin_r5bc0f2_2 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.instLinearOrderSubtypeCopyFinMemFinset
theorem result_map (x : Input) : x.result=(x.proposal.result.1,
    x.proposal.law.states.toList.map (fun Z => CopyList.view (x.update Z))) := by
  unfold Input.result Input.law
  change (x.proposal.result.1,(Vector.map x.update x.proposal.law.states).toList.map CopyList.view)=_
  erw [Vector.toList_map,List.map_map]
  rfl

end MetricKMedian.RationalPhysicalKernel.UpdateProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section

namespace MetricKMedian.SparseIntegerLaw.BinarySparse
variable {α β A : Type}

 theorem table_bind (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β) (v : β → A) :
    table (μ.bindIndexed κ) v=bindData ((raw μ).1,List.ofFn (fun i => table (κ i) v)) :=
  (bindData_raw μ κ v).symm

end MetricKMedian.SparseIntegerLaw.BinarySparse
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
 local instance instLinearOrderCopyFin_r5bc0f2_3 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
theorem metadata_input (x : Input q) : metadata q x.raw=(q.g*x.A.card+q.allowance,List.ofFn (fun c => List.ofFn (x.d c))) := by
  unfold metadata Input.raw Completion.Rational.Program.Input.raw
  dsimp only
  rw [CopyList.view,Completion.Rational.BestProgram.card_view,card_map]

end MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
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
def view {n m : ℕ} (s : SparseSignedPreparation.State n m) : StateRaw :=
  (s.1.toList,(SparseGraph.ListOperation.view s.2.1,List.ofFn s.2.2))
def Input.raw (x : Input) : Raw :=
  (List.replicate x.n (),(List.ofFn (fun e => setView (x.D e)),(List.ofFn x.c,x.p.toList)))

end MetricKMedian.SparseSignedPreparation.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedDataOperations
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView indices)
def KernelInput.raw (x : KernelInput) : KernelRaw := (x.base,SparseSignedPreparation.Program.view x.z)
abbrev KernelInput.encode (x : KernelInput) := enc x.raw

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

def Input.result (x : Input) : Data (List ℕ) :=
  ((SparseIntegerLaw.BinarySparse.raw (law x.q)).1,(law x.q).states.toList.map List.ofFn)
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

def view {n m f : ℕ} (s : SparseSignedPreparation.State n m × SparseCounts.Table f n) : PreparedRaw :=
  (SparseSignedPreparation.Program.view s.1,SparseCounts.ListOperation.view s.2)
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedLawProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView)
def Input.base (x : Input) : BaseRaw :=
  (List.ofFn (fun e => setView (x.D e)),(List.ofFn x.q,(List.ofFn (fun j => setView (x.P j)),
    (List.ofFn x.y,(List.ofFn x.p,x.Δ)))))
def Input.raw (x : Input) : Raw := (x.base,List.ofFn x.c)
abbrev Input.encode (x : Input) := enc x.raw

def Input.result (x : Input) : Data PreparedRaw :=
  ((SparseIntegerLaw.BinarySparse.raw (law x.D x.c x.q x.Δ x.P x.y x.p x.hc x.hq)).1,
    (law x.D x.c x.q x.Δ x.P x.y x.p x.hc x.hq).states.toList.map view)
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierPreparationProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
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
abbrev Input.encode (x : Input) := enc x.raw

 theorem qData_view (x : Input) : qData qR x.raw=List.ofFn (q x.S.y x.S.P x.S.A x.S.c x.S.γ qR.g) := by
  unfold qData Input.raw
  rw [weightsData_view,List.map_ofFn]
  rfl

def Input.prepared (x : Input) : SparsePrepared.Program.Input :=
  ⟨x.n,size x.f x.n,x.f,D x.S.A,a,q x.S.y x.S.P x.S.A x.S.c x.S.γ qR.g,
    x.S.P,x.S.y,x.S.p,qR.Δ,x.S.hy,x.S.hp,a_bounds,
    q_nonneg _ _ _ _ _ _ x.S.hy x.S.hc0 x.S.hγ.le (FixedParameters.positive qR).le⟩
 theorem prepareData_view (x : Input) : prepareData qR x.raw=(x.prepared qR).raw := by
  unfold prepareData
  rw [qData_view]
  change ((targetsData (supplierView x.S),_),flagsData (supplierView x.S))=_
  rw [targetsData_view,flagsData_view]
  rfl
noncomputable def preparedInputProgram : PolyProgram Input.encode SparsePrepared.Program.Input.encode (Input.prepared qR) :=
  (prepareData_poly qR).program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (prepareData_view qR x))

theorem countsData_view (x : Input) (z : SparseSignedPreparation.State x.n (size x.f x.n) × SparseCounts.Table x.f x.n) :
    countsData qR (x.raw,SparsePrepared.Program.view z)=List.ofFn (counts x.S.y x.S.P x.S.A x.S.c x.S.γ qR.g z) := by
  change _=List.ofFn (fun e => Sum.elim _ _ (physicalIndex e))
  rw [ofFn_physical]
  simp only [countsData,Input.raw,supplierView,indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,SparsePrepared.Program.view,
    SparseSignedPreparation.Program.view,SparseCounts.ListOperation.view]
  congr 1
  congr 1
  funext i
  have hq := qData_view qR x
  change (⌊(qData qR x.raw)[i.val]?.getD 0⌋₊+if 0<(z.1.1.toList)[i.val]?.getD 0 then 1 else 0)=_
  rw [hq]
  simp only [SparseOuterLaw.outsideCount,SparseGridRounding.base,index_inl,List.getElem?_ofFn,
    dite_eq_left (show i.val < size x.f x.n from lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)),
    Option.getD_some,Vector.getElem?_toList,Vector.getElem?_eq_getElem (show i.val < size x.f x.n from lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)),
    RationalWeightedStep.point]
  rfl

end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierScanProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
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
def ScanInput.raw (x : ScanInput) : ScanRaw := (supplierView x.S,((List.ofFn (fun i => List.ofFn (x.df i)),List.ofFn (fun c => List.ofFn (x.dc c))),x.budget))
abbrev ScanInput.encode (x : ScanInput) := enc x.raw
def ScanInput.scan (x : ScanInput) : FixedBatch.RationalParameters.PreparedScanProgram.Input :=
  ⟨x.f+x.n*x.f,x.f,x.j,x.df,x.dc,original,x.S.tables qR,x.budget⟩
 theorem originals_view {f n : ℕ} (S : Data f n) : originals (supplierView S)=List.ofFn (fun i => (original (f:=f) (n:=n) i).val) := by
  rw [show (fun e => (original (f:=f) (n:=n) e).val)=(fun e => Sum.elim (fun i : Fin f => i.val) (fun ti : Fin n × Fin f => ti.2.val) (physicalIndex e)) by
    funext e; unfold original; cases physicalIndex e <;> rfl]
  rw [ofFn_physical]
  simp only [originals,supplierView,indices,List.length_ofFn,RoundingList.range_finRange,List.flatMap_def,List.map_ofFn]
  rw [← List.ofFn_eq_map]
  simp [Function.comp_def]

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
-- module Solutions.OAIQ053_KM.KMedian_Programs_UnitScanProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
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
def Input.raw (x : Input) : Raw := (view x.U,x.B)
abbrev Input.encode (x : Input) := enc x.raw
end MetricKMedian.Preparation.RationalUnitInput.ScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalScanProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

def Input.unit (z : Input) : RationalUnitInput.ScanProgram.Input :=
  letI := z.metric
  ⟨count z.a z.k z.ha z.hj z.dc,z.j,z.m,z.toInput.unit.U,z.metric,
    realization z.a z.k z.ha z.hj z.dc z.dd z.df z.hdc z.hdd z.hds z.facility z.client z.hdf z.hc z.hcc,z.B⟩
attribute [local irreducible] RationalUnitInput.ScanProgram.Input.result
variable {η τ : ℝ} (p : RationalAllParameters η τ)
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
end MetricKMedian.Preparation.FractionalRefinement.ScanProgram
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
end MetricKMedian.InstanceProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceRoundProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
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
end MetricKMedian.InstanceProgram
end

end OAI
end


