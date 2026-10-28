-- Prove2me | Definitions.Def_OAIQ035K050
-- name    : OAIQ035K050
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:07:27.010988+00:00
-- url     : https://prove2.me/theorems/c7834da2-9df7-4e60-8f47-67a5c1541024
-- title:
--   Definitions bundle OAIQ035K050 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 105 declarations of OpenAI's Lean: 51 definitions and 54 theorems. The definitions and types are `OAI.MetricKMedian.Binary.IntegerList.numeratorsProgram`, `OAI.MetricKMedian.Binary.IntegerList.sumProgram`, `OAI.MetricKMedian.Binary.PolyProgram.listAllWith`, `OAI.MetricKMedian.Completion.Rational.BestProgram.annotate`, `OAI.MetricKMedian.Completion.Rational.BestProgram.card`, `OAI.MetricKMedian.Completion.Rational.BestProgram.good`, `OAI.MetricKMedian.Completion.Rational.BestProgram.raw`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.Raw`, `OAI.MetricKMedian.Completion.Rational.PackingProgram.stepRaw`, `OAI.MetricKMedian.Completion.Rational.ScoreProgram.raw`, `OAI.MetricKMedian.MaskProgram.get`, `OAI.MetricKMedian.MaskProgram.intersect`, `OAI.MetricKMedian.MaskProgram.nearest`, `OAI.MetricKMedian.MaskProgram.selectedValues`, `OAI.MetricKMedian.RationalBatchData.ActionArrays.Raw`, `OAI.MetricKMedian.RationalBatchData.ActionArrays.bal`, `OAI.MetricKMedian.RationalBatchData.ActionArrays.bias`, `OAI.MetricKMedian.RationalBatchData.ActionArrays.conflict`, `OAI.MetricKMedian.RationalBatchData.ActionArrays.data`, `OAI.MetricKMedian.RationalBatchData.ActionArrays.erase`, `OAI.MetricKMedian.RationalBatchData.ActionArrays.overlap`, `OAI.MetricKMedian.RationalBatchData.ActionList.Raw`, `OAI.MetricKMedian.RationalBatchData.ActionList.codes`, `OAI.MetricKMedian.RationalBatchData.ActionList.units`, `OAI.MetricKMedian.RationalBatchData.ActionList.valid`, `OAI.MetricKMedian.RationalBatchData.ActionTransition.Raw`, `OAI.MetricKMedian.RationalBatchData.ActionTransition.dead`, `OAI.MetricKMedian.RationalBatchData.ActionTransition.selected`, `OAI.MetricKMedian.RationalBatchData.ActionTransition.sources`, `OAI.MetricKMedian.RationalBatchData.GraphData.Raw`, `OAI.MetricKMedian.RationalBatchData.GraphData.data`, `OAI.MetricKMedian.RationalBatchData.GraphData.heavy`, `OAI.MetricKMedian.RationalBatchData.GraphData.masses`, `OAI.MetricKMedian.RationalBatchData.GraphData.prepare`, `OAI.MetricKMedian.RationalBatchData.GraphData.transpose`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.Raw`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyList.active`, `OAI.MetricKMedian.RoundingProgram.Row`, `OAI.MetricKMedian.SparseBernoulli.ListOperation.tests`, `OAI.MetricKMedian.SparseGraph.ListOperation.dimensions` and 11 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Binary_BinaryListExtras`, `KMedian_Compression_IntegerListProgram`, `KMedian_Geometry_GraphListOperations`, `KMedian_Probability_BernoulliListOperations`, `KMedian_Process_ActionTransitionList`, `KMedian_Process_BatchActionArrays`, `KMedian_Process_BatchActionList`, `KMedian_Process_BatchGraphData`, `KMedian_Process_CopyGraphProgram`, `KMedian_Process_CopyListEncoding`, `KMedian_Process_PhysicalBatchList`, `KMedian_Process_RoundingUniformStep`, `KMedian_Programs_FinsetMaskProgram`, `KMedian_Programs_GreedyPackingProgram`, `KMedian_Programs_MaskBestProgram`, `KMedian_Programs_ScoreProgram`, `KMedian_Programs_TaggedBestProgram`.
--
--   **Imports.** It imports the bundles `OAIQ035K046` and `OAIQ035K047` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K054`, `OAIQ035K055`, `OAIQ035K056`, `OAIQ035K057` and `OAIQ035K062`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K046
import Definitions.Def_OAIQ035K047

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
noncomputable def listAllWith {p : γ × α → Bool} (P : PolyProgram (encodePair ec ea) encodeBool p) (a0 : α) :
    PolyProgram (encodePair ec (encodeList ea)) encodeBool (fun x => x.2.all (fun a => p (x.1,a))) :=
  ((P.listMapWith a0 false).comp (listAll (identity encodeBool) false)).congr _ (fun x => by simp only [Function.comp_apply,List.all_map,Function.id_comp])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_IntegerListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary
open PolyProgram Function
namespace IntegerList

noncomputable def sumProgram : PolyProgram er Signed.encode List.sum :=
  (((ratOfInt.listMap 0).comp ratSum).comp ratNum).congr _ (fun xs => by
    simp only [Function.comp_apply,← Int.cast_list_sum,Rat.num_intCast])
noncomputable def numeratorsProgram : PolyProgram (encodeList Ratio.encode) er numerators := by
  let mul := (exchange Ratio.encode Ratio.encode).comp ratMul
  let output := (((denominatorProgram.comp ratOfInt).fanout (identity (encodeList Ratio.encode))).comp ((mul.comp ratNum).listMapWith 0 0))
  exact output.congr _ (fun _ => rfl)

end IntegerList
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingUniformStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.RoundingList
open Binary Binary.Automatic Binary.Automatic.Poly

@[fun_prop] theorem features_poly : Poly features := by
  have h : Poly (fun p : Row => p.flatMap (fun x => p.map (fun y => x*y))) := by
    apply list_flatMap
    · apply list_map <;> fun_prop
    · fun_prop
  exact comp (f:=fun x : Row × Row => x.1++x.2)
    (g:=fun p : Row => (p,p.flatMap (fun x => p.map (fun y => x*y)))) list_append (pair identity h)
@[fun_prop] theorem dimensions_poly : Poly dimensions := by
  have h1 : Poly (fun p : Row => (indices p).map (fun _ => ())) := by
    apply list_map <;> fun_prop
  have h2 : Poly (fun p : Row => (square p).map (fun _ => ())) := by
    apply list_map <;> fun_prop
  exact comp (f:=fun x : List Unit × List Unit => x.1++x.2)
    (g:=fun p : Row => ((indices p).map (fun _ => ()),(square p).map (fun _ => ()))) list_append (pair h1 h2)

end MetricKMedian.RoundingList

namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse
abbrev Row := RoundingList.Row

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GraphListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGraph.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
@[fun_prop] theorem indices_poly {α : Type} [Coding α] [Inhabited α] : Poly (indices (α:=α)) := list_indices

def edges (x : List Unit × Table) : List ℚ :=
  (indices x.1).flatMap (fun h => x.2.map (fun col => if (col[h]?.getD false) then 1 else 0))
def featureList (x : List Unit × Table) : List ℚ := RoundingList.features (edges x)
def nextTable (x : (ℕ × Table) × Row) : Table :=
  (indices x.1.2).map (fun i => if i=x.1.1 then x.2 else x.1.2[i]?.getD [])
def dimensions (x : List Unit × List (SparseIntegerLaw.BinarySparse.Data Row)) : List Unit :=
  let bs := x.1.flatMap (fun _ => x.2.map (fun _ => (0:ℚ)))
  RoundingList.dimensions bs

@[fun_prop] theorem edges_poly : Poly edges := by
  unfold edges
  apply list_flatMap
  · apply list_map <;> fun_prop
  · fun_prop
@[fun_prop] theorem featureList_poly : Poly featureList := by unfold featureList; fun_prop
@[fun_prop] theorem nextTable_poly : Poly nextTable := by
  unfold nextTable
  apply list_map <;> fun_prop
@[fun_prop] theorem dimensions_poly : Poly dimensions := by
  unfold dimensions
  apply comp RoundingList.dimensions_poly
  apply list_flatMap
  · apply list_map <;> fun_prop
  · fun_prop

end MetricKMedian.SparseGraph.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.SparseBernoulli.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly

@[fun_prop] theorem units_poly (d : ℕ) : Poly (units d) := by
  induction d with
  | zero => exact const [()]
  | succ d ih =>
    change Poly (fun q => (false::q).flatMap (fun _ => units d q))
    apply list_flatMap
    · exact comp ih fst
    · fun_prop

@[simp] theorem units_length (d : ℕ) (q : Row) : (units d q).length=(q.length+1)^d := by
  induction d with
  | zero => simp [units]
  | succ d ih => simp [units,List.length_flatMap,ih,pow_succ,Nat.mul_comm]; ring

def tests (d : ℕ) (q : Row) (j : ℕ) : List Bool :=
  (List.range d).map (fun a => q[j/(q.length+1)^a%(q.length+1)]?.getD true)

end MetricKMedian.SparseBernoulli.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchActionList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.RationalBatchData.ActionList
open Binary Binary.Automatic Binary.Automatic.Poly FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)
abbrev Raw := Table × Row

def valid (x : Raw) (c : ℕ) : Bool :=
  if c<x.2.length then !(x.2[c]?.getD false)
  else (x.2[parent x.2.length c]?.getD false) &&
    ((x.1[parent x.2.length c]?.getD [])[child x.2.length c]?.getD false)
def units (x : Raw) : List Unit :=
  x.2.map (fun _ => ()) ++ x.2.flatMap (fun _ => x.2.map (fun _ => ()))
def codes (x : Raw) : List ℕ := (indices (units x)).filter (valid x)

@[fun_prop] theorem parent_poly : Poly (fun x : ℕ × ℕ => parent x.1 x.2) := by unfold parent; fun_prop
@[fun_prop] theorem child_poly : Poly (fun x : ℕ × ℕ => child x.1 x.2) := by unfold child; fun_prop
@[fun_prop] theorem valid_poly : Poly (fun x : Raw × ℕ => valid x.1 x.2) := by unfold valid; fun_prop
@[fun_prop] theorem units_poly : Poly units := by
  unfold units
  apply comp (g:=fun x : Raw => (x.2.map (fun _ => ()),x.2.flatMap (fun _ => x.2.map (fun _ => ())))) Poly.list_append
  apply Poly.pair
  · apply list_map <;> fun_prop
  · apply list_flatMap
    · apply list_map <;> fun_prop
    · fun_prop
@[fun_prop] theorem codes_poly : Poly codes := by unfold codes; apply list_filter <;> fun_prop

end MetricKMedian.RationalBatchData.ActionList
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalBatchList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.SparsePhysicalBatch.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table er et indices)

abbrev Raw := (Row × Table) × (ℚ × List ℚ)

def conflictFree (x : Table × Row) (e : ℕ) : Bool :=
  ((indices x.2).map (fun f => !(x.1[e]?.getD [])[f]?.getD false || !(x.2[f]?.getD false))).all id

def select (bal : Bool) (x : Raw × Row) : Row :=
  (indices x.2).map (fun e =>
    if bal then x.2[e]?.getD false && conflictFree (x.1.1.2,x.2) e && (x.1.1.1[e]?.getD false)
    else x.2[e]?.getD false && !(x.1.1.1[e]?.getD false))

@[fun_prop] theorem conflictFree_poly : Poly (fun x : (Table × Row) × ℕ => conflictFree x.1 x.2) := by
  unfold conflictFree
  apply comp bool_all
  apply list_map <;> fun_prop
@[fun_prop] theorem select_poly (bal : Bool) : Poly (select bal) := by
  unfold select
  apply list_map <;> fun_prop

end MetricKMedian.SparsePhysicalBatch.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchActionArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.RationalBatchData.ActionArrays
open Binary Binary.Automatic Binary.Automatic.Poly FixedBatch Finset
open SparseGraph.ListOperation (Row Table setView indices)

def erase (x : ActionList.Raw) (c : ℕ) : Row :=
  if c<x.2.length then x.1[c]?.getD []
  else (indices x.2).map (fun i => decide (i=ActionList.child x.2.length c))
def bal (x : ActionList.Raw × ℕ) (c : ℕ) : Bool :=
  decide (c<x.1.2.length) && decide (((erase x.1 c).filter id).length=x.2)
def overlap (a b : Row) : Bool :=
  ((indices a).map (fun i => a[i]?.getD false && b[i]?.getD false)).any id
def conflict (x : ActionList.Raw × ℕ) (e f : ℕ) : Bool :=
  bal x e && bal x f && !(decide (f=e)) && overlap (erase x.1 e) (erase x.1 f)
def bias (x : ((ℚ × ℚ) × List ℚ) × ℕ) (c : ℕ) : ℚ :=
  if 1<(x.1.2[ActionList.parent x.2 c]?.getD 0) then (1+x.1.1.2)*x.1.1.1 else x.1.1.1

@[fun_prop] theorem erase_poly : Poly (fun x : ActionList.Raw × ℕ => erase x.1 x.2) := by
  unfold erase
  have hm : Poly (fun x : ActionList.Raw × ℕ => (indices x.1.2).map (fun i => decide (i=ActionList.child x.1.2.length x.2))) := by
    apply list_map <;> fun_prop
  fun_prop
@[fun_prop] theorem bal_poly : Poly (fun x : (ActionList.Raw × ℕ) × ℕ => bal x.1 x.2) := by
  unfold bal
  have hm : Poly (fun x : (ActionList.Raw × ℕ) × ℕ => (erase x.1.1 x.2).filter id) := by
    apply list_filter <;> fun_prop
  fun_prop
@[fun_prop] theorem overlap_poly : Poly (fun x : Row × Row => overlap x.1 x.2) := by
  unfold overlap
  apply comp bool_any
  apply list_map <;> fun_prop
@[fun_prop] theorem conflict_poly : Poly (fun x : ((ActionList.Raw × ℕ) × ℕ) × ℕ => conflict x.1.1 x.1.2 x.2) := by
  unfold conflict; fun_prop
@[fun_prop] theorem bias_poly : Poly (fun x : (((ℚ × ℚ) × List ℚ) × ℕ) × ℕ => bias x.1 x.2) := by
  unfold bias; fun_prop

abbrev Raw := (((ℚ × ℚ) × List ℚ) × ℕ) × ActionList.Raw

def data (x : Raw) : SparsePhysicalBatch.ListOperation.Raw :=
  (((ActionList.codes x.2).map (bal (x.2,x.1.2)),
    (ActionList.codes x.2).map (fun e => (ActionList.codes x.2).map (conflict (x.2,x.1.2) e))),
    (x.1.1.1.1,(ActionList.codes x.2).map (bias (x.1.1,x.2.2.length))))
@[fun_prop] theorem data_poly : Poly data := by
  unfold data
  apply pair
  · apply pair
    · apply list_map <;> fun_prop
    · apply list_map
      · apply list_map
        · exact comp (g:=fun x : (Raw × ℕ) × ℕ => (((x.1.1.2,x.1.1.1.2),x.1.2),x.2)) conflict_poly (by fun_prop)
        · fun_prop
      · fun_prop
  · apply pair
    · fun_prop
    · apply list_map <;> fun_prop

end MetricKMedian.RationalBatchData.ActionArrays

end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchGraphData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.RationalBatchData.GraphData
open Binary Binary.Automatic Binary.Automatic.Poly FixedBatch Finset
open SparseGraph.ListOperation (Row Table setView indices view)

def transpose (G : Table) : Table := (indices G).map (fun h => G.map (fun col => col[h]?.getD false))
def masses (x : ℚ × Table) : List ℚ := (transpose x.2).map (fun row => x.1*((row.filter id).length:ℚ))
def heavy (x : ℚ × List ℚ) : Row := x.2.map (fun q => decide (max 1 (x.1*amount x.2)<q))
abbrev Raw := ((ℚ × ℚ) × (ℕ × (ℚ × ℚ))) × Table
def prepare (x : Raw) : ActionArrays.Raw :=
  (((x.1.2.2,masses (x.1.1.1,x.2)),x.1.2.1),
    (transpose x.2,heavy (x.1.1.2,masses (x.1.1.1,x.2))))
def data (x : Raw) : SparsePhysicalBatch.ListOperation.Raw := ActionArrays.data (prepare x)

@[fun_prop] theorem transpose_poly : Poly transpose := by
  unfold transpose
  apply list_map
  · apply list_map <;> fun_prop
  · fun_prop
@[fun_prop] theorem masses_poly : Poly masses := by
  unfold masses
  apply list_map
  · have hf : Poly (fun x : (ℚ × Table) × Row => x.2.filter id) := by apply list_filter <;> fun_prop
    fun_prop
  · fun_prop
@[fun_prop] theorem amount_poly : Poly amount := by
  unfold amount
  apply comp rat_sum
  apply list_map <;> fun_prop
@[fun_prop] theorem heavy_poly : Poly heavy := by unfold heavy; apply list_map <;> fun_prop
@[fun_prop] theorem prepare_poly : Poly prepare := by unfold prepare; fun_prop
@[fun_prop] theorem data_poly : Poly data := by unfold data; fun_prop

end MetricKMedian.RationalBatchData.GraphData
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_ActionTransitionList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalBatchData.ActionTransition
open Binary Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)

abbrev Raw := ActionList.Raw × Row

def selected (x : Raw) : List ℕ := (((ActionList.codes x.1).zip x.2).filter Prod.snd).map Prod.fst
def dead (x : Raw) : Row := (indices x.1.2).map fun i =>
  ((selected x).map fun c => (ActionArrays.erase x.1 c)[i]?.getD false).any id
def sources (x : Raw) : Row := (indices x.1.2).map fun i =>
  x.1.2[i]?.getD false || natMember (selected x,i)

@[fun_prop] theorem selected_poly : Poly selected := by
  unfold selected
  apply list_map
  · fun_prop
  · apply list_filter <;> fun_prop
@[fun_prop] theorem dead_poly : Poly dead := by
  unfold dead
  apply list_map
  · apply comp bool_any
    apply list_map <;> fun_prop
  · fun_prop
@[fun_prop] theorem sources_poly : Poly sources := by
  unfold sources
  apply list_map <;> fun_prop

end MetricKMedian.RationalBatchData.ActionTransition
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyListEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyList
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
variable {f Δ : ℕ}
def active (A : Row) : List ℕ := (indices A).filter (fun i => A[i]?.getD false)
@[fun_prop] theorem active_poly : Poly active := by unfold active; apply list_filter <;> fun_prop

end MetricKMedian.RationalPhysicalKernel.CopyList
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open CopyList

abbrev Raw := (((ℚ × ℚ) × ℕ) × List (List ℚ)) × Row

end MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_FinsetMaskProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.MaskProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)

abbrev get (r : Row) (i : ℕ) : Bool := r[i]?.getD false
@[simp] theorem get_view {n : ℕ} (s : Finset (Fin n)) (i : Fin n) : get (setView s) i=decide (i∈s) := by
  simp only [get,setView,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta]

def intersect (x : Row × Row) : Bool := (x.1.zip x.2).any (fun z => z.1 && z.2)
@[fun_prop] theorem intersect_poly : Poly intersect := by
  unfold intersect
  have h : Poly (fun x : Row × Row => (x.1.zip x.2).map (fun z => z.1 && z.2)) := by
    apply list_map <;> fun_prop
  simpa only [List.any_map,Function.comp_def,id_eq] using (comp bool_any h)

def selectedValues (x : List ℚ × Row) : List ℚ :=
  ((indices x.2).filter (fun i => get x.2 i)).map (fun i => x.1[i]?.getD 0)
def nearest (x : List ℚ × Row) : ℕ :=
  (indices x.2).findIdx (fun i => get x.2 i && decide (x.1[i]?.getD 0=LPBinary.minimum (selectedValues x)))
@[fun_prop] theorem selectedValues_poly : Poly selectedValues := by
  unfold selectedValues
  apply list_map
  · fun_prop
  · apply list_filter <;> fun_prop
@[fun_prop] theorem nearest_poly : Poly nearest := by
  unfold nearest
  have hm : Poly LPBinary.minimum := ⟨LPBinary.Program.minimumProgram⟩
  apply list_findIdx <;> fun_prop
 theorem selectedValues_mem {n : ℕ} (R : Fin n → ℚ) (U : Finset (Fin n)) (q : ℚ) :
    q∈selectedValues (List.ofFn R,setView U) ↔ q∈U.image R := by
  simp only [selectedValues,indices,setView,List.length_ofFn,List.mem_map,List.mem_filter,List.mem_range,mem_image]
  constructor
  · rintro ⟨i,⟨hi,hu⟩,he⟩
    have hu' : (⟨i,hi⟩ : Fin n)∈U := by
      simpa only [get,List.getElem?_ofFn,dite_eq_left hi,Option.getD_some,decide_eq_true_eq] using hu
    have he' : R ⟨i,hi⟩=q := by simpa only [List.getElem?_ofFn,dite_eq_left hi,Option.getD_some] using he
    exact ⟨⟨i,hi⟩,hu',he'⟩
  · rintro ⟨i,hi,rfl⟩
    refine ⟨i.val,⟨i.isLt,?_⟩,?_⟩
    · simpa only [get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,decide_eq_true_eq] using hi
    · simp only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta]
end MetricKMedian.MaskProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_GreedyPackingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Completion.Rational.PackingProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram

abbrev Raw := (List ℚ × Table) × Row

def stepRaw (x : Raw × (Row × Row)) : Raw × (Row × Row) :=
  if x.2.1.any id then
    let c := MaskProgram.nearest (x.1.1.1,x.2.1)
    (x.1,((indices x.2.1).map (fun i => MaskProgram.get x.2.1 i &&
      !intersect (x.1.1.2[c]?.getD [],x.1.1.2[i]?.getD [])),
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
 theorem any_view {n : ℕ} (U : Finset (Fin n)) : (setView U).any id=decide U.Nonempty := by
  apply Bool.eq_iff_iff.mpr
  simp only [setView,List.any_eq_true,List.mem_ofFn,id_eq,decide_eq_true_eq]
  constructor
  · rintro ⟨b,⟨i,rfl⟩,hi⟩; exact ⟨i,of_decide_eq_true hi⟩
  · rintro ⟨i,hi⟩; exact ⟨_,⟨i,rfl⟩,decide_eq_true hi⟩

end MetricKMedian.Completion.Rational.PackingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_ScoreProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section
namespace MetricKMedian.Completion.Rational.ScoreProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row setView)
def raw (x : List (List ℚ) × Row) : ℚ :=
  (x.1.map (fun d => LPBinary.minimum (MaskProgram.selectedValues (d,x.2)))).sum
@[fun_prop] theorem raw_poly : Poly raw := by
  have hm : Poly LPBinary.minimum := ⟨LPBinary.Program.minimumProgram⟩
  unfold raw
  apply comp rat_sum
  apply list_map <;> fun_prop
 theorem raw_score {j f : ℕ} (d : Fin j → Fin f → ℚ) (O : Finset (Fin f)) :
    raw (List.ofFn (fun c => List.ofFn (d c)),setView O)=score d O := by
  unfold raw score
  rw [List.map_ofFn,List.sum_ofFn]
  apply sum_congr rfl
  intro c _
  dsimp only [Function.comp_def]
  by_cases h : O.Nonempty
  · rw [dite_eq_left h]
    exact LPBinary.minimum_eq_finset _ _ (h.image _) (MaskProgram.selectedValues_mem (d c) O)
  · rw [dite_eq_right h]
    have he : MaskProgram.selectedValues (List.ofFn (d c),setView O)=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro q hq
      obtain ⟨i,hi,_⟩ := mem_image.mp ((MaskProgram.selectedValues_mem (d c) O q).mp hq)
      exact h ⟨i,hi⟩
    rw [he]
    rfl
end MetricKMedian.Completion.Rational.ScoreProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_TaggedBestProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.SparseSelect
namespace TaggedProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table)
abbrev Tag := Bool × (ℚ × Row)
def choose (x : Tag × Tag) : Bool := x.2.1 && (!x.1.1 || decide (x.2.2.1≤x.1.2.1))
@[fun_prop] theorem choose_poly : Poly choose := by unfold choose; fun_prop
def decoder (a : Tag) : Option Tag := if a.1 then some a else none
def folded (L : List Tag) : Tag := L.reverse.foldl (fun b a => if choose (b,a) then a else b) (false,(0,[]))
@[fun_prop] theorem folded_poly : Poly folded := by
  let dummy : Tag := (false,(0,[]))
  exact ⟨((listReverse enc dummy).fanout (constant (encodeList enc) enc dummy)).comp
    (listChoose choose_poly.program dummy)⟩
 theorem decode_step (a b : Tag) :
    decoder (if choose (b,a) then a else b)=
      (if a.1 then match decoder b with
        | none => some a
        | some c => some (if a.2.1 ≤ c.2.1 then a else c)
       else decoder b) := by
  obtain ⟨pa,ca,a⟩ := a
  obtain ⟨pb,cb,b⟩ := b
  cases pa <;> cases pb <;> by_cases h : ca ≤ cb <;> simp [decoder,choose,h]
 theorem folded_best (L : List Tag) : decoder (folded L)=best Prod.fst (fun a => a.2.1) L := by
  unfold folded
  rw [← List.foldr_eq_foldl_reverse]
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldr_cons,decode_step,ih]
    cases ha : a.1 <;> cases hb : best Prod.fst (fun a => a.2.1) L <;> simp [best,ha,hb]

def raw (L : List Tag) : List Row := if (folded L).1 then [(folded L).2.2] else []
@[fun_prop] theorem raw_poly : Poly raw := by unfold raw; fun_prop
 theorem raw_best (L : List Tag) :
    raw L=((best Prod.fst (fun a => a.2.1) L).map (fun a => a.2.2)).toList := by
  rw [← folded_best]
  unfold raw decoder
  split <;> rfl
end TaggedProgram

end MetricKMedian.SparseSelect
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_MaskBestProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Completion.Rational.BestProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
def card (O : Row) : ℕ := (O.filter id).length
@[fun_prop] theorem card_poly : Poly card := by unfold card; fun_prop
 theorem card_view {f : ℕ} (O : Finset (Fin f)) : card (setView O)=O.card := by
  exact EncodingLists.bool_card O

def good (x : ℚ × Row) : Bool := x.2.any id && decide ((card x.2:ℚ)≤x.1)
@[fun_prop] theorem good_poly : Poly good := by unfold good; fun_prop
 theorem good_view {f : ℕ} (B : ℚ) (O : Finset (Fin f)) :
    good (B,setView O)=decide (O.Nonempty ∧ (O.card:ℚ)≤B) := by
  simp only [good,PackingProgram.any_view,card_view,Bool.decide_and]

def annotate (x : (ℚ × List (List ℚ)) × Table) : List SparseSelect.TaggedProgram.Tag :=
  x.2.map (fun O => (good (x.1.1,O),(ScoreProgram.raw (x.1.2,O),O)))
@[fun_prop] theorem annotate_poly : Poly annotate := by unfold annotate; apply list_map <;> fun_prop

def raw (x : (ℚ × List (List ℚ)) × Table) : Table := SparseSelect.TaggedProgram.raw (annotate x)
@[fun_prop] theorem raw_poly : Poly raw := by unfold raw; fun_prop
 theorem raw_best {f j : ℕ} (B : ℚ) (d : Fin j → Fin f → ℚ) (L : List (Finset (Fin f))) :
    raw ((B,List.ofFn (fun c => List.ofFn (d c))),L.map setView)=
      ((SparseSelect.best (fun O => decide (O.Nonempty ∧ (O.card:ℚ)≤B)) (score d) L).map setView).toList := by
  let ann := fun O : Finset (Fin f) => (decide (O.Nonempty ∧ (O.card:ℚ)≤B),(score d O,setView O))
  have ha : annotate ((B,List.ofFn (fun c => List.ofFn (d c))),L.map setView)=L.map ann := by
    simp only [annotate,List.map_map,Function.comp_def,good_view,ScoreProgram.raw_score]
    rfl
  unfold raw
  rw [ha,SparseSelect.TaggedProgram.raw_best]
  rw [← SparseSelect.best_map (fun O => decide (O.Nonempty ∧ (O.card:ℚ)≤B)) (score d)
    Prod.fst (fun a => a.2.1) ann (fun _ => rfl) (fun _ => rfl)]
  simp only [Option.map_map]
  rfl
end MetricKMedian.Completion.Rational.BestProgram
end

end OAI
end


