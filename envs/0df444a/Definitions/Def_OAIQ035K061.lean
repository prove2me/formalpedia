-- Prove2me | Definitions.Def_OAIQ035K061
-- name    : OAIQ035K061
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:14:54.270405+00:00
-- url     : https://prove2.me/theorems/9faab3e3-77f5-4055-befe-993eeef5ed1d
-- title:
--   Definitions bundle OAIQ035K061 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 83 declarations of OpenAI's Lean: 42 definitions and 41 theorems. The definitions and types are `OAI.MetricKMedian.InputParser.Header`, `OAI.MetricKMedian.InputParser.header`, `OAI.MetricKMedian.InputParser.matrix`, `OAI.MetricKMedian.InputParser.matrixProgram`, `OAI.MetricKMedian.InputParser.raw`, `OAI.MetricKMedian.InputParser.rawProgram`, `OAI.MetricKMedian.InputParser.reshape`, `OAI.MetricKMedian.InputParser.squareUnits`, `OAI.MetricKMedian.InstanceProgram.Raw`, `OAI.MetricKMedian.InstanceProgram.dcData`, `OAI.MetricKMedian.InstanceProgram.ddData`, `OAI.MetricKMedian.InstanceProgram.dfData`, `OAI.MetricKMedian.InstanceProgram.encode`, `OAI.MetricKMedian.InstanceProgram.fractionalData`, `OAI.MetricKMedian.InstanceProgram.lpData`, `OAI.MetricKMedian.InstanceProgram.nzEncode`, `OAI.MetricKMedian.InstanceProgram.subsetRaw`, `OAI.MetricKMedian.InstanceProgram.view`, `OAI.MetricKMedian.Preparation.FractionalRefinement.Program.splitData`, `OAI.MetricKMedian.Preparation.FractionalRefinement.Program.unitData`, `OAI.MetricKMedian.Preparation.RationalSplitting.Program.assignedData`, `OAI.MetricKMedian.Preparation.RationalSplitting.Program.cutsData`, `OAI.MetricKMedian.Preparation.RationalSplitting.Program.originalData`, `OAI.MetricKMedian.Preparation.RationalSplitting.Program.piecesData`, `OAI.MetricKMedian.Preparation.RationalSplitting.Program.previousData`, `OAI.MetricKMedian.Preparation.RationalSplitting.Program.weightsData`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.pairWeight`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.weightsData`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.geometryData`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.ranks`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.repData`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.suppliersData`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.values`, `OAI.MetricKMedian.RationalSortProgram.foldProgram`, `OAI.MetricKMedian.RationalSortProgram.sort`, `OAI.MetricKMedian.SparseBernoulli.Program.activeProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.dimensionsProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.featuresProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.startProgram`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.branchProgram` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Binary_InstanceParserProgram`, `KMedian_Optimization_FractionalInputProgram`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Probability_BernoulliListOperations`, `KMedian_Probability_BernoulliRunHeight`, `KMedian_Probability_BernoulliRunProgram`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_PhysicalBatchProgram`, `KMedian_Programs_DependentSparseProgram`, `KMedian_Programs_InstanceDataProgram`, `KMedian_Programs_InstanceZeroProgram`, `KMedian_Programs_RationalSortProgram`, `KMedian_Programs_SplitListProgram`, `KMedian_Programs_UnitGeometryProgram`, `KMedian_Programs_UnitRepresentativeProgram`, `KMedian_Rounding_GridRoundingProgram`, `KMedian_Sparse_SparseMixProgram`, `KMedian_Sparse_SparseTable`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K054`, `OAIQ035K055`, `OAIQ035K056` and `OAIQ035K057` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K065`, `OAIQ035K066`, `OAIQ035K067` and `OAIQ035K068`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K054
import Definitions.Def_OAIQ035K055
import Definitions.Def_OAIQ035K056
import Definitions.Def_OAIQ035K057

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
def pairWeight (x : SupplierRaw) (s t : ℕ) : ℚ :=
  ((indices x.1).map (fun i => if ((x.2.2.1[s]?.getD [])[i]?.getD false) &&
    ((x.2.1[t]?.getD [])[i]?.getD false) then x.1[i]?.getD 0 else 0)).sum
def weightsData (x : SupplierRaw) : QRow :=
  ((indices x.1).map (fun i => if outsideData x i then x.1[i]?.getD 0 else 0)) ++
  (((indices x.2.2.2.1).flatMap (fun s => (indices x.2.2.2.1).map (fun t => pairWeight x s t))) ++
    x.2.2.2.2.1.map (fun c => x.2.2.2.2.2*c))
@[fun_prop] theorem pairWeight_poly : Poly (fun x : SupplierRaw × (ℕ × ℕ) => pairWeight x.1 x.2.1 x.2.2) := by
  unfold pairWeight; apply comp rat_sum; apply list_map <;> fun_prop
@[fun_prop] theorem weightsData_poly : Poly weightsData := by
  unfold weightsData; apply append_poly
  · apply list_map <;> fun_prop
  · apply append_poly
    · apply list_flatMap
      · apply list_map <;> fun_prop
      · fun_prop
    · apply list_map <;> fun_prop

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

@[fun_prop] theorem insertData_poly : Poly insertData := by
  unfold insertData
  apply Preparation.RationalSuppliers.Program.append_poly
  · apply list_filter <;> fun_prop
  · have hf : Poly (fun x : List ℚ × ℚ => x.1.filter (fun a => decide (x.2<a))) := by apply list_filter <;> fun_prop
    exact comp list_cons (pair (by fun_prop) hf)
 theorem insertData_length (xs : List ℚ) (a : ℚ) :
    (enc (insertData (xs,a))).length≤(enc xs).length+1*(2*(enc a).length+1) := by
  have hh := filters_length Ratio.encode (fun q : ℚ => decide (q<a)) (fun q => decide (a<q))
    (fun q h => (lt_asymm (of_decide_eq_true h.1) (of_decide_eq_true h.2))) xs
  simp only [insertData,enc,Coding.encode,EncodedList.append,List.length_append,EncodedList.cons_length,one_mul]
  change (encodeList Ratio.encode _).length+ (2*(Ratio.encode _).length+1+(encodeList Ratio.encode _).length)≤_
  omega

def sort (xs : List ℚ) : List ℚ := xs.foldl (fun s a => insertData (s,a)) []
noncomputable def foldProgram : PolyProgram (enc : List ℚ × List ℚ → List Bool) enc
    (fun x => x.1.foldl (fun s a => insertData (s,a)) x.2) :=
  insertData_poly.program.listFoldLinear 0 1 insertData_length
@[fun_prop] theorem sort_poly : Poly sort := by
  refine ⟨(((identity enc).fanout (constant enc enc ([] : List ℚ))).comp foldProgram).congr _ (fun _ => rfl)⟩

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
def cutsData (x : Raw × ℕ) : List ℚ :=
  RationalSortProgram.sort ((x.1.1[x.2]?.getD 0 :: x.1.2.map (fun r => r[x.2]?.getD 0)).filter (fun q => decide (0<q)))
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
abbrev Raw := (Row × Row) × (ℕ × Matrix)
def view (I : Instance) : Raw :=
  ((setView I.clients,setView I.facilities),(I.k,List.ofFn (fun i => List.ofFn (I.distance i))))
abbrev encode (I : Instance) := enc (view I)
def dcData (x : Raw) : Matrix := (pickRows (x.2.2,ranks x.1.1)).map (fun d => pullback (d,ranks x.1.2))
@[fun_prop] theorem dcData_poly : Poly dcData := by unfold dcData; apply list_map <;> fun_prop
def ddData (x : Raw) : Matrix := pullbackMatrix (x.2.2,ranks x.1.1)
def dfData (x : Raw) : Matrix := pullbackMatrix (x.2.2,ranks x.1.2)
@[fun_prop] theorem ddData_poly : Poly ddData := by unfold ddData; fun_prop
@[fun_prop] theorem dfData_poly : Poly dfData := by unfold dfData; fun_prop
abbrev nzEncode (I : Nonzero) := encode I.val
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
@[fun_prop] theorem take_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → ℕ} {g : α → List β} (hf : Poly f) (hg : Poly g) : Poly (fun x => (g x).take (f x)) :=
  comp list_take (pair hg hf)
@[fun_prop] theorem drop_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → ℕ} {g : α → List β} (hf : Poly f) (hg : Poly g) : Poly (fun x => (g x).drop (f x)) :=
  comp list_drop (pair hg hf)
def squareUnits (xs : Row) : List Unit := xs.flatMap (fun _ => xs.map (fun _ => ()))
@[fun_prop] theorem squareUnits_poly : Poly squareUnits := by unfold squareUnits; apply list_flatMap; apply list_map <;> fun_prop; fun_prop
 theorem squareUnits_length (xs : Row) : (squareUnits xs).length=xs.length*xs.length := by
  simp only [squareUnits,List.length_flatMap,List.length_map]
  rw [List.map_const',List.sum_replicate]
  simp only [smul_eq_mul]
def reshape (x : Row × List ℚ) : InstanceProgram.Matrix :=
  (indices x.1).map (fun i => (indices x.1).map (fun j => x.2[i*x.1.length+j]?.getD 0))
@[fun_prop] theorem reshape_poly : Poly reshape := by unfold reshape; apply list_map; apply list_map <;> fun_prop; fun_prop
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
def matrix (x : Row × List Bool) : InstanceProgram.Matrix :=
  reshape (x.1,(parse ratRead (squareUnits x.1,x.2)).1)
noncomputable def matrixProgram : PolyProgram enc enc matrix := by
  have hp : Poly (parse ratRead) := ⟨parseProgram ratRead ratRead_poly.program ratRead_rest_length⟩
  have h : Poly matrix := by unfold matrix; fun_prop
  exact h.program
 theorem matrix_encoded {n : ℕ} (S : Finset (Fin n)) (d : Fin n → Fin n → ℚ) (xs : List Bool) :
    matrix (setView S,((List.ofFn (fun i => List.ofFn (d i))).flatten.map encodeRat).flatten++xs)=
      List.ofFn (fun i => List.ofFn (d i)) := by
  unfold matrix
  have hu : squareUnits (setView S)=List.replicate (List.ofFn (fun i => List.ofFn (d i))).flatten.length () := by
    apply List.eq_replicate_iff.mpr
    refine ⟨?_,fun _ _ => rfl⟩
    rw [squareUnits_length,flatten_ofFn]
    simp only [setView,List.length_ofFn]
  rw [hu,parse_encoded ratRead encodeRat ratRead_append]
  exact reshape_flatten S d
abbrev Header := (Row × Row) × ℕ
def header (xs : List Bool) : Header × List Bool :=
  let a := natRead xs
  let b := natRead a.2
  (((b.2.take a.1,(b.2.drop a.1).take a.1),b.1),b.2.drop (a.1+a.1))
@[fun_prop] theorem header_poly : Poly header := by unfold header; fun_prop
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

def raw (xs : List Bool) : Raw :=
  let h := header xs
  (h.1.1,(h.1.2,matrix (h.1.1.1,h.2)))
noncomputable def rawProgram : PolyProgram enc enc raw := by
  have hm : Poly matrix := ⟨matrixProgram⟩
  exact (by unfold raw; fun_prop : Poly raw).program
end MetricKMedian.InputParser
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

 theorem tests_true_iff {n degree : ℕ} (q : Fin n → Bool) (j : Fin ((n+1)^degree)) :
    (tests degree (List.ofFn q) j.val).all id=true ↔ ∀ i∈used (finFunctionFinEquiv.symm j), q i=true := by
  simp only [tests,List.all_map,List.all_eq_true,Function.comp_def,id_eq,List.mem_range,List.length_ofFn]
  constructor
  · intro h i hi
    obtain ⟨a,ha⟩ := (Finset.mem_filter.mp hi).2
    apply (get_true_iff q _).mp (h a.val a.isLt) i
    exact ha
  · intro h a ha
    apply (get_true_iff q _).mpr
    intro i hi
    apply h i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨⟨a,ha⟩,hi⟩⟩

 theorem featureList_ofFn {n degree : ℕ} (q : Fin n → Bool) :
    featureList degree (List.ofFn q)=List.ofFn (features (d:=degree) q) := by
  apply List.ext_getElem
  · simp [featureList]
  · intro i hi hi'
    have hi'' : i<(n+1)^degree := by simpa [featureList] using hi
    simp only [featureList,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    unfold value features monomial
    rw [flag_product]
    congr 1
    exact propext (tests_true_iff q ⟨i,hi''⟩)

end MetricKMedian.SparseBernoulli.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliRunHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.SparseBernoulli
open Binary
variable {n d : ℕ}

theorem denominator_height (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (L : ℕ) (hL : ∀ i, HasHeight (p i) L) (t : ℕ) :
    (run (d:=d) p hp t).law.denominator ≤ (2:ℤ)^(stepHeight n d L*t) := by
  induction t with
  | zero => simp [run,SparseIntegerLaw.dirac]
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · rw [dite_eq_left ht]
      have h := SparseIntegerLaw.step_denominator_height (run (d:=d) p hp t) (features (d:=d))
        (fun _ => p ⟨t,ht⟩) (fun _ => hp ⟨t,ht⟩) (fun q b => endpoint q ⟨t,ht⟩ b)
        ((n+1)^d+1) L 0 (run_length p hp t) (fun _ => hL _) (fun _ _ _ => features_height _ _)
      apply h.trans
      calc
        _ ≤ (2:ℤ)^(stepHeight n d L*t)*(2:ℤ)^(stepHeight n d L) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
        _ = _ := by rw [← pow_add,Nat.mul_succ]
    · rw [dite_eq_right ht]
      exact ih.trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (Nat.le_succ t)))

end MetricKMedian.SparseBernoulli
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_DependentSparseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.SparseIntegerLaw.DependentProgram
open Binary Binary.PolyProgram Function BinarySparse
variable {C A : Type} (T : C → Type)

variable {T} (ec : C → List Bool) (ea : A → List Bool) (view : ∀ c, T c → A)

noncomputable def branchProgram (a0 : A) (p : ∀ c, T c → ℚ) (hp : ∀ c a, 0 ≤ p c a ∧ p c a ≤ 1)
    (next : ∀ c, T c → Fin 2 → T c)
    (P : C × A → ℚ) (E0 E1 : C × A → A)
    (hP : ∀ c a, P (c,view c a)=p c a)
    (hE0 : ∀ c a, E0 (c,view c a)=view c (next c a 0))
    (hE1 : ∀ c a, E1 (c,view c a)=view c (next c a 1))
    (PP : PolyProgram (encodePair ec ea) Ratio.encode P)
    (PE0 : PolyProgram (encodePair ec ea) ea E0) (PE1 : PolyProgram (encodePair ec ea) ea E1) :
    PolyProgram (Bundle.encode ec ea view) (Bundle.encode ec ea view) (Bundle.branch p hp next) := by
  let c := contextProgram ec ea view
  let states := statesProgram ec ea view
  let probs := (c.fanout states).comp (PP.listMapWith a0 0)
  let law := ((lawProgram ec ea view).fanout probs).comp branchLawProgram
  let endpoints := (PE0.fanout PE1).comp pairList
  let outputstates := (c.fanout states).comp (endpoints.listFlatMapWith a0 a0)
  let work := c.fanout (law.fanout outputstates)
  exact work.recode id (fun _ => rfl) (fun x => by
    exact congrArg (encodePair ec (ed ea)) (raw_branch view p hp next P E0 E1 hP hE0 hE1 x))

end MetricKMedian.SparseIntegerLaw.DependentProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram

noncomputable def dimensionsProgram (d : ℕ) : PolyProgram Context.encode IntegerLaw.BinaryCompression.es
    (fun c => List.replicate ((c.input.n+1)^d) ()) := by
  let raw : PolyProgram (encodePair qr Nat.bits) IntegerLaw.BinaryCompression.es
      (fun x : List ℚ × ℕ => ListOperation.units d (x.1.map (fun _ => false))) := by
    apply Binary.Automatic.Poly.program
    exact Binary.Automatic.Poly.comp (ListOperation.units_poly d) (by
      apply Binary.Automatic.Poly.list_map <;> fun_prop)
  exact raw.recode Context.raw (fun _ => rfl) (fun c => by
    simp only [ListOperation.units_eq,List.length_map,List.length_ofFn])
noncomputable def featuresProgram (d : ℕ) : PolyProgram (encodePair Context.encode er) IntegerLaw.BinaryCompression.eqr
    (fun x => ListOperation.featureList d x.2) :=
  (snd Context.encode er).comp (ListOperation.featureList_poly d).program

noncomputable def activeProgram : PolyProgram State.encode encodeBool
    (fun x : State => decide (x.ctx.t<x.ctx.input.n)) := by
  let raw : PolyProgram (encodePair qr Nat.bits) encodeBool
      (fun x : List ℚ × ℕ => decide (x.2<x.1.length)) := Binary.Automatic.Poly.program (by fun_prop)
  let ctx : PolyProgram Context.encode encodeBool (fun c => decide (c.t < c.input.n)) := raw.recode Context.raw (fun _ => rfl) (fun c => by simp only [List.length_ofFn])
  exact (contextProgram Context.encode er view).comp ctx

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram
open SparseIntegerLaw.BinarySparse (el ed)

noncomputable def startProgram : PolyProgram Input.encode State.encode Input.start := by
  let raw : PolyProgram qr (encodePair (encodePair qr Nat.bits) (ed er))
      (fun q : List ℚ => ((q,0),(((1:ℤ),[(1:ℤ)]),[q.map (fun _ => false)]))) := by
    apply Binary.Automatic.Poly.program
    have h : Binary.Automatic.Poly (fun q : List ℚ => q.map (fun _ => false)) := by
      apply Binary.Automatic.Poly.list_map <;> fun_prop
    fun_prop
  exact raw.recode (fun x => List.ofFn x.p) (fun _ => rfl) (fun x => by
    simp only [State.encode,Bundle.encode,Bundle.raw,Input.start,SparseIntegerLaw.dirac,
      Vector.toList_replicate,List.map_replicate,List.ofFn_const]
    change encodePair (encodePair qr Nat.bits) (ed er)
      ((List.ofFn x.p,0),((1,[1]),[(List.ofFn x.p).map (fun _ => false)])) = _
    simp only [List.map_const',List.length_ofFn]
    rfl)

 theorem state_size (x : Input) (d t : ℕ) (ht : t ≤ x.n) :
    (State.encode (x.state d t)).length ≤ (sizePolynomial d).eval x.encode.length := by
  let L := x.encode.length
  obtain ⟨hn,hp⟩ := input_bounds x
  have htL : t ≤ L := ht.trans hn
  have hc : (Context.encode ⟨x,t⟩).length ≤ 3*L+2 := by
    have hbits : t.bits.length ≤ t+1 := NatBinary.length_le_height (Nat.lt_two_pow_self.le)
    change (encodePair qr Nat.bits (List.ofFn x.p,t)).length ≤ _
    rw [encodePair_length]
    change 2*L+1+t.bits.length ≤ _
    omega
  have hN : (x.state d t).law.length ≤ supportBound d L := by
    apply (run_length x.p x.feasible t).trans
    unfold supportBound
    gcongr
  have hH : SparseBernoulli.stepHeight x.n d L*t ≤ heightBound d L := by
    unfold heightBound SparseBernoulli.stepHeight SparseIntegerLaw.stepHeight
    gcongr
  have hD : (x.state d t).law.law.denominator ≤ (2:ℤ)^(heightBound d L) :=
    (denominator_height x.p x.feasible L hp t).trans (pow_le_pow_right₀ (by norm_num) hH)
  have hs (q : Fin x.n → Bool) : (er (List.ofFn q)).length ≤ 3*L := by
    have hh := EncodedList.length_bound encodeBool (List.ofFn q) 1 (fun _ _ => by rfl)
    simp only [List.length_ofFn] at hh
    exact hh.trans (by omega)
  have hb := SparseIntegerLaw.encode_length_bound (fun q : Fin x.n → Bool => er (List.ofFn q))
    (run (d:=d) x.p x.feasible t) (supportBound d L) (heightBound d L) (3*L) hN hD (fun _ => hs _)
  have he : State.encode (x.state d t)=encodePair Context.encode
      (SparseIntegerLaw.BinarySparse.encode (fun q : Fin x.n → Bool => er (List.ofFn q)))
        (⟨x,t⟩,run (d:=d) x.p x.feasible t) := by
    simp only [State.encode,Bundle.encode,Bundle.raw,Input.state,Context.encode,
      SparseIntegerLaw.BinarySparse.encode,SparseIntegerLaw.BinarySparse.raw,ed,encodePair,RoundingProgram.encodeList_map]
  rw [sizePolynomial_eval,he,encodePair_length]
  unfold sizeBound
  dsimp only at ⊢
  simp only [L] at hc hb ⊢
  omega

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly
variable {α A : Type}

 theorem mixData_raw (μ ν : SparseIntegerLaw α) (view : α → A) :
    mixData (((raw μ).1,μ.states.toList.map view),((raw ν).1,ν.states.toList.map view))=
      ((raw (μ.mix ν)).1,(μ.mix ν).states.toList.map view) := by
  have h := bindData_raw (fair) (fun a => if a.val=0 then μ else ν) view
  simpa [mixData,mix,raw,fair,List.ofFn_succ] using h

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalBatchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparsePhysicalBatch.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse SparseIntegerLaw.DependentProgram
open SparseGraph.ListOperation (Row Table et)
def Input.partData (bal : Bool) (x : Input) : Data Row :=
  (((x.part bal).law.denominator,List.ofFn (x.part bal).law.numerator),
    (x.part bal).states.toList.map SparseGraph.ListOperation.setView)
def Input.result (x : Input) : Data Row :=
  (((law x.Z x.C x.p x.q x.hp x.hq).law.denominator,List.ofFn (law x.Z x.C x.p x.q x.hp x.hq).law.numerator),
    (law x.Z x.C x.p x.q x.hp x.hq).states.toList.map SparseGraph.ListOperation.setView)

end MetricKMedian.SparsePhysicalBatch.Program
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
def subsetRaw (x : Row × Row) : Bool := (x.1.zip x.2).all (fun p => !p.1 || p.2)
end MetricKMedian.InstanceProgram
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
@[fun_prop] theorem fractionRow_poly : Poly fractionRow := by unfold fractionRow; apply list_map <;> fun_prop
end MetricKMedian.SparseGridRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseTable
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


