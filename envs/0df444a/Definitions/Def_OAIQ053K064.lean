-- Prove2me | Definitions.Def_OAIQ053K064
-- name    : OAIQ053K064
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:14:42.586994+00:00
-- url     : https://prove2.me/theorems/d4944267-bda9-4465-b58b-c7db888d8c4d
-- title:
--   Definitions bundle OAIQ053K064 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 45 declarations of OpenAI's Lean: 23 definitions and 22 theorems. The definitions and types are `OAI.MetricKMedian.Coverage.Input.reductionProgram`, `OAI.MetricKMedian.Coverage.Raw.medianProgram`, `OAI.MetricKMedian.RationalBatchData.Ordinal.graphView`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.Input.raw`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.Input.encode`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.Input.raw`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.Input.result`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.taperProgram`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.result`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.view`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.ctxEncode`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.ctxRaw`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.ctxResult`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.Input.raw`, `OAI.MetricKMedian.RoundingProgram.branchProgram`, `OAI.MetricKMedian.RoundingProgram.branchRawProgram`, `OAI.MetricKMedian.RoundingProgram.runProgram`, `OAI.MetricKMedian.RoundingProgram.stepProgram`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.table`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.contextProgram`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.lawProgram`, `OAI.MetricKMedian.SparsePhysicalBatch.Program.Input.encode`, `OAI.MetricKMedian.TaperGraphProgram.Input.encode`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Hardness_Encoding`, `KMedian_Process_BatchOrdinalArrays`, `KMedian_Process_BatchProposalProgram`, `KMedian_Process_CopyGraphProgram`, `KMedian_Process_CopyListEncoding`, `KMedian_Process_CopyNearestProgram`, `KMedian_Process_CountsMaskProgram`, `KMedian_Process_PhysicalBatchProgram`, `KMedian_Process_PhysicalBatchUpdateProgram`, `KMedian_Process_PhysicalHistoriesProgram`, `KMedian_Process_PhysicalRoundProgram`, `KMedian_Process_RoundingRunProgram`, `KMedian_Process_RoundingStateCompiler`, `KMedian_Process_RoundingUniformStep`, `KMedian_Process_TaperGraphProgram`, `KMedian_Programs_CardinalRoundProgram`, `KMedian_Programs_DependentSparseProgram`, `KMedian_Programs_MaximumProgram`, `KMedian_Programs_NearestMaskProgram`, `KMedian_Programs_OriginalMaskProgram`, `KMedian_Sparse_SparseTable`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K054`, `OAIQ053K055`, `OAIQ053K056` and `OAIQ053K057` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K071`, `OAIQ053K072` and `OAIQ053K073`; the proof of `OAI.MetricKMedian.below_threshold_impossible_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K054
import Definitions.Def_OAIQ053K055
import Definitions.Def_OAIQ053K056
import Definitions.Def_OAIQ053K057

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Encoding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Binary Binary.Automatic Binary.Automatic.Poly

namespace Raw

noncomputable def medianProgram : PolyProgram id id (fun xs => (parse xs).medianBytes) :=
  PolyProgram.comp (f := fun xs : List Bool => (parse xs).medianBytes)
    (g := id) typedMedianProgram BooleanLists.unpackProgram

end Raw

namespace Input

theorem indices_raw (C : Input) : C.raw.indices = List.range (C.m + C.n) := by
  have hm : C.m ≤ C.raw.table.length := by
    rw [C.table_length]; exact Nat.le_mul_of_pos_right _ C.n_pos
  have hn : C.n ≤ C.raw.table.length := by
    rw [C.table_length]; exact Nat.le_mul_of_pos_left _ C.m_pos
  simp only [Raw.indices, List.length_append, List.length_take]
  change List.range (min C.m C.raw.table.length + min C.n C.raw.table.length) = _
  rw [Nat.min_eq_left hm, Nat.min_eq_left hn]

theorem mem_clients_iff (C : Input) (x : Fin (C.m + C.n)) :
    x ∈ C.toMedian.clients ↔ x.val < C.m := by
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective x
  cases a with
  | inl j =>
    constructor
    · intro _; exact j.isLt
    · intro _; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  | inr i =>
    constructor
    · intro hx
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
      exact False.elim (C.client_ne_facility j i hj)
    · intro hx
      change C.m + i.val < C.m at hx
      omega

theorem mem_facilities_iff (C : Input) (x : Fin (C.m + C.n)) :
    x ∈ C.toMedian.facilities ↔ C.m ≤ x.val := by
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective x
  cases a with
  | inl j =>
    constructor
    · intro hx
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
      exact False.elim (C.client_ne_facility j i hi.symm)
    · intro hx
      change C.m ≤ j.val at hx
      omega
  | inr i =>
    constructor
    · intro _; change C.m ≤ C.m + i.val; omega
    · intro _; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem medianBytes_correct (C : Input) : C.raw.medianBytes = encodeInstance C.toMedian := by
  change C.raw.medianBytes =
    encodeNat (C.m + C.n) ++ encodeNat C.k ++
      List.ofFn (fun i : Fin (C.m + C.n) => decide (i ∈ Finset.univ.image C.client)) ++
      List.ofFn (fun i : Fin (C.m + C.n) => decide (i ∈ C.chosenFacilities Finset.univ)) ++
      (List.ofFn (fun i : Fin (C.m + C.n) => (List.ofFn (fun j : Fin (C.m + C.n) =>
        encodeRat (C.pointDistance (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)))).flatten)).flatten
  have hc (x : Fin (C.m + C.n)) : x ∈ Finset.univ.image C.client ↔ x.val < C.m :=
    C.mem_clients_iff x
  have hf (x : Fin (C.m + C.n)) : x ∈ C.chosenFacilities Finset.univ ↔ C.m ≤ x.val :=
    C.mem_facilities_iff x
  have he (x y : Fin (C.m + C.n)) : C.raw.entry x.val y.val =
      encodeRat (C.pointDistance (finSumFinEquiv.symm x) (finSumFinEquiv.symm y)) :=
    C.entry_distance x y
  unfold Raw.medianBytes
  change encodeNat (C.m + C.n) ++ encodeNat C.k ++
    (C.raw.indices.map (fun a => decide (a < C.m))) ++
    (C.raw.indices.map (fun a => decide (C.m ≤ a))) ++
    (C.raw.indices.flatMap (fun a => C.raw.indices.flatMap (fun b => C.raw.entry a b))) = _
  simp only [C.indices_raw, RoundingList.range_finRange,
    ← List.ofFn_eq_map, List.flatMap_def, List.map_ofFn, Function.comp_def, he]
  simp only [hc, hf]

noncomputable def reductionProgram : Binary.PolyProgram encode encodeInstance toMedian :=
  Raw.medianProgram.recode encode (fun _ => rfl) (fun C => by
    simp only [C.parse_encode, C.medianBytes_correct, id_eq])

end Input
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingUniformStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse

noncomputable def branchRawProgram (s : Bool) :
    PolyProgram (encodePair erow (ed erow)) (encodePair erow (ed erow)) (fun x =>
      (x.1,(branchLawData (x.2.1,x.2.2.map (fun p => probability s (x.1,p))),
        x.2.2.flatMap (fun p => [endpoint s false (x.1,p),endpoint s true (x.1,p)])))) := by
  let β := fst erow (ed erow)
  let law := (snd erow (ed erow)).comp (fst el (encodeList erow))
  let states := (snd erow (ed erow)).comp (snd el (encodeList erow))
  let probs := (β.fanout states).comp ((probabilityProgram s).listMapWith [] 0)
  let laws := (law.fanout probs).comp branchLawProgram
  let endpoints := ((endpointProgram s false).fanout (endpointProgram s true)).comp pairList
  let ps := (β.fanout states).comp (endpoints.listFlatMapWith [] [])
  exact (β.fanout (laws.fanout ps)).congr _ (fun _ => rfl)

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchOrdinalArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RationalBatchData.Ordinal
open Finset FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)
variable {I : Type} [LinearOrder I] [Fintype I] {n : ℕ}
variable (r : Fin n ≃o I) (D : Actions I I) (H : Finset I)

 def graphView (G : I → Finset I) : Table := List.ofFn (fun i => sets r (G (r i)))
end MetricKMedian.RationalBatchData.Ordinal
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingStateCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse

noncomputable def branchProgram (s : Bool) : PolyProgram State.encode State.encode (@State.branch s) :=
  (branchRawProgram s).recode State.raw State.encode_raw (fun x => by
    rw [branch_raw,State.encode_raw])

noncomputable def stepProgram (s : Bool) : PolyProgram State.encode State.encode (@State.step s) :=
  (branchProgram s).comp (compressProgram s)

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_DependentSparseProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

noncomputable def contextProgram : PolyProgram (Bundle.encode ec ea view) ec (fun x : Bundle T => x.ctx) :=
  (fst ec (ed ea)).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)
noncomputable def lawProgram : PolyProgram (Bundle.encode ec ea view) el
    (fun x : Bundle T => (x.law.law.denominator,List.ofFn x.law.law.numerator)) :=
  ((snd ec (ed ea)).comp (fst el (encodeList ea))).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)

end MetricKMedian.SparseIntegerLaw.DependentProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchProgram
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
abbrev Input.encode (x : Input) := Binary.Automatic.enc x.raw

end MetricKMedian.SparsePhysicalBatch.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchProposalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalBatchData.ProposalProgram
open Finset FixedBatch Binary Binary.PolyProgram
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
variable {C : Type} (I : C → Type) [∀ c, LinearOrder (I c)] [∀ c, Fintype (I c)]

variable {I}

def Input.raw (x : Input I) : GraphData.Raw :=
  (((x.g,x.b),(x.Δ,(x.p,x.φ))),Ordinal.graphView x.enum x.G)
end MetricKMedian.RationalBatchData.ProposalProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyListEncoding
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
 local instance instLinearOrderCopyFin_rb8ef67_1 : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
theorem active_view (A : Finset (CopyState.Copy (F:=Fin f) Δ)) :
    active (view A)=List.ofFn (fun i => (rank (enumeration A i).val).val) := by
  apply List.SortedLT.eq_of_mem_iff
  · exact ((List.sortedLT_range _).pairwise.filter _).sortedLT
  · exact (enum_rank_strictMono A).sortedLT_ofFn
  · intro k
    simp only [active,indices,view,setView,List.length_ofFn,List.mem_filter,List.mem_range,List.mem_ofFn]
    constructor
    · rintro ⟨hk,ha⟩
      simp only [List.getElem?_ofFn,dite_eq_left hk,Option.getD_some,decide_eq_true_eq,mem_map_equiv] at ha
      let a : A := ⟨finProdFinEquiv.symm ⟨k,hk⟩,ha⟩
      refine ⟨(enumeration A).symm a,?_⟩
      rw [Equiv.apply_symm_apply]
      change ((finProdFinEquiv (finProdFinEquiv.symm ⟨k,hk⟩)).val)=k
      rw [Equiv.apply_symm_apply]
    · rintro ⟨i,rfl⟩
      refine ⟨(rank (enumeration A i).val).isLt,?_⟩
      simp only [List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,decide_eq_true_eq,
        mem_map_equiv,Equiv.symm_apply_apply]
      exact (enumeration A i).property

end MetricKMedian.RationalPhysicalKernel.CopyList
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingRunProgram
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.BinarySparse

noncomputable def runProgram (s : Bool) : PolyProgram Input.encode State.encode (fun x : Input s => x.run x.n) :=
  ((stepProgram s).repeatFrom (startProgram s) (countProgram s) X statePolynomial
    (fun x => by simpa using (input_bounds x).1) (fun x i hi => by
      rw [input_iterate]; exact run_size x i hi)).congr _ (fun x => input_iterate x _)

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_CardinalRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseCardinalRounding.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
 theorem selectedRow_eq {n : ℕ} (q : Vector ℚ n) :
    selectedRow q.toList=SparseGraph.ListOperation.setView (selected q) := by
  apply List.ext_getElem
  · simp only [selectedRow,List.length_map,Vector.length_toList,SparseGraph.ListOperation.setView,List.length_ofFn]
  · intro i hi hi'
    have hin : i<n := by simpa only [SparseGraph.ListOperation.setView,List.length_ofFn] using hi'
    simp only [selectedRow,List.getElem_map,Vector.getElem_toList,SparseGraph.ListOperation.setView,
      List.getElem_ofFn,selected,Finset.mem_filter,Finset.mem_univ,true_and,RationalWeightedStep.point]

end MetricKMedian.SparseCardinalRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.TaperGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse
abbrev Input.encode (x : Input) := enc x.raw

end MetricKMedian.TaperGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyGraphProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

def Input.raw (x : Input) : Raw := ((((x.g,x.P),x.Δ),List.ofFn (fun i => List.ofFn (x.d i))),CopyList.view x.A)
abbrev Input.encode (x : Input) := enc x.raw

 local instance instLinearOrderCopyFin_rb8ef67_2 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.instLinearOrderSubtypeCopyFinMemFinset
theorem prepare_input (x : Input) : prepare x.raw=x.taper.raw := by
  dsimp only [TaperGraphProgram.Input.raw,Input.taper]
  simp only [prepare,Input.raw,active_view,List.map_ofFn,Function.comp_def,rank_owner,
    List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,
    mem_map_equiv,Equiv.symm_symm,own,mem_filter,mem_univ,true_and]
  simp only [Fin.ext_iff]
noncomputable def taperProgram : PolyProgram Input.encode TaperGraphProgram.Input.encode Input.taper :=
  prepare_poly.program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (prepare_input x))

def Input.result (x : Input) : Data Table :=
  ((x.law.law.denominator,List.ofFn x.law.law.numerator),
    x.law.states.toList.map (RationalBatchData.Ordinal.graphView (ordinal x.A)))

 theorem reindexed_lift {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ))
    (G : Fin A.card → Finset (Fin A.card)) :
    RationalBatchData.Ordinal.graphView (ordinal A) (SparseEnumeratedGraph.lift (enumeration A) G)=
      SparseGraph.ListOperation.view G := by
  simp only [RationalBatchData.Ordinal.graphView,RationalBatchData.Ordinal.sets_eq,
    SparseGraph.ListOperation.view]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext h
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [SparseEnumeratedGraph.mem_lift]
  change (enumeration A).symm (enumeration A h)∈G ((enumeration A).symm (enumeration A i)) ↔ _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

 theorem result_eq (x : Input) : x.taper.qInput.result=x.result := by
  unfold Input.result Input.law graphLaw SparseEnumeratedGraph.law
  simp only [SparseIntegerLaw.map,Vector.toList_map,List.map_map,Function.comp_def,reindexed_lift]
  unfold SparseGraph.Program.QInput.result
  rw [taper_q]
  rfl

end MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_MaximumProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.MaskProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
 theorem radius_view {n : ℕ} (d : Fin n → ℚ) (U : Finset (Fin n)) (hU : U.Nonempty) :
    radius (List.ofFn d,setView U)=(U.image d).max' (hU.image _) :=
  maximum_eq_finset _ _ _ (selectedValues_mem d U)
end MetricKMedian.MaskProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_NearestMaskProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Preparation.RationalNearest.MaskProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram

 theorem erase_view {n : ℕ} (U : Finset (Fin n)) (a : Fin n) : erase (a.val,setView U)=setView (U.erase a) := by
  simp only [erase,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_def,MetricKMedian.MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,mem_erase,
    Bool.decide_and]
  simp only [ne_eq,Fin.val_inj]
  exact Bool.and_comm _ _
 theorem insert_view {n : ℕ} (U : Finset (Fin n)) (a : Fin n) : insert (a.val,setView U)=setView (Insert.insert a U) := by
  simp only [insert,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_def,MetricKMedian.MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,mem_insert,Fin.ext_iff,
    Bool.decide_or]
  exact Bool.or_comm _ _

 theorem raw_view {n : ℕ} (d : Fin n → ℚ) (U : Finset (Fin n)) (k : ℕ) :
    raw k (List.ofFn d,setView U)=setView (takeNearest d k U) := by
  induction k generalizing U with
  | zero => simp only [raw,takeNearest,setView,List.map_ofFn,Function.comp_def,notMem_empty,decide_false]
  | succ k ih =>
    unfold raw takeNearest
    rw [Completion.Rational.PackingProgram.any_view]
    by_cases h : U.Nonempty
    · simp only [decide_eq_true h,ite_true,dite_eq_left h]
      rw [MetricKMedian.MaskProgram.nearest_view d U h]
      have he : Preparation.firstNearest U d h=least U d h := rfl
      rw [he,erase_view,ih,insert_view]
    · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,dite_eq_right h,setView,List.map_ofFn,
        Function.comp_def,notMem_empty,decide_false]
end MetricKMedian.Preparation.RationalNearest.MaskProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyNearestProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open RationalPhysicalKernel RationalPhysicalKernel.CopyList
open SparseGraph.ListOperation (Row Table setView indices)
variable {τ : ℝ} (q : RationalParameters τ)
 attribute [local instance] OAI.MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram.instLinearOrderCopyFin
theorem distances_view {f Δ : ℕ} (d : Fin f → ℚ) (A : Finset (CopyState.Copy (F:=Fin f) Δ)) :
    distances Δ (List.ofFn d,view A)=List.ofFn (fun k : Fin (f*Δ) => d (finProdFinEquiv.symm k).1) := by
  simp only [distances,indices,view,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  have hk : k.val/Δ=(finProdFinEquiv.symm k).1.val := by
    simpa only [rank,Equiv.apply_symm_apply] using CopyGraphProgram.rank_owner (finProdFinEquiv.symm k)
  simp only [Function.comp_def,hk,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]

 theorem nearestRaw_view {f j : ℕ} (d : Fin j → Fin f → ℚ) (A : Finset (CopyState.Copy (F:=Fin f) q.Δ)) (c : Fin j) :
    nearestRaw q.Δ (List.ofFn (d c),view A)=view (q.nearest d A c) := by
  unfold nearestRaw
  rw [distances_view,view,Preparation.RationalNearest.MaskProgram.raw_view]
  exact congrArg setView (Preparation.RationalNearest.takeNearest_map orderEquiv (fun a => d c a.1) q.Δ A)

 theorem radiusRaw_view {f j : ℕ} (d : Fin j → Fin f → ℚ) (A : Finset (CopyState.Copy (F:=Fin f) q.Δ))
    (hA : q.Δ≤A.card) (c : Fin j) : radiusRaw q.Δ (List.ofFn (d c),view A)=q.radius d A hA c := by
  unfold radiusRaw
  rw [distances_view,nearestRaw_view q]
  unfold view
  rw [MetricKMedian.MaskProgram.radius_view _ _ ((q.nearest_nonempty d A hA c).map)]
  have he : ((q.nearest d A c).map finProdFinEquiv.toEmbedding).image
      (fun k => d c (finProdFinEquiv.symm k).1)=(q.nearest d A c).image (fun a => d c a.1) := by
    ext r
    simp only [mem_image,mem_map]
    constructor
    · rintro ⟨b,⟨a,ha,rfl⟩,h⟩; exact ⟨a,ha,by simpa using h⟩
    · rintro ⟨a,ha,rfl⟩; exact ⟨finProdFinEquiv a,⟨a,ha,rfl⟩,by simp⟩
  simp only [he,RationalParameters.radius]
end MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountsMaskProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.CopyState.CountsProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open RationalPhysicalKernel.CopyList

 theorem mask_view {f Δ : ℕ} (n : Fin f → ℕ) (hn : ∀ i, n i≤Δ) :
    mask Δ (List.ofFn n)=view (activeSlots n hn) := by
  simp only [mask,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,
    Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,
    List.flatMap_def]
  unfold view setView
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext s
  have he : (⟨i.val*Δ+s.val,by have hi := Nat.mul_le_mul_right Δ (Nat.succ_le_of_lt i.isLt); have hs := s.isLt; nlinarith⟩ : Fin (f*Δ))=rank (i,s) := by
    apply Fin.ext
    change i.val*Δ+s.val=s.val+Δ*i.val
    ac_rfl
  simp only [he,rank,mem_map_equiv,Equiv.symm_apply_apply]
  congr 1
  apply propext
  constructor
  · intro hs
    exact mem_image.mpr ⟨⟨i,⟨s.val,hs⟩⟩,mem_univ _,by rfl⟩
  · intro hs
    obtain ⟨⟨a,t⟩,_,ht⟩ := mem_image.mp hs
    have hi : a=i := congrArg Prod.fst ht
    subst a
    have ht' : t.val=s.val := congrArg (fun x : Copy (F:=Fin f) Δ => x.2.val) ht
    exact ht' ▸ t.isLt
end MetricKMedian.CopyState.CountsProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchUpdateProgram
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
local instance instLinearOrderCopyFin_rb8ef67_3 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.instLinearOrderSubtypeCopyFinMemFinset
def Input.raw (x : Input) : Raw := ((x.ctx.Δ,CopyList.view x.ctx.A),x.proposal.raw)
end MetricKMedian.RationalPhysicalKernel.UpdateProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalRoundProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalPhysicalKernel.RoundProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table)
open CopyList UpdateProgram
def ctxRaw (x : Context) : Raw := (x.toInput.raw,(x.β,(x.p,x.φ)))
abbrev ctxEncode (x : Context) := enc (ctxRaw x)

 local instance instLinearOrderCopyFin_rb8ef67_4 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance instLinearOrderSubtypeCopyFinMemFinset_rb8ef67_1 {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A
theorem attach_input (x : Context) : attach ((ctxRaw x),x.toInput.result)=
    (x.toInput.result.1, (ctxInputs x).map UpdateProgram.Input.raw) := by
  simp only [attach,ctxRaw,CopyGraphProgram.Input.result,ctxInputs,
    List.map_map,Function.comp_def]
  rfl

def ctxResult (x : Context) : Data Row :=
  (((ctxLaw x).law.denominator,List.ofFn (ctxLaw x).law.numerator),(ctxLaw x).states.toList.map CopyList.view)

end MetricKMedian.RationalPhysicalKernel.RoundProgram
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
def table (μ : SparseIntegerLaw α) (v : α → A) : Data A := ((raw μ).1,μ.states.toList.map v)
 theorem table_map (μ : SparseIntegerLaw α) (f : α → β) (v : β → A) :
    table (μ.map f) v=table μ (v ∘ f) := by
  simp only [table,raw,map,Vector.toList_map,List.map_map]

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

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
local instance instLinearOrderCopyFin_rb8ef67_5 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance instLinearOrderSubtypeCopyFinMemFinset_rb8ef67_2 {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A
abbrev view (x : Context) (z : Hist x) := CopyList.view z.1.1
def result (P : ℕ → ℚ) (T : ℕ) (x : Context) : Data Row := table (law P T x) (view x)

end MetricKMedian.RationalPhysicalKernel.HistoryProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_OriginalMaskProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.MaskProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row setView indices)

 theorem imageRaw_view {f h : ℕ} (orig : Fin f → Fin h) (O : Finset (Fin f)) :
    imageRaw ((List.replicate h (),List.ofFn (fun i => (orig i).val)),setView O)=setView (O.image orig) := by
  simp only [imageRaw,indices,List.length_replicate,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  unfold setView
  apply congrArg List.ofFn
  funext a
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_ofFn,id_eq,get,List.getElem?_ofFn,
    dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,decide_eq_true_eq,mem_image]
  constructor
  · rintro ⟨b,⟨i,rfl⟩,hi⟩
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hi
    exact ⟨i,hi.1,Fin.ext hi.2⟩
  · rintro ⟨i,hi,he⟩
    refine ⟨_,⟨i,rfl⟩,?_⟩
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hi,congrArg Fin.val he⟩

 theorem pullback_view {f h : ℕ} (orig : Fin f → Fin h) (d : Fin h → ℚ) :
    pullback (List.ofFn d,List.ofFn (fun i => (orig i).val))=List.ofFn (fun i => d (orig i)) := by
  simp only [pullback,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]

 theorem pullbackMatrix_view {f h : ℕ} (orig : Fin f → Fin h) (d : Fin h → Fin h → ℚ) :
    pullbackMatrix (List.ofFn (fun i => List.ofFn (d i)),List.ofFn (fun i => (orig i).val))=
      List.ofFn (fun i => List.ofFn (fun k => d (orig i) (orig k))) := by
  simp only [pullbackMatrix,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,pullback_view]
end MetricKMedian.MaskProgram
end

end OAI
end


