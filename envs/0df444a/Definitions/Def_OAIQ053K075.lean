-- Prove2me | Definitions.Def_OAIQ053K075
-- name    : OAIQ053K075
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:25:53.397131+00:00
-- url     : https://prove2.me/theorems/c4c4513b-b586-4487-98d1-2ec0215f4492
-- title:
--   Definitions bundle OAIQ053K075 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 40 declarations of OpenAI's Lean: 26 definitions and 14 theorems. The definitions and types are `OAI.MetricKMedian.FixedBatch.RationalParameters.GridDataProgram.Input.raw`, `OAI.MetricKMedian.FixedBatch.RationalParameters.GridDataProgram.Input.selection`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.candidatesProgram`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.itemsProgram`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.program`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.Input.selection`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.program`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.historyProgram`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.itemsProgram`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.program`, `OAI.MetricKMedian.InputParser.instanceProgram`, `OAI.MetricKMedian.InputParser.matrixProgram`, `OAI.MetricKMedian.InputParser.rawProgram`, `OAI.MetricKMedian.InstanceProgram.scanInputProgram`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.Input.encode`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.Input.raw`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.baseProgram`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.budgetProgram`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.unitProgram`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.program`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.program`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.program`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.proposalProgram`, `OAI.MetricKMedian.SparseGridRounding.Program.program`, `OAI.MetricKMedian.SparsePrepared.Program.KernelInput.result`, `OAI.MetricKMedian.SparseSignedPreparation.Program.Input.encode`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_InstanceParserProgram`, `KMedian_Optimization_FractionalScanProgram`, `KMedian_Preparation_PreparedKernelProgram`, `KMedian_Preparation_PreparedLawProgram`, `KMedian_Preparation_PreparedScanProgram`, `KMedian_Process_ActionTransitionList`, `KMedian_Process_CopyNextProgram`, `KMedian_Process_PhysicalBatchUpdateProgram`, `KMedian_Process_PhysicalHistoriesProgram`, `KMedian_Process_PhysicalRoundProgram`, `KMedian_Process_RoundCountsProgram`, `KMedian_Programs_HistorySelectionProgram`, `KMedian_Programs_InstanceRoundProgram`, `KMedian_Rounding_GridDataProgram`, `KMedian_Rounding_GridRoundingProgram`, `KMedian_Rounding_SignedPreparationProgram`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K070`, `OAIQ053K071`, `OAIQ053K072` and `OAIQ053K073` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ053K080`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K070
import Definitions.Def_OAIQ053K071
import Definitions.Def_OAIQ053K072
import Definitions.Def_OAIQ053K073

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_InstanceParserProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
noncomputable def rawProgram : PolyProgram enc enc raw := by
  have hm : Poly matrix := ⟨matrixProgram⟩
  exact (by unfold raw; fun_prop : Poly raw).program
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
-- module Solutions.OAIQ053_KM.KMedian_Process_ActionTransitionList
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalBatchData.ActionTransition
open Binary Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)

variable {I : Type} [LinearOrder I] [Fintype I] {n : ℕ}
variable (r : Fin n ≃o I) (D : Actions I I) (H : Finset I) (Z : Finset (HeavyAction D H))

 theorem selected_light (hD : ∀ i, D.source i=i) (i : Fin n) : i.val∈selected (view r D H Z) ↔
    r i∈(Z∩(heavy D H).ordinary).image (heavy D H).source := by
  rw [selected_mem]
  constructor
  · rintro ⟨e,he,hc⟩
    have hl := (Ordinal.code_light r D H e).mp (hc ▸ i.isLt)
    cases e with
    | inl h =>
      refine mem_image.mpr ⟨.inl h,mem_inter.mpr ⟨he,?_⟩,?_⟩
      · simp only [heavy,mem_filter,mem_univ,Sum.isLeft_inl,and_self]
      · change D.source h.val=r i
        rw [hD]
        have hh : r.symm h.val=i := Fin.ext hc
        exact (r.symm.injective (hh.trans (r.symm_apply_apply i).symm))
    | inr h => cases hl
  · rintro hi
    obtain ⟨e,he,hE⟩ := mem_image.mp hi
    rcases mem_inter.mp he with ⟨he,hord⟩
    cases e with
    | inl h =>
      refine ⟨.inl h,he,?_⟩
      change D.source h.val=r i at hE
      rw [hD] at hE
      simp only [Ordinal.code,hE,OrderIso.symm_apply_apply]
    | inr h => simp only [heavy,mem_filter,mem_univ,Sum.isLeft_inr,Bool.false_eq_true,and_false] at hord

 theorem dead_view : dead (view r D H Z)=Ordinal.sets r (Z.biUnion (heavy D H).erase) := by
  unfold dead
  rw [show (view r D H Z).1.2=Ordinal.sets r H from rfl]
  simp only [indices,RoundingList.range_finRange,
    Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,Ordinal.sets_eq,List.length_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_map,Function.comp_def,id_eq,List.any_eq_true,decide_eq_true_eq,mem_biUnion]
  constructor
  · rintro ⟨c,hc,hv⟩
    obtain ⟨e,he,rfl⟩ := (selected_mem r D H Z c).mp hc
    dsimp only [view] at hv
    rw [Ordinal.erase_code,Ordinal.sets_eq] at hv
    simp only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,decide_eq_true_eq] at hv
    exact ⟨e,he,hv⟩
  · rintro ⟨e,he,hi⟩
    refine ⟨Ordinal.code r D H e,(selected_mem r D H Z _).mpr ⟨e,he,rfl⟩,?_⟩
    dsimp only [view]
    rw [Ordinal.erase_code,Ordinal.sets_eq]
    simp only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,decide_eq_true hi]

 theorem sources_view (hD : ∀ i, D.source i=i) : sources (view r D H Z)=Ordinal.sets r
    (H∪(Z∩(heavy D H).ordinary).image (heavy D H).source) := by
  unfold sources
  rw [show (view r D H Z).1.2=Ordinal.sets r H from rfl]
  simp only [indices,RoundingList.range_finRange,
    Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,Ordinal.sets_eq,List.length_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,Bool.or_eq_true,
    decide_eq_true_eq,natMember_true,mem_union]
  exact or_congr Iff.rfl (selected_light r D H Z hD i)

end MetricKMedian.RationalBatchData.ActionTransition
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyNextProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

 local instance instLinearOrderCopyFin_rbb8f03_1 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.CopyNext.instLinearOrderSubtypeCopyFinMemFinset
theorem transition_view {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (RationalBatchData.graph G) H)) :
    transition ((Δ,view A),RationalBatchData.ActionTransition.view (ordinal A) (RationalBatchData.graph G) H Z)=
      view (RationalBatchData.transition A G H Z) := by
  unfold transition
  dsimp only
  have hd := RationalBatchData.ActionTransition.dead_view (ordinal A) (RationalBatchData.graph G) H Z
  have hs := RationalBatchData.ActionTransition.sources_view (ordinal A) (RationalBatchData.graph G) H Z (fun _ => rfl)
  rw [hd,hs]
  exact next_view A _ _

end MetricKMedian.RationalPhysicalKernel.CopyNext
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchUpdateProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

 local instance instLinearOrderCopyFin_rbb8f03_2 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.instLinearOrderSubtypeCopyFinMemFinset
theorem finish_input (x : Input) : finish (x.raw,x.proposal.result)=x.result := by
  rw [result_map]
  apply Prod.ext
  · rfl
  · change (x.proposal.law.states.toList.map (fun Z => setView (Z.map x.proposal.enumActions.symm.toEmbedding))).map
      (fun Z => CopyNext.transition (x.raw.1,((RationalBatchData.GraphData.prepare x.raw.2).2,Z))) = _
    rw [List.map_map]
    apply List.map_congr_left
    intro Z _
    change CopyNext.transition ((x.ctx.Δ,view x.ctx.A),
      ((RationalBatchData.GraphData.prepare (((x.ctx.g,x.ctx.β),(x.ctx.Δ,(x.ctx.p,x.ctx.φ))),
        RationalBatchData.Ordinal.graphView (ordinal x.ctx.A) x.G)).2,
        setView (Z.map x.proposal.enumActions.symm.toEmbedding)))=_
    rw [RationalBatchData.Ordinal.prepare_graph]
    exact CopyNext.transition_view x.ctx.A x.G _ Z

noncomputable def proposalProgram : PolyProgram Input.encode
    RationalBatchData.ProposalProgram.Input.encode Input.proposal :=
  (snd enc enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)

noncomputable def program : PolyProgram Input.encode (ed SparseGraph.ListOperation.er) Input.result := by
  let ctx : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  exact (ctx.fanout (proposalProgram.comp RationalBatchData.ProposalProgram.program) |>.comp finish_poly.program).congr _ finish_input
end MetricKMedian.RationalPhysicalKernel.UpdateProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalRoundProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

local instance instLinearOrderCopyFin_rbb8f03_3 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance instLinearOrderSubtypeCopyFinMemFinset_rbb8f03_1 {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A
noncomputable def program : PolyProgram ctxEncode (ed SparseGraph.ListOperation.er) ctxResult := by
  let getLaw := fst (α:=LawData) (β:=List UpdateProgram.Input) enc (encodeList UpdateProgram.Input.encode)
  let getInputs := snd (α:=LawData) (β:=List UpdateProgram.Input) enc (encodeList UpdateProgram.Input.encode)
  let cond := getLaw.fanout (getInputs.comp (UpdateProgram.program.listMap dummy))
  exact (inputsProgram.comp cond |>.comp bindData_poly.program).congr _ (fun x => by
    change bindData (x.toInput.result.1,(ctxInputs x).map UpdateProgram.Input.result)=(ctxResult x)
    have hh : (ctxInputs x).map UpdateProgram.Input.result=List.ofFn (fun i =>
      ((raw ((UpdateProgram.Input.mk x x.toInput.law.states[i.val]).law)).1,
        (UpdateProgram.Input.mk x x.toInput.law.states[i.val]).law.states.toList.map CopyList.view)) := by
      simp only [ctxInputs,states_list,List.map_ofFn,Function.comp_def,UpdateProgram.Input.result,raw]
    rw [hh]
    have h := bindData_raw (β:=Finset (CopyState.Copy (F:=Fin x.f) x.Δ)) x.toInput.law
      (fun i => (UpdateProgram.Input.mk x x.toInput.law.states[i.val]).law) CopyList.view
    exact h)

end MetricKMedian.RationalPhysicalKernel.RoundProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalHistoriesProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
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

local instance instLinearOrderCopyFin_rbb8f03_4 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance instLinearOrderSubtypeCopyFinMemFinset_rbb8f03_2 {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A
noncomputable def program (P : ℕ → ℚ) (T : ℕ) (hP : ∀ t<T,0<P t) :
    PolyProgram RoundProgram.ctxEncode (ed SparseGraph.ListOperation.er) (result P T) := by
  induction T with
  | zero =>
    let q : Poly (fun x : RoundProgram.Raw => (((1:ℤ),[(1:ℤ)]),[x.1.2])) := by
      apply pair
      · fun_prop
      · fun_prop
    exact q.program.recode RoundProgram.ctxRaw (fun _ => rfl) (fun _ => rfl)
  | succ T ih =>
    let prev := ih (fun t ht => hP t (by omega))
    let ctx : PolyProgram RoundProgram.ctxEncode enc RoundProgram.ctxRaw :=
      (identity enc).recode RoundProgram.ctxRaw (fun _ => rfl) (fun _ => rfl)
    let attached : PolyProgram RoundProgram.ctxEncode
        (encodePair enc (encodeList RoundProgram.ctxEncode))
        (fun x => ((result P T x).1,inputs P T (hP T (by omega)) x)) :=
      (ctx.fanout prev |>.comp (attach_poly (P T)).program).recode id (fun _ => rfl) (fun x => by
        dsimp only [Function.comp_def,id_eq]
        rw [attach_result P T (hP T (by omega))]
        change encodePair enc (encodeList enc) _=encodePair enc (encodeList RoundProgram.ctxEncode) _
        simp only [encodePair,encodeList_map]
        rfl)
    let getLaw := fst (α:=LawData) (β:=List Context) enc (encodeList RoundProgram.ctxEncode)
    let getInputs := snd (α:=LawData) (β:=List Context) enc (encodeList RoundProgram.ctxEncode)
    let cond := getLaw.fanout (getInputs.comp (RoundProgram.program.listMap RoundProgram.dummy.ctx))
    exact (attached.comp cond |>.comp bindData_poly.program).congr _ (fun x => by
      change bindData ((result P T x).1,(inputs P T (hP T (by omega)) x).map RoundProgram.ctxResult)=result P (T+1) x
      unfold result law histories
      rw [SparseHistories.tree,table_bind]
      apply congrArg bindData
      apply Prod.ext
      · rfl
      · simp only [inputs,Function.comp_def,states_list,List.map_ofFn]
        apply congrArg List.ofFn
        funext i
        exact conditional P T (hP T (by omega)) x _)
end MetricKMedian.RationalPhysicalKernel.HistoryProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_HistorySelectionProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
noncomputable def historyProgram : PolyProgram (Input.encode q) (ed SparseGraph.ListOperation.er)
    (fun x => HistoryProgram.result q.taperAt q.T x.ctx) := by
  let c : PolyProgram (Input.encode q) RoundProgram.ctxEncode (Input.ctx q) :=
    (ctxRaw_poly q).program.recode (Input.raw q) (fun _ => rfl) (fun _ => rfl)
  exact c.comp (HistoryProgram.program q.taperAt q.T (fun t _ => by exact_mod_cast q.taperAt_pos t))

noncomputable def itemsProgram : PolyProgram (Input.encode q) (encodeList Completion.Rational.Program.Input.encode) (Input.items q) := by
  let raw : PolyProgram (Input.encode q) enc (Input.raw q) := (identity enc).recode (Input.raw q) (fun _ => rfl) (fun _ => rfl)
  exact (raw.fanout (historyProgram q) |>.comp attach_poly.program).recode id (fun _ => rfl) (fun x => by
    dsimp only [Function.comp_def,id_eq]
    rw [attach_input q]
    change encodeList enc _=encodeList Completion.Rational.Program.Input.encode _
    rw [encodeList_map]
    rfl)

local instance instLinearOrderCopyFin_rbb8f03_5 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
noncomputable def program : PolyProgram (Input.encode q) SparseGraph.ListOperation.et (Input.result q) := by
  let m := (metadata_poly q).program.recode (Input.raw q) (fun _ => rfl) (fun _ => rfl)
  let complete := (itemsProgram q).comp ((Completion.Rational.Program.program q.Δ).listMap (dummy q))
  exact (m.fanout complete |>.comp Completion.Rational.BestProgram.raw_poly.program).congr _ (fun x => by
    change Completion.Rational.BestProgram.raw
      (metadata q x.raw,x.items.map (fun y => setView (Completion.Rational.output y.d y.R y.A y.B y.hB)))=x.result
    rw [metadata_input q]
    simp only [Input.items,List.map_map,Function.comp_def]
    rw [show (fun z => setView (Completion.Rational.output x.d x.R z.1.1 x.B x.hB))=
      setView ∘ (fun z => RationalPhysicalKernel.completed x.d x.R x.B x.hB q.g q.β z) from rfl]
    rw [← List.map_map,Completion.Rational.BestProgram.raw_best]
    rw [← SparseSelect.best_map (q.completedGood x.d x.R x.A x.B x.hB)
      (fun z => Completion.Rational.score x.d (RationalPhysicalKernel.completed x.d x.R x.B x.hB q.g q.β z))
      (fun O => decide (O.Nonempty ∧ (O.card:ℚ)≤q.g*x.A.card+q.allowance))
      (Completion.Rational.score x.d) (RationalPhysicalKernel.completed x.d x.R x.B x.hB q.g q.β)
      (fun _ => rfl) (fun _ => rfl)]
    rfl)
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
def Input.raw (x : Input q) : Raw := (List.replicate x.f (),((List.ofFn (fun i => List.ofFn (x.d₀ i)),
  List.ofFn (fun c => List.ofFn (x.d c))),view x.A))

local instance instLinearOrderCopyFin_rbb8f03_6 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
def Input.selection (x : Input q) : SelectionProgram.Input q where
  f := x.f
  j := x.j
  d := x.d
  R := q.radius x.d x.A x.enough
  A := x.A
  B := q.nearest x.d x.A
  hB := q.nearest_nonempty x.d x.A x.enough
  d₀ := x.d₀

 theorem prepare_input (x : Input q) : prepare q.Δ x.raw=x.selection.raw := by
  simp only [prepare,Input.raw,List.map_ofFn,Function.comp_def,nearestRaw_view q,radiusRaw_view q x.d x.A x.enough]
  rfl
end MetricKMedian.FixedBatch.RationalParameters.GridDataProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundCountsProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

local instance instLinearOrderCopyFin_rbb8f03_7 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
def Input.selection (x : Input) : SelectionProgram.Input q :=
  if hn : ∀ i, x.n i≤q.Δ then
    if hA : q.Δ≤(CopyState.activeSlots x.n hn).card then
      GridDataProgram.Input.selection q ⟨x.f,x.j,x.d₀,x.d,CopyState.activeSlots x.n hn,hA⟩
    else dummy q
  else dummy q

 theorem prepare_input (x : Input) : prepare q x.raw=(x.selection q).raw := by
  unfold prepare Input.selection
  by_cases hn : ∀ i, x.n i≤q.Δ
  · rw [dite_eq_left hn,valid_input q x hn]
    by_cases hA : q.Δ≤(CopyState.activeSlots x.n hn).card
    · rw [dite_eq_left hA,ite_eq_left (decide_eq_true hA)]
      rw [show (x.raw.1,(x.raw.2.1,CopyState.CountsProgram.mask q.Δ x.raw.2.2))=
        GridDataProgram.Input.raw q ⟨x.f,x.j,x.d₀,x.d,CopyState.activeSlots x.n hn,hA⟩ by
          unfold Input.raw GridDataProgram.Input.raw
          dsimp only
          rw [CopyState.CountsProgram.mask_view x.n hn]]
      exact GridDataProgram.prepare_input q _
    · simp only [dite_eq_right hA,decide_eq_false hA,Bool.false_eq_true,ite_false]
  · rw [dite_eq_right hn]
    have hv : valid q.Δ x.raw=false := by
      unfold valid Input.raw
      dsimp only
      rw [cap_input q x,decide_eq_false hn,Bool.false_and]
    simp only [hv,Bool.false_eq_true,ite_false]

 theorem finish_input (x : Input) : finish q (x.raw,SelectionProgram.Input.result q (x.selection q))=x.result q := by
  unfold finish Input.result RationalParameters.roundCounts
  by_cases hn : ∀ i, x.n i≤q.Δ
  · rw [dite_eq_left hn,valid_input q x hn]
    by_cases hA : q.Δ≤(CopyState.activeSlots x.n hn).card
    · simp only [dite_eq_left hA,decide_eq_true hA,ite_true,Input.selection,dite_eq_left hn]
      rfl
    · simp only [dite_eq_right hA,decide_eq_false hA,Bool.false_eq_true,ite_false,Option.map_none,Option.toList_none]
  · rw [dite_eq_right hn]
    have hv : valid q.Δ x.raw=false := by
      unfold valid Input.raw
      dsimp only
      rw [cap_input q x,decide_eq_false hn,Bool.false_and]
    simp only [hv,Bool.false_eq_true,ite_false,Option.map_none,Option.toList_none]

noncomputable def program : PolyProgram Input.encode SparseGraph.ListOperation.et (Input.result q) := by
  let p : PolyProgram Input.encode (SelectionProgram.Input.encode q) (fun x => x.selection q) :=
    (prepare_poly q).program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (prepare_input q x))
  let r : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  exact (r.fanout (p.comp (SelectionProgram.program q)) |>.comp (finish_poly q).program).congr _ (finish_input q)
end MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedScanProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
noncomputable def itemsProgram : PolyProgram Input.encode (encodeList RoundCountsProgram.Input.encode) Input.items :=
  prepare_poly.program.recode Input.raw (fun _ => rfl) (fun x => by
    change encodeList enc (prepare x.raw)=_
    rw [prepare_input,encodeList_map]
    rfl)

 theorem images_input (x : Input) : images (x.raw,x.items.map (RoundCountsProgram.Input.result q))=
    (x.candidates q).map setView := by
  simp only [images,Input.items,List.map_map,Function.comp_def,RoundCountsProgram.Input.result,
    Input.item,Input.raw]
  rw [List.map_flatten]
  simp only [List.map_map,Function.comp_def,← Option.toList_map,Option.map_map]
  change (x.ns.map (fun n => (((q.roundCounts (fun a b => x.df (x.orig a) (x.orig b))
    (fun c a => x.dc c (x.orig a)) n).map (fun O => MaskProgram.imageRaw
      ((List.replicate x.h (),List.ofFn (fun i => (x.orig i).val)),setView O))).toList))).flatten=_
  simp only [MaskProgram.imageRaw_view]
  simp only [Input.candidates,RationalParameters.countCandidates,
    List.flatMap_def,List.map_flatten,List.map_map]
  simp only [← Option.toList_map,Option.map_map,Function.comp_def]

noncomputable def candidatesProgram : PolyProgram Input.encode SparseGraph.ListOperation.et
    (fun x => (x.candidates q).map setView) := by
  let r : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let p := itemsProgram.comp ((RoundCountsProgram.program q).listMap dummy)
  exact (r.fanout p |>.comp images_poly.program).congr _ (images_input q)

noncomputable def program : PolyProgram Input.encode SparseGraph.ListOperation.et (Input.result q) := by
  let m := metadata_poly.program.recode Input.raw (fun _ => rfl) (fun _ => rfl)
  exact (m.fanout (candidatesProgram q) |>.comp Completion.Rational.BestProgram.raw_poly.program).congr _ (fun x => by
    change Completion.Rational.BestProgram.raw ((x.budget,List.ofFn (fun c => List.ofFn (x.dc c))),
      (x.candidates q).map setView)=x.result q
    rw [Completion.Rational.BestProgram.raw_best]
    rfl)
end MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedPreparationProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparseSignedPreparation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
abbrev Input.encode (x : Input) := enc x.raw

end MetricKMedian.SparseSignedPreparation.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_GridRoundingProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGridRounding.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
 theorem post_result (x : Input) : post (x.raw,SparseCardinalRounding.Program.result x.cardinal)=x.result := by
  have hv : Vector.ofFn x.cardinal.p = fraction x.q := vector_point (fraction x.q)
  have hr : SparseCardinalRounding.round (Vector.ofFn x.cardinal.p) = SparseCardinalRounding.round (fraction x.q) := congrArg (fun p : Vector ℚ x.n => SparseCardinalRounding.round p) hv
  simp only [post,Input.result,law,SparseCardinalRounding.Program.result,SparseGraph.Program.columnRaw,
    SparseIntegerLaw.map,Vector.toList_map,List.map_map,Function.comp_def,Input.raw,
    SparseIntegerLaw.BinarySparse.raw]
  rw [hr]
  congr 2
  funext p

  exact counts_view x.q p

noncomputable def program : PolyProgram Input.encode (enc : Data (List ℕ) → List Bool) Input.result :=
  (((identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)).fanout
    (cardinalInputProgram.comp SparseCardinalRounding.Program.program) |>.comp post_poly.program).congr _ post_result
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

def KernelInput.result (x : KernelInput) : Data PreparedRaw :=
  ((SparseIntegerLaw.BinarySparse.raw (kernel x.D x.q x.Δ x.P x.y x.p x.z)).1,
    (kernel x.D x.q x.Δ x.P x.y x.p x.z).states.toList.map view)
end MetricKMedian.SparsePrepared.Program
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
theorem result_bind (x : Input) : x.result=
    ((SparseIntegerLaw.BinarySparse.raw (x.μ.bindIndexed (fun i => kernel x.D x.q x.Δ x.P x.y x.p x.μ.states[i.val]))).1,
      (x.μ.bindIndexed (fun i => kernel x.D x.q x.Δ x.P x.y x.p x.μ.states[i.val])).states.toList.map view) := rfl
theorem bind_result (x : Input) :
    bindData ((SparseIntegerLaw.BinarySparse.raw x.μ).1,x.kernels.map KernelInput.result)=x.result := by
  rw [result_bind]
  unfold Input.kernels
  simp only [List.map_ofFn,Function.comp_def,KernelInput.result,Input.ker]
  exact bindData_raw x.μ (fun i => kernel x.D x.q x.Δ x.P x.y x.p x.μ.states[i.val]) view
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalScanProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
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
def Input.raw (z : Input) : Raw := (z.toInput.raw,z.B)
abbrev Input.encode (z : Input) := enc z.raw

noncomputable def baseProgram : PolyProgram Input.encode Program.Input.encode Input.toInput :=
  (fst enc enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
noncomputable def budgetProgram : PolyProgram Input.encode enc Input.B :=
  (snd enc enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
noncomputable def unitProgram : PolyProgram Input.encode RationalUnitInput.ScanProgram.Input.encode Input.unit :=
  ((baseProgram.comp Program.unitProgram).fanout budgetProgram).recode id (fun _ => rfl) (fun _ => rfl)
attribute [local irreducible] RationalUnitInput.ScanProgram.Input.result
end MetricKMedian.Preparation.FractionalRefinement.ScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceRoundProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding
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
noncomputable def scanInputProgram : PolyProgram nzEncode FractionalRefinement.ScanProgram.Input.encode (scanInput r hr C) :=
  ((fractionalProgram r hr).fanout (budgetProgram C)).recode id (fun _ => rfl) (fun _ => rfl)
attribute [local irreducible] FractionalRefinement.scan Instance.computedFractional
end MetricKMedian.InstanceProgram
end

end OAI
end


