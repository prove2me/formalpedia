-- Prove2me | Definitions.Def_OAIQ035K069
-- name    : OAIQ035K069
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:21:34.868587+00:00
-- url     : https://prove2.me/theorems/df00b23d-e0ca-463d-8948-34e3cdb4fb42
-- title:
--   Definitions bundle OAIQ035K069 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 34 definitions and 8 theorems. The definitions and types are `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.candidatesProgram`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.program`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.program`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.historyProgram`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.itemsProgram`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.program`, `OAI.MetricKMedian.InstanceProgram.fractionalProgram`, `OAI.MetricKMedian.InstanceProgram.scanInputProgram`, `OAI.MetricKMedian.Preparation.FractionalRefinement.Program.unitProgram`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.baseProgram`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.unitProgram`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.preparedInputProgram`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.program`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.program`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.program`, `OAI.MetricKMedian.SparseBundles.Program.QInput.result`, `OAI.MetricKMedian.SparseBundles.Program.inputProgram`, `OAI.MetricKMedian.SparseBundles.Program.lawProgram`, `OAI.MetricKMedian.SparseCounts.Program.compressProgram`, `OAI.MetricKMedian.SparseCounts.Program.runStateProgram`, `OAI.MetricKMedian.SparseCounts.Program.stepProgram`, `OAI.MetricKMedian.SparseGridRounding.Program.Input.result`, `OAI.MetricKMedian.SparseGridRounding.Program.program`, `OAI.MetricKMedian.SparseOuterLaw.Program.Input.encode`, `OAI.MetricKMedian.SparseOuterLaw.Program.Input.result`, `OAI.MetricKMedian.SparseOuterLaw.Program.signedProgram`, `OAI.MetricKMedian.SparsePrepared.Program.Input.base`, `OAI.MetricKMedian.SparsePrepared.Program.Input.encode`, `OAI.MetricKMedian.SparsePrepared.Program.Input.raw`, `OAI.MetricKMedian.SparsePrepared.Program.Input.result`, `OAI.MetricKMedian.SparsePrepared.Program.KernelInput.result`, `OAI.MetricKMedian.SparsePrepared.Program.bundleInputProgram`, `OAI.MetricKMedian.SparsePrepared.Program.kernelProgram`, `OAI.MetricKMedian.SparsePrepared.Program.view`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Optimization_FractionalInputProgram`, `KMedian_Optimization_FractionalScanProgram`, `KMedian_Preparation_PreparedKernelProgram`, `KMedian_Preparation_PreparedLawProgram`, `KMedian_Preparation_PreparedScanProgram`, `KMedian_Preparation_SupplierPreparationProgram`, `KMedian_Process_CountRunProgram`, `KMedian_Process_CountStepProgram`, `KMedian_Process_PhysicalBatchUpdateProgram`, `KMedian_Process_PhysicalHistoriesProgram`, `KMedian_Process_PhysicalRoundProgram`, `KMedian_Process_RoundCountsProgram`, `KMedian_Programs_BundlesProgram`, `KMedian_Programs_HistorySelectionProgram`, `KMedian_Programs_InstanceDataProgram`, `KMedian_Programs_InstanceRoundProgram`, `KMedian_Programs_OuterLawProgram`, `KMedian_Rounding_GridRoundingProgram`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K065`, `OAIQ035K066` and `OAIQ035K067` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ035K073`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K065
import Definitions.Def_OAIQ035K066
import Definitions.Def_OAIQ035K067

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
noncomputable def unitProgram : PolyProgram Input.encode RationalUnitInput.Program.Input.encode Input.unit :=
  unitData_poly.program.recode Input.raw (fun _ => rfl) (fun z => congrArg enc (unitData_view z))
end MetricKMedian.Preparation.FractionalRefinement.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalBatchUpdateProgram
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

noncomputable def program : PolyProgram Input.encode (ed SparseGraph.ListOperation.er) Input.result := by
  let ctx : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  exact (ctx.fanout (proposalProgram.comp RationalBatchData.ProposalProgram.program) |>.comp finish_poly.program).congr _ finish_input
end MetricKMedian.RationalPhysicalKernel.UpdateProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalRoundProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalHistoriesProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundCountsProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Process_CountStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.SparseCounts.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table er et)

noncomputable def compressProgram : PolyProgram State.encode State.encode
    (Bundle.compress (fun c : Context => c.input.n*c.input.m+(c.input.n*c.input.m)*(c.input.n*c.input.m)) (fun _ => features)) :=
  SparseIntegerLaw.DependentProgram.compressProgram Context.encode et view [] _ (fun _ => features)
    (fun x => ListOperation.featureList (x.1.input.raw.1,x.2))
    (fun _ G => ListOperation.featureList_view G) dimensionsProgram featuresProgram

noncomputable def stepProgram : PolyProgram State.encode State.encode State.step :=
  ((PolyProgram.ite activeProgram (identity State.encode) (productProgram.comp compressProgram)).comp incrementProgram).congr _
    (fun x => by simp only [State.step,Function.comp_def,decide_eq_true_eq,id_eq])
end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseCounts.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table et)

noncomputable def runStateProgram : PolyProgram Input.encode State.encode (fun x => x.state x.m) :=
  (stepProgram.repeatFrom startProgram countProgram X sizePolynomial
    (fun x => by simpa using (input_bounds x).2.1)
    (fun x t ht => by rw [state_iterate]; exact state_size x t ht)).congr _ (fun x => state_iterate x _)
end MetricKMedian.SparseCounts.Program
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
 theorem counts_view {n : ℕ} (q : Fin n → ℚ) (p : Vector ℚ n) :
    counts (List.ofFn q,SparseGraph.ListOperation.setView (SparseCardinalRounding.selected p))=List.ofFn (SparseGridRounding.count q p) := by
  simp only [counts,SparseGraph.ListOperation.indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,
    List.map_ofFn,Function.comp_def,SparseGraph.ListOperation.setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),
    Option.getD_some,Fin.eta,SparseCardinalRounding.selected,Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq]
  rfl

def Input.result (x : Input) : Data (List ℕ) :=
  ((SparseIntegerLaw.BinarySparse.raw (law x.q)).1,(law x.q).states.toList.map List.ofFn)
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
-- module Solutions.OAIQ035_KM.KMedian_Programs_BundlesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseBundles.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram SparseCounts.Program
def QInput.result (x : QInput) : Data SparseCounts.ListOperation.Table :=
  (((SparseBundles.law x.q).law.denominator,List.ofFn (SparseBundles.law x.q).law.numerator),
    (SparseBundles.law x.q).states.toList.map SparseCounts.ListOperation.view)

noncomputable def inputProgram : PolyProgram QInput.encode Input.encode QInput.input := by
  let n := (fst (encodeList (fun _ : Unit => [])) qt).recode QInput.raw (fun _ => rfl) (fun _ => rfl)
  let cols := columnsProgram.comp (SparseGridRounding.Program.program.listMap emptyColumn)
  exact (n.fanout cols).recode id (fun _ => rfl) (fun x => by
    change ei (x.raw.1,x.columns.map SparseGridRounding.Program.Input.result)=Input.encode x.input
    simp only [QInput.columns,List.map_ofFn,Function.comp_def]
    rfl)

noncomputable def lawProgram : PolyProgram QInput.encode (ed SparseCounts.ListOperation.et) QInput.result := by
  let get : PolyProgram State.encode (ed SparseCounts.ListOperation.et) (fun x : State => (x.raw view).2) :=
    (snd Context.encode (ed SparseCounts.ListOperation.et)).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)
  exact (inputProgram.comp runStateProgram |>.comp get).congr _ (fun _ => rfl)
end MetricKMedian.SparseBundles.Program
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

noncomputable def bundleInputProgram : PolyProgram KernelInput.encode SparseBundles.Program.QInput.encode KernelInput.bundles :=
  bundleData_poly.program.recode KernelInput.raw (fun _ => rfl) (fun x => by
    unfold bundleData
    rw [pieces_view]
    simp only [KernelInput.raw,KernelInput.base,List.map_const',List.length_ofFn,
      SparseBundles.Program.QInput.encode,SparseBundles.Program.QInput.raw,KernelInput.bundles]
    rfl)

def view {n m f : ℕ} (s : SparseSignedPreparation.State n m × SparseCounts.Table f n) : PreparedRaw :=
  (SparseSignedPreparation.Program.view s.1,SparseCounts.ListOperation.view s.2)
def KernelInput.result (x : KernelInput) : Data PreparedRaw :=
  ((SparseIntegerLaw.BinarySparse.raw (kernel x.D x.q x.Δ x.P x.y x.p x.z)).1,
    (kernel x.D x.q x.Δ x.P x.y x.p x.z).states.toList.map view)
theorem kernel_result (x : KernelInput) :
    attach (SparseSignedPreparation.Program.view x.z,SparseBundles.Program.QInput.result x.bundles)=x.result := by
  simp only [attach,KernelInput.result,kernel,SparseIntegerLaw.map,SparseIntegerLaw.BinarySparse.raw,
    SparseBundles.Program.QInput.result,KernelInput.bundles,Vector.toList_map,List.map_map,Function.comp_def,view]
noncomputable def kernelProgram : PolyProgram KernelInput.encode (enc : Data PreparedRaw → List Bool) KernelInput.result := by
  let z : PolyProgram KernelInput.encode enc (fun x => SparseSignedPreparation.Program.view x.z) :=
    (snd enc enc).recode KernelInput.raw (fun _ => rfl) (fun _ => rfl)
  exact (z.fanout (bundleInputProgram.comp SparseBundles.Program.lawProgram) |>.comp attach_poly.program).congr _ kernel_result
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
abbrev Input.encode (x : Input) := enc x.raw
noncomputable def signedProgram : PolyProgram Input.encode SparseSignedPreparation.Program.Input.encode Input.signed :=
  post_poly.program.recode Input.raw (fun _ => rfl) (fun x => by
    simp only [post,Input.raw,SparseGridRounding.Program.fractionRow_list,
      SparseSignedPreparation.Program.Input.encode,SparseSignedPreparation.Program.Input.raw,Input.signed])
def Input.result (x : Input) : Data SparseSignedPreparation.Program.StateRaw :=
  ((SparseIntegerLaw.BinarySparse.raw (law x.D x.c x.q x.c_unit x.q_nonnegative)).1,
    (law x.D x.c x.q x.c_unit x.q_nonnegative).states.toList.map SparseSignedPreparation.Program.view)
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
def Input.base (x : Input) : BaseRaw :=
  (List.ofFn (fun e => setView (x.D e)),(List.ofFn x.q,(List.ofFn (fun j => setView (x.P j)),
    (List.ofFn x.y,(List.ofFn x.p,x.Δ)))))
def Input.raw (x : Input) : Raw := (x.base,List.ofFn x.c)
abbrev Input.encode (x : Input) := enc x.raw

def Input.result (x : Input) : Data PreparedRaw :=
  ((SparseIntegerLaw.BinarySparse.raw (law x.D x.c x.q x.Δ x.P x.y x.p x.hc x.hq)).1,
    (law x.D x.c x.q x.Δ x.P x.y x.p x.hc x.hq).states.toList.map view)
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
noncomputable def baseProgram : PolyProgram Input.encode Program.Input.encode Input.toInput :=
  (fst enc enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
noncomputable def unitProgram : PolyProgram Input.encode RationalUnitInput.ScanProgram.Input.encode Input.unit :=
  ((baseProgram.comp Program.unitProgram).fanout budgetProgram).recode id (fun _ => rfl) (fun _ => rfl)
attribute [local irreducible] RationalUnitInput.ScanProgram.Input.result
end MetricKMedian.Preparation.FractionalRefinement.ScanProgram
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
variable (r : ℕ) (hr : 0 < r)
noncomputable def fractionalProgram : PolyProgram nzEncode FractionalRefinement.Program.Input.encode (fractionalInput r hr) :=
  (((identity enc).recode (fun I : Nonzero => view I.val) (fun _ => rfl) (fun _ => rfl) |>.fanout
    (lpProgram.comp (LPBinary.Scale.selectedProgram r hr))).comp fractionalData_poly.program).recode
      id (fun _ => rfl) (fun I => congrArg enc (fractionalData_view r hr I))
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
noncomputable def scanInputProgram : PolyProgram nzEncode FractionalRefinement.ScanProgram.Input.encode (scanInput r hr C) :=
  ((fractionalProgram r hr).fanout (budgetProgram C)).recode id (fun _ => rfl) (fun _ => rfl)
attribute [local irreducible] FractionalRefinement.scan Instance.computedFractional
end MetricKMedian.InstanceProgram
end

end OAI
end


