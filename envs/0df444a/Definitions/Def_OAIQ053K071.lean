-- Prove2me | Definitions.Def_OAIQ053K071
-- name    : OAIQ053K071
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:18:46.877175+00:00
-- url     : https://prove2.me/theorems/124b0eeb-ef13-45c5-9828-3e00ddfa9995
-- title:
--   Definitions bundle OAIQ053K071 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 54 declarations of OpenAI's Lean: 40 definitions and 14 theorems. The definitions and types are `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.Input.result`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.Input.result`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.Input.encode`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.Input.items`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.Input.result`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.dummy`, `OAI.MetricKMedian.InputParser.matrix`, `OAI.MetricKMedian.InputParser.raw`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.Raw`, `OAI.MetricKMedian.RationalBatchData.ActionTransition.view`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.Input.encode`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.inputProgram`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.program`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.program`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.graphProgram`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.inputsProgram`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.Input.encode`, `OAI.MetricKMedian.SparseBernoulli.Program.activeProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.branchProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.compressProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.incrementProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.runStateProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.startProgram`, `OAI.MetricKMedian.SparseBernoulli.Program.stepProgram`, `OAI.MetricKMedian.SparseCardinalRounding.Program.program`, `OAI.MetricKMedian.SparseGraph.Program.activeProgram`, `OAI.MetricKMedian.SparseGraph.Program.compressProgram`, `OAI.MetricKMedian.SparseGraph.Program.inputProgram`, `OAI.MetricKMedian.SparseGraph.Program.lawProgram`, `OAI.MetricKMedian.SparseGraph.Program.runStateProgram`, `OAI.MetricKMedian.SparseGraph.Program.stepProgram`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.branchProgram`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.compressProgram`, `OAI.MetricKMedian.SparseIntegerLaw.DependentProgram.compressionInputProgram`, `OAI.MetricKMedian.SparsePhysicalBatch.Program.bernInputProgram`, `OAI.MetricKMedian.SparsePhysicalBatch.Program.bernProgram`, `OAI.MetricKMedian.SparsePhysicalBatch.Program.partProgram`, `OAI.MetricKMedian.SparsePhysicalBatch.Program.program`, `OAI.MetricKMedian.TaperGraphProgram.program`, `OAI.MetricKMedian.TaperGraphProgram.qInputProgram`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_InstanceParserProgram`, `KMedian_Optimization_FractionalScanProgram`, `KMedian_Preparation_PreparedScanProgram`, `KMedian_Probability_BernoulliRunProgram`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_ActionTransitionList`, `KMedian_Process_BatchOrdinalArrays`, `KMedian_Process_BatchProposalProgram`, `KMedian_Process_CopyGraphProgram`, `KMedian_Process_PhysicalBatchProgram`, `KMedian_Process_PhysicalBatchUpdateProgram`, `KMedian_Process_PhysicalHistoriesProgram`, `KMedian_Process_PhysicalRoundProgram`, `KMedian_Process_RoundCountsProgram`, `KMedian_Process_TaperGraphProgram`, `KMedian_Programs_CardinalRoundProgram`, `KMedian_Programs_DependentSparseProgram`, `KMedian_Programs_GraphLawProgram`, `KMedian_Programs_GraphRunProgram`, `KMedian_Programs_GraphStepProgram`, `KMedian_Programs_HistorySelectionProgram`.
--
--   **Imports.** It imports the bundles `OAIQ053K063`, `OAIQ053K064`, `OAIQ053K065` and `OAIQ053K066` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K075` and `OAIQ053K076`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K063
import Definitions.Def_OAIQ053K064
import Definitions.Def_OAIQ053K065
import Definitions.Def_OAIQ053K066

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
def matrix (x : Row × List Bool) : InstanceProgram.Matrix :=
  reshape (x.1,(parse ratRead (squareUnits x.1,x.2)).1)

def raw (xs : List Bool) : Raw :=
  let h := header xs
  (h.1.1,(h.1.2,matrix (h.1.1.1,h.2)))
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchOrdinalArrays
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

 theorem transpose_graph (G : I → Finset I) :
    GraphData.transpose (graphView r G)=List.ofFn (fun h => sets r ((graph G).erase (r h))) := by
  simp only [GraphData.transpose,graphView,indices,List.length_ofFn,RoundingList.range_finRange,
    Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,sets_eq,List.getElem?_ofFn,
    dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,graph,mem_filter,mem_univ,true_and]
 theorem masses_graph (G : I → Finset I) (g : ℚ) :
    GraphData.masses (g,graphView r G)=List.ofFn (fun h => graphMass G g (r h)) := by
  simp only [GraphData.masses,transpose_graph,List.map_ofFn,Function.comp_def,sets_card]
  rfl
 theorem heavy_graph (G : I → Finset I) (g b : ℚ) :
    GraphData.heavy (b,GraphData.masses (g,graphView r G))=sets r (heavySet (graphMass G g) b) := by
  rw [masses_graph]
  simp only [GraphData.heavy,GraphData.amount_view,List.map_ofFn,Function.comp_def,sets_eq,
    heavySet,mem_filter,mem_univ,true_and]
  have ha : RationalBatchData.amount (fun h => graphMass G g (r h))=RationalBatchData.amount (graphMass G g) :=
    r.toEquiv.sum_comp (fun h => max (1-graphMass G g h) 0)
  rw [ha]
 theorem prepare_graph (G : I → Finset I) (g b p φ : ℚ) (Δ : ℕ) :
    GraphData.prepare (((g,b),(Δ,(p,φ))),graphView r G)=
      ((((p,φ),List.ofFn (fun h => graphMass G g (r h))),Δ),view r (graph G) (heavySet (graphMass G g) b)) := by
  unfold GraphData.prepare
  dsimp only
  rw [heavy_graph,masses_graph,transpose_graph]
  rfl
end MetricKMedian.RationalBatchData.Ordinal
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

noncomputable def compressionInputProgram (a0 : A) (d : C → ℕ) (v : ∀ c, T c → Fin (d c) → ℚ)
    (F : C × A → List ℚ) (hF : ∀ c a, F (c,view c a)=List.ofFn (v c a))
    (D : PolyProgram ec IntegerLaw.BinaryCompression.es (fun c => List.replicate (d c) ()))
    (V : PolyProgram (encodePair ec ea) IntegerLaw.BinaryCompression.eqr F) :
    PolyProgram (Bundle.encode ec ea view) IntegerLaw.BinaryCompression.RationalInput.encode
      (Bundle.compressionInput d v) := by
  let ctx := contextProgram ec ea view
  let rows := (ctx.fanout (statesProgram ec ea view)).comp (V.listMapWith a0 [])
  let work := (ctx.comp D).fanout ((lawProgram ec ea view).fanout rows)
  exact work.recode id (fun _ => rfl) (fun x => by
    change IntegerLaw.BinaryCompression.eqd (List.replicate (d x.ctx) (),
      ((x.law.law.denominator,List.ofFn x.law.law.numerator),
        (x.law.states.toList.map (view x.ctx)).map (fun a => F (x.ctx,a))))=_
    simp only [states_list,List.map_ofFn,Function.comp_def,hF]
    rfl)

noncomputable def compressProgram (a0 : A) (d : C → ℕ) (v : ∀ c, T c → Fin (d c) → ℚ)
    (F : C × A → List ℚ) (hF : ∀ c a, F (c,view c a)=List.ofFn (v c a))
    (D : PolyProgram ec IntegerLaw.BinaryCompression.es (fun c => List.replicate (d c) ()))
    (V : PolyProgram (encodePair ec ea) IntegerLaw.BinaryCompression.eqr F) :
    PolyProgram (Bundle.encode ec ea view) (Bundle.encode ec ea view) (Bundle.compress d v) := by
  let law := (compressionInputProgram ec ea view a0 d v F hF D V).comp IntegerLaw.BinaryCompression.rationalCompressProgram
  let trimmed := (law.fanout (statesProgram ec ea view)).comp (trimDataProgram ea a0)
  let work := (contextProgram ec ea view).fanout trimmed
  exact work.recode id (fun _ => rfl) (fun x => by
    change encodePair ec (ed ea) (x.ctx,
      trimData (((x.law.law.compressAuto (fun i => v x.ctx x.law.states[i.val])).denominator,
       List.ofFn (x.law.law.compressAuto (fun i => v x.ctx x.law.states[i.val])).numerator),
         x.law.states.toList.map (view x.ctx)))=_
    rw [show trimData _= _ from trim_view view x.ctx
      (⟨x.law.length,x.law.states,x.law.law.compressAuto (fun i => v x.ctx x.law.states[i.val])⟩ : SparseIntegerLaw (T x.ctx))]
    rfl)

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
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliStepProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram
 theorem endpoint_view (c : Context) (q : T c) (b : Fin 2) :
    rowEndpoint (decide (b=0)) (c,view c q)=view c (endpoint c q b) := by
  apply List.ext_getElem
  · simp only [rowEndpoint,ListOperation.endpoint,List.length_map,List.length_range,view,List.length_ofFn]
  · intro i hi hi'
    have hin : i < c.input.n := by simpa only [view,List.length_ofFn] using hi'
    simp only [rowEndpoint,ListOperation.endpoint,view,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,List.getElem?_ofFn,dite_eq_left hin,Option.getD_some,endpoint]

noncomputable def branchProgram : PolyProgram State.encode State.encode (Bundle.branch probability probability_unit endpoint) :=
  SparseIntegerLaw.DependentProgram.branchProgram Context.encode er view [] probability probability_unit endpoint
    rowProbability (rowEndpoint true) (rowEndpoint false) probability_view
    (fun c q => endpoint_view c q 0) (fun c q => endpoint_view c q 1)
    probabilityProgram (endpointProgram true) (endpointProgram false)

noncomputable def compressProgram (d : ℕ) : PolyProgram State.encode State.encode
    (Bundle.compress (fun c : Context => (c.input.n+1)^d) (fun _ => features (d:=d))) :=
  SparseIntegerLaw.DependentProgram.compressProgram Context.encode er view [] (fun c => (c.input.n+1)^d) (fun _ => features (d:=d))
    (fun x => ListOperation.featureList d x.2) (fun _ q => ListOperation.featureList_ofFn q)
    (dimensionsProgram d) (featuresProgram d)

noncomputable def incrementProgram : PolyProgram State.encode State.encode State.increment := by
  let old := fst Context.encode (SparseIntegerLaw.BinarySparse.ed er)
  let inp := old.comp ((fst qr Nat.bits).recode Context.raw (fun _ => rfl) (fun _ => rfl))
  let t := old.comp ((snd qr Nat.bits).recode Context.raw (fun _ => rfl) (fun _ => rfl))
  let inc := (t.fanout (constant _ Nat.bits 1)).comp natAdd
  let law := snd Context.encode (SparseIntegerLaw.BinarySparse.ed er)
  exact ((inp.fanout inc).fanout law).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)
noncomputable def activeProgram : PolyProgram State.encode encodeBool
    (fun x : State => decide (x.ctx.t<x.ctx.input.n)) := by
  let raw : PolyProgram (encodePair qr Nat.bits) encodeBool
      (fun x : List ℚ × ℕ => decide (x.2<x.1.length)) := Binary.Automatic.Poly.program (by fun_prop)
  let ctx : PolyProgram Context.encode encodeBool (fun c => decide (c.t < c.input.n)) := raw.recode Context.raw (fun _ => rfl) (fun c => by simp only [List.length_ofFn])
  exact (contextProgram Context.encode er view).comp ctx
noncomputable def stepProgram (d : ℕ) : PolyProgram State.encode State.encode (State.step d) :=
  ((PolyProgram.ite activeProgram (identity State.encode) (branchProgram.comp (compressProgram d))).comp incrementProgram).congr _
    (fun x => by simp only [State.step,Function.comp_def,decide_eq_true_eq,id_eq])

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphStepProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table er et)

noncomputable def compressProgram : PolyProgram State.encode State.encode
    (Bundle.compress (fun c : Context => c.input.n*c.input.m+(c.input.n*c.input.m)*(c.input.n*c.input.m)) (fun _ => features)) :=
  SparseIntegerLaw.DependentProgram.compressProgram Context.encode et view [] _ (fun _ => features)
    (fun x => ListOperation.featureList (x.1.input.raw.1,x.2))
    (fun _ G => ListOperation.featureList_view G) dimensionsProgram featuresProgram

noncomputable def activeProgram : PolyProgram State.encode encodeBool
    (fun x : State => decide (x.ctx.t<x.ctx.input.m)) := by
  let raw : PolyProgram (encodePair ei Nat.bits) encodeBool
      (fun x : InputRaw × ℕ => decide (x.2<x.1.2.length)) := Binary.Automatic.Poly.program (by fun_prop)
  let ctx : PolyProgram Context.encode encodeBool (fun c => decide (c.t < c.input.m)) := raw.recode Context.raw (fun _ => rfl)
    (fun c => by simp only [Context.raw,Input.raw,List.length_ofFn])
  exact (contextProgram Context.encode et view).comp ctx
noncomputable def stepProgram : PolyProgram State.encode State.encode State.step :=
  ((PolyProgram.ite activeProgram (identity State.encode) (productProgram.comp compressProgram)).comp incrementProgram).congr _
    (fun x => by simp only [State.step,Function.comp_def,decide_eq_true_eq,id_eq])
end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_CardinalRoundProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseCardinalRounding.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse

noncomputable def program : PolyProgram encodeInput (ed br) result := by
  let part := inputProgram.comp (RoundingProgram.runProgram false)
  let get : PolyProgram RoundingProgram.State.encode (ed RoundingProgram.erow)
      (fun x : RoundingProgram.State false => RoundingProgram.vectorData x.μ) :=
    (snd RoundingProgram.erow (ed RoundingProgram.erow)).recode RoundingProgram.State.raw
      RoundingProgram.State.encode_raw (fun _ => rfl)
  let post : PolyProgram (ed RoundingProgram.erow) (ed br)
      (fun x : Data (List ℚ) => (x.1,x.2.map selectedRow)) := by
    apply Binary.Automatic.Poly.program
    apply Binary.Automatic.Poly.pair
    · fun_prop
    · apply Binary.Automatic.Poly.list_map <;> fun_prop
  exact (part.comp get |>.comp post).congr _ (fun x => by
    simp only [Function.comp_def,result,RoundingProgram.vectorData,SparseGraph.Program.columnRaw,
      SparseIntegerLaw.map,Vector.toList_map,List.map_map,selectedRow_eq]
    rfl)
end MetricKMedian.SparseCardinalRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphRunProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table et)

noncomputable def runStateProgram : PolyProgram Input.encode State.encode (fun x => x.state x.m) :=
  (stepProgram.repeatFrom startProgram countProgram X sizePolynomial
    (fun x => by simpa using (input_bounds x).2.1)
    (fun x t ht => by rw [state_iterate]; exact state_size x t ht)).congr _ (fun x => state_iterate x _)
end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram

noncomputable def inputProgram : PolyProgram QInput.encode Input.encode QInput.input := by
  let n := (fst (encodeList (fun _ : Unit => [])) qt).recode QInput.raw (fun _ => rfl) (fun _ => rfl)
  let cols := columnsProgram.comp (SparseCardinalRounding.Program.program.listMap emptyColumn)
  exact (n.fanout cols).recode id (fun _ => rfl) (fun x => by
    change ei (x.raw.1,x.columns.map SparseCardinalRounding.Program.result)=Input.encode x.input
    simp only [QInput.columns,List.map_ofFn,Function.comp_def]
    rfl)

noncomputable def lawProgram : PolyProgram QInput.encode (ed ListOperation.et) QInput.result := by
  let get : PolyProgram State.encode (ed ListOperation.et) (fun x : State => (x.raw view).2) :=
    (snd Context.encode (ed ListOperation.et)).recode (Bundle.raw view) (fun _ => rfl) (fun _ => rfl)
  exact (inputProgram.comp runStateProgram |>.comp get).congr _ (fun _ => rfl)
end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperGraphProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.TaperGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse

noncomputable def qInputProgram : PolyProgram Input.encode SparseGraph.Program.QInput.encode Input.qInput :=
  rawQ_poly.program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (rawQ_input x))
noncomputable def program : PolyProgram Input.encode (ed SparseGraph.ListOperation.et)
    (fun x : Input => x.qInput.result) := qInputProgram.comp SparseGraph.Program.lawProgram
end MetricKMedian.TaperGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyGraphProgram
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

noncomputable def program : PolyProgram Input.encode (ed SparseGraph.ListOperation.et) Input.result :=
  (taperProgram.comp TaperGraphProgram.program).congr _ result_eq

end MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliRunProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
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

noncomputable def runStateProgram (d : ℕ) : PolyProgram Input.encode State.encode (fun x => x.state d x.n) :=
  ((stepProgram d).repeatFrom startProgram countProgram X (sizePolynomial d)
    (fun x => by simpa using (input_bounds x).1)
    (fun x t ht => by rw [state_iterate]; exact state_size x d t ht)).congr _ (fun x => state_iterate x d _)

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
local notation "br" => SparseGraph.ListOperation.er

noncomputable def bernInputProgram (bal : Bool) :
    PolyProgram Input.encode SparseBernoulli.Program.Input.encode (Input.bernInput bal) := by
  let raw : PolyProgram Binary.Automatic.enc SparseBernoulli.Program.qr
      (fun x : ListOperation.Raw => if bal then x.2.2.map (fun _ => x.2.1) else x.2.2) := by
    apply Binary.Automatic.Poly.program
    have hm : Binary.Automatic.Poly (fun x : ListOperation.Raw => x.2.2.map (fun _ => x.2.1)) := by
      apply Binary.Automatic.Poly.list_map <;> fun_prop
    fun_prop
  exact raw.recode Input.raw (fun _ => rfl) (fun x => by
    cases bal <;> simp only [Bool.false_eq_true,ite_false,ite_true,Input.raw,List.map_const',List.length_ofFn,
      Input.bernInput,SparseBernoulli.Program.Input.encode,List.ofFn_const,Fin.cast_eq_self])

noncomputable def bernProgram (bal : Bool) : PolyProgram Input.encode (ed br)
    (fun x : Input => (((x.bern bal).law.denominator,List.ofFn (x.bern bal).law.numerator),
      (x.bern bal).states.toList.map List.ofFn)) := by
  let get : PolyProgram SparseBernoulli.Program.State.encode (ed br)
      (fun x : SparseBernoulli.Program.State => (x.raw SparseBernoulli.Program.view).2) :=
    (snd SparseBernoulli.Program.Context.encode (ed br)).recode
      (Bundle.raw SparseBernoulli.Program.view) (fun _ => rfl) (fun _ => rfl)
  exact (bernInputProgram bal |>.comp (SparseBernoulli.Program.runStateProgram 4) |>.comp get).congr _ (fun _ => rfl)

noncomputable def partProgram (bal : Bool) : PolyProgram Input.encode (ed br) (Input.partData bal) := by
  let ctx : PolyProgram Input.encode Binary.Automatic.enc Input.raw := (identity Binary.Automatic.enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let post : PolyProgram (encodePair Binary.Automatic.enc (ed br)) (ed br)
      (fun x : ListOperation.Raw × Data Row => (x.2.1,x.2.2.map (fun row => ListOperation.select bal (x.1,row)))) := by
    apply Binary.Automatic.Poly.program
    apply Binary.Automatic.Poly.pair
    · fun_prop
    · apply Binary.Automatic.Poly.list_map <;> fun_prop
  exact (ctx.fanout (bernProgram bal) |>.comp post).congr _ (fun x => by
    simp only [Function.comp_def,Input.partData,Input.part,SparseIntegerLaw.map,Vector.toList_map,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro ω hω
    exact ListOperation.select_view x.Z x.C x.p x.q ω bal)

noncomputable def program : PolyProgram Input.encode (ed br) Input.result :=
  ((partProgram true).fanout (partProgram false) |>.comp mixData_poly.program).congr _ (fun x => by
    change mixData (((raw (x.part true)).1,(x.part true).states.toList.map SparseGraph.ListOperation.setView),
      ((raw (x.part false)).1,(x.part false).states.toList.map SparseGraph.ListOperation.setView))=_
    rw [mixData_raw]
    rfl)
end MetricKMedian.SparsePhysicalBatch.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchProposalProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
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

abbrev Input.encode (x : Input I) := Binary.Automatic.enc x.raw

 theorem data_input (x : Input I) : GraphData.data x.raw=x.batch.raw := by
  unfold GraphData.data Input.raw
  rw [Ordinal.prepare_graph,Ordinal.data_view]
  rfl
noncomputable def inputProgram : PolyProgram (Input.encode (I:=I)) SparsePhysicalBatch.Program.Input.encode Input.batch :=
  GraphData.data_poly.program.recode Input.raw (fun _ => rfl) (fun x => congrArg Binary.Automatic.enc (data_input x))

noncomputable def program : PolyProgram (Input.encode (I:=I)) (ed SparseGraph.ListOperation.er) Input.result :=
  (inputProgram.comp SparsePhysicalBatch.Program.program).congr _ (fun x => result_eq x)
end MetricKMedian.RationalBatchData.ProposalProgram
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
def view : Raw := (Ordinal.view r D H,setView (Z.map (enumeration D H).symm.toEmbedding))
 theorem selected_mem (c : ℕ) : c∈selected (view r D H Z) ↔ ∃ e∈Z, Ordinal.code r D H e=c := by
  simp only [selected,view,Ordinal.codes_eq,setView,mem_map_equiv,Equiv.symm_symm,
    Gaussian.ListOperation.zip_ofFn,List.mem_map,List.mem_filter,List.mem_ofFn]
  constructor
  · rintro ⟨z,⟨⟨i,rfl⟩,he⟩,hc⟩
    exact ⟨enumeration D H i,of_decide_eq_true he,hc⟩
  · rintro ⟨e,he,rfl⟩
    refine ⟨_,⟨⟨(enumeration D H).symm e,rfl⟩,?_⟩,?_⟩ <;>
      simp only [Equiv.apply_symm_apply,decide_eq_true he]

end MetricKMedian.RationalBatchData.ActionTransition
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchUpdateProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
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
abbrev Input.encode (x : Input) := enc x.raw

end MetricKMedian.RationalPhysicalKernel.UpdateProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalRoundProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
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

noncomputable def graphProgram : PolyProgram ctxEncode (ed SparseGraph.ListOperation.et)
    (fun x => x.toInput.result) :=
  (show PolyProgram ctxEncode CopyGraphProgram.Input.encode (fun x : Context => x.toInput) from
    (fst enc enc).recode ctxRaw (fun _ => rfl) (fun _ => rfl)).comp CopyGraphProgram.program

noncomputable def inputsProgram : PolyProgram ctxEncode
    (encodePair enc (encodeList UpdateProgram.Input.encode)) (fun x => (x.toInput.result.1,(ctxInputs x))) := by
  let ctx : PolyProgram ctxEncode enc ctxRaw := (identity enc).recode ctxRaw (fun _ => rfl) (fun _ => rfl)
  exact (ctx.fanout graphProgram |>.comp attach_poly.program).recode id (fun _ => rfl) (fun x => by
    dsimp only [Function.comp_def,id_eq]
    rw [attach_input]
    change encodePair enc (encodeList enc) _=encodePair enc (encodeList UpdateProgram.Input.encode) _
    apply congrArg (fun w => quote (enc x.toInput.result.1)++w)
    induction ctxInputs x with
    | nil => rfl
    | cons a as ih => simpa only [List.map_cons,encodeList,UpdateProgram.Input.encode] using congrArg (fun w => quote (enc a.raw)++w) ih)

end MetricKMedian.RationalPhysicalKernel.RoundProgram
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
 local instance instLinearOrderCopyFin_r9f6f96_1 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance instLinearOrderSubtypeCopyFinMemFinset_r9f6f96_1 {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A
theorem attach_result (P : ℕ → ℚ) (T : ℕ) (hP : 0<P T) (x : Context) :
    attach (P T) (RoundProgram.ctxRaw x,result P T x)=
      ((result P T x).1,(inputs P T hP x).map RoundProgram.ctxRaw) := by
  simp only [attach,result,table,inputs,List.map_map,Function.comp_def]
  rfl

 theorem conditional (P : ℕ → ℚ) (T : ℕ) (hP : 0<P T) (x : Context) (z : Hist x) :
    RoundProgram.ctxResult (nextCtx x (P T) hP z.1.1)=
      table (SparseHistories.branch (step x.d x.g x.β x.p x.φ (P T) x.hp x.hφ x.hupper) z) (view x) := by
  change table (RoundProgram.ctxLaw (nextCtx x (P T) hP z.1.1)) CopyList.view=_
  have hs := RoundProgram.law_step (nextCtx x (P T) hP z.1.1) z.1 rfl
  rw [hs,table_map]
  unfold SparseHistories.branch
  rw [table_map]
  rfl

end MetricKMedian.RationalPhysicalKernel.HistoryProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_HistorySelectionProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
abbrev Input.encode (x : Input q) := enc x.raw

local instance instLinearOrderCopyFin_r9f6f96_2 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
def Input.items (x : Input q) : List (Completion.Rational.Program.Input q.Δ) :=
  (q.tree x.d₀ x.A).states.toList.map (fun z => {x.toInput with A:=z.1.1})
 theorem attach_input (x : Input q) : attach (x.raw,HistoryProgram.result q.taperAt q.T x.ctx)=
    x.items.map Completion.Rational.Program.Input.raw := by
  simp only [attach,HistoryProgram.result,table,Input.items,List.map_map,Function.comp_def]
  rfl

def dummy : Completion.Rational.Program.Input q.Δ where
  f := 0
  j := 0
  d := fun c => Fin.elim0 c
  R := fun c => Fin.elim0 c
  A := ∅
  B := fun c => Fin.elim0 c
  hB := fun c => Fin.elim0 c

def Input.result (x : Input q) : Table :=
  ((q.selectCompleted x.d₀ x.d x.R x.A x.B x.hB).map setView).toList
end MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundCountsProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
 theorem cap_input (x : Input) : cap q.Δ (List.ofFn x.n)=decide (∀ i, x.n i≤q.Δ) := by
  apply Bool.eq_iff_iff.mpr
  simp [cap]

 local instance instLinearOrderCopyFin_r9f6f96_3 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
theorem valid_input (x : Input) (hn : ∀ i, x.n i≤q.Δ) : valid q.Δ x.raw=decide (q.Δ≤(CopyState.activeSlots x.n hn).card) := by
  unfold valid Input.raw
  dsimp only
  rw [cap_input q x,decide_eq_true hn,Bool.true_and,CopyState.CountsProgram.mask_view x.n hn,
    CopyList.view,Completion.Rational.BestProgram.card_view,card_map]

def Input.result (x : Input) : Table := ((q.roundCounts x.d₀ x.d x.n).map setView).toList

end MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedScanProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
 theorem prepare_input (x : Input) : prepare x.raw=x.items.map RoundCountsProgram.Input.raw := by
  simp only [prepare,Input.raw,List.map_ofFn,Function.comp_def,MaskProgram.pullbackMatrix_view,
    MaskProgram.pullback_view,List.map_map,Input.items]
  apply List.map_congr_left
  intro n _
  simp only [Input.item,RoundCountsProgram.Input.raw]
  congr 1
  simp

def Input.result (x : Input) : Table := ((q.roundList x.df x.dc x.orig x.ns x.budget).map setView).toList
end MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
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
abbrev Raw := Program.Raw × ℚ
attribute [local irreducible] RationalUnitInput.ScanProgram.Input.result
end MetricKMedian.Preparation.FractionalRefinement.ScanProgram
end

end OAI
end


