-- Prove2me | Definitions.Def_OAIQ053K039
-- name    : OAIQ053K039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:03:21.226053+00:00
-- url     : https://prove2.me/theorems/93bde210-57c6-4550-8db1-7ef7340f962c
-- title:
--   Definitions bundle OAIQ053K039 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 55 declarations of OpenAI's Lean: 50 definitions and 5 theorems. The definitions and types are `OAI.MetricKMedian.Binary.BooleanLists.valueProgram`, `OAI.MetricKMedian.Binary.Iteration.program`, `OAI.MetricKMedian.Binary.PolyProgram.iteratesFrom`, `OAI.MetricKMedian.Binary.PolyProgram.listChoose`, `OAI.MetricKMedian.Binary.PolyProgram.loopFrom`, `OAI.MetricKMedian.Binary.PolyProgram.pairList`, `OAI.MetricKMedian.Binary.PolyProgram.repeatFrom`, `OAI.MetricKMedian.Binary.Repeat.program`, `OAI.MetricKMedian.FixedBatch.RationalParameters.countCandidates`, `OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts`, `OAI.MetricKMedian.FixedBatch.RationalParameters.roundList`, `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted`, `OAI.MetricKMedian.FixedBatch.RationalParameters.tree`, `OAI.MetricKMedian.IntegerLaw.ListPivot.el`, `OAI.MetricKMedian.IntegerLaw.compressAuto`, `OAI.MetricKMedian.IntegerLaw.compressRational`, `OAI.MetricKMedian.IntegerLaw.compressSteps`, `OAI.MetricKMedian.IntegerLaw.compressStepsAuto`, `OAI.MetricKMedian.IntegerLaw.compressionStep`, `OAI.MetricKMedian.IntegerLaw.compressionStepAuto`, `OAI.MetricKMedian.IntegerLaw.computedCompress`, `OAI.MetricKMedian.RationalBatchData.events`, `OAI.MetricKMedian.RationalBatchData.proposal`, `OAI.MetricKMedian.RationalPhysicalKernel.graphLaw`, `OAI.MetricKMedian.RationalPhysicalKernel.histories`, `OAI.MetricKMedian.RationalPhysicalKernel.step`, `OAI.MetricKMedian.RationalSignedTerminal.terminal`, `OAI.MetricKMedian.SparseBernoulli.run`, `OAI.MetricKMedian.SparseCardinalRounding.round`, `OAI.MetricKMedian.SparseEnumeratedBatch.law`, `OAI.MetricKMedian.SparseEnumeratedGraph.law`, `OAI.MetricKMedian.SparseGraph.columns`, `OAI.MetricKMedian.SparseGraph.law`, `OAI.MetricKMedian.SparseGraph.run`, `OAI.MetricKMedian.SparseGraph.step`, `OAI.MetricKMedian.SparseGridRounding.law`, `OAI.MetricKMedian.SparseIntegerLaw.bindCompress`, `OAI.MetricKMedian.SparseIntegerLaw.compressAuto`, `OAI.MetricKMedian.SparseIntegerLaw.prodCompress`, `OAI.MetricKMedian.SparseIntegerLaw.step` and 10 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_BinaryBooleanLists`, `KMedian_Binary_BinaryIterations`, `KMedian_Binary_BinaryListSelection`, `KMedian_Binary_BinaryRepeat`, `KMedian_Binary_BooleanLoopFrom`, `KMedian_Compression_ComputedCompression`, `KMedian_Compression_ComputedCompressionStep`, `KMedian_Compression_IntegerRationalCompression`, `KMedian_Geometry_BoundFreeCompression`, `KMedian_Geometry_RationalGridRound`, `KMedian_Geometry_RationalHistorySelection`, `KMedian_Geometry_RationalParameterizedHistory`, `KMedian_Preparation_RationalPreparedScan`, `KMedian_Programs_PivotListProgram`, `KMedian_Rounding_RationalBatchFacts`, `KMedian_Rounding_RationalPhysicalKernel`, `KMedian_Rounding_RationalRoundEvents`, `KMedian_Rounding_RationalSignedTerminal`, `KMedian_Sparse_SparseAlgorithm`, `KMedian_Sparse_SparseBernoulliRun`, `KMedian_Sparse_SparseBind`, `KMedian_Sparse_SparseBranchProgram`, `KMedian_Sparse_SparseCardinalRounding`, `KMedian_Sparse_SparseEnumeratedBatch`, `KMedian_Sparse_SparseEnumeratedGraph`, `KMedian_Sparse_SparseGraphFeatures`, `KMedian_Sparse_SparseGraphLaw`, `KMedian_Sparse_SparseGraphRun`, `KMedian_Sparse_SparseGridRounding`, `KMedian_Sparse_SparseIntegerLaw`, `KMedian_Sparse_SparsePhysicalBatch`, `KMedian_Sparse_SparseProduct`, `KMedian_Sparse_SparseSignedPartial`, `KMedian_Sparse_SparseSignedPreparation`, `KMedian_Sparse_SparseStarActivation`, `KMedian_Sparse_SparseTargetSubset`, `KMedian_Sparse_SparseWeightedPartial`, `KMedian_Sparse_SparseWeightedRounding`.
--
--   **Imports.** It imports the bundles `OAIQ053K028`, `OAIQ053K029`, `OAIQ053K030` and `OAIQ053K031` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K044`, `OAIQ053K045`, `OAIQ053K046` and `OAIQ053K047`; the statements `OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s53`, `OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation_s53`, `OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec_s53`, `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec_s53`, `OAI.MetricKMedian.RationalBatchData.proposal_survival_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.graph_data_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_completion_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_mass_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_valid_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.step_count_tail_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.step_survival_s53`, `OAI.MetricKMedian.SparseBernoulli.conditional_count_tail_s53`, `OAI.MetricKMedian.SparseBernoulli.count_variance_s53`, `OAI.MetricKMedian.SparseCopyState.physical_count_tail_s53`, `OAI.MetricKMedian.SparseEnumeratedBatch.erasure_lower_s53`, `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_error_s53`, `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_le_s53`, `OAI.MetricKMedian.SparseEnumeratedBatch.relevant_generator_estimate_s53`, `OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound_s53`, `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound_s53` and `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound_s53`; the proofs of `OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s53`, `OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation_s53`, `OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec_s53`, `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec_s53`, `OAI.MetricKMedian.RationalBatchData.proposal_survival_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_completion_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_mass_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_valid_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.step_count_tail_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.step_survival_s53`, `OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound_s53`, `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound_s53` and `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K028
import Definitions.Def_OAIQ053K029
import Definitions.Def_OAIQ053K030
import Definitions.Def_OAIQ053K031

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryBooleanLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary
namespace BooleanLists
noncomputable def valueProgram : PolyProgram (encodeList encodeBool) Nat.bits Word.value := unpackProgram.comp PolyProgram.toBits
end BooleanLists
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanLoopFrom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary.PolyProgram
open Turing Function Polynomial
variable {α σ β : Type} {ea : α → List Bool} {es : σ → List Bool} {eb : β → List Bool}
variable {init : α → σ} {body : σ → β ⊕ σ}

noncomputable def loopFrom (start : PolyProgram ea es init)
    (P : PolyProgram es (encodeLoop es eb) body) (g : α → β)
    (iterations sizes : Polynomial ℕ)
    (h : ∀ a, ∃ n ≤ iterations.eval (ea a).length,
      BoundedRun es body (sizes.eval (ea a).length) n (init a) (g a)) :
    PolyProgram ea eb g where
  machine := Compose.machine start.machine (Loop.machine P.machine)
  time := start.time+2*start.sizeBound+2+iterations*(P.time.comp sizes+2*P.sizeBound.comp sizes+3)
  outputs a := Classical.choice (show Nonempty _ from by
    obtain ⟨n,hn,hrun⟩ := h a
    obtain ⟨t,ht,htrace⟩ := P.run_loop hrun
    let hs := start.outputs a
    have hstart : Trace start.machine.step hs.steps (start.machine.initialCfg (ea a))
        (start.machine.finalCfg (es (init a))) := Trace.of_iterate hs.evals_in_steps
    have hall := Compose.run start.machine (Loop.machine P.machine) hstart htrace
    refine ⟨⟨⟨_,hall.iterate_eq⟩,?_⟩⟩
    have hsize := start.length_bound a
    have hr := ht.trans (Nat.mul_le_mul_right (P.passTime (sizes.eval (ea a).length)) hn)
    have htime := hs.steps_le_m
    simp only [eval_add,eval_mul,eval_ofNat,eval_comp,passTime] at hr ⊢
    omega)
end MetricKMedian.Binary.PolyProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryIterations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace Iteration
open PolyProgram
variable {α : Type}

noncomputable def program {ea : α → List Bool} {f : α → α}
    (P : PolyProgram ea ea f) (a0 : α) :
    PolyProgram (enc ea) (encodeLoop (enc ea) (encodeList ea)) (body f) := by
  let n := fst Nat.bits (encodePair ea (encodeList ea))
  let st := snd Nat.bits (encodePair ea (encodeList ea))
  let a := st.comp (fst ea (encodeList ea))
  let bs := st.comp (snd ea (encodeList ea))
  let test := n.comp natZero
  let dec := (n.fanout (constant (enc ea) Nat.bits 1)).comp natSub
  let next := dec.fanout ((a.comp P).fanout ((a.fanout bs).comp (listCons ea)))
  let go := next.comp (injectRight (enc ea) (encodeList ea))
  let stop := (bs.comp (listReverse ea a0)).comp (injectLeft (enc ea) (encodeList ea))
  exact (ite test go stop).congr _ (fun s => by simp only [Function.comp_apply,body,decide_eq_true_eq])

end Iteration

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {f : α → α} {start : β → α} {count : β → ℕ}

noncomputable def iteratesFrom (P : PolyProgram ea ea f) (initial : PolyProgram eb ea start)
    (steps : PolyProgram eb Nat.bits count) (a0 : α) (N A : Polynomial ℕ)
    (hn : ∀ b, count b≤N.eval (eb b).length)
    (ha : ∀ b i, i ≤ count b → (ea (f^[i] (start b))).length≤A.eval (eb b).length) :
    PolyProgram eb (encodeList ea) (fun b => Iteration.iterates f (start b) (count b)) := by
  let init := steps.fanout (initial.fanout (constant eb (encodeList ea) []))
  exact init.loopFrom (Iteration.program P a0) _ (N+1) (2*(N+1)+1+2*A+1+N*(2*A+1)) (fun b => by
    refine ⟨count b+1,by simp only [eval_add,eval_one]; have hh := hn b; omega,?_⟩
    have hr := Iteration.run ea f (N.eval (eb b).length) (A.eval (eb b).length) (count b) (start b) []
      (by simpa using hn b) (ha b) (by simp)
    simpa only [List.reverse_nil,List.nil_append,Iteration.enc,Iteration.bound,eval_add,eval_mul,eval_ofNat,eval_one] using hr)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListSelection
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace PolyProgram
variable {α : Type} {ea : α → List Bool}
noncomputable def listChoose {p : α × α → Bool} (P : PolyProgram (encodePair ea ea) encodeBool p) (a0 : α) :
    PolyProgram (encodePair (encodeList ea) ea) ea
      (fun x : List α × α => x.1.foldl (fun b a => if p (b,a) then a else b) x.2) := by
  let step : PolyProgram (encodePair ea ea) ea (fun x => if p x then x.2 else x.1) :=
    (ite P (fst ea ea) (snd ea ea)).congr _ (fun _ => rfl)
  exact step.listFold a0 X (fun as b pre suf he => by
    rcases ListAlgorithms.foldChoice p pre b with h|h
    · rw [h]
      simp only [eval_X,encodePair_length]; omega
    · have hp : (encodeList ea pre).length ≤ (encodeList ea as).length := by
        rw [he,EncodedList.append,List.length_append]; omega
      have hh := (EncodedList.member_length ea pre _ h).trans hp
      simp only [eval_X,encodePair_length]; omega)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryRepeat
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace Repeat
variable {α : Type}

noncomputable def program {ea : α → List Bool} {f : α → α}
    (P : PolyProgram ea ea f) : PolyProgram (enc ea) (encodeLoop (enc ea) ea) (body f) := by
  open PolyProgram in
  let n := fst Nat.bits ea
  let a := snd Nat.bits ea
  let dec := (n.fanout (constant (enc ea) Nat.bits 1)).comp natSub
  let go := (dec.fanout (a.comp P)).comp (injectRight (enc ea) ea)
  let stop := a.comp (injectLeft (enc ea) ea)
  exact (ite (n.comp natZero) go stop).congr _ (fun _ => by simp only [Function.comp_apply,body,decide_eq_true_eq])

end Repeat

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {f : α → α} {start : β → α} {count : β → ℕ}
noncomputable def repeatFrom (P : PolyProgram ea ea f) (initial : PolyProgram eb ea start)
    (steps : PolyProgram eb Nat.bits count) (N A : Polynomial ℕ)
    (hn : ∀ b, count b≤N.eval (eb b).length)
    (ha : ∀ b i, i ≤ count b → (ea (f^[i] (start b))).length≤A.eval (eb b).length) :
    PolyProgram eb ea (fun b => f^[count b] (start b)) := by
  let init := steps.fanout initial
  exact init.loopFrom (Repeat.program P) _ (N+1) (2*(N+1)+1+A) (fun b => by
    refine ⟨count b+1,by simp only [eval_add,eval_one]; have hh := hn b; omega,?_⟩
    have hr := Repeat.run ea f (N.eval (eb b).length) (A.eval (eb b).length) (count b) (start b) (hn b) (ha b)
    simpa only [Repeat.enc,eval_add,eval_mul,eval_ofNat,eval_one] using hr)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_ComputedCompressionStep
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def compressionStep {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℤ)
    (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) (hsize : d+1 < μ.support.card) :
    IntegerLaw (Fin n) :=
  let z := computedAffineKernel μ v
  have hz := computedAffineKernel_spec μ v L hv hsize
  have hP := positiveSet_nonempty z hz.2.1 hz.1
  let p := computedPivot μ z hP
  have hp := computedPivot_spec μ z hP
  eliminateAt μ z p hp.1 hp.2 hz.2.1

theorem compressionStep_spec {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L)
    (hsize : d+1 < μ.support.card) :
    let ν := compressionStep μ v L hv hsize
    ν.denominator ≤ μ.denominator*(2:ℤ)^((2*(d+1)*(d+1+L))*(n+1)) ∧
      ν.support ⊆ μ.support ∧ ν.support.card < μ.support.card ∧
      ∀ j, (∑ i, ν.rational.weight i*(v i j:ℚ))=∑ i, μ.rational.weight i*(v i j:ℚ) := by
  let z := computedAffineKernel μ v
  have hz := computedAffineKernel_spec μ v L hv hsize
  have hP := positiveSet_nonempty z hz.2.1 hz.1
  let p := computedPivot μ z hP
  have hp := computedPivot_spec μ z hP
  have he := eliminateAt_preserves μ (fun i j => (v i j:ℚ)) z p hp.1 hp.2
    hz.2.1 hz.2.2.1 hz.2.2.2.1
  change (eliminateAt μ z p hp.1 hp.2 hz.2.1).denominator ≤ _ ∧ _
  refine ⟨?_,he.2.2.2.1.trans (erase_subset _ _),?_,he.2.2.2.2⟩
  · change μ.denominator*z p ≤ _
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hz.2.2.2.2 p)) μ.denominator_pos.le
  · change (eliminateAt μ z p hp.1 hp.2 hz.2.1).support.card < μ.support.card
    have hh := card_le_card he.2.2.2.1
    rw [card_erase_of_mem ((μ.mem_support p).mpr he.2.1)] at hh
    omega

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_ComputedCompression
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def compressSteps {n d : ℕ} (v : Fin n → Fin d → ℤ) (L : ℕ)
    (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) : ℕ → IntegerLaw (Fin n) → IntegerLaw (Fin n)
  | 0, μ => μ
  | t+1, μ =>
    if h : d+1 < μ.support.card then
      compressSteps v L hv t (compressionStep μ v L hv h)
    else μ

def computedCompress {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℤ)
    (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) : IntegerLaw (Fin n) :=
  compressSteps v L hv n μ

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_IntegerRationalCompression
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def compressRational {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℚ)
    (L : ℕ) (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) : IntegerLaw (Fin n) :=
  μ.computedCompress (RationalLaw.scaledFeatures v) (L*(n+1))
    (RationalLaw.scaledFeatures_bound v L hnum hden)

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_BoundFreeCompression
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def compressionStepAuto {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) (hsize : d+1 < μ.support.card) : IntegerLaw (Fin n) :=
  let z := computedAffineKernel μ v
  have hz : (∃ i, z i ≠ 0) ∧ (∑ i, z i=0) := by
    obtain ⟨L,hL⟩ := exists_feature_bound v
    have h := computedAffineKernel_spec μ v L hL hsize
    exact ⟨h.1,h.2.1⟩
  have hP := positiveSet_nonempty z hz.2 hz.1
  let p := computedPivot μ z hP
  have hp := computedPivot_spec μ z hP
  eliminateAt μ z p hp.1 hp.2 hz.2

theorem compressionStepAuto_eq {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L)
    (hsize : d+1 < μ.support.card) :
    compressionStepAuto μ v hsize=compressionStep μ v L hv hsize := rfl

def compressStepsAuto {n d : ℕ} (v : Fin n → Fin d → ℤ) :
    ℕ → IntegerLaw (Fin n) → IntegerLaw (Fin n)
  | 0,μ => μ
  | t+1,μ => if h : d+1 < μ.support.card then
      compressStepsAuto v t (compressionStepAuto μ v h) else μ

theorem compressStepsAuto_eq {n d : ℕ} (v : Fin n → Fin d → ℤ)
    (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) (t : ℕ) (μ : IntegerLaw (Fin n)) :
    compressStepsAuto v t μ=compressSteps v L hv t μ := by
  induction t generalizing μ with
  | zero => rfl
  | succ t ih =>
    simp only [compressStepsAuto,compressSteps]
    split_ifs with h
    · rw [compressionStepAuto_eq μ v L hv h,ih]
    · rfl

def compressAuto {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℚ) :
    IntegerLaw (Fin n) :=
  compressStepsAuto (RationalLaw.scaledFeatures v) n μ

theorem compressAuto_eq {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℚ) (L : ℕ)
    (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) :
    μ.compressAuto v=μ.compressRational v L hnum hden :=
  compressStepsAuto_eq _ _ (RationalLaw.scaledFeatures_bound v L hnum hden) n μ

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseIntegerLaw
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
open Finset

namespace SparseIntegerLaw
variable {α : Type}

theorem trim_moment (μ : SparseIntegerLaw α) (f : α → ℚ) :
    μ.trim.moment f=μ.moment f := by
  unfold moment
  change (∑ i : Fin μ.law.support.card,
    μ.law.trim.rational.weight i * f ((Vector.ofFn (fun k =>
      μ.states[(μ.law.support.orderEmbOfFin rfl k).val]))[i.val])) = _
  simp only [Vector.getElem_ofFn]
  convert μ.law.trim_moment (fun i => f μ.states[i.val]) using 1
  all_goals try with_reducible_and_instances rfl

end SparseIntegerLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

def compressAuto {d : ℕ} (μ : SparseIntegerLaw α) (v : α → Fin d → ℚ) :
    SparseIntegerLaw α :=
  let ν : SparseIntegerLaw α := ⟨μ.length,μ.states,
    μ.law.compressAuto (fun i => v μ.states[i.val])⟩
  ν.trim

def step {d : ℕ} (v : α → Fin d → ℚ) (μ : SparseIntegerLaw α)
    (p : α → ℚ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (next : α → Fin 2 → α) :
    SparseIntegerLaw α := (μ.branch p hp next).compressAuto v

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBernoulliRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

def run (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    ℕ → SparseIntegerLaw (Fin n → Bool)
  | 0 => .dirac (fun _ => false)
  | t+1 => if ht : t<n then
      (run p hp t).step (features (d := d)) (fun _ => p ⟨t,ht⟩)
        (fun _ => hp ⟨t,ht⟩) (fun q b => endpoint q ⟨t,ht⟩ b)
    else run p hp t

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

def bindCompress {d : ℕ} (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (v : β → Fin d → ℚ) : SparseIntegerLaw β :=
  (μ.bindIndexed κ).compressAuto v

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePhysicalBatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparsePhysicalBatch
open Finset
variable {n : ℕ}

def law (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) :
    SparseIntegerLaw (Finset (Fin n)) :=
  SparseIntegerLaw.mix
    ((SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).map (balanced Z C))
    ((SparseBernoulli.run (d := 4) q hq n).map (unbalanced Z))

end MetricKMedian.SparsePhysicalBatch

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseEnumeratedBatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

def law (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) :
    SparseIntegerLaw (Finset E) :=
  (SparsePhysicalBatch.law (Z.map enum.symm.toEmbedding)
    (fun a => (C (enum a)).map enum.symm.toEmbedding) p (fun a => q (enum a)) hp
    (fun a => hq (enum a))).map (fun A => A.map enum.toEmbedding)

end MetricKMedian.SparseEnumeratedBatch

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalBatchFacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch PhysicalPotential
variable {I E : Type} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

def proposal (G : I → Finset I) (Δ : ℕ) (g b p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1) {n : ℕ}
    (enum : Fin n ≃ HeavyAction (graph G) (heavySet (graphMass G g) b)) :
    SparseIntegerLaw (Finset (HeavyAction (graph G) (heavySet (graphMass G g) b))) :=
  let m := graphMass G g
  let H := heavySet m b
  let D := heavy (graph G) H
  let q := fun e => bias m p φ (heavyParent (graph G) H e)
  SparseEnumeratedBatch.law enum (balanced D Δ) (conflicts D Δ) p q
    ⟨hp,(by have hh := mul_nonneg hp hφ; nlinarith only [hh,hupper])⟩
    (fun e => bias_probability m hp hφ hupper (heavyParent (graph G) H e))

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalRoundEvents
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch
variable {I : Type} [LinearOrder I] [Fintype I]

def events (μ : SparseIntegerLaw (I → Finset I)) (Δ : ℕ) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1) : SparseIntegerLaw (Event I g β) :=
  μ.bindIndexed (fun i =>
    let G := μ.states[i.val]
    (proposal G Δ g β p φ hp hφ hupper
      (enumeration (graph G) (heavySet (graphMass G g) β))).map (fun Z => ⟨G,Z⟩))

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseWeightedPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedPartial
open Finset RationalWeightedStep
variable {n : ℕ}

 def step (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (μ : SparseIntegerLaw (Vector ℚ n)) : SparseIntegerLaw (Vector ℚ n) :=
  μ.step features (probability β) (probability_unit β hβ) (endpoint β)

 def run (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i) (p : Vector ℚ n) :
    ℕ → SparseIntegerLaw (Vector ℚ n)
  | 0 => .dirac p
  | t+1 => step β hβ (run β hβ p t)

end MetricKMedian.SparseWeightedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCardinalRounding
attribute [-simp] _root_.OAI.MetricKMedian.SparseIntegerLaw.map_states _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCardinalRounding
open Finset RationalWeightedStep
variable {n : ℕ}

def round (p : Vector ℚ n) : SparseIntegerLaw (Vector ℚ n) :=
  SparseWeightedPartial.run (fun _ => 1) (fun _ => by norm_num) p n

end MetricKMedian.SparseCardinalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β γ : Type}

def prodCompress {d : ℕ} (μ : SparseIntegerLaw α) (ν : SparseIntegerLaw β)
    (f : α → β → γ) (v : γ → Fin d → ℚ) : SparseIntegerLaw γ :=
  (μ.prod ν f).compressAuto v

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGraphFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

def step (μ : SparseIntegerLaw (Graph n m)) (ν : SparseIntegerLaw (Finset (Fin n)))
    (i : Fin m) : SparseIntegerLaw (Graph n m) :=
  μ.prodCompress ν (fun G S => next G S i) features

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGraphRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

def run (ν : Fin m → SparseIntegerLaw (Finset (Fin n))) : ℕ → SparseIntegerLaw (Graph n m)
  | 0 => .dirac (fun _ => ∅)
  | t+1 => if ht : t < m then step (run ν t) (ν ⟨t,ht⟩) ⟨t,ht⟩ else run ν t

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGraphLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

def columns (q : Fin n → Fin m → ℚ) (i : Fin m) : SparseIntegerLaw (Finset (Fin n)) :=
  (SparseCardinalRounding.round (Vector.ofFn (fun h => q h i))).map SparseCardinalRounding.selected

def law (q : Fin n → Fin m → ℚ) : SparseIntegerLaw (Graph n m) := run (columns q) m

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseEnumeratedGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedGraph
open Finset
variable {I : Type} [DecidableEq I] {n : ℕ}

def law (enum : Fin n ≃ I) (q : I → I → ℚ) : SparseIntegerLaw (I → Finset I) :=
  (SparseGraph.law (fun h i => q (enum h) (enum i))).map (lift enum)

end MetricKMedian.SparseEnumeratedGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalKernel
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.instLinearOrderCopy
def graphLaw (d : F → F → ℚ) (g P : ℚ) (A : Finset (CopyState.Copy (F := F) Δ)) :
    SparseIntegerLaw (A → Finset A) :=
  SparseEnumeratedGraph.law (enumeration A)
    (fun h i => Taper.sourceMarginals g P (fun a : A => d i.val.1 a.val.1) (own A i) Δ h)

def step (d : F → F → ℚ) (g β p φ P : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) : SparseIntegerLaw (State F Δ g β) :=
  (RationalBatchData.events (graphLaw d g P s.1) Δ g β p φ hp hφ hupper).map
    (updateEvent g β s.1)

def histories (d : F → F → ℚ) (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ) :
    SparseIntegerLaw (SparseHistories.History (State F Δ g β)) :=
  SparseHistories.tree (fun t => step d g β p φ (P t) hp hφ hupper) (A,none) T

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalParameterizedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                    
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)

variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j : ℕ}

local instance rationalParameterizedHistoryCopyOrder_r7bc7f2_1 : LinearOrder (Copy (F := F) q.Δ) := copyOrder
def tree (d₀ : F → F → ℚ) (A : Finset (Copy (F := F) q.Δ)) :=
  histories d₀ q.g q.β q.probabilityQ q.φ q.taperAt q.probabilityQ_pos.le
    (by exact_mod_cast q.φpos.le) q.probabilityQ_le A q.T

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalHistorySelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j : ℕ}

local instance rationalHistorySelectionCopyOrder_r7bc7f2_1 : LinearOrder (Copy (F := F) q.Δ) := copyOrder
def selectCompleted (d₀ : F → F → ℚ) (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (A : Finset (Copy (F := F) q.Δ)) (B : Fin j → Finset (Copy (F := F) q.Δ))
    (hB : ∀ c, (B c).Nonempty) : Option (Finset F) :=
  (SparseSelect.choose (q.tree d₀ A) (q.completedGood d R A B hB)
    (fun z => score d (completed d R B hB q.g q.β z))).map
      (completed d R B hB q.g q.β)

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalGridRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
open Preparation.RationalNearest
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [PseudoMetricSpace X] {j : ℕ}

variable [Fintype F]

attribute [local instance] OAI.MetricKMedian.FixedBatch.RationalParameters.rationalGridRoundCopyOrder
def roundCounts (d₀ : F → F → ℚ) (d : Fin j → F → ℚ) (n : F → ℕ) : Option (Finset F) :=
  if hn : ∀ a, n a ≤ q.Δ then
    let A := activeSlots n hn
    if hA : q.Δ ≤ A.card then
      q.selectCompleted d₀ d (q.radius d A hA) A (q.nearest d A) (q.nearest_nonempty d A hA)
    else none
  else none

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalPreparedScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)
variable {F H X : Type} [LinearOrder F] [Fintype F] [DecidableEq H]
  [PseudoMetricSpace X] {j : ℕ}

def countCandidates (d₀ : H → H → ℚ) (d : Fin j → H → ℚ) (orig : F → H)
    (ns : List (F → ℕ)) : List (Finset H) :=
  ns.flatMap (fun n => ((q.roundCounts (fun a b => d₀ (orig a) (orig b))
    (fun c a => d c (orig a)) n).map (fun O => O.image orig)).toList)

def roundList (d₀ : H → H → ℚ) (d : Fin j → H → ℚ) (orig : F → H)
    (ns : List (F → ℕ)) (B : ℚ) : Option (Finset H) :=
  SparseSelect.best (candidateGood B) (score d) (q.countCandidates d₀ d orig ns)

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_PivotListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.IntegerLaw.ListPivot
open Binary Binary.PolyProgram Function Finset
abbrev el := encodePair Signed.encode er

end MetricKMedian.IntegerLaw.ListPivot
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalSignedTerminal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalSignedTerminal
open Finset RationalWeightedStep RationalSignedStep
variable {n : ℕ}

def terminal (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) : SparseIntegerLaw (Vector ℚ n) :=
  (SparseBernoulli.run (d := 2) (point p) hp n).map (state u p)

end MetricKMedian.RationalSignedTerminal
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Binary.PolyProgram
open Function
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
noncomputable def pairList : PolyProgram (encodePair ea ea) (encodeList ea) (fun x => [x.1,x.2]) := by
  let second := ((snd ea ea).fanout (constant (encodePair ea ea) (encodeList ea) [])).comp (listCons ea)
  exact (((fst ea ea).fanout second).comp (listCons ea)).congr _ (fun _ => rfl)
end MetricKMedian.Binary.PolyProgram

end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGridRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGridRounding
open Finset
open RationalWeightedStep (point)
variable {n : ℕ}

def law (q : Fin n → ℚ) : SparseIntegerLaw (Fin n → ℕ) :=
  (SparseCardinalRounding.round (fraction q)).map (count q)

end MetricKMedian.SparseGridRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPartial
open Finset RationalSignedStep
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features features_single features_pair)
variable {n : ℕ}

 def step (β : Fin n → ℚ) 
    (μ : SparseIntegerLaw (Vector ℚ n)) : SparseIntegerLaw (Vector ℚ n) :=
  μ.step features (probability β) (probability_unit β) (endpoint β)

 def run (β : Fin n → ℚ) (p : Vector ℚ n) :
    ℕ → SparseIntegerLaw (Vector ℚ n)
  | 0 => .dirac p
  | t+1 => step β (run β p t)

end MetricKMedian.SparseSignedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseWeightedRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedRounding
open Finset RationalWeightedStep SparseWeightedPartial
variable {n : ℕ}

def round (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i) (p : Vector ℚ n) :
    SparseIntegerLaw (Vector ℚ n) :=
  (run β hβ p n).step features RationalLastFraction.probability
    RationalLastFraction.probability_unit RationalLastFraction.endpoint

end MetricKMedian.SparseWeightedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseTargetSubset
attribute [-simp] _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseTargetSubset
open Finset RationalWeightedStep
variable {n : ℕ}

def vectors (D : Finset (Fin n)) (q : ℚ) : SparseIntegerLaw (Vector ℚ n) :=
  SparseWeightedRounding.round (fun _ => 1) (fun _ => by norm_num) (initial D q)

def law (D : Finset (Fin n)) (q : ℚ) : SparseIntegerLaw (Finset (Fin n)) :=
  (vectors D q).map SparseCardinalRounding.selected

end MetricKMedian.SparseTargetSubset
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseStarActivation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseStarActivation
open Finset
variable {n m : ℕ}

def law (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) :
    SparseIntegerLaw (Fin m → Finset (Fin n)) :=
  SparseGraph.run (fun e => SparseTargetSubset.law (D e) (q e)) m

end MetricKMedian.SparseStarActivation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPreparation
open Finset
open RationalWeightedStep (point fractional)
variable {n m : ℕ}

def kernel (D : Fin m → Finset (Fin n)) (q : Vector ℚ m)
    (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1) : SparseIntegerLaw (State n m) :=
  (SparseStarActivation.law D (point q)).prod
    (SparseBernoulli.run (d := 2) (point q) hq m) (fun S ω => (q,S,ω))

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
end


