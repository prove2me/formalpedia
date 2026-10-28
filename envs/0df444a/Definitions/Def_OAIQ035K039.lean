-- Prove2me | Definitions.Def_OAIQ035K039
-- name    : OAIQ035K039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:03:23.089799+00:00
-- url     : https://prove2.me/theorems/b4846ac8-dcb4-4d1b-8ba6-54450cd80b77
-- title:
--   Definitions bundle OAIQ035K039 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 34 declarations of OpenAI's Lean: 34 definitions. The definitions and types are `OAI.MetricKMedian.Binary.BooleanLists.valueProgram`, `OAI.MetricKMedian.Binary.Iteration.program`, `OAI.MetricKMedian.Binary.ListFindIdx.loop`, `OAI.MetricKMedian.Binary.ListFindIdx.program`, `OAI.MetricKMedian.Binary.PolyProgram.checkedProgram`, `OAI.MetricKMedian.Binary.PolyProgram.dependentIf`, `OAI.MetricKMedian.Binary.PolyProgram.dependentIfTotal`, `OAI.MetricKMedian.Binary.PolyProgram.iteratesFrom`, `OAI.MetricKMedian.Binary.PolyProgram.listChoose`, `OAI.MetricKMedian.Binary.PolyProgram.listFindIdx`, `OAI.MetricKMedian.Binary.PolyProgram.loopFrom`, `OAI.MetricKMedian.Binary.PolyProgram.pairList`, `OAI.MetricKMedian.Binary.PolyProgram.repeatFrom`, `OAI.MetricKMedian.Binary.PolyProgram.sumElim`, `OAI.MetricKMedian.Binary.PolyProgram.sumLeft`, `OAI.MetricKMedian.Binary.PolyProgram.sumRight`, `OAI.MetricKMedian.Binary.Repeat.program`, `OAI.MetricKMedian.CopyState.advance`, `OAI.MetricKMedian.RationalBatchData.events`, `OAI.MetricKMedian.RationalBatchData.proposal`, `OAI.MetricKMedian.SparseBernoulli.run`, `OAI.MetricKMedian.SparseCardinalRounding.round`, `OAI.MetricKMedian.SparseEnumeratedBatch.law`, `OAI.MetricKMedian.SparseGraph.columns`, `OAI.MetricKMedian.SparseGraph.run`, `OAI.MetricKMedian.SparseGraph.step`, `OAI.MetricKMedian.SparseIntegerLaw.compressAuto`, `OAI.MetricKMedian.SparseIntegerLaw.fair`, `OAI.MetricKMedian.SparseIntegerLaw.mix`, `OAI.MetricKMedian.SparseIntegerLaw.prodCompress`, `OAI.MetricKMedian.SparseIntegerLaw.step`, `OAI.MetricKMedian.SparsePhysicalBatch.law`, `OAI.MetricKMedian.SparseWeightedPartial.run`, `OAI.MetricKMedian.SparseWeightedPartial.step`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Binary_BinaryBooleanLists`, `KMedian_Binary_BinaryGuard`, `KMedian_Binary_BinaryGuardTotal`, `KMedian_Binary_BinaryIterations`, `KMedian_Binary_BinaryListSelection`, `KMedian_Binary_BinaryRepeat`, `KMedian_Binary_BooleanLoopFrom`, `KMedian_Binary_BooleanSum`, `KMedian_Process_PhysicalState`, `KMedian_Rounding_RationalBatchFacts`, `KMedian_Rounding_RationalRoundEvents`, `KMedian_Sparse_SparseAlgorithm`, `KMedian_Sparse_SparseBernoulliRun`, `KMedian_Sparse_SparseBranchProgram`, `KMedian_Sparse_SparseCardinalRounding`, `KMedian_Sparse_SparseEnumeratedBatch`, `KMedian_Sparse_SparseGraphFeatures`, `KMedian_Sparse_SparseGraphLaw`, `KMedian_Sparse_SparseGraphRun`, `KMedian_Sparse_SparseMixture`, `KMedian_Sparse_SparsePhysicalBatch`, `KMedian_Sparse_SparseProduct`, `KMedian_Sparse_SparseWeightedPartial`.
--
--   **Imports.** It imports the bundles `OAIQ035K027`, `OAIQ035K028`, `OAIQ035K029` and `OAIQ035K030` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K046`, `OAIQ035K047`, `OAIQ035K048`, `OAIQ035K049` and `OAIQ035K062`; the statements `OAI.MetricKMedian.CopyState.enumerated_conditional_round_survival`, `OAI.MetricKMedian.CopyState.rational_conditional_round_drift`, `OAI.MetricKMedian.RationalBatchData.proposal_count_tail`, `OAI.MetricKMedian.RationalBatchData.proposal_local_bound`, `OAI.MetricKMedian.RationalBatchData.proposal_survival`, `OAI.MetricKMedian.SparseBernoulli.count_failure`, `OAI.MetricKMedian.SparseBernoulli.count_mean`, `OAI.MetricKMedian.SparseBernoulli.quadratic_variance`, `OAI.MetricKMedian.SparseCopyState.physical_count_tail`, `OAI.MetricKMedian.SparseEnumeratedBatch.erasure_at_least_quarter`, `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_error`, `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_le`, `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_lower`, `OAI.MetricKMedian.SparseEnumeratedBatch.pair_le`, `OAI.MetricKMedian.SparseEnumeratedBatch.relevant_generator_estimate`, `OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound`, `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound` and `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound`; the proofs of `OAI.MetricKMedian.CopyState.enumerated_conditional_round_survival`, `OAI.MetricKMedian.CopyState.rational_conditional_round_drift`, `OAI.MetricKMedian.RationalBatchData.proposal_count_tail`, `OAI.MetricKMedian.RationalBatchData.proposal_local_bound`, `OAI.MetricKMedian.RationalBatchData.proposal_survival`, `OAI.MetricKMedian.SparseBernoulli.count_failure`, `OAI.MetricKMedian.SparseEnumeratedBatch.erasure_at_least_quarter`, `OAI.MetricKMedian.SparseEnumeratedBatch.relevant_generator_estimate`, `OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound`, `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound` and `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K027
import Definitions.Def_OAIQ035K028
import Definitions.Def_OAIQ035K029
import Definitions.Def_OAIQ035K030

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryBooleanLists
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
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryGuard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary.PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

noncomputable def checkedProgram (p : α → Prop) [DecidablePred p]
    (P : PolyProgram ea encodeBool (fun a => decide (p a))) (a0 : {a // p a}) :
    PolyProgram ea (fun a : {a // p a} => ea a.val) (checked p a0) := by
  let raw : PolyProgram ea id ea := (identity ea).recode id (fun _ => rfl) (fun _ => rfl)
  let q := ite P (constant ea id (ea a0.val)) raw
  exact q.recode id (fun _ => rfl) (fun a => by
    by_cases h : p a
    · simp [checked,h]
    · simp [checked,h])

noncomputable def dependentIf (p : α → Prop) [DecidablePred p]
    (P : PolyProgram ea encodeBool (fun a => decide (p a)))
    (f : (a : α) → ¬p a → β) (g : (a : α) → p a → β)
    (F : PolyProgram (fun a : {a // ¬p a} => ea a.val) eb (fun a => f a.val a.property))
    (G : PolyProgram (fun a : {a // p a} => ea a.val) eb (fun a => g a.val a.property))
    (a0 : {a // ¬p a}) (a1 : {a // p a}) :
    PolyProgram ea eb (fun a => if h : p a then g a h else f a h) := by
  let notP := (P.comp boolNot).congr (fun a => decide (¬p a)) (fun a => by simp [Function.comp_apply])
  let FF := (checkedProgram (fun a => ¬p a) notP a0).comp F
  let GG := (checkedProgram p P a1).comp G
  exact (ite P FF GG).congr _ (fun a => by
    by_cases h : p a
    · simp [Function.comp_apply,checked,h]
    · simp [Function.comp_apply,checked,h])
end MetricKMedian.Binary.PolyProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryGuardTotal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Binary.PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
noncomputable def dependentIfTotal (p : α → Prop) [DecidablePred p]
    (P : PolyProgram ea encodeBool (fun a => decide (p a)))
    (f : (a : α) → ¬p a → β) (g : (a : α) → p a → β)
    (F : PolyProgram (fun a : {a // ¬p a} => ea a.val) eb (fun a => f a.val a.property))
    (G : PolyProgram (fun a : {a // p a} => ea a.val) eb (fun a => g a.val a.property)) :
    PolyProgram ea eb (fun a => if h : p a then g a h else f a h) := by
  classical
  by_cases h0 : Nonempty {a // ¬p a}
  · by_cases h1 : Nonempty {a // p a}
    · exact dependentIf p P f g F G h0.some h1.some
    · have h : ∀a, ¬p a := fun a ha => h1 ⟨⟨a,ha⟩⟩
      exact F.recode (fun a => ⟨a,h a⟩) (fun _ => rfl) (fun a => by simp only [dite_eq_right (h a)])
  · have h : ∀a, p a := fun a => by by_contra ha; exact h0 ⟨⟨a,ha⟩⟩
    exact G.recode (fun a => ⟨a,h a⟩) (fun _ => rfl) (fun a => by simp only [dite_eq_left (h a)])
end MetricKMedian.Binary.PolyProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanLoopFrom
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
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryIterations
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
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListFindIdx
variable {α : Type} (ea : α → List Bool) (a0 : α) (p : α → Bool)
noncomputable def program (P : PolyProgram ea encodeBool p) :
    PolyProgram (enc ea) (encodeLoop (enc ea) Nat.bits) (body a0 p) := by
  let ls := PolyProgram.fst (encodeList ea) Nat.bits
  let n := PolyProgram.snd (encodeList ea) Nat.bits
  let hd := (ls.comp (PolyProgram.listHead ea a0)).comp P
  let test := ((ls.comp (PolyProgram.listIsEmpty ea)).fanout hd).comp PolyProgram.boolOr
  let done := n.comp (PolyProgram.injectLeft (enc ea) Nat.bits)
  let inc := (n.fanout (PolyProgram.constant (enc ea) Nat.bits 1)).comp PolyProgram.natAdd
  let cont := (((ls.comp (PolyProgram.listTail ea a0)).fanout inc).comp (PolyProgram.injectRight (enc ea) Nat.bits))
  exact (PolyProgram.ite test cont done).congr _ (fun _ => rfl)
noncomputable def loop (P : PolyProgram ea encodeBool p) : PolyProgram (enc ea) Nat.bits (result p) :=
  (program ea a0 p P).loop (result p) (X+1) X (fun x => by
    obtain ⟨t,ht,hr⟩ := run ea a0 p x.1 x.2 (enc ea x).length le_rfl
    refine ⟨t,?_,?_⟩
    · have hh := EncodedList.length_le ea x.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]
      omega
    · simpa only [eval_X] using hr)
end ListFindIdx
namespace PolyProgram
variable {α : Type} {ea : α → List Bool}
noncomputable def listFindIdx {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) Nat.bits (List.findIdx p) :=
  ((((identity (encodeList ea)).fanout (constant (encodeList ea) Nat.bits 0)).comp
    (ListFindIdx.loop ea a0 p P))).congr _ (fun _ => by simp only [Function.comp_apply,id_eq,ListFindIdx.result,Nat.zero_add])
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
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryRepeat
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
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                  
section
namespace MetricKMedian.Binary
open Function
namespace PolyProgram
variable {α β γ : Type} (ea : α → List Bool) (eb : β → List Bool)
noncomputable def sumLeft (a0 : α) : PolyProgram (encodeLoop eb ea) ea (fun x => x.elim id (fun _ => a0)) := by
  let raw := tail.recode (encodeLoop eb ea) (fun _ => rfl) (fun _ => rfl)
  let deflt := constant (encodeLoop eb ea) id (ea a0)
  refine (ite (sumTag ea eb) raw deflt).recode id (fun _ => rfl) ?_
  intro x
  cases x <;> rfl
noncomputable def sumRight (b0 : β) : PolyProgram (encodeLoop eb ea) eb (fun x => x.elim (fun _ => b0) id) := by
  let raw := tail.recode (encodeLoop eb ea) (fun _ => rfl) (fun _ => rfl)
  let deflt := constant (encodeLoop eb ea) id (eb b0)
  refine (ite (sumTag ea eb) deflt raw).recode id (fun _ => rfl) ?_
  intro x
  cases x <;> rfl
noncomputable def sumElim {ec : γ → List Bool} {f : α → γ} {g : β → γ}
    (F : PolyProgram ea ec f) (G : PolyProgram eb ec g) (a0 : α) (b0 : β) :
    PolyProgram (encodeLoop eb ea) ec (Sum.elim f g) :=
  (ite (sumTag ea eb) ((sumLeft ea eb a0).comp F) ((sumRight ea eb b0).comp G)).congr _
    (fun x => by cases x <;> rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch Analytic
variable {F J X : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]
variable [PseudoMetricSpace X] {Δ : ℕ}

noncomputable def advance (s : State F J Δ) (G : s.1 → Finset s.1) (H : Finset s.1)
    (Z : Finset (HeavyAction (graphActions G) H)) (x g : ℝ)
    (d : J → F → ℝ) : State F J Δ :=
  (next Δ s.1 (roundErased s.1 G H Z) (roundOpened s.1 G H Z),
    fun j => roundAlive s.1 (s.2 j) G H Z x g (d j))

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseAlgorithm
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBernoulliRun
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

def fair : SparseIntegerLaw (Fin 2) where
  length := 2
  states := Vector.ofFn id
  law := {
    denominator := 2
    denominator_pos := by norm_num
    numerator := fun _ => 1
    numerator_nonneg := fun _ => by norm_num
    total := by simp }

def mix (μ ν : SparseIntegerLaw α) : SparseIntegerLaw α :=
  fair.bindIndexed (fun a => if a.val=0 then μ else ν)

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparsePhysicalBatch
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseEnumeratedBatch
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalBatchFacts
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalRoundEvents
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBranchProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseWeightedPartial
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCardinalRounding
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseProduct
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGraphFeatures
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGraphRun
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGraphLaw
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

end MetricKMedian.SparseGraph
end
end

end OAI
end


