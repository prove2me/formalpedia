-- Prove2me | Definitions.Def_Q238L022
-- name    : Q238L022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:24:55.662486+00:00
-- url     : https://prove2.me/theorems/dd1727cb-2104-47b4-9b78-86a622187b41
-- title:
--   Definitions bundle Q238L022 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 93 declarations of OpenAI's Lean: 83 definitions and 10 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.base`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boundedWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.dim`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.doubledGap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.epsilon`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.gap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.power`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.precision`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.precisionArg`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.radius`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.radiusPrecision`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.relaxedWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.rowFactor`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.solved`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.boundCounter`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.prepared`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.gram`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.decision`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.op`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.coefficient`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.payment`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.active`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningConstant.constant`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.active`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.sumWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.summand`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.values` and 43 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Encoding_PushWord`, `KMedianRecovery_Recovery_Basic`, `KMedianRecovery_Recovery_Basic2`, `KMedianRecovery_Recovery_BoundOp`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_Computes`, `KMedianRecovery_Recovery_Copies`, `KMedianRecovery_Recovery_FaceSelection`, `KMedianRecovery_Recovery_IfNat`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_Pack3`, `KMedianRecovery_Recovery_Pack4`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack8`, `KMedianRecovery_Recovery_Pack9`, `KMedianRecovery_Recovery_Rectangular`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Recovery_Store2`, `KMedianRecovery_Recovery_Values`, `KMedianRecovery_Sampling_ExtractPrefix`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L013`, `Q238L014` and `Q238L015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L027`, `Q238L028`, `Q238L029` and `Q238L030`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords_bird_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L013
import Definitions.Def_Q238L014
import Definitions.Def_Q238L015

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_ExtractPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

noncomputable def extractPrefix_computes : PolyComputes extractPrefix := by
  have hh := extractReverse_computes.comp reverse_computes
  simpa only [Function.comp_def,List.reverse_reverse] using hh

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_PushWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

noncomputable def isEmpty_computes : PolyComputes (fun xs=>[decide (xs=[])]) := by
  have hh := FiniteFold.computes true (fun _ _=>false) (fun q=>[q])
  simpa [fold_empty] using hh

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Store2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace WordOperations

noncomputable def tail_computes : PolyComputes (List.tail : List Bool → List Bool) where
  program := tailProgram
  time := 1
  outputs xs := by
    simp only [TM2OutputsInTime,Option.map_some,Polynomial.eval_one]
    apply one_step
    cases xs <;> simp [initList_bool,haltList_bool,FinTM2.step,tailProgram,TM2.step,TM2.stepAux,unit_update]
    all_goals rfl

end WordOperations

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Computes
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.discardPrefix_pairBits _root_.OAI.MetricKMedianRecovery.BitMachine.extractPrefix_pairBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open Turing Turing.TM2 StateTransition
namespace WordSelection
open WordOperations

lemma parse_true (b : Bool) (xs ys : List Bool) :
    program.machine.step (cfg 1 (true::b::xs) ys)=some (cfg 1 xs (b::ys)) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0,upd1]; rfl
lemma restore_nil (xs : List Bool) : program.machine.step (cfg 4 xs [])=some (done xs) := by
  simp [FinTM2.step,program,cfg,done,TM2.step,TM2.stepAux,upd1]; rfl
lemma restore_cons (b : Bool) (xs ys : List Bool) : program.machine.step (cfg 4 xs (b::ys))=some (cfg 4 (b::xs) ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0,upd1]; rfl

noncomputable def parse_phase (xs ys : List Bool) :
    EvalsToInTime program.machine.step (cfg 1 xs ys)
      (some (cfg 3 (discardPrefix xs) ((extractPrefix xs).reverse++ys))) (xs.length+1) := by
  induction xs using List.twoStepInduction generalizing ys with
  | nil => exact one_step (parse_nil ys)
  | singleton b =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_singleton] using
        time_mono (one_step (parse_false [] ys)) (by decide : 1≤2)
    | true => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_singleton] using
        time_mono (one_step (parse_one ys)) (by decide : 1≤2)
  | cons_cons b c xs ih _ =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append] using
        time_mono (one_step (parse_false (c::xs) ys)) (by simp : 1≤(false::c::xs).length+1)
    | true =>
      have hh := step_then (parse_true c xs ys) (ih (c::ys))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def restore_phase (xs ys : List Bool) :
    EvalsToInTime program.machine.step (cfg 4 xs ys)
      (some (done (ys.reverse++xs))) (ys.length+1) := by
  induction ys generalizing xs with
  | nil => exact one_step (restore_nil xs)
  | cons b ys ih =>
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using step_then (restore_cons b xs ys) (ih (b::xs))

noncomputable def discard_phase (xs : List Bool) :
    EvalsToInTime program.machine.step (cfg 2 xs []) (some (done (discardPrefix xs))) (xs.length+1) := by
  induction xs using List.twoStepInduction with
  | nil => exact one_step discard_nil
  | singleton b =>
    cases b with
    | false => simpa only [discardPrefix,List.length_singleton] using
        time_mono (one_step (discard_false [])) (by decide : 1≤2)
    | true => simpa only [discardPrefix,List.length_singleton] using
        time_mono (one_step discard_one) (by decide : 1≤2)
  | cons_cons b c xs ih _ =>
    cases b with
    | false => simpa only [discardPrefix] using
        time_mono (one_step (discard_false (c::xs))) (by simp : 1≤(false::c::xs).length+1)
    | true =>
      have hh := step_then (discard_true c xs) ih
      simp only [discardPrefix]
      exact time_mono hh (by simp)

noncomputable def true_phase (xs : List Bool) :
    EvalsToInTime program.machine.step (cfg 1 xs []) (some (done (extractPrefix xs))) (3*xs.length+3) := by
  have h1 := parse_phase xs []
  have h2 := clear_phase (discardPrefix xs) (extractPrefix xs).reverse
  have h3 := restore_phase [] (extractPrefix xs).reverse
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h3
  have hh := eval_trans h1 (eval_trans h2 h3)
  have hl := ProductBits.projections_length xs
  exact time_mono hh (by omega)

noncomputable def outputs (xs : List Bool) :
    EvalsToInTime program.machine.step (cfg 0 xs []) (some (done (choose xs))) (4*xs.length+4) := by
  cases xs with
  | nil =>
    have hh := step_then start_nil (one_step discard_nil)
    exact time_mono hh (by decide : 2≤4)
  | cons b xs =>
    cases b with
    | false =>
      have hh := step_then (start_false xs) (discard_phase xs)
      simpa only [choose,List.head?_cons,List.tail_cons,Option.some.injEq,Bool.false_eq_true,ite_false, if_false] using
        time_mono hh (by simp only [List.length_cons]; omega)
    | true =>
      have hh := step_then (start_true xs) (true_phase xs)
      simpa only [choose,List.head?_cons,List.tail_cons,ite_true, if_true] using
        time_mono hh (by simp only [List.length_cons]; omega)

noncomputable def choose_computes : PolyComputes choose where
  program := program
  time := 4*Polynomial.X+4
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using outputs xs

end WordSelection

noncomputable def PolyComputes.cond {p : List Bool → Bool} {f g : List Bool → List Bool}
    (hp : PolyComputes (fun xs=>[p xs])) (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun xs=>if p xs then f xs else g xs) := by
  have hh := (hp.append (hf.pair hg)).comp WordSelection.choose_computes
  simpa only [Function.comp_def,List.singleton_append,WordSelection.choose,List.head?_cons,
    List.tail_cons,Option.some.injEq,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeftNum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational

def invWords : List Bool → List Bool := reduce ∘ rawInv

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace UnaryTake

noncomputable def counter_computes : PolyComputes counter := tail_computes.comp extractPrefix_computes
noncomputable def data_computes : PolyComputes data :=
  (tail_computes.comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def output_computes : PolyComputes output :=
  (tail_computes.comp discardPrefix_computes).comp discardPrefix_computes
noncomputable def pack_computes {c d o : List Bool → List Bool} (a : Bool)
    (hc : PolyComputes c) (hd : PolyComputes d) (ho : PolyComputes o) :
    PolyComputes (fun x=>pack a (c x) (d x) (o x)) :=
  (const_computes [a]).append (hc.pair (hd.pair ho))

end UnaryTake
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake
namespace RepeatedAppend

noncomputable def step_computes : PolyComputes step := by
  have ht := pack_computes true (counter_computes.comp tail_computes) data_computes
    (data_computes.append output_computes)
  have hh := (counter_computes.comp isEmpty_computes).cond
    (pack_computes false (const_computes []) data_computes output_computes) ht
  unfold step
  simpa only [Function.comp_def,decide_eq_true_eq] using hh

lemma iterate_bounds (x : List Bool) (j : ℕ) :
    (counter (next^[j] x)).length ≤ (counter x).length ∧ data (next^[j] x)=data x ∧
    (output (next^[j] x)).length ≤ (output x).length+j*(data x).length ∧
    (next^[j] x).length ≤ x.length+2*(counter x).length+2*(data x).length+(output x).length+
      j*(data x).length+3 ∧ rank (next^[j] x) ≤ rank x-j := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply,Nat.sub_zero,Nat.le_refl,Nat.zero_mul,
      Nat.add_zero,true_and,and_true]; omega
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hc := counter_next (next^[j] x)
    have hd := data_next (next^[j] x)
    have ho := output_next (next^[j] x)
    have hl := length_next (next^[j] x)
    have hr := rank_next (next^[j] x)
    rw [ih.2.1] at hd ho
    refine ⟨hc.trans ih.1,hd,?_,?_,?_⟩
    · nlinarith [ih.2.2.1]
    · apply hl.trans; apply max_le
      · nlinarith [ih.2.2.2.1]
      · rw [hd]; nlinarith [ih.1,ih.2.2.1]
    · omega
lemma stop (x : List Bool) : (next^[rank x] x).head?≠some true := by
  have hh := (iterate_bounds x (rank x)).2.2.2.2
  simp only [Nat.sub_self,Nat.le_zero] at hh
  intro hp
  change (if (next^[rank x] x).head?=some true then _ else 0)=0 at hh
  rw [ite_eq_left hp] at hh; omega
noncomputable def loop_computes : PolyComputes (fun x=>next^[rank x] x) := by
  apply step_computes.whileLoop rank (Polynomial.X+1) (20*(Polynomial.X+1)^2)
  · intro x
    have h := (projection_bounds x).1
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    unfold rank; split_ifs <;> omega
  · intro x j hj
    have h := (iterate_bounds x j).2.2.2.1
    obtain ⟨hc,hd,ho⟩ := projection_bounds x
    have hr : rank x ≤ x.length+1 := by unfold rank; split_ifs <;> omega
    have hjd : j*(data x).length ≤ (x.length+1)*x.length := Nat.mul_le_mul (hj.trans hr) hd
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    change (next^[j] x).length ≤ _
    nlinarith
  · exact stop
lemma next_nil (d o : List Bool) : next (pack true [] d o)=pack false [] d o := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,counter_pack,data_pack,output_pack]
lemma next_cons (b : Bool) (c d o : List Bool) :
    next (pack true (b::c) d o)=pack true c d (d++o) := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,counter_pack,reduceCtorEq,ite_false, if_false,
    data_pack,output_pack,List.tail_cons]
lemma loop_spec (c d o : List Bool) : next^[c.length+1] (pack true c d o)=
    pack false [] d (copies c.length d++o) := by
  induction c generalizing o with
  | nil => simp only [List.length_nil,Nat.zero_add,Function.iterate_one,next_nil,copies,List.nil_append]
  | cons b c ih => rw [List.length_cons,Function.iterate_succ_apply,next_cons,ih,copies,List.append_assoc]

noncomputable def run_computes : PolyComputes run := by
  have hi := pack_computes true extractPrefix_computes discardPrefix_computes (const_computes [])
  have hh := (hi.comp loop_computes).comp output_computes
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply,rank,head_pack,ite_true, if_true,counter_pack,loop_spec,output_pack,List.append_nil]
  rfl
lemma run_pair (c d : List Bool) : run (pairBits (c,d))=copies c.length d := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits]

end RepeatedAppend

namespace PolynomialCounter
noncomputable def mul {P Q : Polynomial ℕ} (p : PolynomialCounter P) (q : PolynomialCounter Q) :
    PolynomialCounter (P*Q) where
  word x := RepeatedAppend.copies (p.word x).length (q.word x)
  computes := by
    have hh := (p.computes.pair q.computes).comp RepeatedAppend.run_computes
    simpa only [Function.comp_def,RepeatedAppend.run_pair] using hh
  word_length x := by simp only [RepeatedAppend.length_copies,p.word_length,q.word_length,Polynomial.eval_mul]

theorem nonempty (P : Polynomial ℕ) : Nonempty (PolynomialCounter P) := by
  induction P using Polynomial.induction_on with
  | C n => exact ⟨constant n⟩
  | add P Q hp hq => obtain ⟨p⟩ := hp; obtain ⟨q⟩ := hq; exact ⟨p.add q⟩
  | monomial n a ih =>
    obtain ⟨p⟩ := ih
    rw [pow_succ,←mul_assoc]
    exact ⟨p.mul identity⟩
noncomputable def choose (P : Polynomial ℕ) : PolynomialCounter P := Classical.choice (nonempty P)
end PolynomialCounter

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace UnaryResources

noncomputable def cap : PolynomialCounter (2*Polynomial.X+2) := PolynomialCounter.choose _
noncomputable def lengthBits (x : List Bool) : List Bool :=
  BoundedIteration.run inc (pairBits (x,pairBits (cap.word x,(0:ℕ).bits)))
noncomputable def threePower (x : List Bool) : List Bool :=
  BoundedIteration.run triple (pairBits (x,pairBits (cap.word x,(1:ℕ).bits)))
end UnaryResources
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryEllipsoidIteration
open RationalMatrix BinaryEllipsoidAdvance

noncomputable def boundCounter : PolynomialCounter storagePoly := PolynomialCounter.choose storagePoly
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (extractPrefix x,pairBits (boundCounter.word x,discardPrefix (discardPrefix x)))
noncomputable def run : List Bool → List Bool := BoundedIteration.run BinaryEllipsoidAdvance.run ∘ prepared
end BinaryEllipsoidIteration
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open UnaryResources
namespace BinaryWeakSolve
open RationalMatrix

noncomputable def dimBits : List Bool → List Bool := lengthBits ∘ nword
noncomputable def powerWords (x : List Bool) : List Bool := threePower (budgetWord x++[true])
noncomputable def cubeWords (x : List Bool) : List Bool := (value (dimBits x)*value (dimBits x)*value (dimBits x)).bits
noncomputable def gridWords (x : List Bool) : List Bool := (16*value (cubeWords x)*value (powerWords x)).bits
noncomputable def advanceInput (x : List Bool) : List Bool :=
  pairBits (dimBits x,pairBits (gridWords x,pairBits (rows x,pairBits (shapeWords x,centerWords x))))
noncomputable def prepared (x : List Bool) : List Bool := pairBits (budgetWord x,pairBits (radius x,advanceInput x))
noncomputable def iterated : List Bool → List Bool := BinaryEllipsoidIteration.run ∘ prepared
noncomputable def run : List Bool → List Bool := result ∘ iterated
end BinaryWeakSolve
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryDecision
open UnaryResources NaturalArray

noncomputable def dim : List Bool → List Bool := lengthBits ∘ nword
noncomputable def count : List Bool → List Bool := lengthBits ∘ mword
noncomputable def rowFactor (x : List Bool) : List Bool :=
  (value (count x)+2*value (dim x)+2*(value (dim x)+1)).bits
noncomputable def base (x : List Bool) : List Bool := (value (rowFactor x)*(value (height x)*value (height x))).bits
noncomputable def power (x : List Bool) : List Bool := exponentiate (pairBits (nextDim x,base x))
noncomputable def gap (x : List Bool) : List Bool := (value (factorial x)*value (power x)).bits
noncomputable def doubledGap (x : List Bool) : List Bool := (2*value (gap x)).bits
noncomputable def epsilon (x : List Bool) : List Bool := BinaryRational.encode (1/(value (doubledGap x):ℚ))
noncomputable def precisionArg (x : List Bool) : List Bool := (value (doubledGap x)*value (height x)).bits
noncomputable def precision : List Bool → List Bool := unaryLog ∘ precisionArg
noncomputable def radius (x : List Bool) : List Bool := (value (dim x)*(value (bound x)+1)).bits
noncomputable def radiusPrecision : List Bool → List Bool := unaryLog ∘ radius
end BinaryDecision
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundOp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryDecision
open WordList RationalMatrix

noncomputable def boundedWords (x : List Bool) : List Bool := rows x++boxWords true x++boxWords false x
noncomputable def relaxedWords (x : List Bool) : List Bool := mapWith relaxedOp (pairBits (epsilon x,boundedWords x))
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (nword x,pairBits (precision x,pairBits (radiusPrecision x,pairBits (radius x,relaxedWords x))))
noncomputable def solved : List Bool → List Bool := BinaryWeakSolve.run ∘ prepared
noncomputable def run (x : List Bool) : List Bool := [!decide (solved x=[])]
end BinaryDecision
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundedDecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

namespace BinaryBoundedDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList RationalMatrix

noncomputable def run : List Bool → List Bool := BinaryDecision.run ∘ prepared
end BinaryBoundedDecision
namespace BinaryRationalDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList

noncomputable def run : List Bool → List Bool := BinaryBoundedDecision.run ∘ prepared
end BinaryRationalDecision

open WordOperations
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FaceSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryFace
open WordList
noncomputable def decision : List Bool → List Bool := BinaryRationalDecision.run ∘ decisionInput
noncomputable def op (x : List Bool) : List Bool := if (decision x).head?.getD false then proposed x else Find.accum x
noncomputable def run : List Bool → List Bool := Fold.run op (4*Polynomial.X+4)
end BinaryFace
namespace BinaryFinalFace
open WordList BinaryRationalDecision
noncomputable def run (x : List Bool) : List Bool := BinaryFace.run (Fold.pack (allRows x) (context x) [])
end BinaryFinalFace
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open WordOperations BinaryArithmetic
open scoped Matrix
namespace RationalMatrix
open WordList

noncomputable def updateColWords (x : List Bool) : List Bool :=
  transposeWords (Set.run (updateInput x))
noncomputable def cramerOp (x : List Bool) : List Bool :=
  determinantWords (updateColWords (cramerOpInput x))
noncomputable def cramerWords (x : List Bool) : List Bool := mapWith cramerOp (cramerInput x)

noncomputable def firstDet : List Bool → List Bool := determinantWords ∘ extractPrefix
noncomputable def inverseDet : List Bool → List Bool := BinaryRational.invWords ∘ firstDet
noncomputable def solveInput (x : List Bool) : List Bool := pairBits (inverseDet x,cramerWords x)
noncomputable def solveWords (x : List Bool) : List Bool := mapWith BinaryRational.mulWords (solveInput x)
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Rectangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix
namespace BinaryExactSolve
open WordList BinaryRationalDecision RationalMatrix
noncomputable def transposed (x : List Bool) : List Bool :=
  Rectangular.transpose (pairBits (first x,coeffs (BinaryFinalFace.run x)))
noncomputable def gram (x : List Bool) : List Bool := mapWith rightRowOp (pairBits (transposed x,transposed x))
noncomputable def rhs (x : List Bool) : List Bool :=
  RationalMatrix.mulVec (pairBits (transposed x,bounds (BinaryFinalFace.run x)))
noncomputable def point (x : List Bool) : List Bool := solveWords (pairBits (gram x,rhs x))
noncomputable def run (x : List Bool) : List Bool :=
  if (BinaryRationalDecision.run x).head?.getD false then true::point x else []
end BinaryExactSolve
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryOpeningActivity
open WordList

noncomputable def run (x : List Bool) : List Bool := [decide (Find.run fails x=[])]
end BinaryOpeningActivity
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Values
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningPayment
open WordList RationalLinearFeasibility

noncomputable def active (x : List Bool) : Bool :=
  (BinaryOpeningActivity.run (activityInput x)).head?.getD false

noncomputable def summand (x : List Bool) : ℚ :=
  if active x then
    if distance x≤paramV x*paramZ x then -(scale x*distance x)
    else max (paramZ x-scale x*distance x) 0
  else max (scale x*nearest x-scale x*distance x) 0
noncomputable def values : List Bool → List Bool := mapWith (fun x=>BinaryRational.encode (summand x)) ∘ input
noncomputable def sumWords : List Bool → List Bool := RationalArray.sumWords ∘ values

noncomputable def run (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (field 4 x) -
    (BinaryArithmetic.value (UnaryResources.lengthBits (field 7 x)):ℚ)*BinaryRational.decode (field 5 x) -
    BinaryRational.decode (sumWords x))
end BinaryOpeningPayment
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningConstant
open WordList RationalLinearFeasibility

noncomputable def active (k : ℕ) (x : List Bool) : Bool := BinaryOpeningPayment.active (query k x)
noncomputable def constant (x : List Bool) : ℚ :=
  if tag x=0 then if active 1 x then BinaryOpeningPayment.paramZ x else 0
  else if tag x=1 then if active 1 x then -((1+BinaryOpeningPayment.paramV x*BinaryOpeningPayment.paramV x)*BinaryOpeningPayment.paramZ x) else 0
  else if tag x=2 then if active 1 x then -(BinaryOpeningPayment.scale x*distance 2 1 x) else 0
  else if tag x=3 then if active 1 x then if near x then 0 else -BinaryOpeningPayment.paramZ x else 0
  else if tag x=4 then BinaryRational.decode (BinaryOpeningPayment.run (extractPrefix x))
  else if tag x=6 then if active 3 x then
    if active 1 x then -distance 2 1 x else -(2*distance 2 1 x+distance 2 3 x) else 0
  else if tag x=7 then if active 1 x then -BinaryRational.decode (BinaryOpeningPayment.itemField 4 x) else 0
  else 0

end BinaryOpeningConstant
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_IfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningCoefficient
open WordList RationalLinearFeasibility

noncomputable def payment (x : List Bool) : ℚ :=
  if value (col 0 x)=0 then if BinaryOpeningPayment.active (paymentQuery x) then
    if paymentNear x then 1 else 0 else 0 else 0

noncomputable def coefficient (x : List Bool) : ℚ :=
  if BinaryOpeningConstant.tag (extractPrefix x)=0 then
    if BinaryOpeningConstant.active 1 (extractPrefix x) then -bid 1 x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=1 then
    if BinaryOpeningConstant.active 1 (extractPrefix x) then bid 1 x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=2 then
    if BinaryOpeningConstant.active 1 (extractPrefix x) then bid 1 x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=3 then
    if BinaryOpeningConstant.active 1 (extractPrefix x) then
      if BinaryOpeningConstant.near (extractPrefix x) then 0 else bid 1 x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=4 then -payment x
  else if BinaryOpeningConstant.tag (extractPrefix x)=5 then
    if BinaryOpeningConstant.active 3 (extractPrefix x) then -slack x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=6 then
    if BinaryOpeningConstant.active 3 (extractPrefix x) then
      (if BinaryOpeningConstant.active 1 (extractPrefix x) then bid 1 x else bid 3 x) - slack x else 0
  else if BinaryOpeningConstant.tag (extractPrefix x)=7 then
    if BinaryOpeningConstant.active 1 (extractPrefix x) then dual x else 0
  else 0
end BinaryOpeningCoefficient
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RowInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRawOpening
open WordOperations BinaryArithmetic WordList RationalLinearFeasibility
open BinaryOpeningPayment BinaryOpeningEnumeration
noncomputable def rowCoefficients (x : List Bool) : List Bool :=
  mapWith (fun y=>BinaryRational.encode (BinaryOpeningCoefficient.coefficient y)) (rowInput x)
noncomputable def rowWord (x : List Bool) : List Bool :=
  pairBits (rowCoefficients x,BinaryRational.encode (-BinaryOpeningConstant.constant x))
noncomputable def rows (x : List Bool) : List Bool := mapWith rowWord (pairBits (x,kinds x))
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (Count.run (columns x),pairBits (Count.run (kinds x),pairBits ((⌈bound x⌉₊).bits,rows x)))
end MetricKMedianRecovery.BitMachine.BinaryRawOpening

end OAI
end


