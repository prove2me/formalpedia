-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryPrimality
-- name    : QEC_Coding_BitTuring_UnaryPrimality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:16:55.48021+00:00
-- url     : https://prove2.me/theorems/a069c33b-61c9-4b12-bdf8-323d9fb8a88d
-- title:
--   Unary Primality
-- statement:
--   Definitions and structural lemmas for Unary Primality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPrimality.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTrial
import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Mathlib.Data.Nat.Prime.Basic
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTrial_trial_input_ne_output
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop
open Turing StateTransition
def Remaining (q a b : ℕ) : Prop :=
  ∀ x y : ℕ, 2 ≤ x → x ≤ q → 2 ≤ y → y ≤ q →
    (a < x ∨ (a = x ∧ b ≤ y)) → x*y ≠ q
def rank (q a b : ℕ) : ℕ := (q-a)*(q-1)+(q-b)
theorem remaining_current (q a b : ℕ) (ha : 2 ≤ a) (haq : a ≤ q)
    (hb : 2 ≤ b) (hbq : b ≤ q) (h : Remaining q a b) : a*b ≠ q :=
  h a b ha haq hb hbq (Or.inr ⟨rfl,le_refl _⟩)
theorem remaining_nextB (q a b : ℕ) (ha : 2 ≤ a) (haq : a ≤ q)
    (hb : 2 ≤ b) (hbq : b < q) :
    Remaining q a b ↔ a*b ≠ q ∧ Remaining q a (b+1) := by
  constructor
  · intro h
    refine ⟨remaining_current q a b ha haq hb (le_of_lt hbq) h,?_⟩
    intro x y hx hxq hy hyq hord
    apply h x y hx hxq hy hyq
    omega
  · rintro ⟨hab,h⟩ x y hx hxq hy hyq hord
    by_cases he : a = x ∧ b = y
    · rcases he with ⟨rfl,rfl⟩
      exact hab
    · apply h x y hx hxq hy hyq
      omega
theorem remaining_nextA (q a : ℕ) (ha : 2 ≤ a) (haq : a < q) :
    Remaining q a q ↔ a*q ≠ q ∧ Remaining q (a+1) 2 := by
  constructor
  · intro h
    refine ⟨remaining_current q a q ha (le_of_lt haq) (by omega) (le_refl _) h,?_⟩
    intro x y hx hxq hy hyq hord
    apply h x y hx hxq hy hyq
    omega
  · rintro ⟨hab,h⟩ x y hx hxq hy hyq hord
    by_cases he : a = x ∧ q = y
    · rcases he with ⟨rfl,rfl⟩
      exact hab
    · apply h x y hx hxq hy hyq
      omega
theorem remaining_end (q : ℕ) (hq : 2 ≤ q) : Remaining q q q ↔ q*q ≠ q := by
  constructor
  · exact remaining_current q q q hq (le_refl _) hq (le_refl _)
  · intro h x y hx hxq hy hyq hord
    have he : x=q ∧ y=q := by omega
    rcases he with ⟨rfl,rfl⟩
    exact h
theorem rank_nextB (q a b : ℕ) (hb : b < q) :
    rank q a (b+1)+1 = rank q a b := by
  unfold rank
  omega
theorem rank_nextA (q a : ℕ) (ha : a < q) (hq : 2 ≤ q) :
    rank q (a+1) 2+1 = rank q a q := by
  have he : q-a = q-(a+1)+1 := by omega
  unfold rank
  rw [he,Nat.add_mul]
  omega
theorem rank_le (q a b : ℕ) : rank q a b ≤ q^2 := by
  have h := Nat.mul_le_mul_right (q-1) (Nat.sub_le q a)
  have hs : q*(q-1)+q = q^2 := by
    by_cases hq : q=0
    · simp [hq]
    · have hh : q-1+1=q := by omega
      calc
        q*(q-1)+q = q*(q-1)+q*1 := by simp
        _ = q*((q-1)+1) := by ring
        _ = q^2 := by rw [hh,pow_two]
  unfold rank
  have hb := Nat.sub_le q b
  omega
theorem remaining_start_iff_prime (q : ℕ) (hq : 2 ≤ q) : Remaining q 2 2 ↔ q.Prime := by
  rw [Nat.prime_iff_not_exists_mul_eq]
  constructor
  · intro h
    refine ⟨hq,?_⟩
    rintro ⟨x,y,hx,hy,hm⟩
    have hx2 : 2 ≤ x := by
      by_contra hn
      have hx01 : x=0 ∨ x=1 := by omega
      rcases hx01 with rfl | rfl <;> simp_all
    have hy2 : 2 ≤ y := by
      by_contra hn
      have hy01 : y=0 ∨ y=1 := by omega
      rcases hy01 with rfl | rfl <;> simp_all
    exact h x y hx2 (le_of_lt hx) hy2 (le_of_lt hy) (by omega) hm
  · rintro ⟨_,h⟩ x y hx hxq hy hyq hord hm
    have hxl := Nat.mul_le_mul_left x hy
    have hyl := Nat.mul_le_mul_right y hx
    apply h
    exact ⟨x,y,by omega,by omega,hm⟩
noncomputable def answer (q a b : ℕ) : Bool := by
  classical
  exact decide (Remaining q a b)
@[simp] theorem answer_true (q a b : ℕ) : answer q a b = true ↔ Remaining q a b := by
  classical
  simp [answer]
@[simp] theorem answer_false (q a b : ℕ) : answer q a b = false ↔ ¬ Remaining q a b := by
  classical
  simp [answer]
noncomputable def bodyCost (q : ℕ) := FactorTrial.trialTime.eval (3*q+2)
noncomputable def callCost (q : ℕ) := bodyCost q+2*(3*q+2)+4
def machine : Machine := FlagLoop.machine FactorTrial.trialMachine
noncomputable def bodyExec (q a b : ℕ) (haq : a ≤ q) (hbq : b ≤ q) :
    EvalsToInTime (TM2.step FactorTrial.trialMachine.program)
      (FactorTrial.trialMachine.init (FactorTest.tripleInput a b q))
      (some (FactorTrial.trialMachine.halt
        (FactorTrial.updateBits (decide (a*b=q)) a b q))) (bodyCost q) := by
  have h := FactorTrial.trialPolyExec a b q haq hbq
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  have hl : (FactorTest.tripleInput a b q).length ≤ 3*q+2 := by
    rw [FactorTest.tripleInput_length]
    omega
  have hs := Nat.pow_le_pow_left (show (FactorTest.tripleInput a b q).length+1 ≤ 3*q+2+1 by omega) 2
  have h5 := Nat.mul_le_mul_left 5 hs
  have h7 := Nat.mul_le_mul_left 7 hl
  simp only [bodyCost,FactorTrial.trialTime,FactorTest.time,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow,
    Polynomial.eval_one]
  omega
noncomputable def foundExec (q a b : ℕ) (haq : a ≤ q) (hbq : b ≤ q) (hab : a*b=q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (FactorTest.tripleInput a b q))
      (some (machine.halt [false])) (callCost q) := by
  have hb := bodyExec q a b haq hbq
  simp only [FactorTrial.updateBits,hab,decide_true,ite_true] at hb
  have h := FlagLoop.invocationExec FactorTrial.trialMachine FactorTrial.trial_input_ne_output
    (FactorTest.tripleInput a b q) [false] true (bodyCost q) hb
  simp only [FlagLoop.target] at h
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  simp only [callCost,List.length_cons,List.length_nil]
  omega
noncomputable def nextBExec (q a b : ℕ) (haq : a ≤ q) (hbq : b < q) (hab : a*b≠q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (FactorTest.tripleInput a b q))
      (some (machine.init (FactorTest.tripleInput a (b+1) q))) (callCost q) := by
  have hb := bodyExec q a b haq (le_of_lt hbq)
  simp only [FactorTrial.updateBits,hab,decide_false,Bool.false_eq_true,ite_false,hbq,ite_true] at hb
  have h := FlagLoop.invocationExec FactorTrial.trialMachine FactorTrial.trial_input_ne_output
    (FactorTest.tripleInput a b q) (FactorTest.tripleInput a (b+1) q) false (bodyCost q) hb
  simp only [FlagLoop.target,Bool.false_eq_true] at h
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  simp only [callCost,FactorTest.tripleInput_length]
  omega
noncomputable def nextAExec (q a : ℕ) (haq : a < q) (hq : 2 ≤ q) (hab : a*q≠q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (FactorTest.tripleInput a q q))
      (some (machine.init (FactorTest.tripleInput (a+1) 2 q))) (callCost q) := by
  have hb := bodyExec q a q (le_of_lt haq) (le_refl _)
  simp only [FactorTrial.updateBits,hab,decide_false,Bool.false_eq_true,ite_false,
    lt_self_iff_false,haq,ite_true] at hb
  have h := FlagLoop.invocationExec FactorTrial.trialMachine FactorTrial.trial_input_ne_output
    (FactorTest.tripleInput a q q) (FactorTest.tripleInput (a+1) 2 q) false (bodyCost q) hb
  simp only [FlagLoop.target,Bool.false_eq_true] at h
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  simp only [callCost,FactorTest.tripleInput_length]
  omega
noncomputable def endExec (q : ℕ) (hq : 2 ≤ q) (hab : q*q≠q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (FactorTest.tripleInput q q q))
      (some (machine.halt [true])) (callCost q) := by
  have hb := bodyExec q q q (le_refl _) (le_refl _)
  simp only [FactorTrial.updateBits,hab,decide_false,Bool.false_eq_true,ite_false,
    lt_self_iff_false] at hb
  have h := FlagLoop.invocationExec FactorTrial.trialMachine FactorTrial.trial_input_ne_output
    (FactorTest.tripleInput q q q) [true] true (bodyCost q) hb
  simp only [FlagLoop.target] at h
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  simp only [callCost,List.length_cons,List.length_nil]
  omega
noncomputable def loopExec (q a b : ℕ) (hq : 2 ≤ q) (ha : 2 ≤ a) (haq : a ≤ q)
    (hb : 2 ≤ b) (hbq : b ≤ q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (FactorTest.tripleInput a b q))
      (some (machine.halt [answer q a b])) ((rank q a b+1)*callCost q) := by
  classical
  suffices h : ∀ r a b, rank q a b=r → 2≤a → a≤q → 2≤b → b≤q →
      EvalsToInTime (TM2.step machine.program) (machine.init (FactorTest.tripleInput a b q))
        (some (machine.halt [answer q a b])) ((r+1)*callCost q) by
    exact h _ a b rfl ha haq hb hbq
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
      intro a b he ha haq hb hbq
      by_cases hab : a*b=q
      · have heA : answer q a b=false := (answer_false q a b).2 (fun h =>
          remaining_current q a b ha haq hb hbq h hab)
        rw [heA]
        have h := foundExec q a b haq hbq hab
        refine { h with steps_le_m := h.steps_le_m.trans ?_ }
        exact Nat.le_mul_of_pos_left _ (by omega)
      · by_cases hB : b<q
        · have hr := rank_nextB q a b hB
          have ht := ih (rank q a (b+1)) (by omega) a (b+1) rfl ha haq (by omega) (by omega)
          have heA : answer q a b=answer q a (b+1) := by
            unfold answer
            exact Bool.decide_congr ((remaining_nextB q a b ha haq hb hB).trans (and_iff_right hab))
          rw [← heA] at ht
          have h := EvalsToInTime.trans (TM2.step machine.program) (callCost q)
            ((rank q a (b+1)+1)*callCost q)
            (machine.init (FactorTest.tripleInput a b q))
            (machine.init (FactorTest.tripleInput a (b+1) q))
            (some (machine.halt [answer q a b])) (nextBExec q a b haq hB hab) ht
          refine { h with steps_le_m := h.steps_le_m.trans ?_ }
          have hc : (rank q a (b+1)+1)*callCost q+callCost q =
              (rank q a (b+1)+1+1)*callCost q := by ring
          rw [hc]
          have hh : rank q a (b+1)+1+1=r+1 := by omega
          rw [hh]
        · have hbe : b=q := by omega
          subst b
          by_cases hA : a<q
          · have hr := rank_nextA q a hA hq
            have ht := ih (rank q (a+1) 2) (by omega) (a+1) 2 rfl (by omega) (by omega)
              (le_refl _) hq
            have heA : answer q a q=answer q (a+1) 2 := by
              unfold answer
              exact Bool.decide_congr ((remaining_nextA q a ha hA).trans (and_iff_right hab))
            rw [← heA] at ht
            have h := EvalsToInTime.trans (TM2.step machine.program) (callCost q)
              ((rank q (a+1) 2+1)*callCost q)
              (machine.init (FactorTest.tripleInput a q q))
              (machine.init (FactorTest.tripleInput (a+1) 2 q))
              (some (machine.halt [answer q a q])) (nextAExec q a hA hq hab) ht
            refine { h with steps_le_m := h.steps_le_m.trans ?_ }
            have hc : (rank q (a+1) 2+1)*callCost q+callCost q =
                (rank q (a+1) 2+1+1)*callCost q := by ring
            rw [hc]
            have hh : rank q (a+1) 2+1+1=r+1 := by omega
            rw [hh]
          · have hae : a=q := by omega
            subst a
            have heA : answer q q q=true := (answer_true q q q).2 ((remaining_end q hq).2 hab)
            rw [heA]
            have h := endExec q hq hab
            refine { h with steps_le_m := h.steps_le_m.trans ?_ }
            exact Nat.le_mul_of_pos_left _ (by omega)
noncomputable def time : Polynomial ℕ :=
  (Polynomial.X^2+1) * (FactorTrial.trialTime.comp (Polynomial.C 3*Polynomial.X+Polynomial.C 2)
    + Polynomial.C 6*Polynomial.X+Polynomial.C 8)
theorem loop_budget_le (q a b : ℕ) :
    (rank q a b+1)*callCost q ≤ time.eval (FactorTest.tripleInput a b q).length := by
  let L := (FactorTest.tripleInput a b q).length
  have hq : q≤L := by dsimp [L]; rw [FactorTest.tripleInput_length]; omega
  have hR := (rank_le q a b).trans (Nat.pow_le_pow_left hq 2)
  have hB := Composition.polynomial_eval_monotone FactorTrial.trialTime
    (show 3*q+2≤3*L+2 by omega)
  change FactorTrial.trialTime.eval (3*q+2) ≤ FactorTrial.trialTime.eval (3*L+2) at hB
  have hC : callCost q ≤ FactorTrial.trialTime.eval (3*L+2)+6*L+8 := by
    unfold callCost bodyCost
    omega
  have h := Nat.mul_le_mul (Nat.add_le_add_right hR 1) hC
  simpa only [time,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp,Polynomial.eval_C,L] using h
noncomputable def loopPolyExec (q a b : ℕ) (hq : 2≤q) (ha : 2≤a) (haq : a≤q)
    (hb : 2≤b) (hbq : b≤q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (FactorTest.tripleInput a b q))
      (some (machine.halt [answer q a b])) (time.eval (FactorTest.tripleInput a b q).length) := by
  have h := loopExec q a b hq ha haq hb hbq
  refine { h with steps_le_m := h.steps_le_m.trans (loop_budget_le q a b) }
theorem answer_start (q : ℕ) (hq : 2≤q) : answer q 2 2 = decide q.Prime := by
  classical
  unfold answer
  exact Bool.decide_congr (remaining_start_iff_prime q hq)
noncomputable def primeExec (q : ℕ) (hq : 2≤q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (FactorTest.tripleInput 2 2 q))
      (some (machine.halt [decide q.Prime])) (time.eval (FactorTest.tripleInput 2 2 q).length) := by
  have h := loopPolyExec q 2 2 hq (le_refl _) hq (le_refl _) hq
  simpa only [answer_start q hq] using h
abbrev Input := {q : ℕ // 2≤q}
def input (q : Input) : List Bool := FactorTest.tripleInput 2 2 q.val
def output (q : Input) : List Bool := [decide q.val.Prime]
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input id output where
  tm := machine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun := fun q => by
    change TM2OutputsInTime machine.toFinTM2 (List.map id (input q))
      (some (List.map id (output q))) (time.eval (input q).length)
    have h := Machine.outputsInTime machine _ _ _ (primeExec q.val q.property)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input,output] using h
def initializerMachine : Machine where
  K := Unit
  input := ()
  output := ()
  Λ := Unit
  main := ()
  σ := Unit
  initial := ()
  program := fun _ => .push () (fun _ => false) (.push () (fun _ => true)
    (.push () (fun _ => true) (.push () (fun _ => false) (.push () (fun _ => true)
      (.push () (fun _ => true) .halt)))))
theorem prefix_step (q : ℕ) :
    TM2.step initializerMachine.program (initializerMachine.init (unary q)) =
      some (initializerMachine.halt (FactorTest.tripleInput 2 2 q)) := by
  simp [TM2.step,initializerMachine,Machine.init,Machine.halt,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k
  simp [Function.update,FactorTest.tripleInput,pairInput,unary,List.replicate_succ]
def prefixExec (q : ℕ) :
    EvalsToInTime (TM2.step initializerMachine.program) (initializerMachine.init (unary q))
      (some (initializerMachine.halt (FactorTest.tripleInput 2 2 q))) 1 := by
  refine ⟨⟨1,?_⟩,le_refl _⟩
  change TM2.step initializerMachine.program (initializerMachine.init (unary q)) = _
  exact prefix_step q
def unaryMachine : Machine := Composition.machine initializerMachine machine
noncomputable def unaryTime : Polynomial ℕ :=
  time.comp (Polynomial.X+Polynomial.C 6)+Polynomial.C 2*(Polynomial.X+Polynomial.C 6)
    +Polynomial.C 3
noncomputable def unaryExec (q : ℕ) (hq : 2≤q) :
    EvalsToInTime (TM2.step unaryMachine.program) (unaryMachine.init (unary q))
      (some (unaryMachine.halt [decide q.Prime])) (unaryTime.eval (unary q).length) := by
  have h := Composition.executes initializerMachine machine (unary q) (FactorTest.tripleInput 2 2 q)
    [decide q.Prime] 1 (time.eval (FactorTest.tripleInput 2 2 q).length) (prefixExec q) (primeExec q hq)
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  have hL : (FactorTest.tripleInput 2 2 q).length=q+6 := by
    rw [FactorTest.tripleInput_length]
    omega
  simp only [unaryTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
    Polynomial.eval_X,Polynomial.eval_C,unary_length,hL]
  omega
def unaryInput (q : Input) : List Bool := unary q.val
noncomputable def unaryComputableInPolyTime : TM2ComputableInPolyTime unaryInput id output where
  tm := unaryMachine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := unaryTime
  outputsFun := fun q => by
    change TM2OutputsInTime unaryMachine.toFinTM2 (List.map id (unaryInput q))
      (some (List.map id (output q))) (unaryTime.eval (unaryInput q).length)
    have h := Machine.outputsInTime unaryMachine _ _ _ (unaryExec q.val q.property)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,unaryInput,output] using h
end QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop


