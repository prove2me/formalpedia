-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnarySquareRootTrial
-- name    : QEC_Coding_BitTuring_UnarySquareRootTrial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:07:53.818294+00:00
-- url     : https://prove2.me/theorems/47c7e675-2975-477e-9aa0-285644382159
-- title:
--   Unary Square Root Trial
-- statement:
--   Definitions and structural lemmas for Unary Square Root Trial, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnarySquareRootTrial.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularTrial
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_halt_eq

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.SquareRootAdvance
open Turing StateTransition
abbrev Var := Bool × Option Bool
abbrev Statement := TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 6) Var
def reset : Var := (false, none)
def program : Fin 6 → Statement
  | 0 => .pop 0 (fun _ h => (h.getD false, none)) (.goto fun _ => 1)
  | 1 => .pop 0 (fun v h => (v.1,h))
      (.branch (fun v => v.2.getD false)
        (.branch Prod.fst (.goto fun _ => 1) (.push 1 (fun _ => true) (.goto fun _ => 1)))
        (.branch Prod.fst (.goto fun _ => 2)
          (.push 1 (fun _ => false) (.push 1 (fun _ => true) (.goto fun _ => 2)))))
  | 2 => .pop 0 (fun v h => (v.1,h))
      (.branch (fun v => v.2.getD false)
        (.branch Prod.fst (.push 2 (fun _ => true) (.goto fun _ => 2))
          (.push 1 (fun _ => true) (.goto fun _ => 2)))
        (.branch Prod.fst (.goto fun _ => 3)
          (.push 1 (fun _ => false) (.push 1 (fun _ => true) (.goto fun _ => 3)))))
  | 3 => .pop 0 (fun v h => (v.1,h))
      (.branch (fun v => v.2.getD false)
        (.branch Prod.fst (.goto fun _ => 3) (.push 1 (fun _ => true) (.goto fun _ => 3)))
        (.branch Prod.fst (.goto fun _ => 4) (.push 1 (fun _ => false) (.goto fun _ => 4))))
  | 4 => .pop 0 (fun v h => (v.1,h))
      (.branch (fun v => v.2.isSome)
        (.branch Prod.fst (.goto fun _ => 4) (.push 1 (fun _ => true) (.goto fun _ => 4)))
        (.branch Prod.fst (.push 2 (fun _ => true) (.load (fun _ => reset) .halt))
          (.goto fun _ => 5)))
  | _ => .pop 1 (fun v h => (v.1,h))
      (.branch (fun v => v.2.isSome)
        (.push 2 (fun v => v.2.getD false) (.goto fun _ => 5))
        (.push 2 (fun _ => false) (.load (fun _ => reset) .halt)))
def machine : Machine where
  K := Fin 3
  input := 0
  output := 2
  Λ := Fin 6
  main := 0
  σ := Var
  initial := reset
  program := program
def cfg (l : Fin 6) (s b d : List Bool) (v : Var) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 6) Var := ⟨some l,v,![s,b,d]⟩
def halt (w : List Bool) : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 6) Var :=
  ⟨none,reset,![[],[],w]⟩
theorem read_flag (flag : Bool) (s : List Bool) :
    TM2.step program (cfg 0 (flag::s) [] [] reset) =
      some (cfg 1 s [] [] (flag,none)) := by
  simp [TM2.step,program,cfg,reset,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem target_cons (flag : Bool) (s b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 1 (true::s) b d (flag,v)) =
      some (cfg 1 s (if flag then b else true::b) (d) (flag,some true)) := by
  cases flag <;> simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
    (funext k; fin_cases k <;> simp [Function.update])
theorem target_sep (flag : Bool) (s b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 1 (false::s) b d (flag,v)) =
      some (cfg 2 s (if flag then b else true::false::b) d (flag,some false)) := by
  cases flag <;> simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
    (funext k; fin_cases k <;> simp [Function.update])
theorem operand_cons (flag : Bool) (s b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 2 (true::s) b d (flag,v)) =
      some (cfg 2 s (if flag then b else true::b) (if flag then true::d else d) (flag,some true)) := by
  cases flag <;> simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
    (funext k; fin_cases k <;> simp [Function.update])
theorem operand_sep (flag : Bool) (s b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 2 (false::s) b d (flag,v)) =
      some (cfg 3 s (if flag then b else true::false::b) d (flag,some false)) := by
  cases flag <;> simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
    (funext k; fin_cases k <;> simp [Function.update])
theorem duplicate_cons (flag : Bool) (s b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 3 (true::s) b d (flag,v)) =
      some (cfg 3 s (if flag then b else true::b) (d) (flag,some true)) := by
  cases flag <;> simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
    (funext k; fin_cases k <;> simp [Function.update])
theorem duplicate_sep (flag : Bool) (s b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 3 (false::s) b d (flag,v)) =
      some (cfg 4 s (if flag then b else false::b) d (flag,some false)) := by
  cases flag <;> simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
    (funext k; fin_cases k <;> simp [Function.update])
theorem modulus_cons (flag : Bool) (s b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 4 (true::s) b d (flag,v)) =
      some (cfg 4 s (if flag then b else true::b) d (flag,some true)) := by
  cases flag <;> simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
    (funext k; fin_cases k <;> simp [Function.update])
theorem modulus_nil_true (d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 4 [] [] d (true,v)) = some (halt (true::d)) := by
  simp [TM2.step,program,cfg,halt,reset,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem modulus_nil_false (b d : List Bool) (v : Option Bool) :
    TM2.step program (cfg 4 [] b d (false,v)) = some (cfg 5 [] b d (false,none)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
theorem reverse_cons (x : Bool) (b d : List Bool) (v : Var) :
    TM2.step program (cfg 5 [] (x::b) d v) = some (cfg 5 [] b (x::d) (v.1,some x)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem reverse_nil (d : List Bool) (v : Var) :
    TM2.step program (cfg 5 [] [] d v) = some (halt (false::d)) := by
  simp [TM2.step,program,cfg,halt,reset,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem run_target_false (n : ℕ) (x b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n+1]
      (some (cfg 1 (unary n++false::x) b d (false,v))) =
      some (cfg 2 x (true::false::(unary n++b)) (d) (false,some false)) := by
  induction n generalizing b d v with
  | zero => simp [unary,target_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,target_cons]
      rw [ih]
      simp [unary_append_cons]
theorem run_target_true (n : ℕ) (x b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n+1]
      (some (cfg 1 (unary n++false::x) b d (true,v))) =
      some (cfg 2 x (b) (d) (true,some false)) := by
  induction n generalizing b d v with
  | zero => simp [unary,target_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,target_cons]
      rw [ih]
      simp
theorem run_operand_false (n : ℕ) (x b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n+1]
      (some (cfg 2 (unary n++false::x) b d (false,v))) =
      some (cfg 3 x (true::false::(unary n++b)) (d) (false,some false)) := by
  induction n generalizing b d v with
  | zero => simp [unary,operand_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,operand_cons]
      rw [ih]
      simp [unary_append_cons]
theorem run_operand_true (n : ℕ) (x b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n+1]
      (some (cfg 2 (unary n++false::x) b d (true,v))) =
      some (cfg 3 x (b) (unary n++d) (true,some false)) := by
  induction n generalizing b d v with
  | zero => simp [unary,operand_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,operand_cons]
      rw [ih]
      simp [unary_append_cons]
theorem run_duplicate_false (n : ℕ) (x b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n+1]
      (some (cfg 3 (unary n++false::x) b d (false,v))) =
      some (cfg 4 x (false::(unary n++b)) (d) (false,some false)) := by
  induction n generalizing b d v with
  | zero => simp [unary,duplicate_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,duplicate_cons]
      rw [ih]
      simp [unary_append_cons]
theorem run_duplicate_true (n : ℕ) (x b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n+1]
      (some (cfg 3 (unary n++false::x) b d (true,v))) =
      some (cfg 4 x (b) (d) (true,some false)) := by
  induction n generalizing b d v with
  | zero => simp [unary,duplicate_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,duplicate_cons]
      rw [ih]
      simp
theorem run_modulus_false (q : ℕ) (b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[q+1]
      (some (cfg 4 (unary q) b d (false,v))) =
      some (cfg 5 [] (unary q++b) d (false,none)) := by
  induction q generalizing b v with
  | zero => simp [unary,modulus_nil_false]
  | succ q ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,modulus_cons]
      rw [ih]
      simp [unary_append_cons]
theorem run_modulus_true (q : ℕ) (d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[q+1]
      (some (cfg 4 (unary q) [] d (true,v))) = some (halt (true::d)) := by
  induction q generalizing v with
  | zero => simp [unary,modulus_nil_true]
  | succ q ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,modulus_cons]
      simpa using ih (some true)
theorem run_reverse (b d : List Bool) (v : Var) :
    (fun c => c.bind (TM2.step program))^[b.length+1]
      (some (cfg 5 [] b d v)) = some (halt (false::(b.reverse++d))) := by
  induction b generalizing d v with
  | nil => simp [reverse_nil]
  | cons x b ih =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,reverse_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]
def record (r a q : ℕ) : List Bool := ModularTrial.input a a r q
def falseBuffer (r a q : ℕ) : List Bool :=
  unary q++false::(unary a++true::false::(unary a++true::false::unary r))
theorem falseBuffer_eq (r a q : ℕ) : falseBuffer r a q=(record r (a+1) q).reverse := by
  simp [falseBuffer,record,ModularTrial.input,UnaryOutputEquality.prefixInput,
    FactorTest.tripleInput,pairInput,unary,List.replicate_succ,List.append_assoc]
theorem run_true (r a q : ℕ) :
    (fun c => c.bind (TM2.step program))^[r+2*a+q+5]
      (some (cfg 0 (true::record r a q) [] [] reset)) = some (halt (true::unary a)) := by
  rw [show r+2*a+q+5=(q+1)+(a+1)+(a+1)+(r+1)+1 by omega]
  rw [Function.iterate_add_apply]
  simp only [Function.iterate_one,Option.bind_some,read_flag]
  change (fun c => c.bind (TM2.step program))^[(q+1)+(a+1)+(a+1)+(r+1)]
    (some (cfg 1 (unary r++false::(unary a++false::(unary a++false::unary q))) [] []
      (true,none))) = _
  rw [Function.iterate_add_apply,run_target_true,Function.iterate_add_apply,run_operand_true,
    Function.iterate_add_apply,run_duplicate_true,run_modulus_true]
  simp
theorem run_false (r a q : ℕ) :
    (fun c => c.bind (TM2.step program))^[2*r+4*a+2*q+11]
      (some (cfg 0 (false::record r a q) [] [] reset)) =
      some (halt (false::record r (a+1) q)) := by
  have hlen : (record r (a+1) q).length=r+2*a+q+5 := by
    simp [record,ModularTrial.input,UnaryOutputEquality.prefixInput_length,
      FactorTest.tripleInput_length];omega
  rw [show 2*r+4*a+2*q+11=
    ((record r (a+1) q).length+1)+(q+1)+(a+1)+(a+1)+(r+1)+1 by omega]
  rw [Function.iterate_add_apply]
  simp only [Function.iterate_one,Option.bind_some,read_flag]
  change (fun c => c.bind (TM2.step program))^[
    ((record r (a+1) q).length+1)+(q+1)+(a+1)+(a+1)+(r+1)]
    (some (cfg 1 (unary r++false::(unary a++false::(unary a++false::unary q))) [] []
      (false,none))) = _
  rw [Function.iterate_add_apply,run_target_false,Function.iterate_add_apply,run_operand_false,
    Function.iterate_add_apply,run_duplicate_false,Function.iterate_add_apply,run_modulus_false]
  simp only [List.append_nil]
  change (fun c => c.bind (TM2.step program))^[(record r (a+1) q).length+1]
    (some (cfg 5 [] (falseBuffer r a q) [] (false,none))) = _
  have hr := run_reverse (falseBuffer r a q) [] (false,none)
  simpa only [falseBuffer_eq,List.length_reverse,List.reverse_reverse,List.append_nil] using hr
theorem record_length (r a q : ℕ) : (record r a q).length=r+2*a+q+3 := by
  simp [record,ModularTrial.input,UnaryOutputEquality.prefixInput_length,
    FactorTest.tripleInput_length];omega
theorem init_eq (flag : Bool) (r a q : ℕ) : machine.init (flag::record r a q)=
    cfg 0 (flag::record r a q) [] [] reset := by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem halt_eq (y : List Bool) : machine.halt y=halt y := by
  simp [Machine.halt,machine,halt,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
def output (flag : Bool) (r a q : ℕ) : List Bool :=
  if flag then true::unary a else false::record r (a+1) q
def steps (flag : Bool) (r a q : ℕ) : ℕ :=
  if flag then r+2*a+q+5 else 2*r+4*a+2*q+11
def exec (flag : Bool) (r a q : ℕ) :
    EvalsToInTime (TM2.step machine.program) (machine.init (flag::record r a q))
      (some (machine.halt (output flag r a q))) (2*(flag::record r a q).length+3) := by
  refine ⟨⟨steps flag r a q,?_⟩,?_⟩
  · rw [init_eq,halt_eq]
    cases flag
    · exact run_false r a q
    · exact run_true r a q
  · rw [List.length_cons,record_length]
    cases flag <;> simp [steps] <;> omega
end QEC.Coding.BitTuring.UnaryArithmetic.SquareRootAdvance
namespace QEC.Coding.BitTuring.UnaryArithmetic.SquareRootTrial
open Turing StateTransition
def machine : Machine :=
  Composition.machine (RetainedInput.machine ModularTrial.machine) SquareRootAdvance.machine
noncomputable def time : Polynomial ℕ :=
  ModularTrial.time+Polynomial.C 7*Polynomial.X+Polynomial.C 17
def result (r a q : ℕ) : List Bool :=
  SquareRootAdvance.output (decide ((a*a)%q=r)) r a q
noncomputable def polyExec (r a q : ℕ) (hq : 0<q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (SquareRootAdvance.record r a q))
      (some (machine.halt (result r a q)))
      (time.eval (SquareRootAdvance.record r a q).length) := by
  let L := (SquareRootAdvance.record r a q).length
  let flag := decide ((a*a)%q=r)
  have hA : EvalsToInTime (TM2.step (RetainedInput.machine ModularTrial.machine).program)
      ((RetainedInput.machine ModularTrial.machine).init (SquareRootAdvance.record r a q))
      (some ((RetainedInput.machine ModularTrial.machine).halt
        (flag::SquareRootAdvance.record r a q))) (ModularTrial.time.eval L+3*L+8) := by
    simpa [SquareRootAdvance.record,L,Nat.add_assoc] using
      RetainedInput.executes ModularTrial.machine (ModularTrial.input a a r q) [flag] _
        (ModularTrial.polyExec a a r q hq)
  have hB : EvalsToInTime (TM2.step SquareRootAdvance.machine.program)
      (SquareRootAdvance.machine.init (flag::SquareRootAdvance.record r a q))
      (some (SquareRootAdvance.machine.halt (result r a q))) (2*L+5) := by
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc,result] using
      SquareRootAdvance.exec flag r a q
  have h := Composition.executes (RetainedInput.machine ModularTrial.machine) SquareRootAdvance.machine
    _ _ _ _ _ hA hB
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  change (2*L+5)+(2*(flag::SquareRootAdvance.record r a q).length+2)+
    (ModularTrial.time.eval L+3*L+8)≤time.eval L
  simp only [List.length_cons,time,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  dsimp only [L]
  omega
end QEC.Coding.BitTuring.UnaryArithmetic.SquareRootTrial


