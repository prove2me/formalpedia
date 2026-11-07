-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnarySquareRootInput
-- name    : QEC_Coding_BitTuring_UnarySquareRootInput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:57:56.670349+00:00
-- url     : https://prove2.me/theorems/d4484081-8950-40a9-8cd2-f176aed79b0d
-- title:
--   Unary Square Root Input
-- statement:
--   Definitions and structural lemmas for Unary Square Root Input, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnarySquareRootInput.lean

import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRootTrial
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_halt_eq
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularTrial_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.SquareRootInput
open Turing StateTransition
abbrev Statement := TM2.Stmt (fun _ : Fin 2 => Bool) Unit (Option Bool)
def pushPrefix : ℕ → Statement
  | 0 => .load (fun _ => none) .halt
  | p+1 => .push 1 (fun _ => true) (pushPrefix p)
def program (p : ℕ) : Unit → Statement := fun _ =>
  .pop 0 (fun _ h => h) (.branch (fun v => v.isSome)
    (.push 1 (fun _ => true) (.goto fun _ => ()))
    (.push 1 (fun _ => false) (.push 1 (fun _ => false)
      (.push 1 (fun _ => false) (pushPrefix p)))))
def machine (p : ℕ) : Machine where
  K := Fin 2
  input := 0
  output := 1
  Λ := Unit
  main := ()
  σ := Option Bool
  initial := none
  program := program p
def cfg (s d : List Bool) (v : Option Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) Unit (Option Bool) := ⟨some (),v,![s,d]⟩
def halt (d : List Bool) : TM2.Cfg (fun _ : Fin 2 => Bool) Unit (Option Bool) :=
  ⟨none,none,![[],d]⟩
theorem pushPrefix_aux (p : ℕ) (v : Option Bool) (S : Fin 2 → List Bool) :
    TM2.stepAux (pushPrefix p) v S=⟨none,none,Function.update S 1 (unary p++S 1)⟩ := by
  induction p generalizing S with
  | zero => simp [pushPrefix,TM2.stepAux,unary]
  | succ p ih =>
      simp only [pushPrefix,TM2.stepAux]
      rw [ih]
      simp [unary_append_cons,unary_succ]
theorem copy_cons (p : ℕ) (s d : List Bool) (v : Option Bool) :
    TM2.step (program p) (cfg (true::s) d v)=some (cfg s (true::d) (some true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem copy_nil (p : ℕ) (d : List Bool) (v : Option Bool) :
    TM2.step (program p) (cfg [] d v)=some (halt (unary p++false::false::false::d)) := by
  simp [TM2.step,program,cfg,halt,TM2.stepAux,pushPrefix_aux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem run (p q : ℕ) (d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step (program p)))^[q+1] (some (cfg (unary q) d v))=
      some (halt (unary p++false::false::false::(unary q++d))) := by
  induction q generalizing d v with
  | zero => simp [unary,copy_nil]
  | succ q ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,copy_cons]
      rw [ih]
      simp only [unary_append_cons,unary_succ,List.cons_append]
theorem init_eq (p q : ℕ) : (machine p).init (unary q)=cfg (unary q) [] none := by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem halt_eq (p : ℕ) (d : List Bool) : (machine p).halt d=halt d := by
  simp [Machine.halt,machine,halt,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
def exec (p q : ℕ) :
    EvalsToInTime (TM2.step (machine p).program) ((machine p).init (unary q))
      (some ((machine p).halt (SquareRootAdvance.record p 0 q))) (q+1) := by
  refine ⟨⟨q+1,?_⟩,le_refl _⟩
  rw [init_eq,halt_eq]
  change (fun c => c.bind (TM2.step (program p)))^[q+1]
    (some (cfg (unary q) [] none)) = some (halt (unary p++false::false::false::unary q))
  simpa only [List.append_nil] using run p q [] none
end QEC.Coding.BitTuring.UnaryArithmetic.SquareRootInput
namespace QEC.Coding.BitTuring.UnaryArithmetic.MinusSquareRootInput
open Turing StateTransition
abbrev Statement := TM2.Stmt (fun _ : Fin 2 => Bool) Bool (Option Bool)
def program : Bool → Statement
  | true => .push 1 (fun _ => false) (.push 1 (fun _ => false) (.push 1 (fun _ => false)
      (.pop 0 (fun _ h => h) (.goto fun _ => false))))
  | false => .pop 0 (fun _ h => h) (.branch (fun v => v.isSome)
      (.push 1 (fun _ => true) (.goto fun _ => false)) (.load (fun _ => none) .halt))
def machine : Machine where
  K := Fin 2
  input := 0
  output := 1
  Λ := Bool
  main := true
  σ := Option Bool
  initial := none
  program := program
def cfg (l : Bool) (s d : List Bool) (v : Option Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) Bool (Option Bool) := ⟨some l,v,![s,d]⟩
def halt (d : List Bool) : TM2.Cfg (fun _ : Fin 2 => Bool) Bool (Option Bool) :=
  ⟨none,none,![[],d]⟩
theorem header (s : List Bool) :
    TM2.step program (cfg true (true::s) [] none)=
      some (cfg false s [false,false,false] (some true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem copy_cons (s d : List Bool) (v : Option Bool) :
    TM2.step program (cfg false (true::s) d v)=some (cfg false s (true::d) (some true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem copy_nil (d : List Bool) (v : Option Bool) :
    TM2.step program (cfg false [] d v)=some (halt d) := by
  simp [TM2.step,program,cfg,halt,TM2.stepAux,TM2.Cfg.mk.injEq]
theorem copy_run (n : ℕ) (d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n+1] (some (cfg false (unary n) d v))=
      some (halt (unary n++d)) := by
  induction n generalizing d v with
  | zero => simp [unary,copy_nil]
  | succ n ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,copy_cons]
      rw [ih]
      simp only [unary_append_cons,unary_succ,List.cons_append]
theorem run (q : ℕ) (hq : 0<q) :
    (fun c => c.bind (TM2.step program))^[q+1] (some (cfg true (unary q) [] none))=
      some (halt (unary (q-1)++[false,false,false])) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  simp only [unary_succ]
  rw [Function.iterate_succ_apply]
  simp only [Option.bind_some,header]
  exact copy_run n [false,false,false] (some true)
theorem init_eq (q : ℕ) : machine.init (unary q)=cfg true (unary q) [] none := by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem halt_eq (y : List Bool) : machine.halt y=halt y := by
  simp [Machine.halt,machine,halt,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
def exec (q : ℕ) (hq : 0<q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (unary q))
      (some (machine.halt (unary (q-1)++[false,false,false]))) (q+1) := by
  refine ⟨⟨q+1,?_⟩,le_refl _⟩
  rw [init_eq,halt_eq]
  exact run q hq
noncomputable def retainedExec (q : ℕ) (hq : 0<q) :
    EvalsToInTime (TM2.step (RetainedInput.machine machine).program)
      ((RetainedInput.machine machine).init (unary q))
      (some ((RetainedInput.machine machine).halt (SquareRootAdvance.record (q-1) 0 q)))
      (6*q+11) := by
  have h := RetainedInput.executes machine (unary q) (unary (q-1)++[false,false,false]) _ (exec q hq)
  have hy : (unary (q-1)++[false,false,false])++unary q=SquareRootAdvance.record (q-1) 0 q := by
    simp [SquareRootAdvance.record,ModularTrial.input,UnaryOutputEquality.prefixInput,
      FactorTest.tripleInput,pairInput,unary,List.append_assoc]
  rw [hy] at h
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  simp only [List.length_append,List.length_cons,List.length_nil,unary_length]
  omega
end QEC.Coding.BitTuring.UnaryArithmetic.MinusSquareRootInput


