-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTrial
-- name    : QEC_Coding_BitTuring_UnaryFactorTrial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:07:04.852242+00:00
-- url     : https://prove2.me/theorems/a6d71605-31c5-4495-ae7a-7f39caa37933
-- title:
--   Unary Factor Trial
-- statement:
--   Definitions and structural lemmas for Unary Factor Trial, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFactorTrial.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_halt_eq

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial
open Turing StateTransition
abbrev Var := Option Bool × Bool × Bool
abbrev Statement := TM2.Stmt (fun _ : Fin 7 => Bool) (Fin 12) Var
def reset : Var := (none,false,false)
def scanB : Statement := .pop 2 (fun v h => (h,v.2))
  (.branch (fun v => v.1.isSome)
    (.push 5 (fun _ => true) (.load (fun v => (none,v.2)) (.goto fun _ => 4)))
    (.load (fun v => (none,v.2.1,true)) (.goto fun _ => 4)))
def scanA : Statement := .pop 1 (fun v h => (h,v.2))
  (.branch (fun v => v.1.isSome)
    (.push 4 (fun _ => true) scanB)
    (.load (fun v => (v.1,true,v.2.2)) scanB))
def program : Fin 12 → Statement
  | 0 => .pop 0 (fun v h => (h,v.2))
      (.branch (fun v => v.1.getD false) (.goto fun _ => 1) (.goto fun _ => 2))
  | 1 => .pop 0 (fun v h => (h,v.2))
      (.branch (fun v => v.1.isSome) (.goto fun _ => 1)
        (.push 6 (fun _ => false) (.push 6 (fun _ => true) (.load (fun _ => reset) .halt))))
  | 2 => .pop 0 (fun v h => (h,v.2))
      (.branch (fun v => v.1.getD false)
        (.push 1 (fun _ => true) (.goto fun _ => 2)) (.goto fun _ => 3))
  | 3 => .pop 0 (fun v h => (h,v.2))
      (.branch (fun v => v.1.getD false)
        (.push 2 (fun _ => true) (.goto fun _ => 3))
        (.load (fun v => (none,v.2)) (.goto fun _ => 4)))
  | 4 => .pop 0 (fun v h => (h,v.2))
      (.branch (fun v => v.1.isSome)
        (.push 3 (fun _ => true) scanA)
        (.branch (fun v => v.2.2)
          (.push 5 (fun _ => true) (.goto fun _ => 5))
          (.branch (fun v => v.2.1)
            (.push 4 (fun _ => true) (.goto fun _ => 6)) (.goto fun _ => 7))))
  | 5 => .pop 3 (fun v h => (h,v.2))
      (.branch (fun v => v.1.isSome)
        (.push 6 (fun _ => true) (.goto fun _ => 5))
        (.push 6 (fun _ => false) (.goto fun _ => 10)))
  | 6 => .pop 5 (fun v h => (h,v.2))
      (.branch (fun v => v.1.isSome) (.goto fun _ => 6)
        (.push 5 (fun _ => true) (.push 5 (fun _ => true) (.goto fun _ => 5))))
  | 7 => .pop 3 (fun v h => (h,v.2))
      (.branch (fun v => v.1.isSome) (.goto fun _ => 7) (.goto fun _ => 8))
  | 8 => .pop 5 (fun v h => (h,v.2))
      (.branch (fun v => v.1.isSome) (.goto fun _ => 8) (.goto fun _ => 9))
  | 9 => .pop 4 (fun v h => (h,v.2))
      (.branch (fun v => v.1.isSome) (.goto fun _ => 9)
        (.push 6 (fun _ => true) (.push 6 (fun _ => true) (.load (fun _ => reset) .halt))))
  | 10 => .pop 5 (fun v h => (h,v.2))
      (.branch (fun v => v.1.isSome)
        (.push 6 (fun _ => true) (.goto fun _ => 10))
        (.push 6 (fun _ => false) (.goto fun _ => 11)))
  | _ => .pop 4 (fun v h => (h,v.2))
      (.branch (fun v => v.1.isSome)
        (.push 6 (fun _ => true) (.goto fun _ => 11))
        (.push 6 (fun _ => false) (.load (fun _ => reset) .halt)))
def machine : Machine where
  K := Fin 7
  input := 0
  output := 6
  Λ := Fin 12
  main := 0
  σ := Var
  initial := reset
  program := program
def cfg (phase : Fin 12) (s a b q ar br d : List Bool) (v : Var) :
    TM2.Cfg (fun _ : Fin 7 => Bool) (Fin 12) Var :=
  ⟨some phase,v,![s,a,b,q,ar,br,d]⟩
def halt (d : List Bool) : TM2.Cfg (fun _ : Fin 7 => Bool) (Fin 12) Var :=
  ⟨none,reset,![[],[],[],[],[],[],d]⟩
theorem read_flag (eq : Bool) (s : List Bool) :
    TM2.step program (cfg 0 (eq :: s) [] [] [] [] [] [] reset) =
      some (cfg (if eq then 1 else 2) s [] [] [] [] [] [] (some eq,false,false)) := by
  cases eq <;> simp [TM2.step,program,cfg,reset,TM2.stepAux,TM2.Cfg.mk.injEq] <;>
    (funext k; fin_cases k <;> simp [Function.update])
theorem found_cons (x : Bool) (s d : List Bool) (v : Var) :
    TM2.step program (cfg 1 (x :: s) [] [] [] [] [] d v) =
      some (cfg 1 s [] [] [] [] [] d (some x,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem found_nil (d : List Bool) (v : Var) :
    TM2.step program (cfg 1 [] [] [] [] [] [] d v) = some (halt (true :: false :: d)) := by
  simp [TM2.step,program,cfg,halt,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem parseA_cons (s a b q ar br d : List Bool) (v : Var) :
    TM2.step program (cfg 2 (true :: s) a b q ar br d v) =
      some (cfg 2 s (true :: a) b q ar br d (some true,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem parseA_sep (s a b q ar br d : List Bool) (v : Var) :
    TM2.step program (cfg 2 (false :: s) a b q ar br d v) =
      some (cfg 3 s a b q ar br d (some false,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem parseB_cons (s a b q ar br d : List Bool) (v : Var) :
    TM2.step program (cfg 3 (true :: s) a b q ar br d v) =
      some (cfg 3 s a (true :: b) q ar br d (some true,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem parseB_sep (s a b q ar br d : List Bool) (v : Var) :
    TM2.step program (cfg 3 (false :: s) a b q ar br d v) =
      some (cfg 4 s a b q ar br d (none,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem scan_ss (s a b q ar br d : List Bool) (la lb : Bool) :
    TM2.step program (cfg 4 (true :: s) (true :: a) (true :: b) q ar br d (none,la,lb)) =
      some (cfg 4 s a b (true :: q) (true :: ar) (true :: br) d (none,la,lb)) := by
  simp [TM2.step,program,cfg,scanA,scanB,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem scan_zs (s b q ar br d : List Bool) (la lb : Bool) :
    TM2.step program (cfg 4 (true :: s) [] (true :: b) q ar br d (none,la,lb)) =
      some (cfg 4 s [] b (true :: q) ar (true :: br) d (none,true,lb)) := by
  simp [TM2.step,program,cfg,scanA,scanB,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem scan_sz (s a q ar br d : List Bool) (la lb : Bool) :
    TM2.step program (cfg 4 (true :: s) (true :: a) [] q ar br d (none,la,lb)) =
      some (cfg 4 s a [] (true :: q) (true :: ar) br d (none,la,true)) := by
  simp [TM2.step,program,cfg,scanA,scanB,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem scan_zz (s q ar br d : List Bool) (la lb : Bool) :
    TM2.step program (cfg 4 (true :: s) [] [] q ar br d (none,la,lb)) =
      some (cfg 4 s [] [] (true :: q) ar br d (none,true,true)) := by
  simp [TM2.step,program,cfg,scanA,scanB,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem scan_nil_nextB (q ar br d : List Bool) (la : Bool) :
    TM2.step program (cfg 4 [] [] [] q ar br d (none,la,true)) =
      some (cfg 5 [] [] [] q ar (true :: br) d (none,la,true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem scan_nil_nextA (q ar br d : List Bool) :
    TM2.step program (cfg 4 [] [] [] q ar br d (none,true,false)) =
      some (cfg 6 [] [] [] q (true :: ar) br d (none,true,false)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem scan_nil_end (q ar br d : List Bool) :
    TM2.step program (cfg 4 [] [] [] q ar br d (none,false,false)) =
      some (cfg 7 [] [] [] q ar br d reset) := by
  simp [TM2.step,program,cfg,reset,TM2.stepAux,TM2.Cfg.mk.injEq]
theorem found_run (w d : List Bool) (v : Var) :
    (fun c => c.bind (TM2.step program))^[w.length + 1]
      (some (cfg 1 w [] [] [] [] [] d v)) = some (halt (true :: false :: d)) := by
  induction w generalizing v with
  | nil => simp [found_nil]
  | cons x xs ih =>
      rw [List.length_cons,Nat.add_right_comm,Function.iterate_succ_apply]
      simp only [Option.bind_some,found_cons]
      exact ih (some x,v.2)
theorem parseA_run (n : ℕ) (s a b q ar br d : List Bool) (v : Var) :
    (fun c => c.bind (TM2.step program))^[n + 1]
      (some (cfg 2 (unary n ++ false :: s) a b q ar br d v)) =
      some (cfg 3 s (unary n ++ a) b q ar br d (some false,v.2)) := by
  induction n generalizing a v with
  | zero => simp [parseA_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,parseA_cons]
      simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (true :: a) (some true,v.2)
theorem parseB_run (n : ℕ) (s a b q ar br d : List Bool) (v : Var) :
    (fun c => c.bind (TM2.step program))^[n + 1]
      (some (cfg 3 (unary n ++ false :: s) a b q ar br d v)) =
      some (cfg 4 s a (unary n ++ b) q ar br d (none,v.2)) := by
  induction n generalizing b v with
  | zero => simp [parseB_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,parseB_cons]
      simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (true :: b) (some true,v.2)
theorem scan_run (m a b q ar br : ℕ) (d : List Bool) (la lb : Bool) :
    (fun c => c.bind (TM2.step program))^[m]
      (some (cfg 4 (unary m) (unary a) (unary b) (unary q) (unary ar) (unary br) d
        (none,la,lb))) =
      some (cfg 4 [] (unary (a - m)) (unary (b - m)) (unary (q + m))
        (unary (ar + min a m)) (unary (br + min b m)) d
          (none,la || decide (a < m),lb || decide (b < m))) := by
  induction m generalizing a b q ar br la lb with
  | zero => simp [unary]
  | succ m ih =>
      cases a with
      | zero =>
          cases b with
          | zero =>
              rw [Function.iterate_succ_apply]
              simp only [unary_succ,show unary 0 = [] from rfl,Option.bind_some,scan_zz]
              simpa [unary_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
                ih 0 0 (q + 1) ar br true true
          | succ b =>
              rw [Function.iterate_succ_apply]
              simp only [unary_succ,show unary 0 = [] from rfl,Option.bind_some,scan_zs]
              simpa [unary_succ,Nat.succ_min_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
                ih 0 b (q + 1) ar (br + 1) true lb
      | succ a =>
          cases b with
          | zero =>
              rw [Function.iterate_succ_apply]
              simp only [unary_succ,show unary 0 = [] from rfl,Option.bind_some,scan_sz]
              simpa [unary_succ,Nat.succ_min_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
                ih a 0 (q + 1) (ar + 1) br la true
          | succ b =>
              rw [Function.iterate_succ_apply]
              simp only [unary_succ,Option.bind_some,scan_ss]
              simpa [unary_succ,Nat.succ_min_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
                ih a b (q + 1) (ar + 1) (br + 1) la lb
theorem emitQ_cons (q ar br d : List Bool) (v : Var) :
    TM2.step program (cfg 5 [] [] [] (true :: q) ar br d v) = some (cfg 5 [] [] [] q ar br (true :: d) (some true,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem emitQ_nil (ar br d : List Bool) (v : Var) :
    TM2.step program (cfg 5 [] [] [] [] ar br d v) = some (cfg 10 [] [] [] [] ar br (false :: d) (none,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem emitB_cons (ar br d : List Bool) (v : Var) :
    TM2.step program (cfg 10 [] [] [] [] ar (true :: br) d v) = some (cfg 10 [] [] [] [] ar br (true :: d) (some true,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem emitB_nil (ar d : List Bool) (v : Var) :
    TM2.step program (cfg 10 [] [] [] [] ar [] d v) = some (cfg 11 [] [] [] [] ar [] (false :: d) (none,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem emitA_cons (ar d : List Bool) (v : Var) :
    TM2.step program (cfg 11 [] [] [] [] (true :: ar) [] d v) = some (cfg 11 [] [] [] [] ar [] (true :: d) (some true,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem emitA_nil (d : List Bool) (v : Var) :
    TM2.step program (cfg 11 [] [] [] [] [] [] d v) = some (halt (false :: d)) := by
  simp [TM2.step,program,cfg,halt,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem resetB_cons (q ar br d : List Bool) (v : Var) :
    TM2.step program (cfg 6 [] [] [] q ar (true :: br) d v) = some (cfg 6 [] [] [] q ar br d (some true,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem resetB_nil (q ar d : List Bool) (v : Var) :
    TM2.step program (cfg 6 [] [] [] q ar [] d v) = some (cfg 5 [] [] [] q ar [true,true] d (none,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem drainQ_cons (q ar br d : List Bool) (v : Var) :
    TM2.step program (cfg 7 [] [] [] (true :: q) ar br d v) = some (cfg 7 [] [] [] q ar br d (some true,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem drainQ_nil (ar br d : List Bool) (v : Var) :
    TM2.step program (cfg 7 [] [] [] [] ar br d v) = some (cfg 8 [] [] [] [] ar br d (none,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
theorem drainB_cons (ar br d : List Bool) (v : Var) :
    TM2.step program (cfg 8 [] [] [] [] ar (true :: br) d v) = some (cfg 8 [] [] [] [] ar br d (some true,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem drainB_nil (ar d : List Bool) (v : Var) :
    TM2.step program (cfg 8 [] [] [] [] ar [] d v) = some (cfg 9 [] [] [] [] ar [] d (none,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
theorem drainA_cons (ar d : List Bool) (v : Var) :
    TM2.step program (cfg 9 [] [] [] [] (true :: ar) [] d v) = some (cfg 9 [] [] [] [] ar [] d (some true,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem drainA_nil (d : List Bool) (v : Var) :
    TM2.step program (cfg 9 [] [] [] [] [] [] d v) = some (halt (true :: true :: d)) := by
  simp [TM2.step,program,cfg,halt,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem drainA_run (n : ℕ) (d : List Bool) (v : Var) :
    (fun c => c.bind (TM2.step program))^[n + 1] (some (cfg 9 [] [] [] [] (unary n) [] d v)) = some (halt (true :: true :: d)) := by
  induction n generalizing v with
  | zero => simp [drainA_nil]
  | succ n ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,drainA_cons]
      exact ih (some true,v.2)
theorem drainB_run (n : ℕ) (ar d : List Bool) (v : Var) :
    (fun c => c.bind (TM2.step program))^[n + 1] (some (cfg 8 [] [] [] [] ar (unary n) d v)) = some (cfg 9 [] [] [] [] ar [] d (none,v.2)) := by
  induction n generalizing v with
  | zero => simp [drainB_nil]
  | succ n ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,drainB_cons]
      exact ih (some true,v.2)
theorem drainQ_run (n : ℕ) (ar br d : List Bool) (v : Var) :
    (fun c => c.bind (TM2.step program))^[n + 1] (some (cfg 7 [] [] [] (unary n) ar br d v)) = some (cfg 8 [] [] [] [] ar br d (none,v.2)) := by
  induction n generalizing v with
  | zero => simp [drainQ_nil]
  | succ n ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,drainQ_cons]
      exact ih (some true,v.2)
theorem resetB_run (n : ℕ) (q ar d : List Bool) (v : Var) :
    (fun c => c.bind (TM2.step program))^[n + 1] (some (cfg 6 [] [] [] q ar (unary n) d v)) = some (cfg 5 [] [] [] q ar (unary 2) d (none,v.2)) := by
  induction n generalizing v with
  | zero => simp [resetB_nil]
  | succ n ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,resetB_cons]
      exact ih (some true,v.2)
theorem emitA_run (n : ℕ) (d : List Bool) (v : Var) :
    (fun c => c.bind (TM2.step program))^[n + 1] (some (cfg 11 [] [] [] [] (unary n) [] d v)) = some (halt (false :: (unary n ++ d))) := by
  induction n generalizing d v with
  | zero => simp [emitA_nil]
  | succ n ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,emitA_cons]
      simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (true :: d) (some true,v.2)
theorem emitB_run (n : ℕ) (ar d : List Bool) (v : Var) :
    (fun c => c.bind (TM2.step program))^[n + 1] (some (cfg 10 [] [] [] [] ar (unary n) d v)) = some (cfg 11 [] [] [] [] ar [] (false :: (unary n ++ d)) (none,v.2)) := by
  induction n generalizing d v with
  | zero => simp [emitB_nil]
  | succ n ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,emitB_cons]
      simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (true :: d) (some true,v.2)
theorem emitQ_run (n : ℕ) (ar br d : List Bool) (v : Var) :
    (fun c => c.bind (TM2.step program))^[n + 1] (some (cfg 5 [] [] [] (unary n) ar br d v)) = some (cfg 10 [] [] [] [] ar br (false :: (unary n ++ d)) (none,v.2)) := by
  induction n generalizing d v with
  | zero => simp [emitQ_nil]
  | succ n ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,emitQ_cons]
      simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (true :: d) (some true,v.2)
theorem emit_run (a b q : ℕ) (d : List Bool) (v : Var) :
    (fun c => c.bind (TM2.step program))^[a + b + q + 3]
      (some (cfg 5 [] [] [] (unary q) (unary a) (unary b) d v)) =
      some (halt (false :: (FactorTest.tripleInput a b q ++ d))) := by
  rw [show a + b + q + 3 = ((a + 1) + (b + 1)) + (q + 1) by omega,
    Function.iterate_add_apply,emitQ_run,Function.iterate_add_apply,emitB_run,emitA_run]
  simp [FactorTest.tripleInput,pairInput,List.append_assoc]
theorem drain_run (a b q : ℕ) (d : List Bool) (v : Var) :
    (fun c => c.bind (TM2.step program))^[a + b + q + 3]
      (some (cfg 7 [] [] [] (unary q) (unary a) (unary b) d v)) =
      some (halt (true :: true :: d)) := by
  rw [show a + b + q + 3 = ((a + 1) + (b + 1)) + (q + 1) by omega,
    Function.iterate_add_apply,drainQ_run,Function.iterate_add_apply,drainB_run,drainA_run]
theorem false_prefix_run (a b q : ℕ) :
    (fun c => c.bind (TM2.step program))^[a + b + 3]
      (some (cfg 0 (false :: FactorTest.tripleInput a b q) [] [] [] [] [] [] reset)) =
      some (cfg 4 (unary q) (unary a) (unary b) [] [] [] [] reset) := by
  rw [show a + b + 3 = ((b + 1) + (a + 1)) + 1 by omega,
    Function.iterate_add_apply]
  simp only [Function.iterate_one,Option.bind_some,read_flag,Bool.false_eq_true,ite_false,
    FactorTest.tripleInput,pairInput]
  rw [Function.iterate_add_apply,parseA_run]
  simp only [List.append_nil]
  rw [parseB_run]
  simp only [List.append_nil,reset]
theorem before_dispatch_run (a b q : ℕ) (ha : a ≤ q) (hb : b ≤ q) :
    (fun c => c.bind (TM2.step program))^[a + b + q + 3]
      (some (cfg 0 (false :: FactorTest.tripleInput a b q) [] [] [] [] [] [] reset)) =
      some (cfg 4 [] [] [] (unary q) (unary a) (unary b) []
        (none,decide (a < q),decide (b < q))) := by
  rw [show a + b + q + 3 = q + (a + b + 3) by omega,
    Function.iterate_add_apply,false_prefix_run]
  have h := scan_run q a b 0 0 0 [] false false
  simpa [reset,Nat.sub_eq_zero_of_le ha,Nat.sub_eq_zero_of_le hb,
    Nat.min_eq_left ha,Nat.min_eq_left hb] using h
theorem update_found_run (a b q : ℕ) :
    (fun c => c.bind (TM2.step program))^[(FactorTest.tripleInput a b q).length + 2]
      (some (cfg 0 (true :: FactorTest.tripleInput a b q) [] [] [] [] [] [] reset)) =
      some (halt [true,false]) := by
  rw [show (FactorTest.tripleInput a b q).length + 2 =
      ((FactorTest.tripleInput a b q).length + 1) + 1 by omega,
    Function.iterate_add_apply]
  simp only [Function.iterate_one,Option.bind_some,read_flag,ite_true]
  exact found_run (FactorTest.tripleInput a b q) [] (some true,false,false)
theorem update_nextB_run (a b q : ℕ) (ha : a ≤ q) (hb : b < q) :
    (fun c => c.bind (TM2.step program))^[2 * a + 2 * b + 2 * q + 8]
      (some (cfg 0 (false :: FactorTest.tripleInput a b q) [] [] [] [] [] [] reset)) =
      some (halt (false :: FactorTest.tripleInput a (b + 1) q)) := by
  rw [show 2 * a + 2 * b + 2 * q + 8 =
      ((a + (b + 1) + q + 3) + 1) + (a + b + q + 3) by omega,
    Function.iterate_add_apply,before_dispatch_run a b q ha (le_of_lt hb),
    Function.iterate_add_apply]
  have hh : decide (b < q) = true := by simp [hb]
  simp only [Function.iterate_one,Option.bind_some,hh,scan_nil_nextB]
  simpa only [List.append_nil,unary_succ] using emit_run a (b + 1) q [] (none,decide (a < q),true)
theorem update_nextA_run (a b q : ℕ) (ha : a < q) (hb : b = q) :
    (fun c => c.bind (TM2.step program))^[2 * a + 2 * b + 2 * q + 11]
      (some (cfg 0 (false :: FactorTest.tripleInput a b q) [] [] [] [] [] [] reset)) =
      some (halt (false :: FactorTest.tripleInput (a + 1) 2 q)) := by
  have hbq : b ≤ q := le_of_eq hb
  rw [show 2 * a + 2 * b + 2 * q + 11 =
      (((a + 1 + 2 + q + 3) + (b + 1)) + 1) + (a + b + q + 3) by omega,
    Function.iterate_add_apply,before_dispatch_run a b q (le_of_lt ha) hbq,
    Function.iterate_add_apply]
  have hA : decide (a < q) = true := by simp [ha]
  have hB : decide (b < q) = false := by simp [hb]
  simp only [Function.iterate_one,Option.bind_some,hA,hB,scan_nil_nextA]
  rw [Function.iterate_add_apply,resetB_run]
  simpa only [List.append_nil,unary_succ] using emit_run (a + 1) 2 q [] (none,true,false)
theorem update_end_run (a b q : ℕ) (ha : a = q) (hb : b = q) :
    (fun c => c.bind (TM2.step program))^[2 * a + 2 * b + 2 * q + 7]
      (some (cfg 0 (false :: FactorTest.tripleInput a b q) [] [] [] [] [] [] reset)) =
      some (halt [true,true]) := by
  rw [show 2 * a + 2 * b + 2 * q + 7 =
      ((a + b + q + 3) + 1) + (a + b + q + 3) by omega,
    Function.iterate_add_apply,before_dispatch_run a b q (le_of_eq ha) (le_of_eq hb),
    Function.iterate_add_apply]
  have hA : decide (a < q) = false := by simp [ha]
  have hB : decide (b < q) = false := by simp [hb]
  simp only [Function.iterate_one,Option.bind_some,hA,hB,scan_nil_end]
  exact drain_run a b q [] reset
def updateBits (eq : Bool) (a b q : ℕ) : List Bool :=
  if eq then [true,false] else if b < q then false :: FactorTest.tripleInput a (b + 1) q
    else if a < q then false :: FactorTest.tripleInput (a + 1) 2 q else [true,true]
def steps (eq : Bool) (a b q : ℕ) : ℕ :=
  if eq then (FactorTest.tripleInput a b q).length + 2 else if b < q then 2*a+2*b+2*q+8
    else if a < q then 2*a+2*b+2*q+11 else 2*a+2*b+2*q+7
theorem run_update (eq : Bool) (a b q : ℕ) (ha : a ≤ q) (hb : b ≤ q) :
    (fun c => c.bind (TM2.step program))^[steps eq a b q]
      (some (cfg 0 (eq :: FactorTest.tripleInput a b q) [] [] [] [] [] [] reset)) =
      some (halt (updateBits eq a b q)) := by
  cases eq with
  | true => simpa [steps,updateBits] using update_found_run a b q
  | false =>
      by_cases hB : b < q
      · simpa [steps,updateBits,hB] using update_nextB_run a b q ha hB
      · have hbe : b = q := by omega
        by_cases hA : a < q
        · simpa [steps,updateBits,hB,hA] using update_nextA_run a b q hA hbe
        · have hae : a = q := by omega
          simpa [steps,updateBits,hB,hA] using update_end_run a b q hae hbe
theorem init_eq (eq : Bool) (a b q : ℕ) :
    machine.init (eq :: FactorTest.tripleInput a b q) =
      cfg 0 (eq :: FactorTest.tripleInput a b q) [] [] [] [] [] [] reset := by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem halt_eq (d : List Bool) : machine.halt d = halt d := by
  simp [Machine.halt,machine,halt,TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
def updateExec (eq : Bool) (a b q : ℕ) (ha : a ≤ q) (hb : b ≤ q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (eq :: FactorTest.tripleInput a b q))
      (some (machine.halt (updateBits eq a b q))) (steps eq a b q) := by
  refine ⟨⟨steps eq a b q, ?_⟩, le_refl _⟩
  exact (init_eq eq a b q).symm ▸ (halt_eq (updateBits eq a b q)).symm ▸ run_update eq a b q ha hb
theorem steps_le (eq : Bool) (a b q : ℕ) :
    steps eq a b q ≤ 2 * (eq :: FactorTest.tripleInput a b q).length + 5 := by
  simp only [List.length_cons,FactorTest.tripleInput_length]
  unfold steps
  rw [FactorTest.tripleInput_length]
  cases eq <;> simp only [ite_true,Bool.false_eq_true,ite_false]
  all_goals first | omega | (split_ifs <;> omega)
def trialMachine : Machine := Composition.machine (RetainedInput.machine FactorTest.machine) machine
def trialSteps (a b q : ℕ) : ℕ :=
  FactorTest.steps a b q + steps (decide (a * b = q)) a b q +
    5 * (FactorTest.tripleInput a b q).length + 12
def trialExec (a b q : ℕ) (ha : a ≤ q) (hb : b ≤ q) :
    EvalsToInTime (TM2.step trialMachine.program) (trialMachine.init (FactorTest.tripleInput a b q))
      (some (trialMachine.halt (updateBits (decide (a * b = q)) a b q))) (trialSteps a b q) := by
  have hR := RetainedInput.executes FactorTest.machine (FactorTest.tripleInput a b q)
    (FactorTest.boolBits (decide (a * b = q))) _ (FactorTest.factorExec a b q)
  have hU := updateExec (decide (a * b = q)) a b q ha hb
  have h := Composition.executes (RetainedInput.machine FactorTest.machine) machine
    (FactorTest.tripleInput a b q) (decide (a * b = q) :: FactorTest.tripleInput a b q)
    (updateBits (decide (a * b = q)) a b q) _ _ hR hU
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  simp only [trialSteps,FactorTest.boolBits,List.length_cons,List.length_nil]
  omega
noncomputable def trialTime : Polynomial ℕ :=
  FactorTest.time + Polynomial.C 7 * Polynomial.X + Polynomial.C 19
theorem trial_steps_le (a b q : ℕ) :
    trialSteps a b q ≤ trialTime.eval (FactorTest.tripleInput a b q).length := by
  have hF := FactorTest.steps_le a b q
  have hU := steps_le (decide (a * b = q)) a b q
  simp only [List.length_cons] at hU
  simp only [trialSteps,trialTime,FactorTest.time,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow,Polynomial.eval_one]
  omega
noncomputable def trialPolyExec (a b q : ℕ) (ha : a ≤ q) (hb : b ≤ q) :
    EvalsToInTime (TM2.step trialMachine.program) (trialMachine.init (FactorTest.tripleInput a b q))
      (some (trialMachine.halt (updateBits (decide (a * b = q)) a b q)))
      (trialTime.eval (FactorTest.tripleInput a b q).length) := by
  have h := trialExec a b q ha hb
  refine { h with steps_le_m := h.steps_le_m.trans (trial_steps_le a b q) }
abbrev Record := {x : ℕ × (ℕ × ℕ) // x.1 ≤ x.2.2 ∧ x.2.1 ≤ x.2.2}
def recordInput (r : Record) : List Bool := FactorTest.tripleInput r.val.1 r.val.2.1 r.val.2.2
def trialOutput (r : Record) : List Bool :=
  updateBits (decide (r.val.1 * r.val.2.1 = r.val.2.2)) r.val.1 r.val.2.1 r.val.2.2
noncomputable def trialComputableInPolyTime : TM2ComputableInPolyTime recordInput id trialOutput where
  tm := trialMachine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := trialTime
  outputsFun := fun x => by
    change TM2OutputsInTime trialMachine.toFinTM2 (List.map id (recordInput x))
      (some (List.map id (trialOutput x))) (trialTime.eval (recordInput x).length)
    have h := Machine.outputsInTime trialMachine _ _ _
      (trialPolyExec x.val.1 x.val.2.1 x.val.2.2 x.property.1 x.property.2)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,recordInput,trialOutput] using h
end QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial


