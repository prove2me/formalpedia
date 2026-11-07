-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryMultiplication
-- name    : QEC_Coding_BitTuring_UnaryMultiplication
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:03:15.222472+00:00
-- url     : https://prove2.me/theorems/db0e5e1a-b6b6-4715-82e5-78da68941546
-- title:
--   Unary Multiplication
-- statement:
--   Definitions and structural lemmas for Unary Multiplication, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMultiplication.lean

import Definitions.Def_QEC_Coding_BitTuring_Composition
set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
def multiplicationProgram : Fin 6 → TM2.Stmt (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool)
  | 0 => .pop 0 (fun _ h => h)
      (.branch (fun v => v.getD false)
        (.push 1 (fun _ => true) (.goto fun _ => 0)) (.goto fun _ => 1))
  | 1 => .pop 0 (fun _ h => h)
      (.branch Option.isSome
        (.push 2 (fun v => v.getD false) (.goto fun _ => 1)) (.goto fun _ => 2))
  | 2 => .pop 1 (fun _ h => h)
      (.branch Option.isSome (.goto fun _ => 3) (.goto fun _ => 5))
  | 3 => .pop 2 (fun _ h => h)
      (.branch Option.isSome
        (.push 3 (fun v => v.getD false) (.push 4 (fun v => v.getD false) (.goto fun _ => 3)))
        (.goto fun _ => 4))
  | 4 => .pop 3 (fun _ h => h)
      (.branch Option.isSome
        (.push 2 (fun v => v.getD false) (.goto fun _ => 4)) (.goto fun _ => 2))
  | _ => .pop 2 (fun _ h => h)
      (.branch Option.isSome (.goto fun _ => 5) .halt)
def multiplicationMachine : Machine where
  K := Fin 5
  input := 0
  output := 4
  Λ := Fin 6
  main := 0
  σ := Option Bool
  initial := none
  program := multiplicationProgram
def multiplicationCfg (phase : Fin 6) (source a b buffer output : List Bool) (v : Option Bool) :
    TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) :=
  ⟨some phase,v,![source,a,b,buffer,output]⟩
def multiplicationHalt (output : List Bool) :
    TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) :=
  ⟨none,none,![[],[],[],[],output]⟩
def unary (n : ℕ) := List.replicate n true
def pairInput (a b : ℕ) := unary a ++ false :: unary b
theorem parseA_true (s a b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 0 (true :: s) a b buf d v) = some (multiplicationCfg 0 s (true :: a) b buf d (some true)) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem parseA_separator (s a b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 0 (false :: s) a b buf d v) = some (multiplicationCfg 1 s a b buf d (some false)) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem parseB_cons (x : Bool) (s a b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 1 (x :: s) a b buf d v) = some (multiplicationCfg 1 s a (x :: b) buf d (some x)) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem parseB_nil (a b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 1 [] a b buf d v) = some (multiplicationCfg 2 [] a b buf d none) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
theorem outer_cons (x : Bool) (s a b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 2 s (x :: a) b buf d v) = some (multiplicationCfg 3 s a b buf d (some x)) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem outer_nil (s b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 2 s [] b buf d v) = some (multiplicationCfg 5 s [] b buf d none) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
theorem copyB_cons (x : Bool) (s a b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 3 s a (x :: b) buf d v) = some (multiplicationCfg 3 s a b (x :: buf) (x :: d) (some x)) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem copyB_nil (s a buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 3 s a [] buf d v) = some (multiplicationCfg 4 s a [] buf d none) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
theorem restore_cons (x : Bool) (s a b buf d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 4 s a b (x :: buf) d v) = some (multiplicationCfg 4 s a (x :: b) buf d (some x)) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem restore_nil (s a b d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 4 s a b [] d v) = some (multiplicationCfg 2 s a b [] d none) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
theorem clean_cons (x : Bool) (b d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 5 [] [] (x :: b) [] d v) = some (multiplicationCfg 5 [] [] b [] d (some x)) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, TM2.stepAux, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem clean_nil (d : List Bool) (v : Option Bool) :
    TM2.step multiplicationProgram (multiplicationCfg 5 [] [] [] [] d v) = some (multiplicationHalt d) := by
  simp [TM2.step, multiplicationProgram, multiplicationCfg, multiplicationHalt, TM2.stepAux, TM2.Cfg.mk.injEq]
@[simp] theorem unary_zero : unary 0 = [] := rfl
@[simp] theorem unary_succ (n : ℕ) : unary (n + 1) = true :: unary n := by
  simp [unary, List.replicate_succ]
theorem unary_append_cons (n : ℕ) (d : List Bool) :
    unary n ++ true :: d = unary (n + 1) ++ d := by
  simp [unary, List.replicate_add, List.append_assoc]
theorem unary_add (a b : ℕ) : unary (a + b) = unary a ++ unary b :=
  List.replicate_add a b true
theorem run_parseA (n : ℕ) (s a b buf d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step multiplicationProgram))^[n + 1]
      (some (multiplicationCfg 0 (unary n ++ false :: s) a b buf d v)) =
      some (multiplicationCfg 1 s (unary n ++ a) b buf d (some false)) := by
  induction n generalizing a v with
  | zero => simp [parseA_separator]
  | succ n ih =>
      simp only [unary_succ, List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, parseA_true]
      simpa only [unary_append_cons, unary_succ, List.cons_append] using ih (true :: a) (some true)
theorem run_parseB (n : ℕ) (a b buf d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step multiplicationProgram))^[n + 1]
      (some (multiplicationCfg 1 (unary n) a b buf d v)) =
      some (multiplicationCfg 2 [] a (unary n ++ b) buf d none) := by
  induction n generalizing b v with
  | zero => simp [parseB_nil]
  | succ n ih =>
      simp only [unary_succ, List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, parseB_cons]
      simpa only [unary_append_cons, unary_succ, List.cons_append] using ih (true :: b) (some true)
theorem run_copyB (n : ℕ) (s a buf d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step multiplicationProgram))^[n + 1]
      (some (multiplicationCfg 3 s a (unary n) buf d v)) =
      some (multiplicationCfg 4 s a [] (unary n ++ buf) (unary n ++ d) none) := by
  induction n generalizing buf d v with
  | zero => simp [copyB_nil]
  | succ n ih =>
      simp only [unary_succ, List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, copyB_cons]
      simpa only [unary_append_cons, unary_succ, List.cons_append] using ih (true :: buf) (true :: d) (some true)
theorem run_restoreB (n : ℕ) (s a b d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step multiplicationProgram))^[n + 1]
      (some (multiplicationCfg 4 s a b (unary n) d v)) =
      some (multiplicationCfg 2 s a (unary n ++ b) [] d none) := by
  induction n generalizing b v with
  | zero => simp [restore_nil]
  | succ n ih =>
      simp only [unary_succ, List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, restore_cons]
      simpa only [unary_append_cons, unary_succ, List.cons_append] using ih (true :: b) (some true)
theorem run_cleanB (n : ℕ) (d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step multiplicationProgram))^[n + 1]
      (some (multiplicationCfg 5 [] [] (unary n) [] d v)) = some (multiplicationHalt d) := by
  induction n generalizing v with
  | zero => simp [clean_nil]
  | succ n ih =>
      simp only [unary_succ]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, clean_cons]
      exact ih (some true)
theorem run_outer (a b : ℕ) (d : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step multiplicationProgram))^[a * (2 * b + 3) + b + 2]
      (some (multiplicationCfg 2 [] (unary a) (unary b) [] d v)) =
      some (multiplicationHalt (unary (a * b) ++ d)) := by
  induction a generalizing d v with
  | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, unary_zero, List.nil_append]
      rw [show b + 2 = (b + 1) + 1 by omega, Function.iterate_succ_apply]
      simp only [Option.bind_some, outer_nil]
      exact run_cleanB b d none
  | succ a ih =>
      have ht : (a + 1) * (2 * b + 3) + b + 2 =
          ((a * (2 * b + 3) + b + 2) + (b + 1)) + (b + 1) + 1 := by ring
      rw [ht, Function.iterate_succ_apply]
      simp only [unary_succ, Option.bind_some, outer_cons]
      rw [Function.iterate_add_apply, run_copyB]
      simp only [List.append_nil]
      rw [Function.iterate_add_apply, run_restoreB]
      simp only [List.append_nil]
      simpa only [Nat.add_mul, Nat.one_mul, unary_add, List.append_assoc] using ih (unary b ++ d) none
theorem run_multiplication (a b : ℕ) :
    (fun c => c.bind (TM2.step multiplicationProgram))^[(a + 1) * (2 * b + 4)]
      (some (multiplicationCfg 0 (pairInput a b) [] [] [] [] none)) =
      some (multiplicationHalt (unary (a * b))) := by
  have ht : (a + 1) * (2 * b + 4) =
      ((a * (2 * b + 3) + b + 2) + (b + 1)) + (a + 1) := by ring
  rw [ht, Function.iterate_add_apply]
  simp only [pairInput]
  rw [run_parseA]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply, run_parseB]
  simp only [List.append_nil]
  rw [run_outer]
  simp
theorem machine_init_eq (a b : ℕ) :
    multiplicationMachine.init (pairInput a b) =
      multiplicationCfg 0 (pairInput a b) [] [] [] [] none := by
  simp [Machine.init, multiplicationMachine, multiplicationCfg, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
theorem machine_halt_eq (d : List Bool) :
    multiplicationMachine.halt d = multiplicationHalt d := by
  simp [Machine.halt, multiplicationMachine, multiplicationHalt, TM2.Cfg.mk.injEq]
  funext k
  fin_cases k <;> simp [Function.update]
def multiplicationExec (a b : ℕ) :
    EvalsToInTime (TM2.step multiplicationMachine.program)
      (multiplicationMachine.init (pairInput a b))
      (some (multiplicationMachine.halt (unary (a * b)))) ((a + 1) * (2 * b + 4)) := by
  refine ⟨⟨(a + 1) * (2 * b + 4), ?_⟩, le_refl _⟩
  exact (machine_init_eq a b).symm ▸ (machine_halt_eq (unary (a * b))).symm ▸ run_multiplication a b
theorem pairInput_length (a b : ℕ) : (pairInput a b).length = a + b + 1 := by
  simp [pairInput, unary]
  omega
theorem multiplication_steps_le (a b : ℕ) :
    (a + 1) * (2 * b + 4) ≤ 2 * ((pairInput a b).length + 1) ^ 2 := by
  have ha : a + 1 ≤ (pairInput a b).length + 1 := by rw [pairInput_length]; omega
  have hb : b + 2 ≤ (pairInput a b).length + 1 := by rw [pairInput_length]; omega
  calc
    (a + 1) * (2 * b + 4) = 2 * ((a + 1) * (b + 2)) := by ring
    _ ≤ 2 * (((pairInput a b).length + 1) * ((pairInput a b).length + 1)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul ha hb)
    _ = 2 * ((pairInput a b).length + 1) ^ 2 := by ring
noncomputable def multiplicationTime : Polynomial ℕ := Polynomial.C 2 * (Polynomial.X + 1) ^ 2
noncomputable def multiplicationPolyExec (a b : ℕ) :
    EvalsToInTime (TM2.step multiplicationMachine.program)
      (multiplicationMachine.init (pairInput a b))
      (some (multiplicationMachine.halt (unary (a * b))))
      (multiplicationTime.eval (pairInput a b).length) := by
  have h := multiplicationExec a b
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  simpa [multiplicationTime] using multiplication_steps_le a b
noncomputable def multiplicationComputableInPolyTime :
    TM2ComputableInPolyTime (fun x : ℕ × ℕ => pairInput x.1 x.2) unary (fun x => x.1 * x.2) where
  tm := multiplicationMachine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := multiplicationTime
  outputsFun := fun x => by
    change TM2OutputsInTime multiplicationMachine.toFinTM2
      (List.map id (pairInput x.1 x.2)) (some (List.map id (unary (x.1 * x.2))))
      (multiplicationTime.eval (pairInput x.1 x.2).length)
    have h := Machine.outputsInTime multiplicationMachine _ _ _ (multiplicationPolyExec x.1 x.2)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
end QEC.Coding.BitTuring.UnaryArithmetic


