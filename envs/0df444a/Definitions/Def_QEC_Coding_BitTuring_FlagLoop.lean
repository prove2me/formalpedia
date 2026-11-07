-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_FlagLoop
-- name    : QEC_Coding_BitTuring_FlagLoop
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:03:29.193487+00:00
-- url     : https://prove2.me/theorems/ac7f4f42-3181-49cb-a996-c729ab093ba9
-- title:
--   Flag Loop
-- statement:
--   Definitions and structural lemmas for Flag Loop, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/FlagLoop.lean

import Definitions.Def_QEC_Coding_BitTuring_Composition
set_option autoImplicit false
namespace QEC.Coding.BitTuring.FlagLoop
open Turing StateTransition
variable (A : Machine)
abbrev Stack := A.K ⊕ (Unit ⊕ Unit)
abbrev Label := A.Λ ⊕ Fin 4
abbrev Var := A.σ × Bool × Option Bool
def tapes (S : A.K → List Bool) : Stack A → List Bool
  | .inl k => S k
  | .inr _ => []
def embed : A.Cfg → TM2.Cfg (fun _ : Stack A => Bool) (Label A) (Var A) :=
  liftCfg Sum.inl (fun v => (v,false,none)) (tapes A) (some (.inr 0))
theorem tapes_update (S : A.K → List Bool) (k : A.K) (w : List Bool) :
    Function.update (tapes A S) (.inl k) w = tapes A (Function.update S k w) := by
  funext j
  cases j with
  | inl j => by_cases h : j = k <;> simp [tapes,h]
  | inr j => simp [tapes]
def copyStack (flag : Bool) (k : Fin 3) : Stack A :=
  if k = 0 then .inl A.output else if k = 1 then .inr (.inl ())
    else if flag then .inr (.inr ()) else .inl A.input
def copyTapes (flag : Bool) (S : Fin 3 → List Bool) : Stack A → List Bool
  | .inl k => if k = A.output then S 0 else if flag then [] else if k = A.input then S 2 else []
  | .inr (.inl _) => S 1
  | .inr (.inr _) => if flag then S 2 else []
def copyLabel (phase : Bool) : Label A := .inr (if phase then 1 else 2)
def embedCopy (flag : Bool) : TM2.Cfg (fun _ : Fin 3 => Bool) Bool (Option Bool) →
    TM2.Cfg (fun _ : Stack A => Bool) (Label A) (Var A) :=
  liftCfg (copyLabel A) (fun v => (A.initial,flag,v)) (copyTapes A flag) (some (.inr 3))
theorem copyTapes_read (hio : A.input ≠ A.output) (flag : Bool)
    (S : Fin 3 → List Bool) (k : Fin 3) :
    copyTapes A flag S (copyStack A flag k) = S k := by
  cases flag <;> fin_cases k <;> simp [copyStack,copyTapes,hio]
theorem copyTapes_update (hio : A.input ≠ A.output) (flag : Bool)
    (S : Fin 3 → List Bool) (k : Fin 3) (w : List Bool) :
    Function.update (copyTapes A flag S) (copyStack A flag k) w =
      copyTapes A flag (Function.update S k w) := by
  cases flag <;> fin_cases k <;> funext j
  all_goals
    cases j with
    | inl j =>
        by_cases ho : j = A.output <;> by_cases hi : j = A.input <;>
          simp_all [copyStack,copyTapes]
    | inr j =>
        cases j with
        | inl j => cases j; simp [copyStack,copyTapes]
        | inr j => cases j; simp [copyStack,copyTapes]
def copyStatement (flag phase : Bool) :
    TM2.Stmt (fun _ : Stack A => Bool) (Label A) (Var A) :=
  liftStatement (copyStack A flag) (copyLabel A) (fun v => v.2.2)
    (fun v h => (v.1,v.2.1,h)) (some (.inr 3)) (copyProgram phase)
def program : Label A → TM2.Stmt (fun _ : Stack A => Bool) (Label A) (Var A)
  | .inl l => liftStatement Sum.inl Sum.inl Prod.fst
      (fun v w => (w,v.2)) (some (.inr 0)) (A.program l)
  | .inr 0 => .pop (.inl A.output) (fun v h => (v.1,h.getD false,h))
      (.load (fun v => (v.1,v.2.1,none)) (.goto fun _ => .inr 1))
  | .inr 1 => .branch (fun v => v.2.1) (copyStatement A true true) (copyStatement A false true)
  | .inr 2 => .branch (fun v => v.2.1) (copyStatement A true false) (copyStatement A false false)
  | .inr _ => .branch (fun v => v.2.1)
      (.load (fun _ => (A.initial,false,none)) .halt)
      (.load (fun _ => (A.initial,false,none)) (.goto fun _ => .inl A.main))
theorem stepAux (l : A.Λ) (v : A.σ) (S : A.K → List Bool) :
    TM2.stepAux (program A (.inl l)) (v,false,none) (tapes A S) =
      embed A (TM2.stepAux (A.program l) v S) :=
  stepAux_liftStatement (K := A.K) (K' := Stack A) (Λ := A.Λ) (Λ' := Label A)
    (σ := A.σ) (σ' := Var A) Sum.inl Sum.inl Prod.fst (fun v w => (w,v.2))
    (some (.inr 0)) (fun v => (v,false,none)) (tapes A)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (tapes_update A) (A.program l) v S
theorem step (c c' : A.Cfg) (h : TM2.step A.program c = some c') :
    TM2.step (program A) (embed A c) = some (embed A c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      have hh : TM2.stepAux (A.program l) v S = c' := Option.some.inj h
      rw [← hh]
      exact congrArg some (stepAux A l v S)
theorem stepAuxCopy (hio : A.input ≠ A.output) (flag phase : Bool)
    (v : Option Bool) (S : Fin 3 → List Bool) :
    TM2.stepAux (program A (copyLabel A phase)) (A.initial,flag,v) (copyTapes A flag S) =
      embedCopy A flag (TM2.stepAux (copyProgram phase) v S) := by
  have h := stepAux_liftStatement (K := Fin 3) (K' := Stack A) (Λ := Bool) (Λ' := Label A)
    (σ := Option Bool) (σ' := Var A) (copyStack A flag) (copyLabel A)
    (fun v => v.2.2) (fun v h => (v.1,v.2.1,h)) (some (.inr 3))
    (fun v => (A.initial,flag,v)) (copyTapes A flag)
    (fun _ => rfl) (fun _ _ => rfl) (copyTapes_read A hio flag)
    (copyTapes_update A hio flag) (copyProgram phase) v S
  cases flag <;> cases phase <;>
    simpa [program,copyStatement,copyLabel,embedCopy] using h
theorem stepCopy (hio : A.input ≠ A.output) (flag : Bool)
    (c c' : TM2.Cfg (fun _ : Fin 3 => Bool) Bool (Option Bool))
    (h : TM2.step copyProgram c = some c') :
    TM2.step (program A) (embedCopy A flag c) = some (embedCopy A flag c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      have hh : TM2.stepAux (copyProgram l) v S = c' := Option.some.inj h
      rw [← hh]
      exact congrArg some (stepAuxCopy A hio flag l v S)
def machine : Machine where
  K := Stack A
  input := .inl A.input
  output := .inr (.inr ())
  Λ := Label A
  main := .inl A.main
  σ := Var A
  initial := (A.initial,false,none)
  program := program A
theorem embed_init (w : List Bool) : embed A (A.init w) = (machine A).init w := by
  simp only [embed,liftCfg,Machine.init,machine,Option.elim_some]
  congr 1
  funext j
  cases j with
  | inl j => by_cases h : j = A.input <;> simp [tapes,Function.update,h]
  | inr j => simp [tapes,Function.update]
theorem header (flag : Bool) (w : List Bool) :
    TM2.step (program A) (embed A (A.halt (flag :: w))) =
      some (embedCopy A flag (copyCfg true w [] [] none)) := by
  simp [TM2.step,program,embed,liftCfg,Machine.halt,tapes,embedCopy,copyCfg,copyLabel,
    TM2.stepAux,TM2.Cfg.mk.injEq]
  funext j
  cases j with
  | inl j => by_cases h : j = A.output <;> simp [copyTapes,tapes,Function.update,h]
  | inr j => cases j with
    | inl j => cases j; simp [copyTapes,tapes,Function.update]
    | inr j => cases j; simp [copyTapes,tapes,Function.update]
theorem finish_true (w : List Bool) :
    TM2.step (program A) (embedCopy A true (copyHalt w)) = some ((machine A).halt w) := by
  simp [TM2.step,program,embedCopy,liftCfg,copyHalt,Machine.halt,machine,
    TM2.stepAux,TM2.Cfg.mk.injEq]
  funext j
  cases j with
  | inl j => by_cases h : j = A.output <;> simp [copyTapes,Function.update,h]
  | inr j => cases j with
    | inl j => cases j; simp [copyTapes,Function.update]
    | inr j => cases j; simp [copyTapes,Function.update]
theorem finish_false (hio : A.input ≠ A.output) (w : List Bool) :
    TM2.step (program A) (embedCopy A false (copyHalt w)) = some ((machine A).init w) := by
  simp [TM2.step,program,embedCopy,liftCfg,copyHalt,Machine.init,machine,
    TM2.stepAux,TM2.Cfg.mk.injEq]
  funext j
  cases j with
  | inl j =>
      by_cases ho : j = A.output <;> by_cases hi : j = A.input <;>
        simp_all [copyTapes,Function.update]
  | inr j => cases j with
    | inl j => cases j; simp [copyTapes,Function.update]
    | inr j => cases j; simp [copyTapes,Function.update]
def target (flag : Bool) (w : List Bool) :
    TM2.Cfg (fun _ : Stack A => Bool) (Label A) (Var A) :=
  if flag then (machine A).halt w else (machine A).init w
theorem transfer (hio : A.input ≠ A.output) (flag : Bool) (w : List Bool) :
    (fun c => c.bind (TM2.step (program A)))^[2 * w.length + 4]
      (some (embed A (A.halt (flag :: w)))) = some (target A flag w) := by
  have hc := iterate_lift (TM2.step copyProgram) (TM2.step (program A)) (embedCopy A flag)
    (stepCopy A hio flag) _ _ _ (copyRun w)
  rw [show 2 * w.length + 4 = (1 + (2 * w.length + 2)) + 1 by omega,
    Function.iterate_succ_apply]
  simp only [Option.bind_some,header]
  rw [Function.iterate_add_apply,hc]
  simp only [Function.iterate_one,Option.bind_some]
  cases flag
  · exact finish_false A hio w
  · exact finish_true A w
def invocationExec (hio : A.input ≠ A.output) (x w : List Bool) (flag : Bool) (a : ℕ)
    (hA : EvalsToInTime (TM2.step A.program) (A.init x) (some (A.halt (flag :: w))) a) :
    EvalsToInTime (TM2.step (machine A).program) ((machine A).init x)
      (some (target A flag w)) (a + 2 * w.length + 4) := by
  refine ⟨⟨(2 * w.length + 4) + hA.steps, ?_⟩, ?_⟩
  · have hr := iterate_lift (TM2.step A.program) (TM2.step (program A)) (embed A)
      (step A) _ _ _ hA.evals_in_steps
    have hRun :
        (fun c : Option (TM2.Cfg (fun _ : Stack A => Bool) (Label A) (Var A)) =>
          c.bind (TM2.step (program A)))^[(2 * w.length + 4) + hA.steps]
          (some (embed A (A.init x))) = some (target A flag w) := by
      rw [Function.iterate_add_apply,hr]
      exact transfer A hio flag w
    exact embed_init A x ▸ hRun
  · change (2 * w.length + 4) + hA.steps ≤ a + 2 * w.length + 4
    have hle := hA.steps_le_m
    omega
def state (F : List Bool → Bool × List Bool) (n : ℕ) (x : List Bool) :=
  (fun w => (F w).2)^[n] x
@[simp] theorem state_zero (F : List Bool → Bool × List Bool) (x : List Bool) :
    state F 0 x = x := rfl
theorem state_succ (F : List Bool → Bool × List Bool) (n : ℕ) (x : List Bool) :
    state F (n + 1) x = state F n (F x).2 := Function.iterate_succ_apply _ _ _
def executes (hio : A.input ≠ A.output) (F : List Bool → Bool × List Bool)
    (n : ℕ) (x : List Bool) (b l : ℕ)
    (hA : ∀ i ≤ n, EvalsToInTime (TM2.step A.program) (A.init (state F i x))
      (some (A.halt ((F (state F i x)).1 :: (F (state F i x)).2))) b)
    (hlength : ∀ i ≤ n + 1, (state F i x).length ≤ l)
    (hcontinue : ∀ i < n, (F (state F i x)).1 = false)
    (hfinal : (F (state F n x)).1 = true) :
    EvalsToInTime (TM2.step (machine A).program) ((machine A).init x)
      (some ((machine A).halt (state F (n + 1) x))) ((n + 1) * (b + 2 * l + 4)) := by
  induction n generalizing x with
  | zero =>
      have ha := hA 0 (by omega)
      simp only [state_zero] at ha hfinal
      rw [hfinal] at ha
      have hr := invocationExec A hio x (F x).2 true b ha
      simp only [state_succ,state_zero,Nat.zero_add,Nat.one_mul]
      refine { hr with steps_le_m := hr.steps_le_m.trans ?_ }
      have hl := hlength 1 (by omega)
      simp only [state_succ,state_zero] at hl
      omega
  | succ n ih =>
      have ha := hA 0 (by omega)
      have hf := hcontinue 0 (by omega)
      simp only [state_zero] at ha hf
      rw [hf] at ha
      have hr := invocationExec A hio x (F x).2 false b ha
      have hh : EvalsToInTime (TM2.step (machine A).program) ((machine A).init x)
          (some ((machine A).init (F x).2)) (b + 2 * l + 4) := by
        refine { hr with steps_le_m := hr.steps_le_m.trans ?_ }
        have hl := hlength 1 (by omega)
        simp only [state_succ,state_zero] at hl
        omega
      have ht := ih (F x).2
        (fun i hi => by simpa only [state_succ] using hA (i + 1) (by omega))
        (fun i hi => by simpa only [state_succ] using hlength (i + 1) (by omega))
        (fun i hi => by simpa only [state_succ] using hcontinue (i + 1) (by omega))
        (by simpa only [state_succ] using hfinal)
      have h := EvalsToInTime.trans (TM2.step (machine A).program)
        (b + 2 * l + 4) ((n + 1) * (b + 2 * l + 4))
        ((machine A).init x) ((machine A).init (F x).2)
        (some ((machine A).halt (state F (n + 1) (F x).2))) hh ht
      have hb : (n + 1) * (b + 2 * l + 4) + (b + 2 * l + 4) =
          (n + 1 + 1) * (b + 2 * l + 4) := by ring
      rw [hb] at h
      simpa only [state_succ] using h
noncomputable def timePolynomial (p iterations size : Polynomial ℕ) : Polynomial ℕ :=
  (iterations + 1) * (p.comp size + Polynomial.C 2 * size + Polynomial.C 4)
noncomputable def executes_polynomial (hio : A.input ≠ A.output)
    (F : List Bool → Bool × List Bool) (n : ℕ) (x : List Bool)
    (p iterations size : Polynomial ℕ)
    (hA : ∀ i ≤ n, EvalsToInTime (TM2.step A.program) (A.init (state F i x))
      (some (A.halt ((F (state F i x)).1 :: (F (state F i x)).2)))
      (p.eval (state F i x).length))
    (hn : n ≤ iterations.eval x.length)
    (hlength : ∀ i ≤ n + 1, (state F i x).length ≤ size.eval x.length)
    (hcontinue : ∀ i < n, (F (state F i x)).1 = false)
    (hfinal : (F (state F n x)).1 = true) :
    EvalsToInTime (TM2.step (machine A).program) ((machine A).init x)
      (some ((machine A).halt (state F (n + 1) x)))
      ((timePolynomial p iterations size).eval x.length) := by
  have hRun := executes A hio F n x (p.eval (size.eval x.length)) (size.eval x.length)
    (fun i hi => by
      have h := hA i hi
      refine { h with steps_le_m := h.steps_le_m.trans ?_ }
      exact Composition.polynomial_eval_monotone p (hlength i (by omega)))
    hlength hcontinue hfinal
  refine { hRun with steps_le_m := hRun.steps_le_m.trans ?_ }
  have h := Nat.mul_le_mul_right (p.eval (size.eval x.length) + 2 * size.eval x.length + 4)
    (Nat.add_le_add_right hn 1)
  simpa [timePolynomial] using h
noncomputable def computableInPolyTime (hio : A.input ≠ A.output)
    (F : List Bool → Bool × List Bool) (index : List Bool → ℕ)
    (p iterations size : Polynomial ℕ)
    (hA : ∀ x i, i ≤ index x → EvalsToInTime (TM2.step A.program) (A.init (state F i x))
      (some (A.halt ((F (state F i x)).1 :: (F (state F i x)).2)))
      (p.eval (state F i x).length))
    (hn : ∀ x, index x ≤ iterations.eval x.length)
    (hlength : ∀ x i, i ≤ index x + 1 → (state F i x).length ≤ size.eval x.length)
    (hcontinue : ∀ x i, i < index x → (F (state F i x)).1 = false)
    (hfinal : ∀ x, (F (state F (index x) x)).1 = true) :
    TM2ComputableInPolyTime id id (fun x => state F (index x + 1) x) where
  tm := (machine A).toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial p iterations size
  outputsFun := fun x => by
    change TM2OutputsInTime (machine A).toFinTM2 (List.map id x)
      (some (List.map id (state F (index x + 1) x)))
      ((timePolynomial p iterations size).eval x.length)
    have h := Machine.outputsInTime (machine A) _ _ _
      (executes_polynomial A hio F (index x) x p iterations size (hA x) (hn x)
        (hlength x) (hcontinue x) (hfinal x))
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
end QEC.Coding.BitTuring.FlagLoop


