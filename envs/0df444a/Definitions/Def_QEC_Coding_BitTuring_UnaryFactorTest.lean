-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
-- name    : QEC_Coding_BitTuring_UnaryFactorTest
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:04:33.573376+00:00
-- url     : https://prove2.me/theorems/855d506d-7875-462e-a0fb-374980777796
-- title:
--   Unary Factor Test
-- statement:
--   Definitions and structural lemmas for Unary Factor Test, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFactorTest.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryComparison
set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
open Turing StateTransition
abbrev Stack := Fin 5 ⊕ Fin 2
abbrev Label := Fin 3 ⊕ (Fin 6 ⊕ (Fin 4 ⊕ Unit))
def mulLabel (l : Fin 6) : Label := .inr (.inl l)
def cmpLabel (l : Fin 4) : Label := .inr (.inr (.inl l))
def endLabel : Label := .inr (.inr (.inr ()))
def cmpStack (k : Fin 3) : Stack :=
  if k = 0 then .inr 0 else if k = 1 then .inl 4 else .inr 1
def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .inl 0 => .pop (.inl 0) (fun _ h => h)
      (.branch (fun v => v.getD false)
        (.push (.inl 1) (fun _ => true) (.goto fun _ => .inl 0)) (.goto fun _ => .inl 1))
  | .inl 1 => .pop (.inl 0) (fun _ h => h)
      (.branch (fun v => v.getD false)
        (.push (.inl 2) (fun _ => true) (.goto fun _ => .inl 1)) (.goto fun _ => .inl 2))
  | .inl _ => .pop (.inl 0) (fun _ h => h)
      (.branch Option.isSome
        (.push (.inr 0) (fun v => v.getD false) (.goto fun _ => .inl 2))
        (.goto fun _ => mulLabel 2))
  | .inr (.inl l) => liftStatement Sum.inl mulLabel id (fun _ w => w)
      (some (cmpLabel 1)) (multiplicationProgram l)
  | .inr (.inr (.inl l)) => liftStatement cmpStack cmpLabel id (fun _ w => w)
      (some endLabel) (comparisonProgram l)
  | .inr (.inr (.inr _)) => .pop (.inr 1) (fun _ _ => none)
      (.pop (.inr 1) (fun _ h => h)
        (.push (.inr 1) (fun v => v.getD false) (.load (fun _ => none) .halt)))
def machine : QEC.Coding.BitTuring.Machine where
  K := Stack
  input := .inl 0
  output := .inr 1
  Λ := Label
  main := .inl 0
  σ := Option Bool
  initial := none
  program := program
def prefixCfg (phase : Fin 3) (source a b q : List Bool) (v : Option Bool) :
    TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool) :=
  ⟨some (.inl phase),v,fun k => match k with
    | .inl k => ![source,a,b,[],[]] k
    | .inr k => ![q,[]] k⟩
def mulTapes (q : List Bool) (S : Fin 5 → List Bool) : Stack → List Bool
  | .inl k => S k
  | .inr k => if k = 0 then q else []
def embedMul (q : List Bool) :
    TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool) →
    TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool) :=
  liftCfg mulLabel id (mulTapes q) (some (cmpLabel 1))
theorem mulTapes_update (q : List Bool) (S : Fin 5 → List Bool) (k : Fin 5) (w : List Bool) :
    Function.update (mulTapes q S) (.inl k) w = mulTapes q (Function.update S k w) := by
  funext j
  cases j with
  | inl j => by_cases h : j = k <;> simp [mulTapes,h]
  | inr j => simp [mulTapes]
theorem stepAuxMul (q : List Bool) (l : Fin 6) (v : Option Bool) (S : Fin 5 → List Bool) :
    TM2.stepAux (program (mulLabel l)) v (mulTapes q S) =
      embedMul q (TM2.stepAux (multiplicationProgram l) v S) :=
  stepAux_liftStatement (K := Fin 5) (K' := Stack) (Λ := Fin 6) (Λ' := Label)
    (σ := Option Bool) (σ' := Option Bool) Sum.inl mulLabel id (fun _ w => w)
    (some (cmpLabel 1)) id (mulTapes q) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (mulTapes_update q) (multiplicationProgram l) v S
theorem stepMul (q : List Bool)
    (c c' : TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool))
    (h : TM2.step multiplicationProgram c = some c') :
    TM2.step program (embedMul q c) = some (embedMul q c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      have hh : TM2.stepAux (multiplicationProgram l) v S = c' := Option.some.inj h
      rw [← hh]
      exact congrArg some (stepAuxMul q l v S)
theorem parseA_cons (s a b q : List Bool) (v : Option Bool) :
    TM2.step program (prefixCfg 0 (true :: s) a b q v) =
      some (prefixCfg 0 s (true :: a) b q (some true)) := by
  simp [TM2.step,program,prefixCfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]
theorem parseA_sep (s a b q : List Bool) (v : Option Bool) :
    TM2.step program (prefixCfg 0 (false :: s) a b q v) =
      some (prefixCfg 1 s a b q (some false)) := by
  simp [TM2.step,program,prefixCfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]
theorem parseB_cons (s a b q : List Bool) (v : Option Bool) :
    TM2.step program (prefixCfg 1 (true :: s) a b q v) =
      some (prefixCfg 1 s a (true :: b) q (some true)) := by
  simp [TM2.step,program,prefixCfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]
theorem parseB_sep (s a b q : List Bool) (v : Option Bool) :
    TM2.step program (prefixCfg 1 (false :: s) a b q v) =
      some (prefixCfg 2 s a b q (some false)) := by
  simp [TM2.step,program,prefixCfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]
theorem parseQ_cons (x : Bool) (s a b q : List Bool) (v : Option Bool) :
    TM2.step program (prefixCfg 2 (x :: s) a b q v) =
      some (prefixCfg 2 s a b (x :: q) (some x)) := by
  simp [TM2.step,program,prefixCfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]
theorem parseQ_nil (a b q : List Bool) (v : Option Bool) :
    TM2.step program (prefixCfg 2 [] a b q v) =
      some (embedMul q (multiplicationCfg 2 [] a b [] [] none)) := by
  simp [TM2.step,program,prefixCfg,TM2.stepAux,TM2.Cfg.mk.injEq,embedMul,liftCfg,
    multiplicationCfg,mulLabel]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [mulTapes,Function.update]
  | inr k => fin_cases k <;> simp [mulTapes,Function.update]
def tripleInput (a b q : ℕ) := unary a ++ false :: pairInput b q
theorem run_parseA (n : ℕ) (s a b q : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n + 1]
      (some (prefixCfg 0 (unary n ++ false :: s) a b q v)) =
      some (prefixCfg 1 s (unary n ++ a) b q (some false)) := by
  induction n generalizing a v with
  | zero => simp [parseA_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,parseA_cons]
      simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (true :: a) (some true)
theorem run_parseB (n : ℕ) (s a b q : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n + 1]
      (some (prefixCfg 1 (unary n ++ false :: s) a b q v)) =
      some (prefixCfg 2 s a (unary n ++ b) q (some false)) := by
  induction n generalizing b v with
  | zero => simp [parseB_sep]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,parseB_cons]
      simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (true :: b) (some true)
theorem run_parseQ (n : ℕ) (a b q : List Bool) (v : Option Bool) :
    (fun c => c.bind (TM2.step program))^[n + 1]
      (some (prefixCfg 2 (unary n) a b q v)) =
      some (embedMul (unary n ++ q) (multiplicationCfg 2 [] a b [] [] none)) := by
  induction n generalizing q v with
  | zero => simp [parseQ_nil]
  | succ n ih =>
      simp only [unary_succ,List.cons_append]
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some,parseQ_cons]
      simpa only [unary_append_cons,unary_succ,List.cons_append] using ih (true :: q) (some true)
theorem run_prefix (a b q : ℕ) :
    (fun c => c.bind (TM2.step program))^[a + b + q + 3]
      (some (prefixCfg 0 (tripleInput a b q) [] [] [] none)) =
      some (embedMul (unary q) (multiplicationCfg 2 [] (unary a) (unary b) [] [] none)) := by
  rw [show a + b + q + 3 = ((q + 1) + (b + 1)) + (a + 1) by omega,
    Function.iterate_add_apply]
  simp only [tripleInput,pairInput]
  rw [run_parseA]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply,run_parseB]
  simp only [List.append_nil]
  simpa only [List.append_nil] using run_parseQ q (unary a) (unary b) [] (some false)
theorem run_mul (a b q : ℕ) :
    (fun c => c.bind (TM2.step program))^[a * (2 * b + 3) + b + 2]
      (some (embedMul (unary q) (multiplicationCfg 2 [] (unary a) (unary b) [] [] none))) =
      some (embedMul (unary q) (multiplicationHalt (unary (a * b)))) := by
  have hm := QEC.Coding.BitTuring.UnaryArithmetic.run_outer a b [] none
  simp only [List.append_nil] at hm
  exact iterate_lift (TM2.step multiplicationProgram) (TM2.step program) (embedMul (unary q))
    (stepMul (unary q)) _ _ _ hm
def cmpTapes (S : Fin 3 → List Bool) : Stack → List Bool
  | .inl k => if k = 4 then S 1 else []
  | .inr k => if k = 0 then S 0 else S 2
def embedCmp : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) →
    TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool) :=
  liftCfg cmpLabel id cmpTapes (some endLabel)
theorem cmpTapes_read (S : Fin 3 → List Bool) (k : Fin 3) : cmpTapes S (cmpStack k) = S k := by
  fin_cases k <;> simp [cmpTapes,cmpStack]
theorem cmpTapes_update (S : Fin 3 → List Bool) (k : Fin 3) (w : List Bool) :
    Function.update (cmpTapes S) (cmpStack k) w = cmpTapes (Function.update S k w) := by
  fin_cases k <;> funext j
  all_goals
    cases j with
    | inl j => by_cases h : j = 4 <;> simp [cmpTapes,cmpStack,h]
    | inr j => fin_cases j <;> simp [cmpTapes,cmpStack]
theorem stepAuxCmp (l : Fin 4) (v : Option Bool) (S : Fin 3 → List Bool) :
    TM2.stepAux (program (cmpLabel l)) v (cmpTapes S) =
      embedCmp (TM2.stepAux (comparisonProgram l) v S) :=
  stepAux_liftStatement (K := Fin 3) (K' := Stack) (Λ := Fin 4) (Λ' := Label)
    (σ := Option Bool) (σ' := Option Bool) cmpStack cmpLabel id (fun _ w => w)
    (some endLabel) id cmpTapes (fun _ => rfl) (fun _ _ => rfl)
    cmpTapes_read cmpTapes_update (comparisonProgram l) v S
theorem stepCmp (c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool))
    (h : TM2.step comparisonProgram c = some c') :
    TM2.step program (embedCmp c) = some (embedCmp c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      have hh : TM2.stepAux (comparisonProgram l) v S = c' := Option.some.inj h
      rw [← hh]
      exact congrArg some (stepAuxCmp l v S)
theorem mul_end_cmp_start (a q : ℕ) :
    embedMul (unary q) (multiplicationHalt (unary a)) =
      embedCmp (comparisonCfg 1 (unary q) (unary a) [] none) := by
  simp [embedMul,embedCmp,liftCfg,multiplicationHalt,comparisonCfg,
    TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [mulTapes,cmpTapes]
  | inr k => fin_cases k <;> simp [mulTapes,cmpTapes]
theorem matching_run (a q : ℕ) :
    (fun c => c.bind (TM2.step comparisonProgram))^[max a q + 1]
      (some (comparisonCfg 1 (unary q) (unary a) [] none)) =
      some (comparisonHalt (comparisonBits a q)) := by
  rcases lt_trichotomy a q with h | h | h
  · let r := q - a - 1
    have hq : q = a + r + 1 := by dsimp [r]; omega
    have ht : max a q + 1 = a + r + 2 := by rw [Nat.max_eq_right (le_of_lt h)]; omega
    have hout : comparisonBits a q = [true,false] := by
      simp [comparisonBits,le_of_lt h,ne_of_lt h]
    rw [ht,hout,hq]
    simpa only [List.append_nil] using comparison_run_less a r [] none
  · subst q
    simpa [comparisonBits] using comparison_run_equal a [] none
  · let r := a - q - 1
    have ha : a = q + r + 1 := by dsimp [r]; omega
    have ht : max a q + 1 = q + r + 2 := by rw [Nat.max_eq_left (le_of_lt h)]; omega
    have hout : comparisonBits a q = [false,false] := by
      simp [comparisonBits,not_le.mpr h,ne_of_gt h]
    rw [ht,hout,ha]
    simpa only [List.append_nil] using comparison_run_greater q r [] none
theorem run_cmp (a q : ℕ) :
    (fun c => c.bind (TM2.step program))^[max a q + 1]
      (some (embedCmp (comparisonCfg 1 (unary q) (unary a) [] none))) =
      some (embedCmp (comparisonHalt (comparisonBits a q))) :=
  iterate_lift (TM2.step comparisonProgram) (TM2.step program) embedCmp stepCmp
    _ _ _ (matching_run a q)
def finalHalt (w : List Bool) : TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool) :=
  ⟨none,none,Function.update (fun _ => []) (.inr 1) w⟩
theorem footer (le eq : Bool) :
    TM2.step program (embedCmp (comparisonHalt [le,eq])) = some (finalHalt [eq]) := by
  simp [TM2.step,program,embedCmp,liftCfg,comparisonHalt,endLabel,finalHalt,
    TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [cmpTapes,Function.update]
  | inr k => fin_cases k <;> simp [cmpTapes,Function.update]
def steps (a b q : ℕ) := (a + 1) * (2 * b + 4) + q + max (a * b) q + 3
theorem run_factor_test (a b q : ℕ) :
    (fun c => c.bind (TM2.step program))^[steps a b q]
      (some (prefixCfg 0 (tripleInput a b q) [] [] [] none)) =
      some (finalHalt [decide (a * b = q)]) := by
  have ht : steps a b q =
      ((1 + (max (a * b) q + 1)) + (a * (2 * b + 3) + b + 2)) + (a + b + q + 3) := by
    unfold steps
    ring
  rw [ht,Function.iterate_add_apply,run_prefix,Function.iterate_add_apply,run_mul,
    mul_end_cmp_start,Function.iterate_add_apply,run_cmp]
  simp only [Function.iterate_one,Option.bind_some,comparisonBits,footer]
theorem tripleInput_length (a b q : ℕ) : (tripleInput a b q).length = a + b + q + 2 := by
  simp [tripleInput,pairInput_length,unary]
  omega
def boolBits (b : Bool) : List Bool := [b]
theorem init_eq (a b q : ℕ) :
    machine.init (tripleInput a b q) = prefixCfg 0 (tripleInput a b q) [] [] [] none := by
  simp [Machine.init,machine,prefixCfg,TM2.Cfg.mk.injEq]
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]
def factorExec (a b q : ℕ) :
    EvalsToInTime (TM2.step machine.program) (machine.init (tripleInput a b q))
      (some (machine.halt (boolBits (decide (a * b = q))))) (steps a b q) := by
  refine ⟨⟨steps a b q, ?_⟩, le_refl _⟩
  exact (init_eq a b q).symm ▸ run_factor_test a b q
theorem steps_le (a b q : ℕ) : steps a b q ≤ 5 * ((tripleInput a b q).length + 1) ^ 2 := by
  let L := (tripleInput a b q).length + 1
  have hL : L = a + b + q + 3 := by dsimp [L]; rw [tripleInput_length]
  have ha : a + 1 ≤ L := by omega
  have hb : b + 2 ≤ L := by omega
  have hmul : (a + 1) * (2 * b + 4) ≤ 2 * L ^ 2 := by
    calc
      _ = 2 * ((a + 1) * (b + 2)) := by ring
      _ ≤ 2 * (L * L) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul ha hb)
      _ = _ := by ring
  have hab : a * b ≤ L ^ 2 := by
    calc
      _ ≤ L * L := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hq : q ≤ L := by omega
  have hmax : max (a * b) q ≤ a * b + q := max_le (by omega) (by omega)
  change steps a b q ≤ 5 * L ^ 2
  unfold steps
  have hL3 : 3 ≤ L := by omega
  have hquad : 3 * L ≤ L ^ 2 := by
    calc
      _ ≤ L * L := Nat.mul_le_mul_right L hL3
      _ = _ := by ring
  omega
noncomputable def time : Polynomial ℕ := Polynomial.C 5 * (Polynomial.X + 1) ^ 2
noncomputable def factorPolyExec (a b q : ℕ) :
    EvalsToInTime (TM2.step machine.program) (machine.init (tripleInput a b q))
      (some (machine.halt (boolBits (decide (a * b = q)))))
      (time.eval (tripleInput a b q).length) := by
  have h := factorExec a b q
  refine { h with steps_le_m := h.steps_le_m.trans ?_ }
  simpa [time] using steps_le a b q
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime (fun x : ℕ × (ℕ × ℕ) => tripleInput x.1 x.2.1 x.2.2) boolBits
      (fun x => decide (x.1 * x.2.1 = x.2.2)) where
  tm := machine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun := fun x => by
    change TM2OutputsInTime machine.toFinTM2 (List.map id (tripleInput x.1 x.2.1 x.2.2))
      (some (List.map id (boolBits (decide (x.1 * x.2.1 = x.2.2)))))
      (time.eval (tripleInput x.1 x.2.1 x.2.2).length)
    have h := Machine.outputsInTime machine _ _ _ (factorPolyExec x.1 x.2.1 x.2.2)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
end QEC.Coding.BitTuring.UnaryArithmetic.FactorTest


