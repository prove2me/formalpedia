-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryModularSum
-- name    : QEC_Coding_BitTuring_UnaryModularSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:06:42.195206+00:00
-- url     : https://prove2.me/theorems/d958a05b-85d0-43ac-a6b5-075eaaa5686b
-- title:
--   Unary Modular Sum
-- statement:
--   Definitions and structural lemmas for Unary Modular Sum, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularSum.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryRemainder
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_halt_eq

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularSum
open Turing StateTransition
abbrev Label := Fin 3 ⊕ Fin 5
abbrev Statement := TM2.Stmt (fun _:Fin 4 => Bool) Label (Option Bool)
def program : Label → Statement
  | .inl 0 => .pop 0 (fun _ h => h) (.branch (fun v => v.getD false)
      (.push 1 (fun _ => true) (.goto fun _ => .inl 0)) (.goto fun _ => .inl 1))
  | .inl 1 => .pop 0 (fun _ h => h) (.branch (fun v => v.getD false)
      (.push 1 (fun _ => true) (.goto fun _ => .inl 1)) (.goto fun _ => .inl 2))
  | .inl _ => .pop 0 (fun _ h => h) (.branch Option.isSome
      (.push 2 (fun _ => true) (.goto fun _ => .inl 2))
      (.load (fun _ => none) (.goto fun _ => .inr 2)))
  | .inr l => liftStatement id Sum.inr id (fun _ w => w) none (Remainder.program l)
def machine : Machine where
  K:=Fin 4
  input:=0
  output:=3
  Λ:=Label
  main:=.inl 0
  σ:=Option Bool
  initial:=none
  program:=program
def cfg (l:Fin 3) (s n q:List Bool) (v:Option Bool) :
    TM2.Cfg (fun _:Fin 4 => Bool) Label (Option Bool) := ⟨some (.inl l),v,![s,n,q,[]]⟩
def embed : TM2.Cfg (fun _:Fin 4 => Bool) (Fin 5) (Option Bool) →
    TM2.Cfg (fun _:Fin 4 => Bool) Label (Option Bool) := liftCfg Sum.inr id id none
theorem stepAuxRem (l:Fin 5) (v:Option Bool) (S:Fin 4 → List Bool) :
    TM2.stepAux (program (.inr l)) v S=embed (TM2.stepAux (Remainder.program l) v S) :=
  stepAux_liftStatement (K:=Fin 4) (K':=Fin 4) (Λ:=Fin 5) (Λ':=Label)
    (σ:=Option Bool) (σ':=Option Bool) id Sum.inr id (fun _ w => w) none id id
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (Remainder.program l) v S
theorem stepRem (c c':TM2.Cfg (fun _:Fin 4 => Bool) (Fin 5) (Option Bool))
    (h:TM2.step Remainder.program c=some c') : TM2.step program (embed c)=some (embed c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    have hh:TM2.stepAux (Remainder.program l) v S=c' := Option.some.inj h
    rw [←hh]
    exact congrArg some (stepAuxRem l v S)
theorem parseA_cons (s n q:List Bool) (v:Option Bool) :
    TM2.step program (cfg 0 (true::s) n q v)=some (cfg 0 s (true::n) q (some true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem parseA_sep (s n q:List Bool) (v:Option Bool) :
    TM2.step program (cfg 0 (false::s) n q v)=some (cfg 1 s n q (some false)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem parseB_cons (s n q:List Bool) (v:Option Bool) :
    TM2.step program (cfg 1 (true::s) n q v)=some (cfg 1 s (true::n) q (some true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem parseB_sep (s n q:List Bool) (v:Option Bool) :
    TM2.step program (cfg 1 (false::s) n q v)=some (cfg 2 s n q (some false)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem parseQ_cons (s n q:List Bool) (v:Option Bool) :
    TM2.step program (cfg 2 (true::s) n q v)=some (cfg 2 s n (true::q) (some true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem parseQ_nil (n q:List Bool) (v:Option Bool) :
    TM2.step program (cfg 2 [] n q v)=some (embed (Remainder.cfg 2 [] n q [] none)) := by
  simp [TM2.step,program,cfg,embed,liftCfg,Remainder.cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
theorem runA (a:ℕ) (s n q:List Bool) (v:Option Bool) :
    (fun c => c.bind (TM2.step program))^[a+1] (some (cfg 0 (unary a++false::s) n q v))=
      some (cfg 1 s (unary a++n) q (some false)) := by
  induction a generalizing n v with
  | zero => simp [unary,parseA_sep]
  | succ a ih =>
    simp only [unary_succ,List.cons_append]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,parseA_cons]
    rw [ih];simp [unary_append_cons]
theorem runB (b:ℕ) (s n q:List Bool) (v:Option Bool) :
    (fun c => c.bind (TM2.step program))^[b+1] (some (cfg 1 (unary b++false::s) n q v))=
      some (cfg 2 s (unary b++n) q (some false)) := by
  induction b generalizing n v with
  | zero => simp [unary,parseB_sep]
  | succ b ih =>
    simp only [unary_succ,List.cons_append]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,parseB_cons]
    rw [ih];simp [unary_append_cons]
theorem runQ (q:ℕ) (n d:List Bool) (v:Option Bool) :
    (fun c => c.bind (TM2.step program))^[q+1] (some (cfg 2 (unary q) n d v))=
      some (embed (Remainder.cfg 2 [] n (unary q++d) [] none)) := by
  induction q generalizing d v with
  | zero => simp [unary,parseQ_nil]
  | succ q ih =>
    simp only [unary_succ]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,parseQ_cons]
    rw [ih];simp [unary_append_cons]
theorem parse_run (a b q:ℕ) :
    (fun c => c.bind (TM2.step program))^[a+b+q+3]
      (some (cfg 0 (FactorTest.tripleInput a b q) [] [] none))=
      some (embed (Remainder.cfg 2 [] (unary (a+b)) (unary q) [] none)) := by
  rw [show a+b+q+3=((q+1)+(b+1))+(a+1) by omega,Function.iterate_add_apply]
  simp only [FactorTest.tripleInput,pairInput]
  rw [runA,Function.iterate_add_apply,runB]
  simp only [List.append_nil]
  rw [←unary_add,show b+a=a+b by omega]
  simpa only [List.append_nil] using runQ q (unary (a+b)) [] (some false)
def steps (a b q:ℕ) : ℕ := a+b+2*q+4+((a+b)/q)*(2*q+2)
theorem init_eq (a b q:ℕ) : machine.init (FactorTest.tripleInput a b q)=
    cfg 0 (FactorTest.tripleInput a b q) [] [] none := by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem halt_eq (y:List Bool) : embed (Remainder.halt y)=machine.halt y := by
  simp [embed,liftCfg,Remainder.halt,Machine.halt,machine,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem run (a b q:ℕ) (hq:0<q) :
    (fun c => c.bind (TM2.step machine.program))^[steps a b q]
      (some (machine.init (FactorTest.tripleInput a b q)))=some (machine.halt (unary ((a+b)%q))) := by
  rw [init_eq]
  change (fun c => c.bind (TM2.step program))^[steps a b q]
    (some (cfg 0 (FactorTest.tripleInput a b q) [] [] none))=some (machine.halt (unary ((a+b)%q)))
  rw [show steps a b q=((a+b)/q*(2*q+2)+(q+1))+(a+b+q+3) by simp [steps];omega,
    Function.iterate_add_apply,parse_run]
  have h:=iterate_lift (TM2.step Remainder.program) (TM2.step program) embed stepRem _ _ _
    (Remainder.run_body (a+b) q hq none)
  rw [halt_eq] at h
  exact h
def exec (a b q:ℕ) (hq:0<q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (FactorTest.tripleInput a b q))
      (some (machine.halt (unary ((a+b)%q)))) (steps a b q) :=
  ⟨⟨steps a b q,run a b q hq⟩,le_refl _⟩
theorem steps_le (a b q:ℕ) : steps a b q≤5*((FactorTest.tripleInput a b q).length+1) := by
  rw [FactorTest.tripleInput_length]
  have hd:(a+b)/q≤a+b := Nat.div_le_self _ _
  have hm:(a+b)/q*q≤a+b := Nat.div_mul_le_self _ _
  have hh:(a+b)/q*(2*q+2)≤4*(a+b) := by
    calc
      _=2*((a+b)/q*q)+2*((a+b)/q) := by ring
      _≤2*(a+b)+2*(a+b) := Nat.add_le_add (Nat.mul_le_mul_left 2 hm) (Nat.mul_le_mul_left 2 hd)
      _=4*(a+b) := by ring
  simp only [steps];omega
noncomputable def time : Polynomial ℕ := Polynomial.C 5*(Polynomial.X+1)
noncomputable def polyExec (a b q:ℕ) (hq:0<q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (FactorTest.tripleInput a b q))
      (some (machine.halt (unary ((a+b)%q)))) (time.eval (FactorTest.tripleInput a b q).length) := by
  have h:=exec a b q hq
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  simpa [time] using steps_le a b q
noncomputable def outputsInTime (a b q : ℕ) (hq : 0<q) :
    TM2OutputsInTime machine.toFinTM2 (FactorTest.tripleInput a b q)
      (some (unary ((a+b)%q))) (time.eval (FactorTest.tripleInput a b q).length) :=
  Machine.outputsInTime machine _ _ _ (polyExec a b q hq)
noncomputable def outputsZModSumInTime (a b q : ℕ) (hq : 0<q) :
    TM2OutputsInTime machine.toFinTM2 (FactorTest.tripleInput a b q)
      (some (unary (((a:ZMod q)+(b:ZMod q)).val)))
      (time.eval (FactorTest.tripleInput a b q).length) := by
  let : NeZero q := ⟨hq.ne'⟩
  simpa only [←Nat.cast_add,ZMod.val_natCast] using outputsInTime a b q hq
def input (x : ℕ×(ℕ×ℕ+)) : List Bool := FactorTest.tripleInput x.1 x.2.1 x.2.2.val
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input unary
    (fun x:ℕ×(ℕ×ℕ+) => (x.1+x.2.1)%x.2.2.val) where
  tm := machine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun := fun x => by
    change TM2OutputsInTime machine.toFinTM2 (List.map id (input x))
      (some (List.map id (unary ((x.1+x.2.1)%x.2.2.val)))) (time.eval (input x).length)
    have h := outputsInTime x.1 x.2.1 x.2.2.val x.2.2.pos
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input] using h
end QEC.Coding.BitTuring.UnaryArithmetic.ModularSum


