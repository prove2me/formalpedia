-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
-- name    : QEC_Coding_BitTuring_FixedLiteral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:03:50.795957+00:00
-- url     : https://prove2.me/theorems/974cd84a-3f78-4c9a-a9a1-ac20e392f980
-- title:
--   Fixed Literal
-- statement:
--   Definitions and structural lemmas for Fixed Literal, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/FixedLiteral.lean

import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
set_option autoImplicit false
namespace QEC.Coding.BitTuring.FixedLiteral
open Turing StateTransition
abbrev Statement := TM2.Stmt (fun _:Fin 2=>Bool) Bool (Option Bool)
def write : List Bool → Statement
  | []=>.load (fun _=>none) .halt
  | b::bs=>.push 1 (fun _=>b) (write bs)
def program (w:List Bool) : Bool→Statement
  | true=>.pop 0 (fun _ h=>h) (.branch (fun h=>h.isSome)
      (.goto fun _=>true) (.goto fun _=>false))
  | false=>write w.reverse
def machine (w:List Bool) : Machine where
  K:=Fin 2;input:=0;output:=1;Λ:=Bool;main:=true;σ:=Option Bool;initial:=none;program:=program w
def cfg (l:Bool) (s d:List Bool) (v:Option Bool) :
    TM2.Cfg (fun _:Fin 2=>Bool) Bool (Option Bool) := ⟨some l,v,![s,d]⟩
theorem push_tapes (s d:List Bool) (b:Bool) :
    Function.update (![s,d]:Fin 2→List Bool) 1 (b::d)=![s,b::d] := by
  funext k;fin_cases k <;> simp [Function.update]
theorem write_aux (w s d:List Bool) (v:Option Bool) :
    TM2.stepAux (write w) v ![s,d]=⟨none,none,![s,w.reverse++d]⟩ := by
  induction w generalizing d v with
  | nil=>simp [write,TM2.stepAux]
  | cons b bs ih=>
      simp only [write,TM2.stepAux,Matrix.cons_val_one,Matrix.cons_val_zero,push_tapes]
      simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using ih (b::d) v
theorem drain_cons (w:List Bool) (b:Bool) (s d:List Bool) (v:Option Bool) :
    TM2.step (program w) (cfg true (b::s) d v)=some (cfg true s d (some b)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem drain_nil (w d:List Bool) (v:Option Bool) :
    TM2.step (program w) (cfg true [] d v)=some (cfg false [] d none) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
theorem drain_run (w s d:List Bool) (v:Option Bool) :
    (fun c=>c.bind (TM2.step (program w)))^[s.length+1] (some (cfg true s d v))=
      some (cfg false [] d none) := by
  induction s generalizing v with
  | nil=>simp [drain_nil]
  | cons b bs ih=>
      rw [List.length_cons,Nat.add_right_comm,Function.iterate_succ_apply]
      simp only [Option.bind_some,drain_cons]
      exact ih (some b)
theorem init_eq (w s:List Bool) : (machine w).init s=cfg true s [] none := by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem emit (w:List Bool) : TM2.step (program w) (cfg false [] [] none)=
    some ((machine w).halt w) := by
  simp only [TM2.step,cfg,program,write_aux,List.reverse_reverse,List.append_nil]
  simp [Machine.halt,machine,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
def exec (w s:List Bool) : EvalsToInTime (TM2.step (machine w).program) ((machine w).init s)
    (some ((machine w).halt w)) (s.length+2) := by
  refine ⟨⟨s.length+2,?_⟩,le_refl _⟩
  rw [init_eq]
  change (fun c=>c.bind (TM2.step (program w)))^[s.length+2] (some (cfg true s [] none))=_
  rw [show s.length+2=1+(s.length+1) by omega,Function.iterate_add_apply,drain_run]
  simp only [Function.iterate_one,Option.bind_some,emit]
  rfl
noncomputable def time : Polynomial ℕ := Polynomial.X+Polynomial.C 2
noncomputable def polyExec (w s:List Bool) : EvalsToInTime (TM2.step (machine w).program)
    ((machine w).init s) (some ((machine w).halt w)) (time.eval s.length) := by
  simpa only [time,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C] using exec w s
noncomputable def computableInPolyTime (w:List Bool) : TM2ComputableInPolyTime id id (fun _:List Bool=>w) where
  tm:=(machine w).toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time
  outputsFun:=fun s=>by
    change TM2OutputsInTime (machine w).toFinTM2 (List.map id s) (some (List.map id w)) (time.eval s.length)
    have h:=Machine.outputsInTime (machine w) _ _ _ (polyExec w s)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
def prefixMachine (w:List Bool) := RetainedInput.machine (machine w)
noncomputable def prefixTime (w:List Bool) : Polynomial ℕ :=
  Polynomial.C 4*Polynomial.X+Polynomial.C (2*w.length+8)
noncomputable def prefixExec (w s:List Bool) :
    EvalsToInTime (TM2.step (prefixMachine w).program) ((prefixMachine w).init s)
      (some ((prefixMachine w).halt (w++s))) ((prefixTime w).eval s.length) := by
  have h:=RetainedInput.executes (machine w) s w _ (exec w s)
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  simp only [prefixTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  omega
end QEC.Coding.BitTuring.FixedLiteral


