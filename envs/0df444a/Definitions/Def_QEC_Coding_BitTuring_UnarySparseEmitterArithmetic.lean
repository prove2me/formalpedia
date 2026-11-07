-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnarySparseEmitterArithmetic
-- name    : QEC_Coding_BitTuring_UnarySparseEmitterArithmetic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:08:10.729356+00:00
-- url     : https://prove2.me/theorems/4a737683-fc7b-4d4a-8593-eb777df1404c
-- title:
--   Unary Sparse Emitter Arithmetic
-- statement:
--   Definitions and structural lemmas for Unary Sparse Emitter Arithmetic, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnarySparseEmitterArithmetic.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_halt_eq

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterSum
open QEC.Coding.BitTuring Turing StateTransition
abbrev Statement:=TM2.Stmt (fun _:Fin 2=>Bool) Unit (Option Bool)
def program (_:Unit):Statement:=
 .pop 0 (fun _ h=>h) (.branch Option.isSome
  (.branch (fun v=>v.getD false)
   (.push 1 (fun _=>true) (.goto fun _=>())) (.goto fun _=>()))
  (.load (fun _=>none) .halt))
def machine:Machine where
 K:=Fin 2;input:=0;output:=1;Λ:=Unit;main:=();σ:=Option Bool;initial:=none;program:=program
def cfg (v:Option Bool) (I O:List Bool):TM2.Cfg (fun _:Fin 2=>Bool) Unit (Option Bool):=
 ⟨some (),v,![I,O]⟩
def halt (O:List Bool):TM2.Cfg (fun _:Fin 2=>Bool) Unit (Option Bool):=⟨none,none,![[],O]⟩
def trueCount:List Bool→ℕ
 | []=>0
 | true::w=>trueCount w+1
 | false::w=>trueCount w
theorem step_true (v:Option Bool) (I O:List Bool):
 TM2.step program (cfg v (true::I) O)=some (cfg (some true) I (true::O)):=by
 simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext k;fin_cases k <;>simp [Function.update]
theorem step_false (v:Option Bool) (I O:List Bool):
 TM2.step program (cfg v (false::I) O)=some (cfg (some false) I O):=by
 simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext k;fin_cases k <;>simp [Function.update]
theorem step_nil (v:Option Bool) (O:List Bool):
 TM2.step program (cfg v [] O)=some (halt O):=by
 simp [TM2.step,program,cfg,halt,TM2.stepAux]
theorem run (w:List Bool) (v:Option Bool) (n:ℕ):
 (fun c=>c.bind (TM2.step program))^[w.length+1] (some (cfg v w (unary n)))=
 some (halt (unary (trueCount w+n))):=by
 induction w generalizing v n with
 | nil=>simp [step_nil,trueCount]
 | cons b w ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  cases b with
  | false=>simp only [Option.bind_some,step_false,trueCount];exact ih (some false) n
  | true=>
   simp only [Option.bind_some,step_true]
   rw [←unary_succ]
   simpa only [trueCount,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (some true) (n+1)
theorem init_eq (w:List Bool):machine.init w=cfg none w []:=by
 simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
 funext k;fin_cases k <;>simp [Function.update]
theorem halt_eq (w:List Bool):halt w=machine.halt w:=by
 simp [Machine.halt,machine,halt,TM2.Cfg.mk.injEq]
 funext k;fin_cases k <;>simp [Function.update]
def exec (w:List Bool):EvalsToInTime (TM2.step machine.program) (machine.init w)
 (some (machine.halt (unary (trueCount w)))) (w.length+1):=by
 refine ⟨⟨w.length+1,?_⟩,le_rfl⟩
 rw [init_eq,←halt_eq]
 change (fun c=>c.bind (TM2.step program))^[w.length+1] (some (cfg none w []))=some (halt (unary (trueCount w)))
 have h:=run w none 0
 simpa only [unary,List.replicate_zero,Nat.add_zero] using h
theorem trueCount_unary_append (n:ℕ) (w:List Bool):trueCount (unary n++w)=n+trueCount w:=by
 induction n with
 | zero=>simp [unary]
 | succ n ih=>simp [unary_succ,trueCount,ih];omega
theorem trueCount_unary (n:ℕ):trueCount (unary n)=n:=by
 have h:=trueCount_unary_append n []
 simpa [trueCount] using h
theorem trueCount_pair (a b:ℕ):trueCount (pairInput a b)=a+b:=by
 simp [pairInput,trueCount_unary_append,trueCount_unary,trueCount]
noncomputable def time:Polynomial ℕ:=Polynomial.X+1
noncomputable def additionExec (a b:ℕ):EvalsToInTime (TM2.step machine.program) (machine.init (pairInput a b))
 (some (machine.halt (unary (a+b)))) (time.eval (pairInput a b).length):=by
 have h:=exec (pairInput a b)
 rw [trueCount_pair] at h
 simpa only [time,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using h
end QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterSum
namespace QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterRowCount
open QEC.Coding.BitTuring Turing StateTransition FieldProjection
abbrev Statement:=TM2.Stmt (fun _:Fin 2=>Bool) (Fin 4) (Option Bool)
def advance (k:Fin 4):Fin 4:=⟨(k.val+1)%4,Nat.mod_lt _ (by decide)⟩
def program (k:Fin 4):Statement:=
 .pop 0 (fun _ h=>h) (.branch Option.isSome
  (.branch (fun v=>v.getD false) (.goto fun _=>k)
   (if k=3 then .push 1 (fun _=>true) (.goto fun _=>0) else .goto fun _=>advance k))
  (.load (fun _=>none) .halt))
def machine:Machine where
 K:=Fin 2;input:=0;output:=1;Λ:=Fin 4;main:=0;σ:=Option Bool;initial:=none;program:=program
def cfg (k:Fin 4) (v:Option Bool) (I O:List Bool):TM2.Cfg (fun _:Fin 2=>Bool) (Fin 4) (Option Bool):=
 ⟨some k,v,![I,O]⟩
def halt (O:List Bool):TM2.Cfg (fun _:Fin 2=>Bool) (Fin 4) (Option Bool):=⟨none,none,![[],O]⟩
def rowCount (k:Fin 4):List Bool→ℕ
 | []=>0
 | true::w=>rowCount k w
 | false::w=>if k=3 then rowCount 0 w+1 else rowCount (advance k) w
theorem step_true (k:Fin 4) (v:Option Bool) (I O:List Bool):
 TM2.step program (cfg k v (true::I) O)=some (cfg k (some true) I O):=by
 simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;>simp [Function.update]
theorem step_sep (k:Fin 4) (v:Option Bool) (I O:List Bool):
 TM2.step program (cfg k v (false::I) O)=
 some (cfg (if k=3 then 0 else advance k) (some false) I (if k=3 then true::O else O)):=by
 by_cases h:k=3 <;>simp [TM2.step,program,cfg,TM2.stepAux,h,TM2.Cfg.mk.injEq]
 all_goals funext j;fin_cases j <;>simp [Function.update]
theorem step_nil (k:Fin 4) (v:Option Bool) (O:List Bool):
 TM2.step program (cfg k v [] O)=some (halt O):=by
 simp [TM2.step,program,cfg,halt,TM2.stepAux]
theorem run (w:List Bool) (k:Fin 4) (v:Option Bool) (n:ℕ):
 (fun c=>c.bind (TM2.step program))^[w.length+1] (some (cfg k v w (unary n)))=
 some (halt (unary (rowCount k w+n))):=by
 induction w generalizing k v n with
 | nil=>simp [step_nil,rowCount]
 | cons b w ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  cases b with
  | true=>simp only [Option.bind_some,step_true,rowCount];exact ih k (some true) n
  | false=>
   simp only [Option.bind_some,step_sep]
   by_cases hk:k=3
   · simp only [hk,if_true]
     rw [←unary_succ]
     simpa only [rowCount,hk,if_true,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih 0 (some false) (n+1)
   · simp only [hk,if_false]
     simpa only [rowCount,hk,if_false] using ih (advance k) (some false) n
theorem init_eq (w:List Bool):machine.init w=cfg 0 none w []:=by
 simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
 funext k;fin_cases k <;>simp [Function.update]
theorem halt_eq (w:List Bool):halt w=machine.halt w:=by
 simp [Machine.halt,machine,halt,TM2.Cfg.mk.injEq]
 funext k;fin_cases k <;>simp [Function.update]
def exec (w:List Bool):EvalsToInTime (TM2.step machine.program) (machine.init w)
 (some (machine.halt (unary (rowCount 0 w)))) (w.length+1):=by
 refine ⟨⟨w.length+1,?_⟩,le_rfl⟩
 rw [init_eq,←halt_eq]
 change (fun c=>c.bind (TM2.step program))^[w.length+1] (some (cfg 0 none w []))=some (halt (unary (rowCount 0 w)))
 have h:=run w 0 none 0
 simpa only [unary,List.replicate_zero,Nat.add_zero] using h
noncomputable def time:Polynomial ℕ:=Polynomial.X+1
end QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterRowCount


