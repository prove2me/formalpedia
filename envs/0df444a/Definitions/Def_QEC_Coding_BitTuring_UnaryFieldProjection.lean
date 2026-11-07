-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
-- name    : QEC_Coding_BitTuring_UnaryFieldProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:07:08.383245+00:00
-- url     : https://prove2.me/theorems/2ee31e24-9d3d-44a7-8414-b1139ce22c6d
-- title:
--   Unary Field Projection
-- statement:
--   Definitions and structural lemmas for Unary Field Projection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldProjection.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_halt_eq
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
open Turing StateTransition
variable (n:ℕ) (keep:Fin (n+1) → Bool)
abbrev Label (n:ℕ) := Fin (n+1) ⊕ Unit
abbrev Statement (n:ℕ) := TM2.Stmt (fun _:Fin 3 => Bool) (Label n) (Option Bool)
def nextStatement (k:Fin (n+1)) : Statement n :=
  if h:k.val<n then .goto (fun _ => .inl ⟨k.val+1,Nat.succ_lt_succ h⟩)
  else .pop 1 (fun _ _ => none) (.goto fun _ => .inr ())
def program : Label n → Statement n
  | .inl k => .pop 0 (fun _ h => h) (.branch (fun v => v.getD false)
      (if keep k then .push 1 (fun _ => true) (.goto fun _ => .inl k) else .goto fun _ => .inl k)
      (if keep k then .push 1 (fun _ => false) (nextStatement n k) else nextStatement n k))
  | .inr _ => liftStatement id (fun _ => .inr ()) id (fun _ w => w) none (copyProgram false)
def machine : Machine where
  K:=Fin 3
  input:=0
  output:=2
  Λ:=Label n
  main:=.inl 0
  σ:=Option Bool
  initial:=none
  program:=program n keep
def cfg (k:Fin (n+1)) (s b d:List Bool) (v:Option Bool) :
    TM2.Cfg (fun _:Fin 3 => Bool) (Label n) (Option Bool) := ⟨some (.inl k),v,![s,b,d]⟩
def revCfg (s b d:List Bool) (v:Option Bool) :
    TM2.Cfg (fun _:Fin 3 => Bool) (Label n) (Option Bool) := ⟨some (.inr ()),v,![s,b,d]⟩
def halt (d:List Bool) : TM2.Cfg (fun _:Fin 3 => Bool) (Label n) (Option Bool) :=
  ⟨none,none,![[],[],d]⟩
theorem bit_step (k:Fin (n+1)) (s b d:List Bool) (v:Option Bool) :
    TM2.step (program n keep) (cfg n k (true::s) b d v)=
      some (cfg n k s (if keep k then true::b else b) d (some true)) := by
  cases hk:keep k <;> simp [TM2.step,program,cfg,TM2.stepAux,hk,TM2.Cfg.mk.injEq] <;>
    (funext j;fin_cases j <;> simp [Function.update])
theorem sep_step_lt (k:Fin (n+1)) (hk:k.val<n) (s b d:List Bool) (v:Option Bool) :
    TM2.step (program n keep) (cfg n k (false::s) b d v)=
      some (cfg n ⟨k.val+1,Nat.succ_lt_succ hk⟩ s
        (if keep k then false::b else b) d (some false)) := by
  cases h:keep k <;> simp [TM2.step,program,cfg,nextStatement,TM2.stepAux,h,hk,TM2.Cfg.mk.injEq] <;>
    (funext j;fin_cases j <;> simp [Function.update])
theorem sep_step_last (k:Fin (n+1)) (hk:k.val=n) (s b d:List Bool) (v:Option Bool) :
    TM2.step (program n keep) (cfg n k (false::s) b d v)=
      some (revCfg n s ((if keep k then false::b else b).tail) d none) := by
  have hkn:¬k.val<n := by omega
  cases h:keep k <;> simp [TM2.step,program,cfg,revCfg,nextStatement,TM2.stepAux,h,hkn,TM2.Cfg.mk.injEq] <;>
    (funext j;fin_cases j <;> simp [Function.update])
theorem reverse_cons (x:Bool) (b d:List Bool) (v:Option Bool) :
    TM2.step (program n keep) (revCfg n [] (x::b) d v)=
      some (revCfg n [] b (x::d) (some x)) := by
  simp [TM2.step,program,revCfg,copyProgram,liftStatement,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext j;fin_cases j <;> simp [Function.update]
theorem reverse_nil (d:List Bool) (v:Option Bool) :
    TM2.step (program n keep) (revCfg n [] [] d v)=some (halt n d) := by
  simp [TM2.step,program,revCfg,halt,copyProgram,liftStatement,TM2.stepAux,TM2.Cfg.mk.injEq]
theorem reverse_run (b d:List Bool) (v:Option Bool) :
    (fun c => c.bind (TM2.step (program n keep)))^[b.length+1]
      (some (revCfg n [] b d v))=some (halt n (b.reverse++d)) := by
  induction b generalizing d v with
  | nil => simp [reverse_nil]
  | cons x b ih =>
    simp only [List.length_cons]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,reverse_cons]
    rw [ih];simp [List.reverse_cons,List.append_assoc]
theorem field_lt (k:Fin (n+1)) (hk:k.val<n) (a:ℕ) (s b d:List Bool) (v:Option Bool) :
    (fun c => c.bind (TM2.step (program n keep)))^[a+1]
      (some (cfg n k (unary a++false::s) b d v))=
      some (cfg n ⟨k.val+1,Nat.succ_lt_succ hk⟩ s
        (if keep k then false::(unary a++b) else b) d (some false)) := by
  induction a generalizing b v with
  | zero => simp [unary,sep_step_lt n keep k hk]
  | succ a ih =>
    simp only [unary_succ,List.cons_append]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,bit_step]
    rw [ih]
    cases h:keep k <;> simp [unary_append_cons]
theorem field_last (k:Fin (n+1)) (hk:k.val=n) (a:ℕ) (s b d:List Bool) (v:Option Bool) :
    (fun c => c.bind (TM2.step (program n keep)))^[a+1]
      (some (cfg n k (unary a++false::s) b d v))=
      some (revCfg n s ((if keep k then false::(unary a++b) else b).tail) d none) := by
  induction a generalizing b v with
  | zero => simp [unary,sep_step_last n keep k hk]
  | succ a ih =>
    simp only [unary_succ,List.cons_append]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,bit_step]
    rw [ih]
    cases h:keep k <;> simp [unary_append_cons]
def stream : List ℕ → List Bool
  | [] => []
  | a::xs => unary a++false::stream xs
def maskAt (i:ℕ) : Bool := keep ⟨i%(n+1),Nat.mod_lt _ (by omega)⟩
theorem maskAt_val (k:Fin (n+1)) : maskAt n keep k.val=keep k := by
  simp only [maskAt,Nat.mod_eq_of_lt k.isLt]
def buffer : ℕ → List ℕ → List Bool → List Bool
  | _,[],b => b
  | i,a::xs,b => buffer (i+1) xs (if maskAt n keep i then false::(unary a++b) else b)
theorem parse_fields (xs:List ℕ) (k:Fin (n+1)) (hk:k.val+xs.length=n+1) (hne:xs≠[])
    (b d:List Bool) (v:Option Bool) :
    (fun c => c.bind (TM2.step (program n keep)))^[(stream xs).length]
      (some (cfg n k (stream xs) b d v))=
      some (revCfg n [] (buffer n keep k.val xs b).tail d none) := by
  induction xs generalizing k b d v with
  | nil => exact False.elim (hne rfl)
  | cons a xs ih =>
    cases xs with
    | nil =>
      have hkl:k.val=n := by simp only [List.length_cons,List.length_nil] at hk;omega
      have h:=field_last n keep k hkl a [] b d v
      simpa only [stream,List.length_append,List.length_cons,List.length_nil,unary_length,
        List.append_nil,buffer,maskAt_val] using h
    | cons c xs =>
      have hkl:k.val<n := by simp only [List.length_cons] at hk;omega
      rw [show (stream (a::c::xs)).length=(stream (c::xs)).length+(a+1) by
        change (unary a++false::stream (c::xs)).length=_
        simp only [List.length_append,List.length_cons,unary_length];omega]
      change (fun c => c.bind (TM2.step (program n keep)))^[(stream (c::xs)).length+(a+1)]
        (some (cfg n k (unary a++false::stream (c::xs)) b d v))=_
      rw [Function.iterate_add_apply,field_lt n keep k hkl]
      have htail:(⟨k.val+1,Nat.succ_lt_succ hkl⟩:Fin (n+1)).val+(c::xs).length=n+1 := by
        simp only [List.length_cons] at hk ⊢;omega
      have h:=ih ⟨k.val+1,Nat.succ_lt_succ hkl⟩ htail (by simp)
        (if keep k then false::(unary a++b) else b) d (some false)
      simpa only [buffer,maskAt_val] using h
theorem buffer_length_le (i:ℕ) (xs:List ℕ) (b:List Bool) :
    (buffer n keep i xs b).length≤(stream xs).length+b.length := by
  induction xs generalizing i b with
  | nil => simp [buffer,stream]
  | cons a xs ih =>
    have h:=ih (i+1) (if maskAt n keep i then false::(unary a++b) else b)
    cases hm:maskAt n keep i <;>
      simp only [buffer,hm,Bool.false_eq_true,↓reduceIte,
        List.length_cons,List.length_append,unary_length,stream] at h ⊢ <;> omega
def fields : ℕ→List ℕ→List ℕ
  | _,[]=>[]
  | i,a::xs=>if maskAt n keep i then a::fields (i+1) xs else fields (i+1) xs
theorem buffer_eq (i:ℕ) (xs:List ℕ) (b:List Bool) :
    buffer n keep i xs b=(stream (fields n keep i xs)).reverse++b := by
  induction xs generalizing i b with
  | nil => simp [buffer,fields,stream]
  | cons a xs ih =>
    cases hm:maskAt n keep i <;>
      simp [buffer,fields,hm,ih,stream,List.reverse_append,unary,List.append_assoc]
def raw (xs:List ℕ) := (stream xs).dropLast
theorem buffer_output (xs:List ℕ) :
    (buffer n keep 0 xs []).tail.reverse=raw (fields n keep 0 xs) := by
  rw [buffer_eq]
  simp [raw]
def steps (xs:List ℕ) := (stream xs).length+(buffer n keep 0 xs []).tail.length+1
theorem init_eq (xs:List ℕ) : (machine n keep).init (stream xs)=
    cfg n 0 (stream xs) [] [] none := by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem halt_eq (y:List Bool) : halt n y=(machine n keep).halt y := by
  simp [halt,Machine.halt,machine,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem run (xs:List ℕ) (hx:xs.length=n+1) :
    (fun c=>c.bind (TM2.step (machine n keep).program))^[steps n keep xs]
      (some ((machine n keep).init (stream xs)))=
      some ((machine n keep).halt (raw (fields n keep 0 xs))) := by
  rw [init_eq]
  change (fun c=>c.bind (TM2.step (program n keep)))^[steps n keep xs]
    (some (cfg n 0 (stream xs) [] [] none))=_
  rw [show steps n keep xs=((buffer n keep 0 xs []).tail.length+1)+(stream xs).length by
    simp only [steps];omega,Function.iterate_add_apply,
    parse_fields n keep xs 0 (by simpa using hx) (by intro h;subst xs;simp at hx)]
  have h:=reverse_run n keep (buffer n keep 0 xs []).tail [] none
  rw [buffer_output,List.append_nil,halt_eq] at h
  exact h
def exec (xs:List ℕ) (hx:xs.length=n+1) :
    EvalsToInTime (TM2.step (machine n keep).program) ((machine n keep).init (stream xs))
      (some ((machine n keep).halt (raw (fields n keep 0 xs)))) (steps n keep xs) :=
  ⟨⟨steps n keep xs,run n keep xs hx⟩,le_refl _⟩
theorem steps_le (xs:List ℕ) : steps n keep xs≤2*(stream xs).length+1 := by
  have h:=buffer_length_le n keep 0 xs []
  have ht:(buffer n keep 0 xs []).tail.length≤(buffer n keep 0 xs []).length := by
    simp only [List.length_tail];omega
  simp only [List.length_nil,Nat.add_zero,steps] at h ⊢
  omega
noncomputable def time : Polynomial ℕ := Polynomial.C 2*Polynomial.X+1
noncomputable def polyExec (xs:List ℕ) (hx:xs.length=n+1) :
    EvalsToInTime (TM2.step (machine n keep).program) ((machine n keep).init (stream xs))
      (some ((machine n keep).halt (raw (fields n keep 0 xs))))
      (time.eval (stream xs).length) := by
  have h:=exec n keep xs hx
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  simpa [time] using steps_le n keep xs
def Input := {xs:List ℕ//xs.length=n+1}
def input (x:Input n) := stream x.val
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime (input n) id (fun x:Input n=>raw (fields n keep 0 x.val)) where
  tm:=(machine n keep).toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time
  outputsFun:=fun x=>by
    change TM2OutputsInTime (machine n keep).toFinTM2 (List.map id (input n x))
      (some (List.map id (raw (fields n keep 0 x.val)))) (time.eval (input n x).length)
    have h:=Machine.outputsInTime (machine n keep) _ _ _ (polyExec n keep x.val x.property)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input] using h
end QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
end QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
end QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection


