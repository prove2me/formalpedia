-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixReverseDrop
-- name    : QEC_Coding_BitTuring_UnaryPrefixReverseDrop
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:57:33.542835+00:00
-- url     : https://prove2.me/theorems/2f4496ba-211d-49f2-a81d-69bd7fed5404
-- title:
--   Unary Prefix Reverse Drop
-- statement:
--   Definitions and structural lemmas for Unary Prefix Reverse Drop, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPrefixReverseDrop.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.PrefixReverseDrop
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
abbrev Label (n:ℕ):=Fin (n+2)
abbrev Statement (n:ℕ):=TM2.Stmt (fun _:Fin 2=>Bool) (Label n) (Option Bool)
def tailLabel (n:ℕ):Label n:=⟨n,by omega⟩
def endLabel (n:ℕ):Label n:=⟨n+1,by omega⟩
def program (n:ℕ) (k:Label n):Statement n:=
 if h:k.val<n then .pop 0 (fun _ h=>h) (.branch (fun v=>v.getD false)
  (.goto fun _=>k) (.goto fun _=>⟨k.val+1,by omega⟩))
 else if k.val=n then .pop 0 (fun _ h=>h) (.branch Option.isSome
  (.push 1 (fun v=>v.getD false) (.goto fun _=>tailLabel n)) (.goto fun _=>endLabel n))
 else .pop 1 (fun _ h=>h) (.load (fun _=>none) .halt)
def machine (n:ℕ):Machine where
 K:=Fin 2;input:=0;output:=1;Λ:=Label n;main:=0;σ:=Option Bool;initial:=none;program:=program n
def cfg (n:ℕ) (k:Label n) (h:Option Bool) (I O:List Bool):
 TM2.Cfg (fun _:Fin 2=>Bool) (Label n) (Option Bool):=⟨some k,h,![I,O]⟩
theorem field_bit (n:ℕ) (k:Label n) (h:Option Bool) (I O:List Bool) (hk:k.val<n):
 TM2.step (program n) (cfg n k h (true::I) O)=some (cfg n k (some true) I O):=by
 simp [TM2.step,program,cfg,TM2.stepAux,hk,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;>simp [Function.update]
theorem field_sep (n:ℕ) (k:Label n) (h:Option Bool) (I O:List Bool) (hk:k.val<n):
 TM2.step (program n) (cfg n k h (false::I) O)=
 some (cfg n ⟨k.val+1,by omega⟩ (some false) I O):=by
 simp [TM2.step,program,cfg,TM2.stepAux,hk,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;>simp [Function.update]
theorem field_run (n:ℕ) (k:Label n) (h:Option Bool) (a:ℕ) (I O:List Bool) (hk:k.val<n):
 (fun c=>c.bind (TM2.step (program n)))^[a+1] (some (cfg n k h (unary a++false::I) O))=
 some (cfg n ⟨k.val+1,by omega⟩ (some false) I O):=by
 induction a generalizing h with
 |zero=>simp [unary,field_sep n k h I O hk]
 |succ a ih=>
  simp only [unary_succ,List.cons_append]
  rw [Function.iterate_succ_apply]
  simp only [Option.bind_some,field_bit n k h _ O hk]
  exact ih (some true)
theorem parse_run (n:ℕ) (xs:List ℕ) (k:Label n) (h:Option Bool) (I O:List Bool)
 (hk:k.val+xs.length=n):
 (fun c=>c.bind (TM2.step (program n)))^[(stream xs).length] (some (cfg n k h (stream xs++I) O))=
 some (cfg n (tailLabel n) (if xs=[] then h else some false) I O):=by
 induction xs generalizing k h with
 |nil=>
  have he:k=tailLabel n:=by apply Fin.ext;simp only [List.length_nil] at hk;exact hk
  subst k;simp [stream]
 |cons a xs ih=>
  have hl:k.val<n:=by simp only [List.length_cons] at hk;omega
  let j:Label n:=⟨k.val+1,by omega⟩
  have ht:=ih j (some false) (by dsimp [j];simp only [List.length_cons] at hk;omega)
  have hs:(stream (a::xs)).length=(stream xs).length+(a+1):=by
   simp only [stream,List.length_append,List.length_cons,unary_length];omega
  rw [hs,Function.iterate_add_apply]
  have he:stream (a::xs)++I=unary a++false::(stream xs++I):=by
   simp only [stream,List.append_assoc,List.cons_append]
  rw [he,field_run n k h a (stream xs++I) O hl,ht]
  cases xs <;> simp
theorem tail_cons (n:ℕ) (h:Option Bool) (a:Bool) (I O:List Bool):
 TM2.step (program n) (cfg n (tailLabel n) h (a::I) O)=
 some (cfg n (tailLabel n) (some a) I (a::O)):=by
 simp [TM2.step,program,cfg,tailLabel,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;>simp [Function.update]
theorem tail_nil (n:ℕ) (h:Option Bool) (O:List Bool):
 TM2.step (program n) (cfg n (tailLabel n) h [] O)=some (cfg n (endLabel n) none [] O):=by
 simp [TM2.step,program,cfg,tailLabel,TM2.stepAux]
theorem tail_run (n:ℕ) (h:Option Bool) (I O:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[I.length+1] (some (cfg n (tailLabel n) h I O))=
 some (cfg n (endLabel n) none [] (I.reverse++O)):=by
 induction I generalizing h O with
 |nil=>simp [tail_nil]
 |cons a I ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,tail_cons]
  rw [ih]
  simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
theorem final_step (n:ℕ) (h:Option Bool) (O:List Bool):
 TM2.step (program n) (cfg n (endLabel n) h [] O)=some ((machine n).halt (O.drop 1)):=by
 simp [TM2.step,program,cfg,endLabel,TM2.stepAux,Machine.halt,machine,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;>simp [Function.update]
theorem init_eq (n:ℕ) (w:List Bool):(machine n).init w=cfg n 0 none w []:=by
 simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;>simp [Function.update]
theorem run (n:ℕ) (xs:List ℕ) (s:List Bool) (hlen:xs.length=n):
 (fun c=>c.bind (TM2.step (machine n).program))^[(stream xs++s).length+2]
  (some ((machine n).init (stream xs++s)))=some ((machine n).halt (s.reverse.drop 1)):=by
 rw [init_eq]
 change (fun c=>c.bind (TM2.step (program n)))^[(stream xs++s).length+2]
  (some (cfg n 0 none (stream xs++s) []))=_
 have ht:(stream xs++s).length+2=1+(s.length+1)+(stream xs).length:=by simp;omega
 rw [ht,Function.iterate_add_apply,parse_run n xs 0 none s [] (by simpa using hlen),
  Function.iterate_add_apply,tail_run]
 simp only [Function.iterate_one,Option.bind_some,List.append_nil]
 exact final_step n none s.reverse
def exec (n:ℕ) (xs:List ℕ) (s:List Bool) (hlen:xs.length=n):
 EvalsToInTime (TM2.step (machine n).program) ((machine n).init (stream xs++s))
  (some ((machine n).halt (s.reverse.drop 1))) ((stream xs++s).length+2):=
 ⟨⟨(stream xs++s).length+2,run n xs s hlen⟩,le_refl _⟩
end QEC.Coding.BitTuring.UnaryArithmetic.PrefixReverseDrop


