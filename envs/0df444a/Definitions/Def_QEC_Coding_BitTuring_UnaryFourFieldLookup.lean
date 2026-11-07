-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldLookup
-- name    : QEC_Coding_BitTuring_UnaryFourFieldLookup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:57:16.56633+00:00
-- url     : https://prove2.me/theorems/6b4544a2-7645-4bee-963e-9bfac6d1ff55
-- title:
--   Unary Four Field Lookup
-- statement:
--   Definitions and structural lemmas for Unary Four Field Lookup, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldLookup.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_halt_eq
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_append_last
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_length_le
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_length
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
abbrev Label:=(Bool×Fin 4)⊕Fin 4
abbrev Statement:=TM2.Stmt (fun _:Fin 3=>Bool) Label (Option Bool)
def fieldNext (copy:Bool) (k:Fin 4):Statement:=
 if h:k.val<3 then
  if copy then .push 2 (fun _=>false) (.goto fun _=>.inl (copy,⟨k.val+1,by omega⟩))
  else .goto fun _=>.inl (copy,⟨k.val+1,by omega⟩)
 else .goto fun _=>.inr (if copy then 3 else 2)
def program:Label→Statement
 | .inl (copy,k)=>.pop 0 (fun _ h=>h) (.branch (fun v=>v.getD false)
   (if copy then .push 2 (fun _=>true) (.goto fun _=>.inl (copy,k))
    else .goto fun _=>.inl (copy,k)) (fieldNext copy k))
 | .inr 0=>.pop 0 (fun _ h=>h) (.branch (fun v=>v.getD false)
   (.goto fun _=>.inr 0) (.goto fun _=>.inr 1))
 | .inr 1=>.pop 0 (fun _ h=>h) (.branch (fun v=>v.getD false)
   (.push 1 (fun _=>true) (.goto fun _=>.inr 1)) (.goto fun _=>.inr 2))
 | .inr 2=>.pop 1 (fun _ h=>h) (.branch Option.isSome
   (.goto fun _=>.inl (false,0)) (.goto fun _=>.inl (true,0)))
 | .inr _=>.pop 0 (fun _ h=>h) (.branch Option.isSome
   (.goto fun _=>.inr 3) (.load (fun _=>none) .halt))
def machine:Machine where
 K:=Fin 3;input:=0;output:=2;Λ:=Label;main:=.inr 0;σ:=Option Bool;initial:=none;program:=program
def cfg (l:Label) (h:Option Bool) (I C O:List Bool):
 TM2.Cfg (fun _:Fin 3=>Bool) Label (Option Bool):=⟨some l,h,![I,C,O]⟩
def next (c:Option (TM2.Cfg (fun _:Fin 3=>Bool) Label (Option Bool))):=c.bind (TM2.step program)
def halt (w:List Bool):TM2.Cfg (fun _:Fin 3=>Bool) Label (Option Bool):=⟨none,none,![[],[],w]⟩
theorem halt_eq (w:List Bool):halt w=machine.halt w:=by
 simp [halt,Machine.halt,machine,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;>simp [Function.update]
theorem init_eq (w:List Bool):machine.init w=cfg (.inr 0) none w [] []:=by
 simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;>simp [Function.update]
theorem q_bit (h:Option Bool) (I C O:List Bool):
 TM2.step program (cfg (.inr 0) h (true::I) C O)=some (cfg (.inr 0) (some true) I C O):=by
 simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;>simp [Function.update]
theorem q_sep (h:Option Bool) (I C O:List Bool):
 TM2.step program (cfg (.inr 0) h (false::I) C O)=some (cfg (.inr 1) (some false) I C O):=by
 simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;>simp [Function.update]
theorem q_run (h:Option Bool) (q:ℕ) (I C O:List Bool):
 next^[q+1] (some (cfg (.inr 0) h (unary q++false::I) C O))=
 some (cfg (.inr 1) (some false) I C O):=by
 induction q generalizing h with
 | zero=>simp [unary,next,q_sep]
 | succ q ih=>
  simp only [unary_succ,List.cons_append]
  rw [Function.iterate_succ_apply]
  simp only [next,Option.bind_some,q_bit]
  exact ih (some true)
theorem index_bit (h:Option Bool) (I C O:List Bool):
 TM2.step program (cfg (.inr 1) h (true::I) C O)=some (cfg (.inr 1) (some true) I (true::C) O):=by
 simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;>simp [Function.update]
theorem index_sep (h:Option Bool) (I C O:List Bool):
 TM2.step program (cfg (.inr 1) h (false::I) C O)=some (cfg (.inr 2) (some false) I C O):=by
 simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;>simp [Function.update]
theorem unary_append_true (i:ℕ) (w:List Bool):unary i++true::w=true::(unary i++w):=by
 induction i with
 | zero=>rfl
 | succ i ih=>
  simp only [unary_succ,List.cons_append]
  rw [ih]
theorem index_run (h:Option Bool) (i:ℕ) (I C O:List Bool):
 next^[i+1] (some (cfg (.inr 1) h (unary i++false::I) C O))=
 some (cfg (.inr 2) (some false) I (unary i++C) O):=by
 induction i generalizing h C with
 | zero=>simp [unary,next,index_sep]
 | succ i ih=>
  simp only [unary_succ,List.cons_append]
  rw [Function.iterate_succ_apply]
  simp only [next,Option.bind_some,index_bit]
  rw [ih]
  rw [unary_append_true]
theorem choose_skip (h:Option Bool) (I C O:List Bool):
 TM2.step program (cfg (.inr 2) h (I) (true::C) O)=some (cfg (.inl (false,0)) (some true) I C O):=by
 simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;>simp [Function.update]
theorem choose_copy (h:Option Bool) (I O:List Bool):
 TM2.step program (cfg (.inr 2) h I [] O)=some (cfg (.inl (true,0)) none I [] O):=by
 simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
def afterField (copy:Bool) (k:Fin 4):Label:=
 if h:k.val<3 then .inl (copy,⟨k.val+1,by omega⟩) else .inr (if copy then 3 else 2)
def fieldOutput (copy:Bool) (k:Fin 4) (a:ℕ) (O:List Bool):List Bool:=
 if copy then (if k.val<3 then false::(unary a++O) else unary a++O) else O
theorem field_bit (copy:Bool) (k:Fin 4) (h:Option Bool) (I C O:List Bool):
 TM2.step program (cfg (.inl (copy,k)) h (true::I) C O)=
 some (cfg (.inl (copy,k)) (some true) I C (if copy then true::O else O)):=by
 cases copy <;> simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
 all_goals (funext j;fin_cases j <;>simp [Function.update])
theorem field_sep (copy:Bool) (k:Fin 4) (h:Option Bool) (I C O:List Bool) (hk:k.val<3):
 TM2.step program (cfg (.inl (copy,k)) h (false::I) C O)=
 some (cfg (.inl (copy,⟨k.val+1,by omega⟩)) (some false) I C (if copy then false::O else O)):=by
 cases copy <;> simp [TM2.step,program,fieldNext,hk,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
 all_goals (funext j;fin_cases j <;>simp [Function.update])
theorem field_last_sep (copy:Bool) (h:Option Bool) (I C O:List Bool):
 TM2.step program (cfg (.inl (copy,3)) h (false::I) C O)=
 some (cfg (.inr (if copy then 3 else 2)) (some false) I C O):=by
 cases copy <;> simp [TM2.step,program,fieldNext,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
 all_goals (funext j;fin_cases j <;>simp [Function.update])
theorem field_run (copy:Bool) (k:Fin 4) (h:Option Bool) (a:ℕ) (I C O:List Bool):
 next^[a+1] (some (cfg (.inl (copy,k)) h (unary a++false::I) C O))=
 some (cfg (afterField copy k) (some false) I C (fieldOutput copy k a O)):=by
 induction a generalizing h O with
 | zero=>
  simp only [Nat.zero_add,Function.iterate_one,unary,List.replicate_zero,List.nil_append,next,Option.bind_some]
  by_cases hk:k.val<3
  · rw [field_sep copy k h I C O hk]
    simp [afterField,fieldOutput,hk,unary]
  · have he:k=3:=by apply Fin.ext;dsimp;omega
    subst k
    rw [field_last_sep]
    simp [afterField,fieldOutput,unary]
 | succ a ih=>
  simp only [unary_succ,List.cons_append]
  rw [Function.iterate_succ_apply]
  simp only [next,Option.bind_some,field_bit]
  rw [ih]
  cases copy with
  | false=>simp [fieldOutput]
  | true=>
   simp only [fieldOutput,↓reduceIte,unary_succ,List.cons_append]
   rw [unary_append_true]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
theorem stream_nonempty (xs:List ℕ) (hx:xs≠[]):stream xs≠[]:=by
 cases xs with
 | nil=>contradiction
 | cons a xs=>
  intro he
  have h:=congrArg List.length he
  simp only [stream,List.length_append,unary_length,List.length_cons,List.length_nil] at h
  omega
theorem raw_cons (a:ℕ) (xs:List ℕ) (hx:xs≠[]):raw (a::xs)=unary a++false::raw xs:=by
 have hn:=stream_nonempty xs hx
 simp only [raw,stream]
 rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _),List.dropLast_cons_of_ne_nil hn]
theorem fields_run (copy:Bool) (xs:List ℕ) (k:Fin 4) (h:Option Bool) (I C O:List Bool)
 (hlen:k.val+xs.length=4):
 next^[(stream xs).length] (some (cfg (.inl (copy,k)) h (stream xs++I) C O))=
 some (cfg (.inr (if copy then 3 else 2)) (some false) I C
  (if copy then (raw xs).reverse++O else O)):=by
 induction xs generalizing k h O with
 | nil=>simp only [List.length_nil,Nat.add_zero] at hlen;omega
 | cons a xs ih=>
  cases xs with
  | nil=>
   have he:k=3:=by apply Fin.ext;simp only [List.length_cons,List.length_nil] at hlen;dsimp;omega
   subst k
   have he:stream [a]++I=unary a++false::I:=by simp [stream]
   rw [he]
   have hl:(stream [a]).length=a+1:=by simp [stream,unary_length]
   rw [hl,field_run]
   simp only [afterField,fieldOutput,show ¬(3:Fin 4).val<3 by decide,↓reduceDIte,↓reduceIte]
   have hr:raw [a]=unary a:=by simpa [stream] using raw_append_last [] a
   rw [hr]
   simp only [unary,List.reverse_replicate]
  | cons b xs=>
   have hk:k.val<3:=by simp only [List.length_cons] at hlen;omega
   let j:Fin 4:=⟨k.val+1,by omega⟩
   have ht:=ih j (some false) (fieldOutput copy k a O) (by dsimp [j];simp only [List.length_cons] at hlen;omega)
   have hl:(stream (a::b::xs)).length=(stream (b::xs)).length+(a+1):=by
    simp only [stream,List.length_append,unary_length,List.length_cons];omega
   have he:stream (a::b::xs)++I=unary a++false::(stream (b::xs)++I):=by
    simp only [stream,List.append_assoc,List.cons_append]
   rw [hl,Function.iterate_add_apply,he,field_run]
   have hj:afterField copy k=.inl (copy,j):=by simp [afterField,hk,j]
   rw [hj,ht]
   cases copy with
   | false=>simp [fieldOutput]
   | true=>
    simp only [fieldOutput,hk,↓reduceIte]
    rw [raw_cons a (b::xs) (by simp),List.reverse_append,List.reverse_cons]
    simp only [unary,List.reverse_replicate,List.append_assoc,List.cons_append,List.nil_append]
theorem drain_cons (h:Option Bool) (b:Bool) (I O:List Bool):
 TM2.step program (cfg (.inr 3) h (b::I) [] O)=some (cfg (.inr 3) (some b) I [] O):=by
 simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;>simp [Function.update]
theorem drain_nil (h:Option Bool) (O:List Bool):
 TM2.step program (cfg (.inr 3) h [] [] O)=some (halt O):=by
 simp [TM2.step,program,cfg,TM2.stepAux,halt]
theorem drain_run (h:Option Bool) (I O:List Bool):
 next^[I.length+1] (some (cfg (.inr 3) h I [] O))=some (halt O):=by
 induction I generalizing h with
 | nil=>simp [next,drain_nil]
 | cons b I ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [next,Option.bind_some,drain_cons]
  exact ih (some b)
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
theorem stream_append (xs ys:List ℕ):stream (xs++ys)=stream xs++stream ys:=by
  induction xs with
  | nil=>simp [stream]
  | cons a xs ih=>simp [stream,ih,List.append_assoc]
def rows (R:List (List ℕ)):List Bool:=stream R.flatten
theorem rows_cons (r:List ℕ) (R:List (List ℕ)):rows (r::R)=stream r++rows R:=by
 simp only [rows,List.flatten_cons,stream_append]
theorem row_run (R:List (List ℕ)) (i:ℕ) (hi:i<R.length)
 (hr:∀r∈R,r.length=4) (h:Option Bool):
 next^[(rows R).length+i+2] (some (cfg (.inr 2) h (rows R) (unary i) []))=
 some (halt (raw R[i]).reverse):=by
 induction R generalizing i h with
 | nil=>simp at hi
 | cons r R ih=>
  have ha:r.length=4:=hr r (by simp)
  have ht:∀r∈R,r.length=4:=by intro r hh;exact hr r (by simp [hh])
  cases i with
  | zero=>
   have hl:(rows (r::R)).length+0+2=((rows R).length+1)+((stream r).length+1):=by rw [rows_cons,List.length_append];omega
   have hf:next^[(stream r).length+1] (some (cfg (.inr 2) h (stream r++rows R) (unary 0) []))=
     some (cfg (.inr 3) (some false) (rows R) [] (raw r).reverse):=by
    rw [Function.iterate_succ_apply]
    simp only [next,Option.bind_some,unary,List.replicate_zero,choose_copy]
    simpa only [Bool.true_eq,↓reduceIte,List.append_nil] using fields_run true r 0 none (rows R) [] [] (by simpa using ha)
   rw [hl,Function.iterate_add_apply,rows_cons,hf,drain_run]
   simp only [List.getElem_cons_zero]
  | succ i=>
   have hi':i<R.length:=by simp only [List.length_cons] at hi;omega
   have hh:=ih i hi' ht (some false)
   have hl:(rows (r::R)).length+(i+1)+2=((rows R).length+i+2)+((stream r).length+1):=by rw [rows_cons,List.length_append];omega
   have hf:next^[(stream r).length+1] (some (cfg (.inr 2) h (stream r++rows R) (unary (i+1)) []))=
     some (cfg (.inr 2) (some false) (rows R) (unary i) []):=by
    rw [Function.iterate_succ_apply]
    simp only [unary_succ,next,Option.bind_some,choose_skip]
    simpa only [Bool.false_eq_true,↓reduceIte] using fields_run false r 0 (some true) (rows R) (unary i) [] (by simpa using ha)
   rw [hl,Function.iterate_add_apply,rows_cons,hf,hh]
   simp only [List.getElem_cons_succ]
def input (q i:ℕ) (R:List (List ℕ)):List Bool:=stream [q,i]++rows R
theorem run (q i:ℕ) (R:List (List ℕ)) (hi:i<R.length) (hr:∀r∈R,r.length=4):
 next^[(input q i R).length+i+2] (some (machine.init (input q i R)))=
 some (machine.halt (raw R[i]).reverse):=by
 have hl:(input q i R).length+i+2=((rows R).length+i+2)+(i+1)+(q+1):=by
  simp only [input,List.length_append,stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega
 rw [hl,init_eq,Function.iterate_add_apply,Function.iterate_add_apply]
 have he:input q i R=unary q++false::(unary i++false::rows R):=by simp [input,stream,List.append_assoc]
 rw [he,q_run,index_run]
 simp only [List.append_nil]
 rw [row_run R i hi hr (some false),halt_eq]
 rfl
def exec (q i:ℕ) (R:List (List ℕ)) (hi:i<R.length) (hr:∀r∈R,r.length=4):
 EvalsToInTime (TM2.step machine.program) (machine.init (input q i R))
 (some (machine.halt (raw R[i]).reverse)) ((input q i R).length+i+2):=
 ⟨⟨_,run q i R hi hr⟩,le_refl _⟩
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
theorem index_le_input_length (q i:ℕ) (R:List (List ℕ)):i≤(input q i R).length:=by
 simp only [input,List.length_append,stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
 omega
theorem selected_length_le (R:List (List ℕ)) (i:ℕ) (hi:i<R.length):(raw R[i]).length≤(rows R).length:=by
 apply (raw_length_le _).trans
 induction R generalizing i with
 | nil=>simp at hi
 | cons r R ih=>
  rw [rows_cons,List.length_append]
  cases i with
  | zero=>simp only [List.getElem_cons_zero];omega
  | succ i=>
   have hi':i<R.length:=by simp only [List.length_cons] at hi;omega
   simpa only [List.getElem_cons_succ] using (ih i hi').trans (Nat.le_add_left _ _)
def forwardMachine:=Composition.machine machine BitReverse.machine
noncomputable def forwardTime:Polynomial ℕ:=Polynomial.C 5*Polynomial.X+Polynomial.C 5
noncomputable def forwardExec (q i:ℕ) (R:List (List ℕ)) (hi:i<R.length) (hr:∀r∈R,r.length=4):
 EvalsToInTime (TM2.step forwardMachine.program) (forwardMachine.init (input q i R))
 (some (forwardMachine.halt (raw R[i]))) (forwardTime.eval (input q i R).length):=by
 have h:=Composition.executes machine BitReverse.machine (input q i R) (raw R[i]).reverse (raw R[i]) _ _
  (exec q i R hi hr) (by simpa only [List.reverse_reverse] using BitReverse.exec (raw R[i]).reverse)
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hs:(raw R[i]).length≤(input q i R).length:=(selected_length_le R i hi).trans (by simp [input])
 have hi':=index_le_input_length q i R
 simp only [List.length_reverse,forwardTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 omega
noncomputable def forwardOutputsInTime (q i:ℕ) (R:List (List ℕ)) (hi:i<R.length) (hr:∀r∈R,r.length=4):
 TM2OutputsInTime forwardMachine.toFinTM2 (input q i R) (some (raw R[i]))
 (forwardTime.eval (input q i R).length):=
 Machine.outputsInTime forwardMachine _ _ _ (forwardExec q i R hi hr)
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup


