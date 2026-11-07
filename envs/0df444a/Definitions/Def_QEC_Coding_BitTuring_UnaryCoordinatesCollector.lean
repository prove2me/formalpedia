-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryCoordinatesCollector
-- name    : QEC_Coding_BitTuring_UnaryCoordinatesCollector
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:57:37.298588+00:00
-- url     : https://prove2.me/theorems/adf00920-e099-4e5c-8808-8529664e4154
-- title:
--   Unary Coordinates Collector
-- statement:
--   Definitions and structural lemmas for Unary Coordinates Collector, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryCoordinatesCollector.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.CoordinatesCollector
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
abbrev Label (n:ℕ):=Fin (n+1)⊕Fin 6
abbrev Var:=Bool×Option Bool
abbrev Statement (n:ℕ):=TM2.Stmt (fun _:Fin 5=>Bool) (Label n) Var
def fieldNext (n:ℕ) (k:Fin (n+1)):Statement n:=
 if h:k.val<n then .goto (fun _=>.inl ⟨k.val+1,Nat.succ_lt_succ h⟩)
 else .goto (fun v=>.inr (if v.1 then 1 else 3))
def setHead (v:Var) (h:Option Bool):Var:=(v.1,h)
def program (n:ℕ):Label n→Statement n
 | .inl k=>.pop 0 setHead (.branch (fun v=>v.2.getD false)
    (.push 1 (fun _=>true)
      (if k.val=0 then .goto (fun _=>.inl k) else .push 2 (fun _=>true) (.goto fun _=>.inl k)))
    (.push 1 (fun _=>false)
      (if k.val=0 then fieldNext n k else .push 2 (fun _=>false) (fieldNext n k))))
 | .inr 0=>.pop 0 (fun _ h=>(h.getD false,h)) (.goto fun _=>.inl 0)
 | .inr 1=>.pop 2 setHead (.branch (fun v=>v.2.isSome)
    (.push 3 (fun v=>v.2.getD false) (.goto fun _=>.inr 1)) (.goto fun _=>.inr 2))
 | .inr 2=>.pop 3 setHead (.branch (fun v=>v.2.isSome)
    (.push 1 (fun v=>v.2.getD false) (.goto fun _=>.inr 2)) (.goto fun _=>.inr 4))
 | .inr 3=>.pop 2 setHead (.branch (fun v=>v.2.isSome)
    (.goto fun _=>.inr 3) (.goto fun _=>.inr 4))
 | .inr 4=>.pop 0 setHead (.branch (fun v=>v.2.isSome)
    (.push 1 (fun v=>v.2.getD false) (.goto fun _=>.inr 4)) (.goto fun _=>.inr 5))
 | .inr 5=>.pop 1 setHead (.branch (fun v=>v.2.isSome)
    (.push 4 (fun v=>v.2.getD false) (.goto fun _=>.inr 5)) (.load (fun _=>(false,none)) .halt))
def machine (n:ℕ):Machine where
 K:=Fin 5;input:=0;output:=4;Λ:=Label n;main:=.inr 0;σ:=Var;initial:=(false,none);program:=program n
def cfg (n:ℕ) (l:Label n) (flag:Bool) (h:Option Bool) (I H R T O:List Bool):
 TM2.Cfg (fun _:Fin 5=>Bool) (Label n) Var:=⟨some l,(flag,h),![I,H,R,T,O]⟩
theorem initial (n:ℕ) (flag:Bool) (w:List Bool):
 TM2.step (program n) ((machine n).init (flag::w))=some (cfg n (.inl 0) flag (some flag) w [] [] [] []):=by
 simp [TM2.step,program,Machine.init,machine,cfg,TM2.stepAux,TM2.Cfg.mk.injEq,Function.update]
 funext j;fin_cases j <;> simp [Function.update]
theorem copy_cons (n:ℕ) (flag:Bool) (h:Option Bool) (a:Bool) (I H R T O:List Bool):
 TM2.step (program n) (cfg n (.inr 1) flag h I H (a::R) T O)=
 some (cfg n (.inr 1) flag (some a) I H R (a::T) O):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
theorem copy_nil (n:ℕ) (flag:Bool) (h:Option Bool) (I H T O:List Bool):
 TM2.step (program n) (cfg n (.inr 1) flag h I H [] T O)=
 some (cfg n (.inr 2) flag none I H [] T O):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux]
theorem copy_run (n:ℕ) (flag:Bool) (h:Option Bool) (I H R T O:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[R.length+1] (some (cfg n (.inr 1) flag h I H R T O))=
 some (cfg n (.inr 2) flag none I H [] (R.reverse++T) O):=by
 induction R generalizing h T with
 |nil=>simp [copy_nil]
 |cons a R ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,copy_cons]
  rw [ih];simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
theorem prepend_cons (n:ℕ) (flag:Bool) (h:Option Bool) (a:Bool) (I H T O:List Bool):
 TM2.step (program n) (cfg n (.inr 2) flag h I H [] (a::T) O)=
 some (cfg n (.inr 2) flag (some a) I (a::H) [] T O):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
theorem prepend_nil (n:ℕ) (flag:Bool) (h:Option Bool) (I H O:List Bool):
 TM2.step (program n) (cfg n (.inr 2) flag h I H [] [] O)=
 some (cfg n (.inr 4) flag none I H [] [] O):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux]
theorem prepend_run (n:ℕ) (flag:Bool) (h:Option Bool) (I H T O:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[T.length+1] (some (cfg n (.inr 2) flag h I H [] T O))=
 some (cfg n (.inr 4) flag none I (T.reverse++H) [] [] O):=by
 induction T generalizing h H with
 |nil=>simp [prepend_nil]
 |cons a T ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,prepend_cons]
  rw [ih];simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
theorem drain_cons (n:ℕ) (flag:Bool) (h:Option Bool) (a:Bool) (I H R O:List Bool):
 TM2.step (program n) (cfg n (.inr 3) flag h I H (a::R) [] O)=
 some (cfg n (.inr 3) flag (some a) I H R [] O):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
theorem drain_nil (n:ℕ) (flag:Bool) (h:Option Bool) (I H O:List Bool):
 TM2.step (program n) (cfg n (.inr 3) flag h I H [] [] O)=
 some (cfg n (.inr 4) flag none I H [] [] O):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux]
theorem drain_run (n:ℕ) (flag:Bool) (h:Option Bool) (I H R O:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[R.length+1] (some (cfg n (.inr 3) flag h I H R [] O))=
 some (cfg n (.inr 4) flag none I H [] [] O):=by
 induction R generalizing h with
 |nil=>simp [drain_nil]
 |cons a R ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,drain_cons]
  rw [ih]
theorem tail_cons (n:ℕ) (flag:Bool) (h:Option Bool) (a:Bool) (I H O:List Bool):
 TM2.step (program n) (cfg n (.inr 4) flag h (a::I) H [] [] O)=
 some (cfg n (.inr 4) flag (some a) I (a::H) [] [] O):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
theorem tail_nil (n:ℕ) (flag:Bool) (h:Option Bool) (H O:List Bool):
 TM2.step (program n) (cfg n (.inr 4) flag h [] H [] [] O)=
 some (cfg n (.inr 5) flag none [] H [] [] O):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux]
theorem tail_run (n:ℕ) (flag:Bool) (h:Option Bool) (I H O:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[I.length+1] (some (cfg n (.inr 4) flag h I H [] [] O))=
 some (cfg n (.inr 5) flag none [] (I.reverse++H) [] [] O):=by
 induction I generalizing h H with
 |nil=>simp [tail_nil]
 |cons a I ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,tail_cons]
  rw [ih];simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
theorem reverse_cons (n:ℕ) (flag:Bool) (h:Option Bool) (a:Bool) (H O:List Bool):
 TM2.step (program n) (cfg n (.inr 5) flag h [] (a::H) [] [] O)=
 some (cfg n (.inr 5) flag (some a) [] H [] [] (a::O)):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
theorem reverse_nil (n:ℕ) (flag:Bool) (h:Option Bool) (O:List Bool):
 TM2.step (program n) (cfg n (.inr 5) flag h [] [] [] [] O)=some ((machine n).halt O):=by
 simp [TM2.step,program,cfg,setHead,TM2.stepAux,Machine.halt,machine,TM2.Cfg.mk.injEq]
 funext j;fin_cases j <;> simp [Function.update]
theorem reverse_run (n:ℕ) (flag:Bool) (h:Option Bool) (H O:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[H.length+1] (some (cfg n (.inr 5) flag h [] H [] [] O))=
 some ((machine n).halt (H.reverse++O)):=by
 induction H generalizing h O with
 |nil=>
  simp only [List.length_nil,Nat.zero_add,Function.iterate_one,Option.bind_some,List.reverse_nil,List.nil_append]
  exact reverse_nil n flag h O
 |cons a H ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,reverse_cons]
  rw [ih];simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
  rfl
def nextLabel (n:ℕ) (k:Fin (n+1)) (flag:Bool):Label n:=
 if h:k.val<n then .inl ⟨k.val+1,Nat.succ_lt_succ h⟩ else .inr (if flag then 1 else 3)
theorem field_bit (n:ℕ) (k:Fin (n+1)) (flag:Bool) (h:Option Bool) (I H R T O:List Bool):
 TM2.step (program n) (cfg n (.inl k) flag h (true::I) H R T O)=
 some (cfg n (.inl k) flag (some true) I (true::H) (if k.val=0 then R else true::R) T O):=by
 by_cases hk:k.val=0 <;>
  simp [TM2.step,program,cfg,setHead,TM2.stepAux,hk,TM2.Cfg.mk.injEq] <;>
  (funext j;fin_cases j <;> simp [Function.update])
theorem field_sep (n:ℕ) (k:Fin (n+1)) (flag:Bool) (h:Option Bool) (I H R T O:List Bool):
 TM2.step (program n) (cfg n (.inl k) flag h (false::I) H R T O)=
 some (cfg n (nextLabel n k flag) flag (some false) I (false::H)
  (if k.val=0 then R else false::R) T O):=by
 cases flag <;> by_cases hk:k.val=0
 all_goals
  by_cases hn:k.val<n
  all_goals
   try have hz : 0<n := by omega
   try have hz : ¬0<n := by omega
   simp_all [TM2.step,program,cfg,setHead,fieldNext,nextLabel,TM2.stepAux,TM2.Cfg.mk.injEq]
   try simp [dif_neg (by omega : ¬k.val<n),TM2.stepAux,TM2.Cfg.mk.injEq]
   funext j;fin_cases j <;> simp [Function.update]
theorem field_run (n:ℕ) (k:Fin (n+1)) (flag:Bool) (h:Option Bool) (a:ℕ) (I H R T O:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[a+1]
  (some (cfg n (.inl k) flag h (unary a++false::I) H R T O))=
 some (cfg n (nextLabel n k flag) flag (some false) I (false::(unary a++H))
  (if k.val=0 then R else false::(unary a++R)) T O):=by
 induction a generalizing h H R with
 |zero=>simp [unary,field_sep]
 |succ a ih=>
  simp only [unary_succ,List.cons_append]
  rw [Function.iterate_succ_apply]
  simp only [Option.bind_some,field_bit]
  rw [ih]
  by_cases hk:k.val=0 <;> simp only [hk,↓reduceIte,unary_append_cons,unary_succ,List.cons_append]
theorem parse_rest (n:ℕ) (xs:List ℕ) (k:Fin (n+1)) (flag:Bool) (h:Option Bool)
 (I H R T O:List Bool) (hk:k.val+xs.length=n+1) (hpos:0<k.val) (hne:xs≠[]):
 (fun c=>c.bind (TM2.step (program n)))^[(stream xs).length]
  (some (cfg n (.inl k) flag h (stream xs++I) H R T O))=
 some (cfg n (.inr (if flag then 1 else 3)) flag (some false) I
  ((stream xs).reverse++H) ((stream xs).reverse++R) T O):=by
 induction xs generalizing k h H R with
 |nil=>exact False.elim (hne rfl)
 |cons a xs ih=>
  have hkn:k.val≠0:=by omega
  cases xs with
  |nil=>
   have hl:k.val=n:=by simp only [List.length_cons,List.length_nil] at hk;omega
   have hr:=field_run n k flag h a I H R T O
   have ht:¬k.val<n:=by omega
   simp only [nextLabel,dif_neg ht,hkn,↓reduceIte] at hr
   simpa only [stream,List.append_nil,List.length_append,List.length_cons,List.length_nil,
    unary_length,List.cons_append,List.reverse_append,List.reverse_cons,List.reverse_nil,
    show (unary a).reverse=unary a by simp [unary],List.nil_append,List.append_assoc] using hr
  |cons b xs=>
   have hl:k.val<n:=by simp only [List.length_cons] at hk;omega
   let j:Fin (n+1):=⟨k.val+1,Nat.succ_lt_succ hl⟩
   have hstep:=field_run n k flag h a (stream (b::xs)++I) H R T O
   simp only [nextLabel,dif_pos hl,hkn,↓reduceIte] at hstep
   have htail:j.val+(b::xs).length=n+1:=by dsimp [j];simp only [List.length_cons] at hk ⊢;omega
   have hpj:0<j.val:=by dsimp [j];omega
   have ht:=ih j (some false) (false::(unary a++H)) (false::(unary a++R)) htail hpj (by simp)
   have hlen:(stream (a::b::xs)).length=(stream (b::xs)).length+(a+1):=by
    simp only [stream,List.length_append,List.length_cons,unary_length];omega
   rw [hlen,Function.iterate_add_apply]
   have he:stream (a::b::xs)++I=unary a++false::(stream (b::xs)++I):=by
    simp only [stream,List.append_assoc,List.cons_append]
   rw [he,hstep,ht]
   simp only [stream,List.reverse_append,List.reverse_cons,
    show (unary a).reverse=unary a by simp [unary],List.append_assoc,List.cons_append,List.nil_append]
theorem parse_run (n q:ℕ) (xs:List ℕ) (flag:Bool) (I:List Bool)
 (hlen:xs.length=n) (hn:0<n):
 (fun c=>c.bind (TM2.step (program n)))^[(stream (q::xs)).length+1]
  (some ((machine n).init (flag::(stream (q::xs)++I))))=
 some (cfg n (.inr (if flag then 1 else 3)) flag (some false) I
  (stream (q::xs)).reverse (stream xs).reverse [] []):=by
 have he:stream (q::xs)++I=unary q++false::(stream xs++I):=by
  simp only [stream,List.cons_append,List.append_assoc]
 rw [Function.iterate_succ_apply]
 simp only [Option.bind_some]
 change (fun c=>c.bind (TM2.step (program n)))^[(stream (q::xs)).length]
  (TM2.step (program n) ((machine n).init (flag::(stream (q::xs)++I))))=_
 rw [initial,he]
 have hf:=field_run n 0 flag (some flag) q (stream xs++I) [] [] [] []
 have hzero:(0:Fin (n+1)).val<n:=hn
 simp only [nextLabel] at hf
 rw [dif_pos hzero] at hf
 simp only [Fin.val_zero,↓reduceIte,List.append_nil] at hf
 let k:Fin (n+1):=⟨1,by omega⟩
 have ht:=parse_rest n xs k flag (some false) I (false::unary q) [] [] []
  (by dsimp [k];omega) (by dsimp [k];omega) (by intro h;rw [h] at hlen;simp at hlen;omega)
 have hl:(stream (q::xs)).length=(stream xs).length+(q+1):=by
  simp only [stream,List.length_append,List.length_cons,unary_length];omega
 rw [hl,Function.iterate_add_apply,hf,ht]
 simp only [List.append_nil,stream,List.reverse_append,List.reverse_cons,
  show (unary q).reverse=unary q by simp [unary],List.append_assoc,List.singleton_append]
theorem finish_true (n:ℕ) (h:Option Bool) (I H R:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[(I.reverse++(R++H)).length+1+(I.length+1)+(R.length+1)+(R.length+1)]
  (some (cfg n (.inr 1) true h I H R [] []))=
 some ((machine n).halt (H.reverse++R.reverse++I)):=by
 rw [Function.iterate_add_apply,copy_run]
 simp only [List.append_nil]
 have hr: R.reverse.length=R.length:=List.length_reverse
 rw [←hr,Function.iterate_add_apply,prepend_run]
 simp only [List.reverse_reverse]
 rw [Function.iterate_add_apply,tail_run,reverse_run]
 simp only [List.reverse_append,List.reverse_reverse,List.append_nil,List.append_assoc]
 rfl
theorem finish_false (n:ℕ) (h:Option Bool) (I H R:List Bool):
 (fun c=>c.bind (TM2.step (program n)))^[(I.reverse++H).length+1+(I.length+1)+(R.length+1)]
  (some (cfg n (.inr 3) false h I H R [] []))=
 some ((machine n).halt (H.reverse++I)):=by
 rw [Function.iterate_add_apply,drain_run,Function.iterate_add_apply,tail_run,reverse_run]
 simp only [List.reverse_append,List.reverse_reverse,List.append_nil]
 rfl
def output (q:ℕ) (xs:List ℕ) (flag:Bool) (I:List Bool):List Bool:=
 stream (q::xs)++(if flag then stream xs else [])++I
def steps (q:ℕ) (xs:List ℕ) (flag:Bool) (I:List Bool):ℕ:=
 2*(stream (q::xs)).length+(if flag then 3*(stream xs).length+5 else (stream xs).length+4)+2*I.length
theorem run (n q:ℕ) (xs:List ℕ) (flag:Bool) (I:List Bool) (hlen:xs.length=n) (hn:0<n):
 (fun c=>c.bind (TM2.step (machine n).program))^[steps q xs flag I]
  (some ((machine n).init (flag::(stream (q::xs)++I))))=
 some ((machine n).halt (output q xs flag I)):=by
 have hp:=parse_run n q xs flag I hlen hn
 dsimp only [Machine.Cfg,Machine.init,Machine.halt,machine] at hp ⊢
 cases flag
 · have hf:=finish_false n (some false) I (stream (q::xs)).reverse (stream xs).reverse
   simp only [List.length_append,List.length_reverse,List.reverse_reverse] at hf
   have hs:steps q xs false I=
    ((I.length+(stream (q::xs)).length)+1+(I.length+1)+((stream xs).length+1))+
    ((stream (q::xs)).length+1):=by simp [steps];omega
   simp only [Bool.false_eq_true,↓reduceIte] at hp
   rw [hs,Function.iterate_add_apply,hp]
   simp only [output,Bool.false_eq_true,↓reduceIte,List.append_nil]
   exact hf
 · have hf:=finish_true n (some false) I (stream (q::xs)).reverse (stream xs).reverse
   simp only [List.length_append,List.length_reverse,List.reverse_reverse] at hf
   have hs:steps q xs true I=
    ((I.length+((stream xs).length+(stream (q::xs)).length))+1+(I.length+1)+
     ((stream xs).length+1)+((stream xs).length+1))+((stream (q::xs)).length+1):=by
    simp [steps];omega
   simp only [↓reduceIte] at hp
   rw [hs,Function.iterate_add_apply,hp]
   simp only [output,↓reduceIte]
   exact hf
def exec (n q:ℕ) (xs:List ℕ) (flag:Bool) (I:List Bool) (hlen:xs.length=n) (hn:0<n):
 EvalsToInTime (TM2.step (machine n).program) ((machine n).init (flag::(stream (q::xs)++I)))
  (some ((machine n).halt (output q xs flag I))) (steps q xs flag I):=
 ⟨⟨steps q xs flag I,run n q xs flag I hlen hn⟩,le_refl _⟩
noncomputable def time:Polynomial ℕ:=Polynomial.C 8*(Polynomial.X+1)
noncomputable def polyExec (n q:ℕ) (xs:List ℕ) (flag:Bool) (I:List Bool) (hlen:xs.length=n) (hn:0<n):
 EvalsToInTime (TM2.step (machine n).program) ((machine n).init (flag::(stream (q::xs)++I)))
  (some ((machine n).halt (output q xs flag I))) (time.eval (flag::(stream (q::xs)++I)).length):=by
 have h:=exec n q xs flag I hlen hn
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hl:(stream xs).length≤(stream (q::xs)).length:=by
  simp only [stream,List.length_append,List.length_cons,unary_length];omega
 simp only [steps,time,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,
  Polynomial.eval_X,Polynomial.eval_one,List.length_cons,List.length_append]
 cases flag <;> simp <;> omega
end QEC.Coding.BitTuring.UnaryArithmetic.CoordinatesCollector


