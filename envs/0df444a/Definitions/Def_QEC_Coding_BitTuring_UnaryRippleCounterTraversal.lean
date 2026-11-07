-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
-- name    : QEC_Coding_BitTuring_UnaryRippleCounterTraversal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:12:08.994821+00:00
-- url     : https://prove2.me/theorems/48f132e1-2cc8-46b9-ab4e-7a0c46138fc6
-- title:
--   Unary Ripple Counter Traversal
-- statement:
--   Definitions and structural lemmas for Unary Ripple Counter Traversal, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryRippleCounterTraversal.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounter
import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
def rank (q:ℕ):List ℕ→ℕ
 | [] =>0
 | x::xs =>x+q*rank q xs
theorem digit_reconstruct (q x:ℕ) (carry:Bool):
 digit q x carry+q*bump (carried q x carry)=x+bump carry:=by
 by_cases h:candidate x carry=q
 · simp only [digit,carried,h,decide_true,↓reduceIte,bump,Nat.zero_add,Nat.mul_one]
   exact h.symm
 · have hc:carried q x carry=false:=by simp [carried,h]
   simp only [digit,hc,Bool.false_eq_true,↓reduceIte,bump,Nat.mul_zero,Nat.add_zero]
   rfl
theorem digits_rank (q:ℕ) (carry:Bool) (xs:List ℕ):
 rank q (digits q carry xs).2+q^xs.length*bump (digits q carry xs).1=rank q xs+bump carry:=by
 induction xs generalizing carry with
 |nil=>simp [digits,rank]
 |cons x xs ih=>
  have ht:=ih (carried q x carry)
  have h0:=digit_reconstruct q x carry
  change digit q x carry+q*rank q (digits q (carried q x carry) xs).2+
   q^((x::xs).length)*bump (digits q (carried q x carry) xs).1=
   x+q*rank q xs+bump carry
  simp only [List.length_cons,pow_succ]
  calc
   _=digit q x carry+q*(rank q (digits q (carried q x carry) xs).2+
      q^xs.length*bump (digits q (carried q x carry) xs).1):=by ring
   _=digit q x carry+q*(rank q xs+bump (carried q x carry)):=by rw [ht]
   _=(digit q x carry+q*bump (carried q x carry))+q*rank q xs:=by ring
   _=(x+bump carry)+q*rank q xs:=by rw [h0]
   _=_:=by ring
theorem rank_lt (q:ℕ) (xs:List ℕ) (hx:∀x∈xs,x<q):rank q xs<q^xs.length:=by
 induction xs with
 |nil=>simp [rank]
 |cons x xs ih=>
  have h0:=hx x (by simp)
  have ht:=ih (fun z hz=>hx z (by simp [hz]))
  have hm:=Nat.mul_le_mul_left q (Nat.succ_le_of_lt ht)
  simp only [rank,List.length_cons,pow_succ]
  nlinarith
theorem overflow_iff_last (q:ℕ) (xs:List ℕ) (hx:∀x∈xs,x<q):
 (digits q true xs).1=true ↔ rank q xs+1=q^xs.length:=by
 have hr:=digits_rank q true xs
 have hn:=rank_lt q (digits q true xs).2 (digits_lt q true xs hx)
 have hold:=rank_lt q xs hx
 rw [digits_length] at hn
 cases hf:(digits q true xs).1 <;> simp [hf,bump] at hr ⊢ <;> omega
theorem rank_next (q:ℕ) (xs:List ℕ) (hf:(digits q true xs).1=false):
 rank q (digits q true xs).2=rank q xs+1:=by
 have h:=digits_rank q true xs
 simpa only [hf,bump,Bool.false_eq_true,↓reduceIte,Nat.mul_zero,Nat.add_zero] using h
theorem rank_wrap (q:ℕ) (xs:List ℕ) (hx:∀x∈xs,x<q) (hf:(digits q true xs).1=true):
 rank q (digits q true xs).2=0:=by
 have hr:=digits_rank q true xs
 have hl:rank q xs+1=q^xs.length:=(overflow_iff_last q xs hx).mp hf
 simp only [hf,bump,↓reduceIte,Nat.mul_one] at hr
 omega
theorem rank_eq_zero_list (q:ℕ) (xs:List ℕ) (hq:0<q) (h:rank q xs=0):xs=List.replicate xs.length 0:=by
 induction xs with
 |nil=>rfl
 |cons x xs ih=>
  have he:x=0 ∧ rank q xs=0:=by
   simp only [rank] at h
   have hr:rank q xs=0:=by nlinarith
   exact ⟨by omega,hr⟩
  rw [he.1,ih he.2]
  simp only [List.length_cons,List.length_replicate,List.replicate_succ]
theorem header_length_le (n q:ℕ) (xs:List ℕ) (hlen:xs.length=n+1) (hx:∀x∈xs,x<q):
 (stream (q::xs)).length≤(n+2)*(q+1):=by
 have hb:=MatrixListQuery.stream_length_bound q xs hx
 rw [hlen] at hb
 simp only [stream,List.length_append,List.length_cons,unary_length]
 nlinarith
def payload (q:ℕ) (xs:List ℕ) (s:List Bool):List Bool:=stream (q::xs)++s
def loopMachine (n:ℕ):Machine:=FlagLoop.machine (machine n)
def uniformSize (n q:ℕ) (s:List Bool):ℕ:=(n+2)*(q+1)+s.length
def callBudget (n q:ℕ) (s:List Bool):ℕ:=(8*(n+2)+8)*(uniformSize n q s+1)+2*uniformSize n q s+4
noncomputable def invocationExec (n q:ℕ) (xs:List ℕ) (s:List Bool) (hlen:xs.length=n+1) (hx:∀x∈xs,x<q):
 EvalsToInTime (TM2.step (loopMachine n).program) ((loopMachine n).init (payload q xs s))
  (some (if (digits q true xs).1 then (loopMachine n).halt (payload q (digits q true xs).2 s)
   else (loopMachine n).init (payload q (digits q true xs).2 s))) (callBudget n q s):=by
 have hb:=polyExec n q xs s hlen hx
 change EvalsToInTime _ _ (some ((machine n).halt ((digits q true xs).1::payload q (digits q true xs).2 s))) _ at hb
 have h:=FlagLoop.invocationExec (machine n) (by change (0:Fin 8)≠6;decide)
  (payload q xs s) (payload q (digits q true xs).2 s) (digits q true xs).1 _ hb
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have h0:(payload q xs s).length≤uniformSize n q s:=by
  simpa only [payload,uniformSize,List.length_append] using Nat.add_le_add_right (header_length_le n q xs hlen hx) s.length
 have h1:(payload q (digits q true xs).2 s).length≤uniformSize n q s:=by
  simpa only [payload,uniformSize,List.length_append] using Nat.add_le_add_right (output_header_length_le n q xs hlen hx) s.length
 have ht:=Nat.mul_le_mul_left (8*(n+2)+8) (Nat.add_le_add_right h0 1)
 dsimp only [payload] at h0 h1 ht
 simp only [time,callBudget,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,payload]
 omega
noncomputable def traverseAux (n q m:ℕ) (xs:List ℕ) (s:List Bool) (hq:0<q)
 (hlen:xs.length=n+1) (hx:∀x∈xs,x<q) (hr:rank q xs+(m+1)=q^(n+1)):
 EvalsToInTime (TM2.step (loopMachine n).program) ((loopMachine n).init (payload q xs s))
  (some ((loopMachine n).halt (payload q (List.replicate (n+1) 0) s))) ((m+1)*callBudget n q s):=by
 induction m generalizing xs with
 |zero=>
  have hf:(digits q true xs).1=true:=
   (overflow_iff_last q xs hx).mpr (by simpa only [hlen] using hr)
  have hz:=rank_wrap q xs hx hf
  have he:=rank_eq_zero_list q (digits q true xs).2 hq hz
  rw [digits_length,hlen] at he
  have h:=invocationExec n q xs s hlen hx
  simpa only [hf,↓reduceIte,he,Nat.zero_add,Nat.one_mul] using h
 |succ m ih=>
  have hn:rank q xs+1≠q^xs.length:=by rw [hlen];omega
  have hf:(digits q true xs).1=false:=by
   cases he:(digits q true xs).1 with
   |false=>rfl
   |true=>exact False.elim (hn ((overflow_iff_last q xs hx).mp he))
  have he:=rank_next q xs hf
  have ht:=ih (digits q true xs).2 (by simpa only [digits_length] using hlen)
   (digits_lt q true xs hx) (by rw [he];omega)
  have h0:=invocationExec n q xs s hlen hx
  rw [hf] at h0
  simp only [Bool.false_eq_true,↓reduceIte] at h0
  have h:=EvalsToInTime.trans (TM2.step (loopMachine n).program)
   (callBudget n q s) ((m+1)*callBudget n q s) _ _ _ h0 ht
  have heq:(m+1)*callBudget n q s+callBudget n q s=(m+1+1)*callBudget n q s:=by ring
  rw [heq] at h
  exact h
noncomputable def traverseExec (n q:ℕ) (xs:List ℕ) (s:List Bool) (hq:0<q)
 (hlen:xs.length=n+1) (hx:∀x∈xs,x<q):
 EvalsToInTime (TM2.step (loopMachine n).program) ((loopMachine n).init (payload q xs s))
  (some ((loopMachine n).halt (payload q (List.replicate (n+1) 0) s)))
  ((q^(n+1)-rank q xs)*callBudget n q s):=by
 have hlt:=rank_lt q xs hx
 rw [hlen] at hlt
 have hpos:0<q^(n+1)-rank q xs:=by omega
 have h:=traverseAux n q (q^(n+1)-rank q xs-1) xs s hq hlen hx (by omega)
 have he:q^(n+1)-rank q xs-1+1=q^(n+1)-rank q xs:=by omega
 rwa [he] at h
noncomputable def sizePolynomial (n:ℕ):Polynomial ℕ:=Polynomial.C (n+2)*(Polynomial.X+1)+Polynomial.X
noncomputable def callPolynomial (n:ℕ):Polynomial ℕ:=
 Polynomial.C (8*(n+2)+8)*(sizePolynomial n+1)+Polynomial.C 2*sizePolynomial n+Polynomial.C 4
noncomputable def traverseTime (n:ℕ):Polynomial ℕ:=(Polynomial.X+1)^(n+1)*callPolynomial n
noncomputable def traversePolyExec (n q:ℕ) (xs:List ℕ) (s:List Bool) (hq:0<q)
 (hlen:xs.length=n+1) (hx:∀x∈xs,x<q):
 EvalsToInTime (TM2.step (loopMachine n).program) ((loopMachine n).init (payload q xs s))
  (some ((loopMachine n).halt (payload q (List.replicate (n+1) 0) s)))
  ((traverseTime n).eval (payload q xs s).length):=by
 have h:=traverseExec n q xs s hq hlen hx
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 let L:=(payload q xs s).length
 have hqL:q≤L+1:=by dsimp [L,payload];simp only [stream,List.length_append,List.length_cons,unary_length];omega
 have hs:s.length≤L:=by dsimp [L,payload];simp only [List.length_append];omega
 have hq1:q+1≤L+1:=by dsimp [L,payload];simp only [stream,List.length_append,List.length_cons,unary_length];omega
 have hsize:uniformSize n q s≤(sizePolynomial n).eval L:=by
  have ht:=Nat.mul_le_mul_left (n+2) hq1
  simp only [uniformSize,sizePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
   Polynomial.eval_X,Polynomial.eval_one]
  omega
 have hcall:callBudget n q s≤(callPolynomial n).eval L:=by
  have ht:=Nat.mul_le_mul_left (8*(n+2)+8) (Nat.add_le_add_right hsize 1)
  have hm:=Nat.mul_le_mul_left 2 hsize
  simp only [callBudget,callPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one]
  omega
 have hp:q^(n+1)-rank q xs≤(L+1)^(n+1):=
  (Nat.sub_le _ _).trans (Nat.pow_le_pow_left hqL (n+1))
 change (q^(n+1)-rank q xs)*callBudget n q s≤(traverseTime n).eval L
 simpa only [traverseTime,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using Nat.mul_le_mul hp hcall
noncomputable def traversalComputableInPolyTime (n:ℕ):
 TM2ComputableInPolyTime (input n) id
  (fun x:Input n=>payload x.1.val.1 (List.replicate (n+1) 0) x.2) where
 tm:=(loopMachine n).toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=traverseTime n
 outputsFun:=fun x=>by
  change TM2OutputsInTime (loopMachine n).toFinTM2 (List.map id (input n x))
   (some (List.map id (payload x.1.val.1 (List.replicate (n+1) 0) x.2)))
   ((traverseTime n).eval (input n x).length)
  have h:=Machine.outputsInTime (loopMachine n) _ _ _
   (traversePolyExec n x.1.val.1 x.1.val.2 x.2 x.1.property.1 x.1.property.2.1 x.1.property.2.2)
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [input,payload,List.map_id] using h
end QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter


