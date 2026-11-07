-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixProduct
-- name    : QEC_Coding_BitTuring_UnaryMatrixProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:11:44.126534+00:00
-- url     : https://prove2.me/theorems/9ef5af89-b516-48f9-9e4d-fcf67c6e5d79
-- title:
--   Unary Matrix Product
-- statement:
--   Definitions and structural lemmas for Unary Matrix Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMatrixProduct.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularDot
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_fields_stream_length_le
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_append_last
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_length_le
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_reverse_raw_four
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_length
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularMatrixProduct
open Turing StateTransition
open FieldProjection
def entryMachine (n:ℕ) (keep:Fin (n+1)→Bool) := Composition.machine (machine n keep)
  (Composition.machine BitDelimiter.machine (Composition.machine ModularDot.dotMachine UnaryDelimiter.machine))
def retainedEntryMachine (n:ℕ) (keep:Fin (n+1)→Bool) := RetainedInput.machine (entryMachine n keep)
noncomputable def entryTime : Polynomial ℕ := Polynomial.C 500*(Polynomial.X+1)^2
noncomputable def retainedEntryTime : Polynomial ℕ := Polynomial.C 600*(Polynomial.X+1)^2
noncomputable def entryExec (n:ℕ) (keep:Fin (n+1)→Bool) (xs:List ℕ)
    (hx:xs.length=n+1) (a b c d q:ℕ) (hq:0<q)
    (hf:fields n keep 0 xs=[a,b,c,d,q]) :
    EvalsToInTime (TM2.step (entryMachine n keep).program) ((entryMachine n keep).init (stream xs))
      (some ((entryMachine n keep).halt (unary ((a*c+b*d)%q)++[false])))
      (entryTime.eval (stream xs).length) := by
  have hp:=FieldProjection.polyExec n keep xs hx
  rw [hf] at hp
  have he:raw [a,b,c,d,q]++[false]=stream [a,b,c,d,q] := by
    have h:=raw_append_last [a,b,c,d] q
    simp only [List.cons_append,List.nil_append] at h
    rw [h];simp [stream,List.append_assoc]
  have hd:=BitDelimiter.exec (raw [a,b,c,d,q])
  rw [he] at hd
  have hm:=ModularDot.polyExec a b c d q hq
  have hfout:=UnaryDelimiter.exec ((a*c+b*d)%q)
  have hmd:=Composition.executes ModularDot.dotMachine UnaryDelimiter.machine
    (stream [a,b,c,d,q]) (unary ((a*c+b*d)%q)) (unary ((a*c+b*d)%q)++[false])
    _ _ hm hfout
  have hdm:=Composition.executes BitDelimiter.machine
    (Composition.machine ModularDot.dotMachine UnaryDelimiter.machine)
    (raw [a,b,c,d,q]) (stream [a,b,c,d,q]) (unary ((a*c+b*d)%q)++[false]) _ _ hd hmd
  have h:=Composition.executes (machine n keep)
    (Composition.machine BitDelimiter.machine (Composition.machine ModularDot.dotMachine UnaryDelimiter.machine))
    (stream xs) (raw [a,b,c,d,q]) (unary ((a*c+b*d)%q)++[false]) _ _ hp hdm
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hl:=fields_stream_length_le n keep 0 xs
  rw [hf] at hl
  have hr: (raw [a,b,c,d,q]).length≤(stream xs).length := (raw_length_le _).trans hl
  have hqL:q≤(stream xs).length := by
    have hs:(stream [a,b,c,d,q]).length=a+b+c+d+q+5 := by
      simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
    rw [hs] at hl
    omega
  have hv:(a*c+b*d)%q<q:=Nat.mod_lt _ hq
  have hs:((stream [a,b,c,d,q]).length+1)^2≤((stream xs).length+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  simp only [entryTime,ModularDot.time,FieldProjection.time,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.eval_one,Polynomial.eval_pow,unary_length]
  nlinarith [sq_nonneg ((stream xs).length+1)]
noncomputable def retainedEntryExec (n:ℕ) (keep:Fin (n+1)→Bool) (xs:List ℕ)
    (hx:xs.length=n+1) (a b c d q:ℕ) (hq:0<q)
    (hf:fields n keep 0 xs=[a,b,c,d,q]) :
    EvalsToInTime (TM2.step (retainedEntryMachine n keep).program)
      ((retainedEntryMachine n keep).init (stream xs))
      (some ((retainedEntryMachine n keep).halt (stream (((a*c+b*d)%q)::xs))))
      (retainedEntryTime.eval (stream xs).length) := by
  have ha:=entryExec n keep xs hx a b c d q hq hf
  have h:=RetainedInput.executes (entryMachine n keep) (stream xs)
    (unary ((a*c+b*d)%q)++[false]) _ ha
  rw [show (unary ((a*c+b*d)%q)++[false])++stream xs=stream (((a*c+b*d)%q)::xs) by
    simp only [stream,List.append_assoc,List.singleton_append]] at h
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hl:=fields_stream_length_le n keep 0 xs
  rw [hf] at hl
  have hqL:q≤(stream xs).length := by
    have hs:(stream [a,b,c,d,q]).length=a+b+c+d+q+5 := by
      simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
    rw [hs] at hl
    omega
  have hv:(a*c+b*d)%q<q:=Nat.mod_lt _ hq
  simp only [entryTime,retainedEntryTime,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,
    List.length_append,List.length_singleton,unary_length]
  nlinarith [sq_nonneg ((stream xs).length+1)]
def mask00 (k:Fin 9):Bool := k.val==0 || k.val==1 || k.val==4 || k.val==6 || k.val==8
def mask01 (k:Fin 10):Bool := k.val==1 || k.val==2 || k.val==6 || k.val==8 || k.val==9
def mask10 (k:Fin 11):Bool := k.val==4 || k.val==5 || k.val==6 || k.val==8 || k.val==10
def mask11 (k:Fin 12):Bool := k.val==5 || k.val==6 || k.val==8 || k.val==10 || k.val==11
def maskOutput (k:Fin 13):Bool := k.val==0 || k.val==1 || k.val==2 || k.val==3
theorem select00 (a b c d e f g h q:ℕ) : fields 8 mask00 0 [a,b,c,d,e,f,g,h,q]=[a,b,e,g,q] := by
  simp [fields,maskAt,mask00]
theorem select01 (u a b c d e f g h q:ℕ) : fields 9 mask01 0 [u,a,b,c,d,e,f,g,h,q]=[a,b,f,h,q] := by
  simp [fields,maskAt,mask01]
theorem select10 (v u a b c d e f g h q:ℕ) : fields 10 mask10 0 [v,u,a,b,c,d,e,f,g,h,q]=[c,d,e,g,q] := by
  simp [fields,maskAt,mask10]
theorem select11 (w v u a b c d e f g h q:ℕ) : fields 11 mask11 0 [w,v,u,a,b,c,d,e,f,g,h,q]=[c,d,f,h,q] := by
  simp [fields,maskAt,mask11]
theorem selectOutput (z w v u a b c d e f g h q:ℕ) :
    fields 12 maskOutput 0 [z,w,v,u,a,b,c,d,e,f,g,h,q]=[z,w,v,u] := by
  simp [fields,maskAt,maskOutput]
def outputMachine := Composition.machine (machine 12 maskOutput) BitReverse.machine
def productMachine := Composition.machine (retainedEntryMachine 8 mask00)
  (Composition.machine (retainedEntryMachine 9 mask01)
    (Composition.machine (retainedEntryMachine 10 mask10)
      (Composition.machine (retainedEntryMachine 11 mask11) outputMachine)))
noncomputable def exec (a b c d e f g h q:ℕ) (hq:0<q) := by
  let u:ℕ:=(a*e+b*g)%q
  let v:ℕ:=(a*f+b*h)%q
  let w:ℕ:=(c*e+d*g)%q
  let z:ℕ:=(c*f+d*h)%q
  have h00:=retainedEntryExec 8 mask00 [a,b,c,d,e,f,g,h,q] (by simp) a b e g q hq (select00 ..)
  have h01:=retainedEntryExec 9 mask01 [u,a,b,c,d,e,f,g,h,q] (by simp) a b f h q hq (select01 ..)
  have h10:=retainedEntryExec 10 mask10 [v,u,a,b,c,d,e,f,g,h,q] (by simp) c d e g q hq (select10 ..)
  have h11:=retainedEntryExec 11 mask11 [w,v,u,a,b,c,d,e,f,g,h,q] (by simp) c d f h q hq (select11 ..)
  have hp:=FieldProjection.polyExec 12 maskOutput [z,w,v,u,a,b,c,d,e,f,g,h,q] (by simp)
  rw [selectOutput] at hp
  have hr:=BitReverse.exec (raw [z,w,v,u])
  rw [reverse_raw_four] at hr
  have ho:=Composition.executes (machine 12 maskOutput) BitReverse.machine
    (stream [z,w,v,u,a,b,c,d,e,f,g,h,q]) (raw [z,w,v,u]) (raw [u,v,w,z]) _ _ hp hr
  have h11o:=Composition.executes (retainedEntryMachine 11 mask11) outputMachine
    (stream [w,v,u,a,b,c,d,e,f,g,h,q]) (stream [z,w,v,u,a,b,c,d,e,f,g,h,q])
    (raw [u,v,w,z]) _ _ h11 ho
  have h10o:=Composition.executes (retainedEntryMachine 10 mask10)
    (Composition.machine (retainedEntryMachine 11 mask11) outputMachine)
    (stream [v,u,a,b,c,d,e,f,g,h,q]) (stream [w,v,u,a,b,c,d,e,f,g,h,q])
    (raw [u,v,w,z]) _ _ h10 h11o
  have h01o:=Composition.executes (retainedEntryMachine 9 mask01)
    (Composition.machine (retainedEntryMachine 10 mask10)
      (Composition.machine (retainedEntryMachine 11 mask11) outputMachine))
    (stream [u,a,b,c,d,e,f,g,h,q]) (stream [v,u,a,b,c,d,e,f,g,h,q])
    (raw [u,v,w,z]) _ _ h01 h10o
  exact Composition.executes (retainedEntryMachine 8 mask00)
    (Composition.machine (retainedEntryMachine 9 mask01)
      (Composition.machine (retainedEntryMachine 10 mask10)
        (Composition.machine (retainedEntryMachine 11 mask11) outputMachine)))
    (stream [a,b,c,d,e,f,g,h,q]) (stream [u,a,b,c,d,e,f,g,h,q]) (raw [u,v,w,z]) _ _ h00 h01o
noncomputable def time : Polynomial ℕ := Polynomial.C 20000*(Polynomial.X+1)^2
noncomputable def polyExec (a b c d e f g h q:ℕ) (hq:0<q) :
    EvalsToInTime (TM2.step productMachine.program) (productMachine.init (stream [a,b,c,d,e,f,g,h,q]))
      (some (productMachine.halt (raw [(a*e+b*g)%q,(a*f+b*h)%q,(c*e+d*g)%q,(c*f+d*h)%q])))
      (time.eval (stream [a,b,c,d,e,f,g,h,q]).length) := by
  have hh:=exec a b c d e f g h q hq
  refine {hh with steps_le_m:=hh.steps_le_m.trans ?_}
  let u:ℕ:=(a*e+b*g)%q
  let v:ℕ:=(a*f+b*h)%q
  let w:ℕ:=(c*e+d*g)%q
  let z:ℕ:=(c*f+d*h)%q
  have hu:u<q:=Nat.mod_lt _ hq
  have hv:v<q:=Nat.mod_lt _ hq
  have hw:w<q:=Nat.mod_lt _ hq
  have hz:z<q:=Nat.mod_lt _ hq
  let L:ℕ:=(stream [a,b,c,d,e,f,g,h,q]).length
  let L1:ℕ:=(stream [u,a,b,c,d,e,f,g,h,q]).length
  let L2:ℕ:=(stream [v,u,a,b,c,d,e,f,g,h,q]).length
  let L3:ℕ:=(stream [w,v,u,a,b,c,d,e,f,g,h,q]).length
  let L4:ℕ:=(stream [z,w,v,u,a,b,c,d,e,f,g,h,q]).length
  have hqL:q+1≤L := by
    dsimp only [L];simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have h1:L1=L+u+1 := by
    dsimp only [L1,L];simp only [stream,List.length_append,List.length_cons,unary_length];omega
  have h2:L2=L1+v+1 := by
    dsimp only [L2,L1];simp only [stream,List.length_append,List.length_cons,unary_length];omega
  have h3:L3=L2+w+1 := by
    dsimp only [L3,L2];simp only [stream,List.length_append,List.length_cons,unary_length];omega
  have h4:L4=L3+z+1 := by
    dsimp only [L4,L3];simp only [stream,List.length_append,List.length_cons,unary_length];omega
  have hs1:(L1+1)^2≤4*(L+1)^2 := by
    calc _≤(2*(L+1))^2:=Nat.pow_le_pow_left (by omega) 2
         _=4*(L+1)^2:=by ring
  have hs2:(L2+1)^2≤9*(L+1)^2 := by
    calc _≤(3*(L+1))^2:=Nat.pow_le_pow_left (by omega) 2
         _=9*(L+1)^2:=by ring
  have hs3:(L3+1)^2≤16*(L+1)^2 := by
    calc _≤(4*(L+1))^2:=Nat.pow_le_pow_left (by omega) 2
         _=16*(L+1)^2:=by ring
  have hr:(raw [z,w,v,u]).length≤4*L := by
    have ht:=raw_length_le [z,w,v,u]
    have hs:(stream [z,w,v,u]).length=z+w+v+u+4 := by
      simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
    rw [hs] at ht;omega
  change (raw [z,w,v,u]).length+1+(2*(raw [z,w,v,u]).length+2)+FieldProjection.time.eval L4+
    (2*L4+2)+retainedEntryTime.eval L3+(2*L3+2)+retainedEntryTime.eval L2+
    (2*L2+2)+retainedEntryTime.eval L1+(2*L1+2)+retainedEntryTime.eval L≤time.eval L
  simp only [time,retainedEntryTime,FieldProjection.time,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  nlinarith [sq_nonneg (L+1)]
end QEC.Coding.BitTuring.UnaryArithmetic.ModularMatrixProduct
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularMatrixProduct
open Turing
open FieldProjection
structure Input where
  a:ℕ
  b:ℕ
  c:ℕ
  d:ℕ
  e:ℕ
  f:ℕ
  g:ℕ
  h:ℕ
  q:ℕ+
def input (x:Input) := stream [x.a,x.b,x.c,x.d,x.e,x.f,x.g,x.h,x.q.val]
def output (x:Input) := raw [(x.a*x.e+x.b*x.g)%x.q.val,(x.a*x.f+x.b*x.h)%x.q.val,
  (x.c*x.e+x.d*x.g)%x.q.val,(x.c*x.f+x.d*x.h)%x.q.val]
noncomputable def outputsInTime (a b c d e f g h q:ℕ) (hq:0<q) :
    TM2OutputsInTime productMachine.toFinTM2 (stream [a,b,c,d,e,f,g,h,q])
      (some (raw [(a*e+b*g)%q,(a*f+b*h)%q,(c*e+d*g)%q,(c*f+d*h)%q]))
      (time.eval (stream [a,b,c,d,e,f,g,h,q]).length) :=
  Machine.outputsInTime productMachine _ _ _ (polyExec a b c d e f g h q hq)
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input id output where
  tm:=productMachine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time
  outputsFun:=fun x=>by
    change TM2OutputsInTime productMachine.toFinTM2 (List.map id (input x))
      (some (List.map id (output x))) (time.eval (input x).length)
    have h:=outputsInTime x.a x.b x.c x.d x.e x.f x.g x.h x.q.val x.q.pos
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input,output] using h
end QEC.Coding.BitTuring.UnaryArithmetic.ModularMatrixProduct


