-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryQuaternionMatrix
-- name    : QEC_Coding_BitTuring_UnaryQuaternionMatrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:12:20.203197+00:00
-- url     : https://prove2.me/theorems/ca0af5d6-98d8-43ce-a81a-bdd67933289e
-- title:
--   Unary Quaternion Matrix
-- statement:
--   Definitions and structural lemmas for Unary Quaternion Matrix, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryQuaternionMatrix.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularAdjugate
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularSum
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryInverseInput
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Definitions.Def_QEC_Coding_BitTuring_ModulusQuery
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Mathlib.Tactic.Linarith
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_fields_stream_length_le
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_length_le
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_triple
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_reverse_raw_four
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_length
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly
open Turing StateTransition FieldProjection
def retainedBinary (n:ℕ) (keep:Fin (n+1)→Bool) (body:Machine) :=
  RetainedInput.machine (Composition.machine (FieldProjection.machine n keep)
    (Composition.machine body UnaryDelimiter.machine))
noncomputable def binaryStageExec (n:ℕ) (keep:Fin (n+1)→Bool) (body:Machine) (p:Polynomial ℕ)
    (xs:List ℕ) (hx:xs.length=n+1) (a b q r:ℕ) (hr:r<q)
    (hf:fields n keep 0 xs=[a,b,q])
    (hb:EvalsToInTime (TM2.step body.program) (body.init (FactorTest.tripleInput a b q))
      (some (body.halt (unary r))) (p.eval (FactorTest.tripleInput a b q).length)) :
    EvalsToInTime (TM2.step (retainedBinary n keep body).program)
      ((retainedBinary n keep body).init (stream xs))
      (some ((retainedBinary n keep body).halt (stream (r::xs))))
      ((ModulusQuery.time p).eval (stream xs).length) := by
  have hp:=FieldProjection.polyExec n keep xs hx
  rw [hf,raw_triple] at hp
  have hd:=Composition.executes body UnaryDelimiter.machine _ _ _ _ _ hb (UnaryDelimiter.exec r)
  have hbody:=Composition.executes (FieldProjection.machine n keep)
    (Composition.machine body UnaryDelimiter.machine) _ _ _ _ _ hp hd
  have h:=RetainedInput.executes
    (Composition.machine (FieldProjection.machine n keep) (Composition.machine body UnaryDelimiter.machine))
    (stream xs) (unary r++[false]) _ hbody
  rw [show (unary r++[false])++stream xs=stream (r::xs) by simp [stream,List.append_assoc]] at h
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hs:=fields_stream_length_le n keep 0 xs
  rw [hf] at hs
  have hslen:(stream [a,b,q]).length=a+b+q+3 := by
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  rw [hslen] at hs
  have hL:(FactorTest.tripleInput a b q).length≤(stream xs).length := by
    rw [FactorTest.tripleInput_length];omega
  have hpol:p.eval (FactorTest.tripleInput a b q).length≤p.eval (stream xs).length :=
    Composition.polynomial_eval_monotone p hL
  simp only [ModulusQuery.time,FieldProjection.time,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,unary_length,
    List.length_append,List.length_singleton]
  omega
noncomputable def productStageExec (n:ℕ) (keep:Fin (n+1)→Bool) (xs:List ℕ) (hx:xs.length=n+1)
    (a b q:ℕ) (hq:0<q) (hf:fields n keep 0 xs=[a,b,q]) :=
  binaryStageExec n keep ModularProduct.machine ModularProduct.time xs hx a b q ((a*b)%q)
    (Nat.mod_lt _ hq) hf (ModularProduct.polyExec a b q hq)
noncomputable def sumStageExec (n:ℕ) (keep:Fin (n+1)→Bool) (xs:List ℕ) (hx:xs.length=n+1)
    (a b q:ℕ) (hq:0<q) (hf:fields n keep 0 xs=[a,b,q]) :=
  binaryStageExec n keep ModularSum.machine ModularSum.time xs hx a b q ((a+b)%q)
    (Nat.mod_lt _ hq) hf (ModularSum.polyExec a b q hq)
theorem negation_lt (a q:ℕ) (hq:0<q) (ha:a<q) : ModularNegation.output a q<q := by
  unfold ModularNegation.output
  split_ifs <;> omega
def mask0 (k:Fin 7):Bool := k.val==1 || k.val==2 || k.val==6
theorem select0 (S Y D C B A q:ℕ) : fields 6 mask0 0 [S,Y,D,C,B,A,q]=[Y,D,q] := by
  simp [fields,maskAt,mask0]
def stage0 := retainedBinary 6 mask0 ModularProduct.machine
def mask1 (k:Fin 8):Bool := k.val==2 || k.val==5 || k.val==7
theorem select1 (S Y D C B A q u:ℕ) : fields 7 mask1 0 [u,S,Y,D,C,B,A,q]=[Y,B,q] := by
  simp [fields,maskAt,mask1]
def stage1 := retainedBinary 7 mask1 ModularProduct.machine
def mask2 (k:Fin 9):Bool := k.val==0 || k.val==8
theorem select2 (S Y D C B A q u v:ℕ) : fields 8 mask2 0 [v,u,S,Y,D,C,B,A,q]=[v,q] := by
  simp [fields,maskAt,mask2]
def stage2 := ModularAdjugate.retainedNegation 8 mask2
def mask3 (k:Fin 10):Bool := k.val==6 || k.val==9
theorem select3 (S Y D C B A q u v nv:ℕ) : fields 9 mask3 0 [nv,v,u,S,Y,D,C,B,A,q]=[C,q] := by
  simp [fields,maskAt,mask3]
def stage3 := ModularAdjugate.retainedNegation 9 mask3
def mask4 (k:Fin 11):Bool := k.val==3 || k.val==10
theorem select4 (S Y D C B A q u v nv nc:ℕ) : fields 10 mask4 0 [nc,nv,v,u,S,Y,D,C,B,A,q]=[u,q] := by
  simp [fields,maskAt,mask4]
def stage4 := ModularAdjugate.retainedNegation 10 mask4
def mask5 (k:Fin 12):Bool := k.val==4 || k.val==10 || k.val==11
theorem select5 (S Y D C B A q u v nv nc nu:ℕ) : fields 11 mask5 0 [nu,nc,nv,v,u,S,Y,D,C,B,A,q]=[u,A,q] := by
  simp [fields,maskAt,mask5]
def stage5 := retainedBinary 11 mask5 ModularSum.machine
def mask6 (k:Fin 13):Bool := k.val==0 || k.val==6 || k.val==12
theorem select6 (S Y D C B A q u v nv nc nu f00:ℕ) : fields 12 mask6 0 [f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]=[f00,S,q] := by
  simp [fields,maskAt,mask6]
def stage6 := retainedBinary 12 mask6 ModularProduct.machine
def mask7 (k:Fin 14):Bool := k.val==4 || k.val==10 || k.val==13
theorem select7 (S Y D C B A q u v nv nc nu f00 e00:ℕ) : fields 13 mask7 0 [e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]=[nv,C,q] := by
  simp [fields,maskAt,mask7]
def stage7 := retainedBinary 13 mask7 ModularSum.machine
def mask8 (k:Fin 15):Bool := k.val==0 || k.val==8 || k.val==14
theorem select8 (S Y D C B A q u v nv nc nu f00 e00 f01:ℕ) : fields 14 mask8 0 [f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]=[f01,S,q] := by
  simp [fields,maskAt,mask8]
def stage8 := retainedBinary 14 mask8 ModularProduct.machine
def mask9 (k:Fin 16):Bool := k.val==5 || k.val==6 || k.val==15
theorem select9 (S Y D C B A q u v nv nc nu f00 e00 f01 e01:ℕ) : fields 15 mask9 0 [e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]=[nc,nv,q] := by
  simp [fields,maskAt,mask9]
def stage9 := retainedBinary 15 mask9 ModularSum.machine
def mask10 (k:Fin 17):Bool := k.val==0 || k.val==10 || k.val==16
theorem select10 (S Y D C B A q u v nv nc nu f00 e00 f01 e01 f10:ℕ) : fields 16 mask10 0 [f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]=[f10,S,q] := by
  simp [fields,maskAt,mask10]
def stage10 := retainedBinary 16 mask10 ModularProduct.machine
def mask11 (k:Fin 18):Bool := k.val==6 || k.val==16 || k.val==17
theorem select11 (S Y D C B A q u v nv nc nu f00 e00 f01 e01 f10 e10:ℕ) : fields 17 mask11 0 [e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]=[nu,A,q] := by
  simp [fields,maskAt,mask11]
def stage11 := retainedBinary 17 mask11 ModularSum.machine
def mask12 (k:Fin 19):Bool := k.val==0 || k.val==12 || k.val==18
theorem select12 (S Y D C B A q u v nv nc nu f00 e00 f01 e01 f10 e10 f11:ℕ) : fields 18 mask12 0 [f11,e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]=[f11,S,q] := by
  simp [fields,maskAt,mask12]
def stage12 := retainedBinary 18 mask12 ModularProduct.machine
def maskOutput (k:Fin 20):Bool := k.val==0 || k.val==2 || k.val==4 || k.val==6
theorem selectOutput (S Y D C B A q u v nv nc nu f00 e00 f01 e01 f10 e10 f11 e11:ℕ) : fields 19 maskOutput 0 [e11,f11,e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]=[e11,e10,e01,e00] := by
  simp [fields,maskAt,maskOutput]
def outputMachine := Composition.machine (FieldProjection.machine 19 maskOutput) BitReverse.machine
def machine := (Composition.machine stage0 (Composition.machine stage1 (Composition.machine stage2 (Composition.machine stage3 (Composition.machine stage4 (Composition.machine stage5 (Composition.machine stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 (Composition.machine stage12 outputMachine)))))))))))))
def output (S Y D C B A q:ℕ) :=
  let u:=(Y*D)%q
  let v:=(Y*B)%q
  let nv:=ModularNegation.output v q
  let nc:=ModularNegation.output C q
  let nu:=ModularNegation.output u q
  let f00:=(u+A)%q
  let e00:=(f00*S)%q
  let f01:=(nv+C)%q
  let e01:=(f01*S)%q
  let f10:=(nc+nv)%q
  let e10:=(f10*S)%q
  let f11:=(nu+A)%q
  let e11:=(f11*S)%q
  raw [e00,e01,e10,e11]
noncomputable def exec (S Y D C B A q:ℕ) (hq:0<q) (hc:C<q) := by
  let u:=(Y*D)%q
  let v:=(Y*B)%q
  let nv:=ModularNegation.output v q
  let nc:=ModularNegation.output C q
  let nu:=ModularNegation.output u q
  let f00:=(u+A)%q
  let e00:=(f00*S)%q
  let f01:=(nv+C)%q
  let e01:=(f01*S)%q
  let f10:=(nc+nv)%q
  let e10:=(f10*S)%q
  let f11:=(nu+A)%q
  let e11:=(f11*S)%q
  have hu:u<q:=Nat.mod_lt _ hq
  have hv:v<q:=Nat.mod_lt _ hq
  have hf00:f00<q:=Nat.mod_lt _ hq
  have he00:e00<q:=Nat.mod_lt _ hq
  have hf01:f01<q:=Nat.mod_lt _ hq
  have he01:e01<q:=Nat.mod_lt _ hq
  have hf10:f10<q:=Nat.mod_lt _ hq
  have he10:e10<q:=Nat.mod_lt _ hq
  have hf11:f11<q:=Nat.mod_lt _ hq
  have he11:e11<q:=Nat.mod_lt _ hq
  have hnv:nv<q:=negation_lt v q hq hv
  have hnc:nc<q:=negation_lt C q hq hc
  have hnu:nu<q:=negation_lt u q hq hu
  have h0:=productStageExec 6 mask0 [S,Y,D,C,B,A,q] (by simp) Y D q hq (select0 S Y D C B A q)
  have h1:=productStageExec 7 mask1 [u,S,Y,D,C,B,A,q] (by simp) Y B q hq (select1 S Y D C B A q u)
  have h2:=ModularAdjugate.negationStageExec 8 mask2 [v,u,S,Y,D,C,B,A,q] (by simp) v q hv (select2 S Y D C B A q u v)
  have h3:=ModularAdjugate.negationStageExec 9 mask3 [nv,v,u,S,Y,D,C,B,A,q] (by simp) C q hc (select3 S Y D C B A q u v nv)
  have h4:=ModularAdjugate.negationStageExec 10 mask4 [nc,nv,v,u,S,Y,D,C,B,A,q] (by simp) u q hu (select4 S Y D C B A q u v nv nc)
  have h5:=sumStageExec 11 mask5 [nu,nc,nv,v,u,S,Y,D,C,B,A,q] (by simp) u A q hq (select5 S Y D C B A q u v nv nc nu)
  have h6:=productStageExec 12 mask6 [f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q] (by simp) f00 S q hq (select6 S Y D C B A q u v nv nc nu f00)
  have h7:=sumStageExec 13 mask7 [e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q] (by simp) nv C q hq (select7 S Y D C B A q u v nv nc nu f00 e00)
  have h8:=productStageExec 14 mask8 [f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q] (by simp) f01 S q hq (select8 S Y D C B A q u v nv nc nu f00 e00 f01)
  have h9:=sumStageExec 15 mask9 [e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q] (by simp) nc nv q hq (select9 S Y D C B A q u v nv nc nu f00 e00 f01 e01)
  have h10:=productStageExec 16 mask10 [f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q] (by simp) f10 S q hq (select10 S Y D C B A q u v nv nc nu f00 e00 f01 e01 f10)
  have h11:=sumStageExec 17 mask11 [e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q] (by simp) nu A q hq (select11 S Y D C B A q u v nv nc nu f00 e00 f01 e01 f10 e10)
  have h12:=productStageExec 18 mask12 [f11,e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q] (by simp) f11 S q hq (select12 S Y D C B A q u v nv nc nu f00 e00 f01 e01 f10 e10 f11)
  have hp:=FieldProjection.polyExec 19 maskOutput [e11,f11,e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q] (by simp)
  rw [selectOutput] at hp
  have hr:=BitReverse.exec (raw [e11,e10,e01,e00])
  rw [reverse_raw_four] at hr
  have ho:=Composition.executes (FieldProjection.machine 19 maskOutput) BitReverse.machine _ _ _ _ _ hp hr
  have hc12:=Composition.executes stage12 outputMachine _ _ _ _ _ h12 ho
  have hc11:=Composition.executes stage11 (Composition.machine stage12 outputMachine) _ _ _ _ _ h11 hc12
  have hc10:=Composition.executes stage10 (Composition.machine stage11 (Composition.machine stage12 outputMachine)) _ _ _ _ _ h10 hc11
  have hc9:=Composition.executes stage9 (Composition.machine stage10 (Composition.machine stage11 (Composition.machine stage12 outputMachine))) _ _ _ _ _ h9 hc10
  have hc8:=Composition.executes stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 (Composition.machine stage12 outputMachine)))) _ _ _ _ _ h8 hc9
  have hc7:=Composition.executes stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 (Composition.machine stage12 outputMachine))))) _ _ _ _ _ h7 hc8
  have hc6:=Composition.executes stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 (Composition.machine stage12 outputMachine)))))) _ _ _ _ _ h6 hc7
  have hc5:=Composition.executes stage5 (Composition.machine stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 (Composition.machine stage12 outputMachine))))))) _ _ _ _ _ h5 hc6
  have hc4:=Composition.executes stage4 (Composition.machine stage5 (Composition.machine stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 (Composition.machine stage12 outputMachine)))))))) _ _ _ _ _ h4 hc5
  have hc3:=Composition.executes stage3 (Composition.machine stage4 (Composition.machine stage5 (Composition.machine stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 (Composition.machine stage12 outputMachine))))))))) _ _ _ _ _ h3 hc4
  have hc2:=Composition.executes stage2 (Composition.machine stage3 (Composition.machine stage4 (Composition.machine stage5 (Composition.machine stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 (Composition.machine stage12 outputMachine)))))))))) _ _ _ _ _ h2 hc3
  have hc1:=Composition.executes stage1 (Composition.machine stage2 (Composition.machine stage3 (Composition.machine stage4 (Composition.machine stage5 (Composition.machine stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 (Composition.machine stage12 outputMachine))))))))))) _ _ _ _ _ h1 hc2
  have hc0:=Composition.executes stage0 (Composition.machine stage1 (Composition.machine stage2 (Composition.machine stage3 (Composition.machine stage4 (Composition.machine stage5 (Composition.machine stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 (Composition.machine stage12 outputMachine)))))))))))) _ _ _ _ _ h0 hc1
  exact hc0
noncomputable def time : Polynomial ℕ := Polynomial.C 100000*(Polynomial.X+1)^2
noncomputable def polyExec (S Y D C B A q:ℕ) (hq:0<q) (hc:C<q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (stream [S,Y,D,C,B,A,q]))
      (some (machine.halt (output S Y D C B A q)))
      (time.eval (stream [S,Y,D,C,B,A,q]).length) := by
  have h:=exec S Y D C B A q hq hc
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  let u:=(Y*D)%q
  let v:=(Y*B)%q
  let nv:=ModularNegation.output v q
  let nc:=ModularNegation.output C q
  let nu:=ModularNegation.output u q
  let f00:=(u+A)%q
  let e00:=(f00*S)%q
  let f01:=(nv+C)%q
  let e01:=(f01*S)%q
  let f10:=(nc+nv)%q
  let e10:=(f10*S)%q
  let f11:=(nu+A)%q
  let e11:=(f11*S)%q
  have hu:u<q:=Nat.mod_lt _ hq
  have hv:v<q:=Nat.mod_lt _ hq
  have hf00:f00<q:=Nat.mod_lt _ hq
  have he00:e00<q:=Nat.mod_lt _ hq
  have hf01:f01<q:=Nat.mod_lt _ hq
  have he01:e01<q:=Nat.mod_lt _ hq
  have hf10:f10<q:=Nat.mod_lt _ hq
  have he10:e10<q:=Nat.mod_lt _ hq
  have hf11:f11<q:=Nat.mod_lt _ hq
  have he11:e11<q:=Nat.mod_lt _ hq
  have hnv:nv<q:=negation_lt v q hq hv
  have hnc:nc<q:=negation_lt C q hq hc
  have hnu:nu<q:=negation_lt u q hq hu
  let L:ℕ:=(stream [S,Y,D,C,B,A,q]).length
  let Bnd:ℕ:=(L+1)^2
  have hLB:L+1≤Bnd := by dsimp only [Bnd];nlinarith
  have hProd (m:ℕ) (hm:m≤14*L) :
      (ModulusQuery.time ModularProduct.time).eval m≤9800*Bnd := by
    have hsq:(m+1)^2≤196*Bnd := by
      calc
        (m+1)^2≤(14*(L+1))^2:=Nat.pow_le_pow_left (by omega) 2
        _=196*Bnd:=by dsimp only [Bnd];ring
    have hlin:m+1≤14*Bnd := by omega
    simp only [ModulusQuery.time,ModularProduct.time,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_pow]
    omega
  have hSum (m:ℕ) (hm:m≤14*L) :
      (ModulusQuery.time ModularSum.time).eval m≤420*Bnd := by
    have hlin:m+1≤14*Bnd := by omega
    simp only [ModulusQuery.time,ModularSum.time,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hNeg (m:ℕ) (hm:m≤14*L) :
      ModularAdjugate.stageTime.eval m≤420*Bnd := by
    have hlin:m+1≤14*Bnd := by omega
    simp only [ModularAdjugate.stageTime,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hL0:(stream [S,Y,D,C,B,A,q]).length≤14*L := by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have hT0:(ModulusQuery.time ModularProduct.time).eval (stream [S,Y,D,C,B,A,q]).length≤9800*Bnd:=
    hProd _ hL0
  have hL1:(stream [u,S,Y,D,C,B,A,q]).length≤14*L := by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have hT1:(ModulusQuery.time ModularProduct.time).eval (stream [u,S,Y,D,C,B,A,q]).length≤9800*Bnd:=
    hProd _ hL1
  have hL2:(stream [v,u,S,Y,D,C,B,A,q]).length≤14*L := by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have hT2:(ModularAdjugate.stageTime).eval (stream [v,u,S,Y,D,C,B,A,q]).length≤420*Bnd:=
    hNeg _ hL2
  have hL3:(stream [nv,v,u,S,Y,D,C,B,A,q]).length≤14*L := by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have hT3:(ModularAdjugate.stageTime).eval (stream [nv,v,u,S,Y,D,C,B,A,q]).length≤420*Bnd:=
    hNeg _ hL3
  have hL4:(stream [nc,nv,v,u,S,Y,D,C,B,A,q]).length≤14*L := by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have hT4:(ModularAdjugate.stageTime).eval (stream [nc,nv,v,u,S,Y,D,C,B,A,q]).length≤420*Bnd:=
    hNeg _ hL4
  have hL5:(stream [nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤14*L := by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have hT5:(ModulusQuery.time ModularSum.time).eval (stream [nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤420*Bnd:=
    hSum _ hL5
  have hL6:(stream [f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤14*L := by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have hT6:(ModulusQuery.time ModularProduct.time).eval (stream [f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤9800*Bnd:=
    hProd _ hL6
  have hL7:(stream [e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤14*L := by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have hT7:(ModulusQuery.time ModularSum.time).eval (stream [e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤420*Bnd:=
    hSum _ hL7
  have hL8:(stream [f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤14*L := by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have hT8:(ModulusQuery.time ModularProduct.time).eval (stream [f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤9800*Bnd:=
    hProd _ hL8
  have hL9:(stream [e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤14*L := by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have hT9:(ModulusQuery.time ModularSum.time).eval (stream [e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤420*Bnd:=
    hSum _ hL9
  have hL10:(stream [f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤14*L := by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have hT10:(ModulusQuery.time ModularProduct.time).eval (stream [f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤9800*Bnd:=
    hProd _ hL10
  have hL11:(stream [e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤14*L := by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have hT11:(ModulusQuery.time ModularSum.time).eval (stream [e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤420*Bnd:=
    hSum _ hL11
  have hL12:(stream [f11,e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤14*L := by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have hT12:(ModulusQuery.time ModularProduct.time).eval (stream [f11,e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤9800*Bnd:=
    hProd _ hL12
  have hL13:(stream [e11,f11,e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length≤14*L := by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have hR:(raw [e11,e10,e01,e00]).length≤4*L := by
    have hraw:=raw_length_le [e11,e10,e01,e00]
    have he:(stream [e11,e10,e01,e00]).length=e11+e10+e01+e00+4 := by
      simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
    rw [he] at hraw
    have hqL:q+1≤L := by
      dsimp only [L]
      simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
    omega
  change (raw [e11,e10,e01,e00]).length+1+(2*(raw [e11,e10,e01,e00]).length+2)+FieldProjection.time.eval (stream [e11,f11,e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+(2*(stream [e11,f11,e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+2)+(ModulusQuery.time ModularProduct.time).eval (stream [f11,e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+(2*(stream [f11,e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+2)+(ModulusQuery.time ModularSum.time).eval (stream [e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+(2*(stream [e10,f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+2)+(ModulusQuery.time ModularProduct.time).eval (stream [f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+(2*(stream [f10,e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+2)+(ModulusQuery.time ModularSum.time).eval (stream [e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+(2*(stream [e01,f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+2)+(ModulusQuery.time ModularProduct.time).eval (stream [f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+(2*(stream [f01,e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+2)+(ModulusQuery.time ModularSum.time).eval (stream [e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+(2*(stream [e00,f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+2)+(ModulusQuery.time ModularProduct.time).eval (stream [f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+(2*(stream [f00,nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+2)+(ModulusQuery.time ModularSum.time).eval (stream [nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+(2*(stream [nu,nc,nv,v,u,S,Y,D,C,B,A,q]).length+2)+(ModularAdjugate.stageTime).eval (stream [nc,nv,v,u,S,Y,D,C,B,A,q]).length+(2*(stream [nc,nv,v,u,S,Y,D,C,B,A,q]).length+2)+(ModularAdjugate.stageTime).eval (stream [nv,v,u,S,Y,D,C,B,A,q]).length+(2*(stream [nv,v,u,S,Y,D,C,B,A,q]).length+2)+(ModularAdjugate.stageTime).eval (stream [v,u,S,Y,D,C,B,A,q]).length+(2*(stream [v,u,S,Y,D,C,B,A,q]).length+2)+(ModulusQuery.time ModularProduct.time).eval (stream [u,S,Y,D,C,B,A,q]).length+(2*(stream [u,S,Y,D,C,B,A,q]).length+2)+(ModulusQuery.time ModularProduct.time).eval (stream [S,Y,D,C,B,A,q]).length≤time.eval L
  simp only [FieldProjection.time,time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_pow]
  change _≤100000*Bnd
  omega
open Turing StateTransition FieldProjection
open Turing FieldProjection
structure Input where
  S:ℕ
  Y:ℕ
  D:ℕ
  C:ℕ
  B:ℕ
  A:ℕ
  q:ℕ+
  c_lt:C<q.val
def input (x:Input) := stream [x.S,x.Y,x.D,x.C,x.B,x.A,x.q.val]
def result (x:Input) := output x.S x.Y x.D x.C x.B x.A x.q.val
noncomputable def outputsInTime (S Y D C B A q:ℕ) (hq:0<q) (hc:C<q) :
    TM2OutputsInTime machine.toFinTM2 (stream [S,Y,D,C,B,A,q]) (some (output S Y D C B A q))
      (time.eval (stream [S,Y,D,C,B,A,q]).length) :=
  Machine.outputsInTime machine _ _ _ (polyExec S Y D C B A q hq hc)
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input id result where
  tm:=machine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time
  outputsFun:=fun x=>by
    change TM2OutputsInTime machine.toFinTM2 (List.map id (input x)) (some (List.map id (result x)))
      (time.eval (input x).length)
    have h:=outputsInTime x.S x.Y x.D x.C x.B x.A x.q.val x.q.pos x.c_lt
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input,result] using h
end QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly


