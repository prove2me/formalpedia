-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryDeterminantPredicate
-- name    : QEC_Coding_BitTuring_UnaryDeterminantPredicate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:13:25.347445+00:00
-- url     : https://prove2.me/theorems/630b8732-eca1-4cac-8eb0-37216954f454
-- title:
--   Unary Determinant Predicate
-- statement:
--   Definitions and structural lemmas for Unary Determinant Predicate, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryDeterminantPredicate.lean

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_QEC_Coding_BitTuring_UnaryQuaternionMatrix
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection QuaternionAssembly
def mask0 (k:Fin 5):Bool:=k.val==0 || k.val==3 || k.val==4
theorem select0 (a b c d q:ℕ):fields 4 mask0 0 [a,b,c,d,q]=[a,d,q] :=by simp [fields,maskAt,mask0]
def stage0:=retainedBinary 4 mask0 ModularProduct.machine
def mask1 (k:Fin 6):Bool:=k.val==2 || k.val==3 || k.val==5
theorem select1 (ad a b c d q:ℕ):fields 5 mask1 0 [ad,a,b,c,d,q]=[b,c,q] :=by simp [fields,maskAt,mask1]
def stage1:=retainedBinary 5 mask1 ModularProduct.machine
def mask2 (k:Fin 7):Bool:=k.val==0 || k.val==6
theorem select2 (bc ad a b c d q:ℕ):fields 6 mask2 0 [bc,ad,a,b,c,d,q]=[bc,q] :=by simp [fields,maskAt,mask2]
def stage2:=ModularAdjugate.retainedNegation 6 mask2
def mask3 (k:Fin 8):Bool:=k.val==0 || k.val==2 || k.val==7
theorem select3 (nbc bc ad a b c d q:ℕ):fields 7 mask3 0 [nbc,bc,ad,a,b,c,d,q]=[nbc,ad,q] :=by simp [fields,maskAt,mask3]
def stage3:=retainedBinary 7 mask3 ModularSum.machine
def outputMask (k:Fin 9):Bool:=k.val==0
theorem selectOutput (r nbc bc ad a b c d q:ℕ):fields 8 outputMask 0 [r,nbc,bc,ad,a,b,c,d,q]=[r] :=by simp [fields,maskAt,outputMask]
def arithmeticMachine:=Composition.machine stage0 (Composition.machine stage1
   (Composition.machine stage2 (Composition.machine stage3 (FieldProjection.machine 8 outputMask))))
def result (a b c d q:ℕ):ℕ :=(ModularNegation.output ((b*c)%q) q+(a*d)%q)%q
noncomputable def exec (a b c d q:ℕ) (hq:0<q) :=by
  let ad:=(a*d)%q
  let bc:=(b*c)%q
  let nbc:=ModularNegation.output bc q
  let r:=result a b c d q
  have h0:=productStageExec 4 mask0 [a,b,c,d,q] (by simp) a d q hq (select0 a b c d q)
  have h1:=productStageExec 5 mask1 [ad,a,b,c,d,q] (by simp) b c q hq (select1 ad a b c d q)
  have h2:=ModularAdjugate.negationStageExec 6 mask2 [bc,ad,a,b,c,d,q] (by simp) bc q
    (Nat.mod_lt _ hq) (select2 bc ad a b c d q)
  have h3:=sumStageExec 7 mask3 [nbc,bc,ad,a,b,c,d,q] (by simp) nbc ad q hq (select3 nbc bc ad a b c d q)
  have hp:=FieldProjection.polyExec 8 outputMask [r,nbc,bc,ad,a,b,c,d,q] (by simp)
  rw [selectOutput,ModularAdjugate.raw_one] at hp
  have h3p:=Composition.executes stage3 (FieldProjection.machine 8 outputMask) _ _ _ _ _ h3 hp
  have h23:=Composition.executes stage2 (Composition.machine stage3 (FieldProjection.machine 8 outputMask)) _ _ _ _ _ h2 h3p
  have h123:=Composition.executes stage1 (Composition.machine stage2 (Composition.machine stage3 (FieldProjection.machine 8 outputMask))) _ _ _ _ _ h1 h23
  have h0123:=Composition.executes stage0 (Composition.machine stage1 (Composition.machine stage2 (Composition.machine stage3 (FieldProjection.machine 8 outputMask)))) _ _ _ _ _ h0 h123
  exact h0123
noncomputable def time : Polynomial ℕ:=Polynomial.C 6000*(Polynomial.X+1)^2
noncomputable def polyExec (a b c d q:ℕ) (hq:0<q) :
    EvalsToInTime (TM2.step arithmeticMachine.program) (arithmeticMachine.init (stream [a,b,c,d,q]))
      (some (arithmeticMachine.halt (unary (result a b c d q)))) (time.eval (stream [a,b,c,d,q]).length) :=by
  have hrun:=exec a b c d q hq
  refine {hrun with steps_le_m:=hrun.steps_le_m.trans ?_}
  let ad:=(a*d)%q
  let bc:=(b*c)%q
  let nbc:=ModularNegation.output bc q
  let r:=result a b c d q
  have had:ad<q:=Nat.mod_lt _ hq
  have hbc:bc<q:=Nat.mod_lt _ hq
  have hnbc:nbc<q:=negation_lt bc q hq hbc
  have hr:r<q:=Nat.mod_lt _ hq
  let L:ℕ:=(stream [a,b,c,d,q]).length
  let Bnd:ℕ:=(L+1)^2
  have hLB:L+1≤Bnd:=by dsimp only [Bnd];nlinarith
  have hProd (m:ℕ) (hm:m≤5*L) : (ModulusQuery.time ModularProduct.time).eval m≤1000*Bnd :=by
    have hsq:(m+1)^2≤25*Bnd:=by
      calc
        (m+1)^2≤(5*(L+1))^2:=Nat.pow_le_pow_left (by omega) 2
        _=25*Bnd:=by dsimp only [Bnd];ring
    have hlin:m+1≤5*Bnd:=by omega
    simp only [ModulusQuery.time,ModularProduct.time,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_pow];omega
  have hSum (m:ℕ) (hm:m≤5*L) : (ModulusQuery.time ModularSum.time).eval m≤125*Bnd :=by
    simp only [ModulusQuery.time,ModularSum.time,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one];omega
  have hNeg (m:ℕ) (hm:m≤5*L) : ModularAdjugate.stageTime.eval m≤150*Bnd :=by
    simp only [ModularAdjugate.stageTime,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one];omega
  have hL0:(stream [a,b,c,d,q]).length≤5*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT0:(ModulusQuery.time ModularProduct.time).eval (stream [a,b,c,d,q]).length≤1000*Bnd:=hProd _ hL0
  have hL1:(stream [ad,a,b,c,d,q]).length≤5*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT1:(ModulusQuery.time ModularProduct.time).eval (stream [ad,a,b,c,d,q]).length≤1000*Bnd:=hProd _ hL1
  have hL2:(stream [bc,ad,a,b,c,d,q]).length≤5*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT2:ModularAdjugate.stageTime.eval (stream [bc,ad,a,b,c,d,q]).length≤150*Bnd:=hNeg _ hL2
  have hL3:(stream [nbc,bc,ad,a,b,c,d,q]).length≤5*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT3:(ModulusQuery.time ModularSum.time).eval (stream [nbc,bc,ad,a,b,c,d,q]).length≤125*Bnd:=hSum _ hL3
  have hL4:(stream [r,nbc,bc,ad,a,b,c,d,q]).length≤5*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  change FieldProjection.time.eval (stream [r,nbc,bc,ad,a,b,c,d,q]).length+(2*(stream [r,nbc,bc,ad,a,b,c,d,q]).length+2)+(ModulusQuery.time ModularSum.time).eval (stream [nbc,bc,ad,a,b,c,d,q]).length+(2*(stream [nbc,bc,ad,a,b,c,d,q]).length+2)+ModularAdjugate.stageTime.eval (stream [bc,ad,a,b,c,d,q]).length+(2*(stream [bc,ad,a,b,c,d,q]).length+2)+(ModulusQuery.time ModularProduct.time).eval (stream [ad,a,b,c,d,q]).length+(2*(stream [ad,a,b,c,d,q]).length+2)+(ModulusQuery.time ModularProduct.time).eval (stream [a,b,c,d,q]).length≤time.eval L
  simp only [FieldProjection.time,time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_pow]
  change _≤6000*Bnd
  omega
def targetPrefixMachine:=RetainedInput.machine (FixedLiteral.machine [true,false])
def predicateMachine:=Composition.machine targetPrefixMachine (UnaryOutputEquality.machine arithmeticMachine)
noncomputable def predicateExec (a b c d q:ℕ) (hq:0<q) :=by
  have hp:=RetainedInput.executes (FixedLiteral.machine [true,false]) (stream [a,b,c,d,q]) [true,false] _
    (FixedLiteral.exec [true,false] (stream [a,b,c,d,q]))
  have he:[true,false]++stream [a,b,c,d,q]=UnaryOutputEquality.prefixInput 1 (stream [a,b,c,d,q]) :=rfl
  rw [he] at hp
  have hb:=UnaryOutputEquality.executes arithmeticMachine 1 (result a b c d q) (stream [a,b,c,d,q]) _
    (polyExec a b c d q hq)
  have h:=Composition.executes targetPrefixMachine (UnaryOutputEquality.machine arithmeticMachine) _ _ _ _ _ hp hb
  exact h
noncomputable def predicateTime : Polynomial ℕ:=Polynomial.C 10000*(Polynomial.X+1)^2
noncomputable def predicatePolyExec (a b c d q:ℕ) (hq:0<q) :
    EvalsToInTime (TM2.step predicateMachine.program) (predicateMachine.init (stream [a,b,c,d,q]))
      (some (predicateMachine.halt [decide (result a b c d q=1)]))
      (predicateTime.eval (stream [a,b,c,d,q]).length) :=by
  have h:=predicateExec a b c d q hq
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hr:result a b c d q<q:=Nat.mod_lt _ hq
  let L:ℕ:=(stream [a,b,c,d,q]).length
  have hqL:q≤L:=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hmax:max (result a b c d q) 1≤L+1:=max_le (by omega) (by omega)
  have hsq:L+1≤(L+1)^2:=by nlinarith
  simp only [predicateTime,time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_pow,
    UnaryOutputEquality.prefixInput_length,List.length_cons,List.length_nil]
  dsimp only [L] at hsq hqL hmax
  omega
structure Input where
  a:ℕ
  b:ℕ
  c:ℕ
  d:ℕ
  q:ℕ
  positive:0<q
def input (x:Input):=stream [x.a,x.b,x.c,x.d,x.q]
def output (x:Input):=[decide (result x.a x.b x.c x.d x.q=1)]
noncomputable def outputsInTime (x:Input):TM2OutputsInTime predicateMachine.toFinTM2
    (input x) (some (output x)) (predicateTime.eval (input x).length):=
  Machine.outputsInTime predicateMachine _ _ _ (predicatePolyExec x.a x.b x.c x.d x.q x.positive)
noncomputable def computableInPolyTime:TM2ComputableInPolyTime input id output where
  tm:=predicateMachine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=predicateTime
  outputsFun:=fun x=>by
    change TM2OutputsInTime predicateMachine.toFinTM2 (List.map id (input x))
      (some (List.map id (output x))) (predicateTime.eval (input x).length)
    have h:=outputsInTime x
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
end QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate


