-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryModularDot
-- name    : QEC_Coding_BitTuring_UnaryModularDot
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:10:38.467704+00:00
-- url     : https://prove2.me/theorems/adf0a69f-9ec5-497d-a07f-4989a78a6faa
-- title:
--   Unary Modular Dot
-- statement:
--   Definitions and structural lemmas for Unary Modular Dot, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularDot.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularSum
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Definitions.Def_QEC_Coding_BitTuring_UnaryInverseInput
import Mathlib.Tactic.Linarith
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_triple
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_length
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularDot
open Turing StateTransition
open FieldProjection
def maskA (k:Fin 5) : Bool := k.val==0 || k.val==2 || k.val==4
def maskB (k:Fin 6) : Bool := k.val==2 || k.val==4 || k.val==5
def maskS (k:Fin 7) : Bool := k.val==0 || k.val==1 || k.val==6
def stageA := Composition.machine (machine 4 maskA)
  (Composition.machine ModularProduct.machine UnaryDelimiter.machine)
def stageB := Composition.machine (machine 5 maskB)
  (Composition.machine ModularProduct.machine UnaryDelimiter.machine)
def stageS := Composition.machine (machine 6 maskS) ModularSum.machine
def retainedA := RetainedInput.machine stageA
def retainedB := RetainedInput.machine stageB
def dotMachine := Composition.machine retainedA (Composition.machine retainedB stageS)
theorem selectA (a b c d q:ℕ) : fields 4 maskA 0 [a,b,c,d,q]=[a,c,q] := by
  simp [fields,maskAt,maskA]
theorem selectB (u a b c d q:ℕ) : fields 5 maskB 0 [u,a,b,c,d,q]=[b,d,q] := by
  simp [fields,maskAt,maskB]
theorem selectS (v u a b c d q:ℕ) : fields 6 maskS 0 [v,u,a,b,c,d,q]=[v,u,q] := by
  simp [fields,maskAt,maskS]
noncomputable def productDelimitedExec (a b q:ℕ) (hq:0<q) :=
  Composition.executes ModularProduct.machine UnaryDelimiter.machine
    (FactorTest.tripleInput a b q) (unary ((a*b)%q)) (unary ((a*b)%q)++[false])
    (ModularProduct.time.eval (FactorTest.tripleInput a b q).length) (((a*b)%q)+2)
    (ModularProduct.polyExec a b q hq) (UnaryDelimiter.exec ((a*b)%q))
noncomputable def execA (a b c d q:ℕ) (hq:0<q) := by
  have hp:=FieldProjection.polyExec 4 maskA [a,b,c,d,q] (by simp)
  rw [selectA,raw_triple] at hp
  exact Composition.executes (machine 4 maskA)
    (Composition.machine ModularProduct.machine UnaryDelimiter.machine)
    (stream [a,b,c,d,q]) (FactorTest.tripleInput a c q) (unary ((a*c)%q)++[false])
    (FieldProjection.time.eval (stream [a,b,c,d,q]).length)
    ((((a*c)%q)+2)+(2*(unary ((a*c)%q)).length+2)+
      ModularProduct.time.eval (FactorTest.tripleInput a c q).length)
    hp (productDelimitedExec a c q hq)
noncomputable def execB (u a b c d q:ℕ) (hq:0<q) := by
  have hp:=FieldProjection.polyExec 5 maskB [u,a,b,c,d,q] (by simp)
  rw [selectB,raw_triple] at hp
  exact Composition.executes (machine 5 maskB)
    (Composition.machine ModularProduct.machine UnaryDelimiter.machine)
    (stream [u,a,b,c,d,q]) (FactorTest.tripleInput b d q) (unary ((b*d)%q)++[false])
    (FieldProjection.time.eval (stream [u,a,b,c,d,q]).length)
    ((((b*d)%q)+2)+(2*(unary ((b*d)%q)).length+2)+
      ModularProduct.time.eval (FactorTest.tripleInput b d q).length)
    hp (productDelimitedExec b d q hq)
noncomputable def execS (v u a b c d q:ℕ) (hq:0<q) := by
  have hp:=FieldProjection.polyExec 6 maskS [v,u,a,b,c,d,q] (by simp)
  rw [selectS,raw_triple] at hp
  exact Composition.executes (machine 6 maskS) ModularSum.machine
    (stream [v,u,a,b,c,d,q]) (FactorTest.tripleInput v u q) (unary ((v+u)%q))
    (FieldProjection.time.eval (stream [v,u,a,b,c,d,q]).length)
    (ModularSum.time.eval (FactorTest.tripleInput v u q).length)
    hp (ModularSum.polyExec v u q hq)
noncomputable def retainedExecA (a b c d q:ℕ) (hq:0<q) := by
  have h:=execA a b c d q hq
  have hr:=RetainedInput.executes stageA (stream [a,b,c,d,q])
    (unary ((a*c)%q)++[false]) _ h
  rw [show (unary ((a*c)%q)++[false])++stream [a,b,c,d,q]=
    stream [((a*c)%q),a,b,c,d,q] by simp only [stream,List.append_assoc,List.singleton_append]] at hr
  exact hr
noncomputable def retainedExecB (u a b c d q:ℕ) (hq:0<q) := by
  have h:=execB u a b c d q hq
  have hr:=RetainedInput.executes stageB (stream [u,a,b,c,d,q])
    (unary ((b*d)%q)++[false]) _ h
  rw [show (unary ((b*d)%q)++[false])++stream [u,a,b,c,d,q]=
    stream [((b*d)%q),u,a,b,c,d,q] by simp only [stream,List.append_assoc,List.singleton_append]] at hr
  exact hr
noncomputable def exec (a b c d q:ℕ) (hq:0<q) := by
  let u:ℕ:=(a*c)%q
  let v:ℕ:=(b*d)%q
  have hb:=retainedExecB u a b c d q hq
  have hs:=execS v u a b c d q hq
  have hbs:=Composition.executes retainedB stageS (stream [u,a,b,c,d,q])
    (stream [v,u,a,b,c,d,q]) (unary ((v+u)%q)) _ _ hb hs
  have ha:=retainedExecA a b c d q hq
  have h:=Composition.executes retainedA (Composition.machine retainedB stageS)
    (stream [a,b,c,d,q]) (stream [u,a,b,c,d,q]) (unary ((v+u)%q)) _ _ ha hbs
  have he:(v+u)%q=(a*c+b*d)%q := by
    dsimp [u,v];rw [←Nat.add_mod];congr 1;omega
  rw [he] at h
  exact h
noncomputable def time : Polynomial ℕ := Polynomial.C 200*(Polynomial.X+1)^2
noncomputable def polyExec (a b c d q:ℕ) (hq:0<q) :
    EvalsToInTime (TM2.step dotMachine.program) (dotMachine.init (stream [a,b,c,d,q]))
      (some (dotMachine.halt (unary ((a*c+b*d)%q))))
      (time.eval (stream [a,b,c,d,q]).length) := by
  have h:=exec a b c d q hq
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hu:(a*c)%q<q:=Nat.mod_lt _ hq
  have hv:(b*d)%q<q:=Nat.mod_lt _ hq
  simp only [FieldProjection.time,ModularProduct.time,ModularSum.time,time,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.eval_one,Polynomial.eval_pow,unary_length,FactorTest.tripleInput_length,
    stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
    List.length_append] at ⊢
  nlinarith [sq_nonneg (a+b+c+d+q+6),sq_nonneg (a+c+q+3),sq_nonneg (b+d+q+3)]
end QEC.Coding.BitTuring.UnaryArithmetic.ModularDot
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularDot
open Turing
open FieldProjection
structure Input where
  a:ℕ
  b:ℕ
  c:ℕ
  d:ℕ
  q:ℕ+
def input (x:Input) := stream [x.a,x.b,x.c,x.d,x.q.val]
def output (x:Input) := (x.a*x.c+x.b*x.d)%x.q.val
noncomputable def outputsInTime (a b c d q:ℕ) (hq:0<q) :
    TM2OutputsInTime dotMachine.toFinTM2 (stream [a,b,c,d,q])
      (some (unary ((a*c+b*d)%q))) (time.eval (stream [a,b,c,d,q]).length) :=
  Machine.outputsInTime dotMachine _ _ _ (polyExec a b c d q hq)
noncomputable def outputsZModInTime (a b c d q:ℕ) (hq:0<q) :
    TM2OutputsInTime dotMachine.toFinTM2 (stream [a,b,c,d,q])
      (some (unary (((a:ZMod q)*(c:ZMod q)+(b:ZMod q)*(d:ZMod q)).val)))
      (time.eval (stream [a,b,c,d,q]).length) := by
  let : NeZero q:=⟨hq.ne'⟩
  simpa only [←Nat.cast_mul,←Nat.cast_add,ZMod.val_natCast] using outputsInTime a b c d q hq
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input unary output where
  tm:=dotMachine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time
  outputsFun:=fun x=>by
    change TM2OutputsInTime dotMachine.toFinTM2 (List.map id (input x))
      (some (List.map id (unary (output x)))) (time.eval (input x).length)
    have h:=outputsInTime x.a x.b x.c x.d x.q.val x.q.pos
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input,output] using h
end QEC.Coding.BitTuring.UnaryArithmetic.ModularDot


