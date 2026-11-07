-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryModularAdjugate
-- name    : QEC_Coding_BitTuring_UnaryModularAdjugate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:11:30.057207+00:00
-- url     : https://prove2.me/theorems/172d4afb-b309-4bc7-970a-177b49beecba
-- title:
--   Unary Modular Adjugate
-- statement:
--   Definitions and structural lemmas for Unary Modular Adjugate, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularAdjugate.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularNegation
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Definitions.Def_QEC_Coding_BitTuring_UnaryInverseInput
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_fields_stream_length_le
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_append_last
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_length_le
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_reverse_raw_four
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_length
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularAdjugate
open Turing StateTransition
open FieldProjection
def retainedUnary (n:ℕ) (keep:Fin (n+1)→Bool) :=
  RetainedInput.machine (Composition.machine (machine n keep) UnaryDelimiter.machine)
def retainedNegation (n:ℕ) (keep:Fin (n+1)→Bool) :=
  RetainedInput.machine (Composition.machine (machine n keep)
    (Composition.machine ModularNegation.machine UnaryDelimiter.machine))
noncomputable def stageTime : Polynomial ℕ := Polynomial.C 30*(Polynomial.X+1)
theorem raw_one (a:ℕ) : raw [a]=unary a := by
  simpa only [List.nil_append,stream,List.append_nil] using raw_append_last [] a
theorem raw_pair (a q:ℕ) : raw [a,q]=pairInput a q := by
  simpa [stream,pairInput,List.append_assoc] using raw_append_last [a] q
noncomputable def unaryStageExec (n:ℕ) (keep:Fin (n+1)→Bool) (xs:List ℕ)
    (hx:xs.length=n+1) (a:ℕ) (hf:fields n keep 0 xs=[a]) :
    EvalsToInTime (TM2.step (retainedUnary n keep).program) ((retainedUnary n keep).init (stream xs))
      (some ((retainedUnary n keep).halt (stream (a::xs))))
      (stageTime.eval (stream xs).length) := by
  have hp:=FieldProjection.polyExec n keep xs hx
  rw [hf,raw_one] at hp
  have ha:=Composition.executes (machine n keep) UnaryDelimiter.machine
    (stream xs) (unary a) (unary a++[false]) _ _ hp (UnaryDelimiter.exec a)
  have h:=RetainedInput.executes (Composition.machine (machine n keep) UnaryDelimiter.machine)
    (stream xs) (unary a++[false]) _ ha
  rw [show (unary a++[false])++stream xs=stream (a::xs) by
    simp only [stream,List.append_assoc,List.singleton_append]] at h
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hl:=fields_stream_length_le n keep 0 xs
  rw [hf] at hl
  have hs:(stream [a]).length=a+1 := by simp [stream,unary_length]
  rw [hs] at hl
  simp only [stageTime,FieldProjection.time,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,List.length_append,
    List.length_singleton,unary_length]
  omega
noncomputable def negationStageExec (n:ℕ) (keep:Fin (n+1)→Bool) (xs:List ℕ)
    (hx:xs.length=n+1) (a q:ℕ) (haq:a<q) (hf:fields n keep 0 xs=[a,q]) :
    EvalsToInTime (TM2.step (retainedNegation n keep).program)
      ((retainedNegation n keep).init (stream xs))
      (some ((retainedNegation n keep).halt (stream (ModularNegation.output a q::xs))))
      (stageTime.eval (stream xs).length) := by
  have hp:=FieldProjection.polyExec n keep xs hx
  rw [hf,raw_pair] at hp
  let r:=ModularNegation.output a q
  have hn:=ModularNegation.polyExec a q haq.le
  have hd:=UnaryDelimiter.exec r
  have hnd:=Composition.executes ModularNegation.machine UnaryDelimiter.machine
    (pairInput a q) (unary r) (unary r++[false]) _ _ hn hd
  have ha:=Composition.executes (machine n keep)
    (Composition.machine ModularNegation.machine UnaryDelimiter.machine)
    (stream xs) (pairInput a q) (unary r++[false]) _ _ hp hnd
  have h:=RetainedInput.executes
    (Composition.machine (machine n keep) (Composition.machine ModularNegation.machine UnaryDelimiter.machine))
    (stream xs) (unary r++[false]) _ ha
  rw [show (unary r++[false])++stream xs=stream (r::xs) by
    simp only [stream,List.append_assoc,List.singleton_append]] at h
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hl:=fields_stream_length_le n keep 0 xs
  rw [hf] at hl
  have hs:(stream [a,q]).length=a+q+2 := by
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  rw [hs] at hl
  have hr:r≤q := by
    dsimp only [r,ModularNegation.output]
    split_ifs <;> omega
  simp only [stageTime,FieldProjection.time,ModularNegation.time,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,
    List.length_append,List.length_singleton,unary_length,pairInput_length]
  omega
def maskD (k:Fin 5):Bool := k.val==3
def maskB (k:Fin 6):Bool := k.val==2 || k.val==5
def maskC (k:Fin 7):Bool := k.val==4 || k.val==6
def maskA (k:Fin 8):Bool := k.val==3
def maskOutput (k:Fin 9):Bool := k.val==0 || k.val==1 || k.val==2 || k.val==3
theorem selectD (a b c d q:ℕ) : fields 4 maskD 0 [a,b,c,d,q]=[d] := by
  simp [fields,maskAt,maskD]
theorem selectB (a b c d q:ℕ) : fields 5 maskB 0 [d,a,b,c,d,q]=[b,q] := by
  simp [fields,maskAt,maskB]
theorem selectC (nb a b c d q:ℕ) : fields 6 maskC 0 [nb,d,a,b,c,d,q]=[c,q] := by
  simp [fields,maskAt,maskC]
theorem selectA (nc nb a b c d q:ℕ) : fields 7 maskA 0 [nc,nb,d,a,b,c,d,q]=[a] := by
  simp [fields,maskAt,maskA]
theorem selectOutput (nc nb a b c d q:ℕ) : fields 8 maskOutput 0 [a,nc,nb,d,a,b,c,d,q]=[a,nc,nb,d] := by
  simp [fields,maskAt,maskOutput]
def outputMachine := Composition.machine (machine 8 maskOutput) BitReverse.machine
def inverseMachine := Composition.machine (retainedUnary 4 maskD)
  (Composition.machine (retainedNegation 5 maskB)
    (Composition.machine (retainedNegation 6 maskC)
      (Composition.machine (retainedUnary 7 maskA) outputMachine)))
end QEC.Coding.BitTuring.UnaryArithmetic.ModularAdjugate
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularAdjugate
open Turing StateTransition
open FieldProjection
noncomputable def exec (a b c d q:ℕ) (_hq:0<q) (hb:b<q) (hc:c<q) := by
  let nb:=ModularNegation.output b q
  let nc:=ModularNegation.output c q
  have hD:=unaryStageExec 4 maskD [a,b,c,d,q] (by simp) d (selectD ..)
  have hB:=negationStageExec 5 maskB [d,a,b,c,d,q] (by simp) b q hb (selectB ..)
  have hC:=negationStageExec 6 maskC [nb,d,a,b,c,d,q] (by simp) c q hc (selectC ..)
  have hA:=unaryStageExec 7 maskA [nc,nb,d,a,b,c,d,q] (by simp) a (selectA ..)
  have hp:=FieldProjection.polyExec 8 maskOutput [a,nc,nb,d,a,b,c,d,q] (by simp)
  rw [selectOutput] at hp
  have hr:=BitReverse.exec (raw [a,nc,nb,d])
  rw [reverse_raw_four] at hr
  have ho:=Composition.executes (machine 8 maskOutput) BitReverse.machine
    (stream [a,nc,nb,d,a,b,c,d,q]) (raw [a,nc,nb,d]) (raw [d,nb,nc,a]) _ _ hp hr
  have hAo:=Composition.executes (retainedUnary 7 maskA) outputMachine
    (stream [nc,nb,d,a,b,c,d,q]) (stream [a,nc,nb,d,a,b,c,d,q]) (raw [d,nb,nc,a]) _ _ hA ho
  have hCo:=Composition.executes (retainedNegation 6 maskC)
    (Composition.machine (retainedUnary 7 maskA) outputMachine)
    (stream [nb,d,a,b,c,d,q]) (stream [nc,nb,d,a,b,c,d,q]) (raw [d,nb,nc,a]) _ _ hC hAo
  have hBo:=Composition.executes (retainedNegation 5 maskB)
    (Composition.machine (retainedNegation 6 maskC) (Composition.machine (retainedUnary 7 maskA) outputMachine))
    (stream [d,a,b,c,d,q]) (stream [nb,d,a,b,c,d,q]) (raw [d,nb,nc,a]) _ _ hB hCo
  exact Composition.executes (retainedUnary 4 maskD)
    (Composition.machine (retainedNegation 5 maskB)
      (Composition.machine (retainedNegation 6 maskC) (Composition.machine (retainedUnary 7 maskA) outputMachine)))
    (stream [a,b,c,d,q]) (stream [d,a,b,c,d,q]) (raw [d,nb,nc,a]) _ _ hD hBo
noncomputable def time : Polynomial ℕ := Polynomial.C 600*(Polynomial.X+1)
noncomputable def polyExec (a b c d q:ℕ) (hq:0<q) (hb:b<q) (hc:c<q) :
    EvalsToInTime (TM2.step inverseMachine.program) (inverseMachine.init (stream [a,b,c,d,q]))
      (some (inverseMachine.halt (raw [d,ModularNegation.output b q,ModularNegation.output c q,a])))
      (time.eval (stream [a,b,c,d,q]).length) := by
  have h:=exec a b c d q hq hb hc
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  let nb:=ModularNegation.output b q
  let nc:=ModularNegation.output c q
  have hnb:nb≤q := by dsimp only [nb,ModularNegation.output];split_ifs <;> omega
  have hnc:nc≤q := by dsimp only [nc,ModularNegation.output];split_ifs <;> omega
  let L:ℕ:=(stream [a,b,c,d,q]).length
  let L1:ℕ:=(stream [d,a,b,c,d,q]).length
  let L2:ℕ:=(stream [nb,d,a,b,c,d,q]).length
  let L3:ℕ:=(stream [nc,nb,d,a,b,c,d,q]).length
  let L4:ℕ:=(stream [a,nc,nb,d,a,b,c,d,q]).length
  have hqL:q+1≤L := by
    dsimp only [L];simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have haL:a+1≤L := by
    dsimp only [L];simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hdL:d+1≤L := by
    dsimp only [L];simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have h1:L1=L+d+1 := by
    dsimp only [L1,L];simp only [stream,List.length_append,List.length_cons,unary_length];omega
  have h2:L2=L1+nb+1 := by
    dsimp only [L2,L1];simp only [stream,List.length_append,List.length_cons,unary_length];omega
  have h3:L3=L2+nc+1 := by
    dsimp only [L3,L2];simp only [stream,List.length_append,List.length_cons,unary_length];omega
  have h4:L4=L3+a+1 := by
    dsimp only [L4,L3];simp only [stream,List.length_append,List.length_cons,unary_length];omega
  have hr:(raw [a,nc,nb,d]).length≤4*L := by
    have ht:=raw_length_le [a,nc,nb,d]
    have hs:(stream [a,nc,nb,d]).length=a+nc+nb+d+4 := by
      simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
    rw [hs] at ht;omega
  change (raw [a,nc,nb,d]).length+1+(2*(raw [a,nc,nb,d]).length+2)+FieldProjection.time.eval L4+
    (2*L4+2)+stageTime.eval L3+(2*L3+2)+stageTime.eval L2+
    (2*L2+2)+stageTime.eval L1+(2*L1+2)+stageTime.eval L≤time.eval L
  simp only [time,stageTime,FieldProjection.time,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  omega
end QEC.Coding.BitTuring.UnaryArithmetic.ModularAdjugate
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularAdjugate
open Turing
open FieldProjection
structure Input where
  a:ℕ
  b:ℕ
  c:ℕ
  d:ℕ
  q:ℕ+
  b_lt:b<q.val
  c_lt:c<q.val
def input (x:Input) := stream [x.a,x.b,x.c,x.d,x.q.val]
def output (x:Input) := raw [x.d,ModularNegation.output x.b x.q.val,
  ModularNegation.output x.c x.q.val,x.a]
noncomputable def outputsInTime (a b c d q:ℕ) (hq:0<q) (hb:b<q) (hc:c<q) :
    TM2OutputsInTime inverseMachine.toFinTM2 (stream [a,b,c,d,q])
      (some (raw [d,ModularNegation.output b q,ModularNegation.output c q,a]))
      (time.eval (stream [a,b,c,d,q]).length) :=
  Machine.outputsInTime inverseMachine _ _ _ (polyExec a b c d q hq hb hc)
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input id output where
  tm:=inverseMachine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time
  outputsFun:=fun x=>by
    change TM2OutputsInTime inverseMachine.toFinTM2 (List.map id (input x))
      (some (List.map id (output x))) (time.eval (input x).length)
    have h:=outputsInTime x.a x.b x.c x.d x.q.val x.q.pos x.b_lt x.c_lt
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input,output] using h
end QEC.Coding.BitTuring.UnaryArithmetic.ModularAdjugate


