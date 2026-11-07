-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryPSLComparison
-- name    : QEC_Coding_BitTuring_UnaryPSLComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:13:14.661969+00:00
-- url     : https://prove2.me/theorems/87dcea14-838b-4abf-a120-dc9344419afd
-- title:
--   Unary PSLComparison
-- statement:
--   Definitions and structural lemmas for Unary PSLComparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPSLComparison.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryPSLComparisonSupport
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_length_le
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection
open QEC.Coding.BitTuring.UnaryArithmetic.PSLComparisonSupport
def mask0 (k:Fin 9):Bool:=k.val==0 || k.val==8
theorem select0 (a b c d e f g h q:ℕ) :
    fields 8 mask0 0 [a,b,c,d,e,f,g,h,q]=[a,q] :=by
  simp [fields,maskAt,mask0]
def stage0:=ModularAdjugate.retainedNegation 8 mask0
def mask1 (k:Fin 10):Bool:=k.val==2 || k.val==9
theorem select1 (na a b c d e f g h q:ℕ) :
    fields 9 mask1 0 [na,a,b,c,d,e,f,g,h,q]=[b,q] :=by
  simp [fields,maskAt,mask1]
def stage1:=ModularAdjugate.retainedNegation 9 mask1
def mask2 (k:Fin 11):Bool:=k.val==4 || k.val==10
theorem select2 (nb na a b c d e f g h q:ℕ) :
    fields 10 mask2 0 [nb,na,a,b,c,d,e,f,g,h,q]=[c,q] :=by
  simp [fields,maskAt,mask2]
def stage2:=ModularAdjugate.retainedNegation 10 mask2
def mask3 (k:Fin 12):Bool:=k.val==6 || k.val==11
theorem select3 (nc nb na a b c d e f g h q:ℕ) :
    fields 11 mask3 0 [nc,nb,na,a,b,c,d,e,f,g,h,q]=[d,q] :=by
  simp [fields,maskAt,mask3]
def stage3:=ModularAdjugate.retainedNegation 11 mask3
def mask4 (k:Fin 13):Bool:=k.val==4 || k.val==8
theorem select4 (nd nc nb na a b c d e f g h q:ℕ) :
    fields 12 mask4 0 [nd,nc,nb,na,a,b,c,d,e,f,g,h,q]=[a,e] :=by
  simp [fields,maskAt,mask4]
def stage4:=retainedEquality 12 mask4
def mask5 (k:Fin 14):Bool:=k.val==6 || k.val==10
theorem select5 (ra nd nc nb na a b c d e f g h q:ℕ) :
    fields 13 mask5 0 [ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]=[b,f] :=by
  simp [fields,maskAt,mask5]
def stage5:=retainedEquality 13 mask5
def mask6 (k:Fin 15):Bool:=k.val==8 || k.val==12
theorem select6 (rb ra nd nc nb na a b c d e f g h q:ℕ) :
    fields 14 mask6 0 [rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]=[c,g] :=by
  simp [fields,maskAt,mask6]
def stage6:=retainedEquality 14 mask6
def mask7 (k:Fin 16):Bool:=k.val==10 || k.val==14
theorem select7 (rc rb ra nd nc nb na a b c d e f g h q:ℕ) :
    fields 15 mask7 0 [rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]=[d,h] :=by
  simp [fields,maskAt,mask7]
def stage7:=retainedEquality 15 mask7
def mask8 (k:Fin 17):Bool:=k.val==7 || k.val==12
theorem select8 (rd rc rb ra nd nc nb na a b c d e f g h q:ℕ) :
    fields 16 mask8 0 [rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]=[na,e] :=by
  simp [fields,maskAt,mask8]
def stage8:=retainedEquality 16 mask8
def mask9 (k:Fin 18):Bool:=k.val==7 || k.val==14
theorem select9 (sa rd rc rb ra nd nc nb na a b c d e f g h q:ℕ) :
    fields 17 mask9 0 [sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]=[nb,f] :=by
  simp [fields,maskAt,mask9]
def stage9:=retainedEquality 17 mask9
def mask10 (k:Fin 19):Bool:=k.val==7 || k.val==16
theorem select10 (sb sa rd rc rb ra nd nc nb na a b c d e f g h q:ℕ) :
    fields 18 mask10 0 [sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]=[nc,g] :=by
  simp [fields,maskAt,mask10]
def stage10:=retainedEquality 18 mask10
def mask11 (k:Fin 20):Bool:=k.val==7 || k.val==18
theorem select11 (sc sb sa rd rc rb ra nd nc nb na a b c d e f g h q:ℕ) :
    fields 19 mask11 0 [sc,sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]=[nd,h] :=by
  simp [fields,maskAt,mask11]
def stage11:=retainedEquality 19 mask11
def outputMask (k:Fin 21):Bool:=k.val<8
theorem selectOutput (sd sc sb sa rd rc rb ra nd nc nb na a b c d e f g h q:ℕ) :
    fields 20 outputMask 0 [sd,sc,sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]=[sd,sc,sb,sa,rd,rc,rb,ra] :=by
  simp [fields,maskAt,outputMask]
def outputMachine:=Composition.machine (FieldProjection.machine 20 outputMask) EightFlagOr.machine
def predicateMachine:=(Composition.machine stage0 (Composition.machine stage1 (Composition.machine stage2 (Composition.machine stage3 (Composition.machine stage4 (Composition.machine stage5 (Composition.machine stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 outputMachine))))))))))))
def result (a b c d e f g h q:ℕ):Bool:=(decide (ModularNegation.output d q=h)&&decide (ModularNegation.output c q=g)&&decide (ModularNegation.output b q=f)&&decide (ModularNegation.output a q=e))||(decide (d=h)&&decide (c=g)&&decide (b=f)&&decide (a=e))
noncomputable def exec (a b c d e f g h q:ℕ) (ha:a<q) (hb:b<q) (hc:c<q) (hd:d<q) :=by
  let na:=ModularNegation.output a q
  let nb:=ModularNegation.output b q
  let nc:=ModularNegation.output c q
  let nd:=ModularNegation.output d q
  let ra:=equalValue a e
  let rb:=equalValue b f
  let rc:=equalValue c g
  let rd:=equalValue d h
  let sa:=equalValue na e
  let sb:=equalValue nb f
  let sc:=equalValue nc g
  let sd:=equalValue nd h
  have h0:=ModularAdjugate.negationStageExec 8 mask0 [a,b,c,d,e,f,g,h,q] (by simp) a q ha (select0 a b c d e f g h q)
  have h1:=ModularAdjugate.negationStageExec 9 mask1 [na,a,b,c,d,e,f,g,h,q] (by simp) b q hb (select1 na a b c d e f g h q)
  have h2:=ModularAdjugate.negationStageExec 10 mask2 [nb,na,a,b,c,d,e,f,g,h,q] (by simp) c q hc (select2 nb na a b c d e f g h q)
  have h3:=ModularAdjugate.negationStageExec 11 mask3 [nc,nb,na,a,b,c,d,e,f,g,h,q] (by simp) d q hd (select3 nc nb na a b c d e f g h q)
  have h4:=equalityStageExec 12 mask4 [nd,nc,nb,na,a,b,c,d,e,f,g,h,q] (by simp) a e (select4 nd nc nb na a b c d e f g h q)
  have h5:=equalityStageExec 13 mask5 [ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q] (by simp) b f (select5 ra nd nc nb na a b c d e f g h q)
  have h6:=equalityStageExec 14 mask6 [rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q] (by simp) c g (select6 rb ra nd nc nb na a b c d e f g h q)
  have h7:=equalityStageExec 15 mask7 [rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q] (by simp) d h (select7 rc rb ra nd nc nb na a b c d e f g h q)
  have h8:=equalityStageExec 16 mask8 [rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q] (by simp) na e (select8 rd rc rb ra nd nc nb na a b c d e f g h q)
  have h9:=equalityStageExec 17 mask9 [sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q] (by simp) nb f (select9 sa rd rc rb ra nd nc nb na a b c d e f g h q)
  have h10:=equalityStageExec 18 mask10 [sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q] (by simp) nc g (select10 sb sa rd rc rb ra nd nc nb na a b c d e f g h q)
  have h11:=equalityStageExec 19 mask11 [sc,sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q] (by simp) nd h (select11 sc sb sa rd rc rb ra nd nc nb na a b c d e f g h q)
  have hp:=FieldProjection.polyExec 20 outputMask [sd,sc,sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q] (by simp)
  rw [selectOutput] at hp
  have hr:=EightFlagOr.exec (decide (ModularNegation.output d q=h)) (decide (ModularNegation.output c q=g)) (decide (ModularNegation.output b q=f)) (decide (ModularNegation.output a q=e)) (decide (d=h)) (decide (c=g)) (decide (b=f)) (decide (a=e))
  change EvalsToInTime (TM2.step EightFlagOr.machine.program)
    (EightFlagOr.machine.init (raw [sd,sc,sb,sa,rd,rc,rb,ra]))
    (some (EightFlagOr.machine.halt [result a b c d e f g h q])) 16 at hr
  have ho:=Composition.executes (FieldProjection.machine 20 outputMask) EightFlagOr.machine _ _ _ _ _ hp hr
  have h11o:=Composition.executes stage11 outputMachine _ _ _ _ _ h11 ho
  have h10o:=Composition.executes stage10 (Composition.machine stage11 outputMachine) _ _ _ _ _ h10 h11o
  have h9o:=Composition.executes stage9 (Composition.machine stage10 (Composition.machine stage11 outputMachine)) _ _ _ _ _ h9 h10o
  have h8o:=Composition.executes stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 outputMachine))) _ _ _ _ _ h8 h9o
  have h7o:=Composition.executes stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 outputMachine)))) _ _ _ _ _ h7 h8o
  have h6o:=Composition.executes stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 outputMachine))))) _ _ _ _ _ h6 h7o
  have h5o:=Composition.executes stage5 (Composition.machine stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 outputMachine)))))) _ _ _ _ _ h5 h6o
  have h4o:=Composition.executes stage4 (Composition.machine stage5 (Composition.machine stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 outputMachine))))))) _ _ _ _ _ h4 h5o
  have h3o:=Composition.executes stage3 (Composition.machine stage4 (Composition.machine stage5 (Composition.machine stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 outputMachine)))))))) _ _ _ _ _ h3 h4o
  have h2o:=Composition.executes stage2 (Composition.machine stage3 (Composition.machine stage4 (Composition.machine stage5 (Composition.machine stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 outputMachine))))))))) _ _ _ _ _ h2 h3o
  have h1o:=Composition.executes stage1 (Composition.machine stage2 (Composition.machine stage3 (Composition.machine stage4 (Composition.machine stage5 (Composition.machine stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 outputMachine)))))))))) _ _ _ _ _ h1 h2o
  have h0o:=Composition.executes stage0 (Composition.machine stage1 (Composition.machine stage2 (Composition.machine stage3 (Composition.machine stage4 (Composition.machine stage5 (Composition.machine stage6 (Composition.machine stage7 (Composition.machine stage8 (Composition.machine stage9 (Composition.machine stage10 (Composition.machine stage11 outputMachine))))))))))) _ _ _ _ _ h0 h1o
  exact h0o
noncomputable def time : Polynomial ℕ:=Polynomial.C 15000*(Polynomial.X+1)
noncomputable def polyExec (a b c d e f g h q:ℕ) (ha:a<q) (hb:b<q) (hc:c<q) (hd:d<q) :
    EvalsToInTime (TM2.step predicateMachine.program) (predicateMachine.init (stream [a,b,c,d,e,f,g,h,q]))
      (some (predicateMachine.halt [result a b c d e f g h q])) (time.eval (stream [a,b,c,d,e,f,g,h,q]).length) :=by
  have hrun:=exec a b c d e f g h q ha hb hc hd
  refine {hrun with steps_le_m:=hrun.steps_le_m.trans ?_}
  let na:=ModularNegation.output a q
  let nb:=ModularNegation.output b q
  let nc:=ModularNegation.output c q
  let nd:=ModularNegation.output d q
  let ra:=equalValue a e
  let rb:=equalValue b f
  let rc:=equalValue c g
  let rd:=equalValue d h
  let sa:=equalValue na e
  let sb:=equalValue nb f
  let sc:=equalValue nc g
  let sd:=equalValue nd h
  have hna:na≤q :=by
    dsimp only [na,ModularNegation.output];split_ifs <;> omega
  have hnb:nb≤q :=by
    dsimp only [nb,ModularNegation.output];split_ifs <;> omega
  have hnc:nc≤q :=by
    dsimp only [nc,ModularNegation.output];split_ifs <;> omega
  have hnd:nd≤q :=by
    dsimp only [nd,ModularNegation.output];split_ifs <;> omega
  have hra:ra≤1 :=by
    dsimp only [ra,equalValue,FlagUnary.value];split_ifs <;> omega
  have hrb:rb≤1 :=by
    dsimp only [rb,equalValue,FlagUnary.value];split_ifs <;> omega
  have hrc:rc≤1 :=by
    dsimp only [rc,equalValue,FlagUnary.value];split_ifs <;> omega
  have hrd:rd≤1 :=by
    dsimp only [rd,equalValue,FlagUnary.value];split_ifs <;> omega
  have hsa:sa≤1 :=by
    dsimp only [sa,equalValue,FlagUnary.value];split_ifs <;> omega
  have hsb:sb≤1 :=by
    dsimp only [sb,equalValue,FlagUnary.value];split_ifs <;> omega
  have hsc:sc≤1 :=by
    dsimp only [sc,equalValue,FlagUnary.value];split_ifs <;> omega
  have hsd:sd≤1 :=by
    dsimp only [sd,equalValue,FlagUnary.value];split_ifs <;> omega
  let L:ℕ:=(stream [a,b,c,d,e,f,g,h,q]).length
  have hNeg (m:ℕ) (hm:m≤14*L) : ModularAdjugate.stageTime.eval m≤420*(L+1) :=by
    simp only [ModularAdjugate.stageTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one];omega
  have hEq (m:ℕ) (hm:m≤14*L) : equalityTime.eval m≤560*(L+1) :=by
    simp only [equalityTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one];omega
  have hL0:(stream [a,b,c,d,e,f,g,h,q]).length≤14*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT0:ModularAdjugate.stageTime.eval (stream [a,b,c,d,e,f,g,h,q]).length≤420*(L+1):=hNeg _ hL0
  have hL1:(stream [na,a,b,c,d,e,f,g,h,q]).length≤14*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT1:ModularAdjugate.stageTime.eval (stream [na,a,b,c,d,e,f,g,h,q]).length≤420*(L+1):=hNeg _ hL1
  have hL2:(stream [nb,na,a,b,c,d,e,f,g,h,q]).length≤14*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT2:ModularAdjugate.stageTime.eval (stream [nb,na,a,b,c,d,e,f,g,h,q]).length≤420*(L+1):=hNeg _ hL2
  have hL3:(stream [nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤14*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT3:ModularAdjugate.stageTime.eval (stream [nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤420*(L+1):=hNeg _ hL3
  have hL4:(stream [nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤14*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT4:equalityTime.eval (stream [nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤560*(L+1):=hEq _ hL4
  have hL5:(stream [ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤14*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT5:equalityTime.eval (stream [ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤560*(L+1):=hEq _ hL5
  have hL6:(stream [rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤14*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT6:equalityTime.eval (stream [rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤560*(L+1):=hEq _ hL6
  have hL7:(stream [rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤14*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT7:equalityTime.eval (stream [rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤560*(L+1):=hEq _ hL7
  have hL8:(stream [rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤14*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT8:equalityTime.eval (stream [rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤560*(L+1):=hEq _ hL8
  have hL9:(stream [sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤14*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT9:equalityTime.eval (stream [sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤560*(L+1):=hEq _ hL9
  have hL10:(stream [sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤14*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT10:equalityTime.eval (stream [sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤560*(L+1):=hEq _ hL10
  have hL11:(stream [sc,sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤14*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hT11:equalityTime.eval (stream [sc,sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤560*(L+1):=hEq _ hL11
  have hL12:(stream [sd,sc,sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length≤14*L :=by
    dsimp only [L]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hR:(raw [sd,sc,sb,sa,rd,rc,rb,ra]).length≤16 :=by
    have hh:=raw_length_le [sd,sc,sb,sa,rd,rc,rb,ra]
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at hh
    omega
  change 16+(2*(raw [sd,sc,sb,sa,rd,rc,rb,ra]).length+2)+FieldProjection.time.eval (stream [sd,sc,sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+(2*(stream [sd,sc,sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+2)+equalityTime.eval (stream [sc,sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+(2*(stream [sc,sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+2)+equalityTime.eval (stream [sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+(2*(stream [sb,sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+2)+equalityTime.eval (stream [sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+(2*(stream [sa,rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+2)+equalityTime.eval (stream [rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+(2*(stream [rd,rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+2)+equalityTime.eval (stream [rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+(2*(stream [rc,rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+2)+equalityTime.eval (stream [rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+(2*(stream [rb,ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+2)+equalityTime.eval (stream [ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+(2*(stream [ra,nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+2)+equalityTime.eval (stream [nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+(2*(stream [nd,nc,nb,na,a,b,c,d,e,f,g,h,q]).length+2)+ModularAdjugate.stageTime.eval (stream [nc,nb,na,a,b,c,d,e,f,g,h,q]).length+(2*(stream [nc,nb,na,a,b,c,d,e,f,g,h,q]).length+2)+ModularAdjugate.stageTime.eval (stream [nb,na,a,b,c,d,e,f,g,h,q]).length+(2*(stream [nb,na,a,b,c,d,e,f,g,h,q]).length+2)+ModularAdjugate.stageTime.eval (stream [na,a,b,c,d,e,f,g,h,q]).length+(2*(stream [na,a,b,c,d,e,f,g,h,q]).length+2)+ModularAdjugate.stageTime.eval (stream [a,b,c,d,e,f,g,h,q]).length≤time.eval L
  simp only [FieldProjection.time,time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one]
  omega
structure Input where
  a:ℕ
  b:ℕ
  c:ℕ
  d:ℕ
  e:ℕ
  f:ℕ
  g:ℕ
  h:ℕ
  q:ℕ
  a_lt:a<q
  b_lt:b<q
  c_lt:c<q
  d_lt:d<q
def input (x:Input) :=stream [x.a,x.b,x.c,x.d,x.e,x.f,x.g,x.h,x.q]
def output (x:Input) :=[result x.a x.b x.c x.d x.e x.f x.g x.h x.q]
noncomputable def outputsInTime (x:Input) : TM2OutputsInTime predicateMachine.toFinTM2
    (input x) (some (output x)) (time.eval (input x).length) :=
  Machine.outputsInTime predicateMachine _ _ _
    (polyExec x.a x.b x.c x.d x.e x.f x.g x.h x.q x.a_lt x.b_lt x.c_lt x.d_lt)
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input id output where
  tm:=predicateMachine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time
  outputsFun:=fun x=>by
    change TM2OutputsInTime predicateMachine.toFinTM2 (List.map id (input x))
      (some (List.map id (output x))) (time.eval (input x).length)
    have h:=outputsInTime x
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
end QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison


