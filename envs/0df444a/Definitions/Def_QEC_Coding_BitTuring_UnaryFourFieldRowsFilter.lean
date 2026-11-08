-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
-- name    : QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:04:33.963244+00:00
-- url     : https://prove2.me/theorems/d1568428-e8fb-4382-962c-18c5d42a5869
-- title:
--   Unary Four Field Rows Filter
-- statement:
--   Definitions and structural lemmas for Unary Four Field Rows Filter, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFourFieldRowsFilter.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
abbrev Stack:=P.K⊕Fin 3
abbrev Label:=P.Λ⊕Fin 15
abbrev Var:=P.σ×Bool×Option Bool
abbrev Statement:=TM2.Stmt (fun _:Stack P=>Bool) (Label P) (Var P)
def setHead (v:Var P) (h:Option Bool):Var P:=(v.1,v.2.1,h)
def scan (k:Fin 15) (source:Stack P) (next:Fin 15) (save:Bool):Statement P:=
 .pop source (setHead P) (if save then
  .push (.inr 0) (fun v=>v.2.2.getD false)
   (.branch (fun v=>v.2.2.getD false) (.goto fun _=>.inr k) (.goto fun _=>.inr next))
  else .branch (fun v=>v.2.2.getD false) (.goto fun _=>.inr k) (.goto fun _=>.inr next))
def program:Label P→Statement P
 | .inl l=>liftStatement Sum.inl Sum.inl Prod.fst (fun v w=>(w,v.2))
   (some (.inr 3)) (P.program l)
 | .inr k=>
  if k=0 then scan P 0 (.inl P.input) 1 true
  else if k=1 then .peek (.inl P.input) (setHead P)
   (.branch (fun v=>v.2.2.isSome) (.goto fun _=>.inr 2) (.goto fun _=>.inr 12))
  else if k=2 then .pop (.inr 0) (setHead P) (.branch (fun v=>v.2.2.isSome)
   (.push (.inl P.input) (fun v=>v.2.2.getD false) (.goto fun _=>.inr 2))
   (.load (fun _=>(P.initial,false,none)) (.goto fun _=>.inl P.main)))
  else if k=3 then .pop (.inl P.output) (fun v h=>(v.1,h.getD false,h)) (.goto fun _=>.inr 4)
  else if k=4 then scan P 4 (.inl P.output) 5 true
  else if hk:5≤k.val ∧ k.val≤8 then
   .pop (.inl P.output) (setHead P)
    (.branch (fun v=>v.2.1)
     (.branch (fun v=>v.2.2.getD false) (.goto fun _=>.inr k)
      (.goto fun _=>.inr ⟨k.val+1,by omega⟩))
     (.push (.inr 1) (fun v=>v.2.2.getD false)
      (.branch (fun v=>v.2.2.getD false) (.goto fun _=>.inr k)
       (.goto fun _=>.inr ⟨k.val+1,by omega⟩))))
  else if k=9 then .pop (.inl P.output) (setHead P) (.branch (fun v=>v.2.2.isSome)
   (.push (.inr 2) (fun v=>v.2.2.getD false) (.goto fun _=>.inr 9)) (.goto fun _=>.inr 10))
  else if k=10 then .pop (.inr 2) (setHead P) (.branch (fun v=>v.2.2.isSome)
   (.push (.inl P.input) (fun v=>v.2.2.getD false) (.goto fun _=>.inr 10)) (.goto fun _=>.inr 11))
  else if k=11 then .pop (.inr 0) (setHead P) (.branch (fun v=>v.2.2.isSome)
   (.push (.inl P.input) (fun v=>v.2.2.getD false) (.goto fun _=>.inr 11))
   (.load (fun _=>(P.initial,false,none)) (.goto fun _=>.inr 0)))
  else if k=12 then .pop (.inr 0) (setHead P) (.branch (fun v=>v.2.2.isSome)
   (.goto fun _=>.inr 12) (.goto fun _=>.inr 13))
  else if k=13 then .pop (.inr 1) (setHead P) (.goto fun _=>.inr 14)
  else .pop (.inr 1) (setHead P) (.branch (fun v=>v.2.2.isSome)
   (.push (.inl P.output) (fun v=>v.2.2.getD false) (.goto fun _=>.inr 14))
   (.load (fun _=>(P.initial,false,none)) .halt))
def machine:Machine where
 K:=Stack P;input:=.inl P.input;output:=.inl P.output;Λ:=Label P;main:=.inr 0
 σ:=Var P;initial:=(P.initial,false,none);program:=program P
def cfg (k:Fin 15) (f:Bool) (h:Option Bool) (I O H C B:List Bool):TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P):=
 ⟨some (.inr k),(P.initial,f,h),fun j=>match j with
 | .inl j=>DrainInput.tapes P I O j
 | .inr j=>![H,C,B] j⟩
def bodyTapes (C:List Bool) (S:P.K→List Bool):Stack P→List Bool
 | .inl j=>S j
 | .inr j=>![[],C,[]] j
def embedBody (C:List Bool):P.Cfg→TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P):=
 liftCfg Sum.inl (fun v=>(v,false,none)) (bodyTapes P C) (some (.inr 3))
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)
def pushed (f:Bool) (w C:List Bool):List Bool:=if f then C else w.reverse++C
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)
abbrev next:=fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P))
def qword (q:ℕ):List Bool:=unary q++[false]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter


