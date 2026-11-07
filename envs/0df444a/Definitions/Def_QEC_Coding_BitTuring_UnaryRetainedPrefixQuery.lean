-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedPrefixQuery
-- name    : QEC_Coding_BitTuring_UnaryRetainedPrefixQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:57:44.167232+00:00
-- url     : https://prove2.me/theorems/f2fd3b8f-70cf-4795-9c39-7d511bc7bfe6
-- title:
--   Unary Retained Prefix Query
-- statement:
--   Definitions and structural lemmas for Unary Retained Prefix Query, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryRetainedPrefixQuery.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixListQuery
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_length_le
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PrefixProjection_fields_all

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.RetainedPrefixQuery
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (n:ℕ) (A:Machine)
def queryMachine:=RetainedInput.machine
  (Composition.machine (QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.prefixMachine n (QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.allMask n))
    (Composition.machine BitDelimiter.machine A))
noncomputable def time (p:Polynomial ℕ):Polynomial ℕ:=p+Polynomial.C 20*(Polynomial.X+1)
noncomputable def queryExec (xs:List ℕ) (hx:xs.length=n+1) (s:List Bool) (b:Bool) (p:Polynomial ℕ)
    (hA:EvalsToInTime (TM2.step A.program) (A.init (stream xs)) (some (A.halt [b])) (p.eval (stream xs).length)):
    EvalsToInTime (TM2.step (queryMachine n A).program) ((queryMachine n A).init (stream xs++s))
      (some ((queryMachine n A).halt ([b]++(stream xs++s)))) ((time p).eval (stream xs++s).length):=by
  have hp:=QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.polyExec n (QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.allMask n) xs hx s
  rw [QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.fields_all] at hp
  have hd:=BitDelimiter.exec (raw xs)
  rw [MatrixListQuery.delimiter_raw xs (by intro h;subst xs;simp at hx)] at hd
  have hc:=Composition.executes BitDelimiter.machine A _ _ _ _ _ hd hA
  have hpc:=Composition.executes (QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.prefixMachine n (QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.allMask n))
    (Composition.machine BitDelimiter.machine A) _ _ _ _ _ hp hc
  have hr:=RetainedInput.executes
    (Composition.machine (QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.prefixMachine n (QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.allMask n))
      (Composition.machine BitDelimiter.machine A)) _ _ _ hpc
  refine {hr with steps_le_m:=hr.steps_le_m.trans ?_}
  have hpmono:=Composition.polynomial_eval_monotone p (show (stream xs).length≤(stream xs++s).length by simp)
  have hrlen:=raw_length_le xs
  simp only [QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.time,time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one,List.length_cons,List.length_nil,List.length_append] at *
  omega
end QEC.Coding.BitTuring.UnaryArithmetic.RetainedPrefixQuery


