-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_ModulusQuery
-- name    : QEC_Coding_BitTuring_ModulusQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:09:51.922303+00:00
-- url     : https://prove2.me/theorems/6f1a12c2-7ac3-4893-bbc3-5ac64e595e78
-- title:
--   Modulus Query
-- statement:
--   Definitions and structural lemmas for Modulus Query, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/ModulusQuery.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryInverseInput
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_fields_stream_length_le
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_append_last
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.ModulusQuery
open Turing StateTransition UnaryArithmetic FieldProjection
def mask (n:ℕ) (k:Fin (n+1)) : Bool := k.val==n
def machine (n:ℕ) (A:Machine) := RetainedInput.machine
  (Composition.machine (FieldProjection.machine n (mask n)) (Composition.machine A UnaryDelimiter.machine))
noncomputable def time (p:Polynomial ℕ) := p+Polynomial.C 20*(Polynomial.X+1)
noncomputable def exec (n:ℕ) (A:Machine) (p:Polynomial ℕ) (xs:List ℕ)
    (hx:xs.length=n+1) (q r:ℕ) (hr:r<q)
    (hf:fields n (mask n) 0 xs=[q])
    (hA:EvalsToInTime (TM2.step A.program) (A.init (unary q))
      (some (A.halt (unary r))) (p.eval q)) :
    EvalsToInTime (TM2.step (machine n A).program) ((machine n A).init (stream xs))
      (some ((machine n A).halt (stream (r::xs)))) ((time p).eval (stream xs).length) := by
  have hp:=FieldProjection.polyExec n (mask n) xs hx
  rw [hf] at hp
  have he:raw [q]=unary q := by
    simpa only [List.nil_append,stream,List.append_nil] using raw_append_last [] q
  rw [he] at hp
  have hb:=Composition.executes A UnaryDelimiter.machine _ _ _ _ _ hA (UnaryDelimiter.exec r)
  have hbody:=Composition.executes (FieldProjection.machine n (mask n))
    (Composition.machine A UnaryDelimiter.machine) _ _ _ _ _ hp hb
  have h:=RetainedInput.executes
    (Composition.machine (FieldProjection.machine n (mask n)) (Composition.machine A UnaryDelimiter.machine))
    (stream xs) (unary r++[false]) _ hbody
  rw [show (unary r++[false])++stream xs=stream (r::xs) by simp [stream,List.append_assoc]] at h
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hl:=fields_stream_length_le n (mask n) 0 xs
  rw [hf] at hl
  have hs:(stream [q]).length=q+1 := by simp [stream,unary_length]
  rw [hs] at hl
  have hpol:=Composition.polynomial_eval_monotone p (show q≤(stream xs).length by omega)
  change p.eval q≤p.eval (stream xs).length at hpol
  simp only [time,FieldProjection.time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one,List.length_append,List.length_singleton,unary_length]
  omega
end QEC.Coding.BitTuring.ModulusQuery


