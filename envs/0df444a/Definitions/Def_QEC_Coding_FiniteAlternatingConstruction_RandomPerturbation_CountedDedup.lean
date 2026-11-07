-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:08:01.652843+00:00
-- url     : https://prove2.me/theorems/4b51c7d8-8099-495c-ae6a-5d6fa8539a2a
-- title:
--   Counted Dedup
-- statement:
--   Definitions and structural lemmas for Counted Dedup, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedDedup.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Mathlib.Data.List.Dedup
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
def memberQuery {A : Type*} (eq : A → A → Bool × ℕ) (a : A) : List A → Bool × ℕ
  | [] => (false,0)
  | b::L => let qb := eq a b
            if qb.1 then (true,qb.2+1) else
              let tail := memberQuery eq a L
              (tail.1,qb.2+tail.2+1)
def dedupQuery {A : Type*} (eq : A → A → Bool × ℕ) : List A → List A × ℕ
  | [] => ([],0)
  | a::L => let tail := dedupQuery eq L
            let q := memberQuery eq a tail.1
            (if q.1 then tail.1 else a::tail.1,tail.2+q.2+1)
end QEC.Coding.BDL26RandomPerturbation


