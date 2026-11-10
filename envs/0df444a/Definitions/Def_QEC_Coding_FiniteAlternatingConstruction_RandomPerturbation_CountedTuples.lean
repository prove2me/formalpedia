-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T03:03:27.212761+00:00
-- url     : https://prove2.me/theorems/90d1f5d0-b79c-4da4-aef7-be8064ea1a89
-- title:
--   Counted Tuples
-- statement:
--   Definitions and structural lemmas for Counted Tuples, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedTuples.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
def flatMapQuery {A B : Type*} (q : A → List B × ℕ) : List A → List B × ℕ
  | [] => ([],0)
  | a::L => let qa := q a; let tail := flatMapQuery q L
            (qa.1++tail.1,qa.2+tail.2+qa.1.length+1)
def fourTuple1Query {A : Type*} (L : List A) (a b c : A) : List (List A) × ℕ :=
  flatMapQuery (fun d => ([[a,b,c,d]],8)) L
def fourTuple2Query {A : Type*} (L : List A) (a b : A) : List (List A) × ℕ :=
  flatMapQuery (fourTuple1Query L a b) L
def fourTuple3Query {A : Type*} (L : List A) (a : A) : List (List A) × ℕ :=
  flatMapQuery (fourTuple2Query L a) L
def fourTuplesQuery {A : Type*} (L : List A) : List (List A) × ℕ :=
  flatMapQuery (fourTuple3Query L) L
end QEC.Coding.BDL26RandomPerturbation


