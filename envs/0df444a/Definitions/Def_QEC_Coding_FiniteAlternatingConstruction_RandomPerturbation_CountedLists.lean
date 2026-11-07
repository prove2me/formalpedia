-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:51:58.440642+00:00
-- url     : https://prove2.me/theorems/551a7330-c75e-4316-9fdc-170c042b593b
-- title:
--   Counted Lists
-- statement:
--   Definitions and structural lemmas for Counted Lists, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedLists.lean

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Tactic
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
def indexQuery {A : Type*} [DecidableEq A] (a : A) : List A → ℕ × ℕ
  | [] => (0,0)
  | b::L => if b = a then (0,1) else
      let q := indexQuery a L
      (q.1+1,q.2+1)
def orderedInsertQuery {A : Type*} (cmp : A → A → Bool × ℕ) (a : A) : List A → List A × ℕ
  | [] => ([a],1)
  | b::L =>
      let c := cmp a b
      if c.1 then (a::b::L,c.2+1) else
        let q := orderedInsertQuery cmp a L
        (b::q.1,c.2+q.2+1)
def sortQuery {A : Type*} (cmp : A → A → Bool × ℕ) : List A → List A × ℕ
  | [] => ([],0)
  | a::L =>
      let q := sortQuery cmp L
      let ins := orderedInsertQuery cmp a q.1
      (ins.1,q.2+ins.2)
end QEC.Coding.BDL26RandomPerturbation


