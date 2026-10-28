-- Prove2me | Definitions.Def_CountingMatroid_Bridge_ExchangeCandidateQuery
-- name    : CountingMatroid_Bridge_ExchangeCandidateQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T18:04:23.59733+00:00
-- url     : https://prove2.me/theorems/70c67d1a-027e-47a2-9f82-e04075c1be8e
-- title:
--   Fixed machine for constructing and querying a directed exchange candidate
-- statement:
--   A fixed binary-register program forms insert(v, I.erase(u)) from the canonical membership vector of I and unary indices u and v, then queries the selected exact independence oracle. It leaves the candidate vector canonical, clears scratch registers, makes exactly one oracle call, and has exact preprocessing and query bit costs.
-- source:
--   Lean 4.33.1 construction from the already verified indexed finite-set setter and exact oracle instruction. No Arlib dependency.

import Definitions.Def_CountingMatroid_Bridge_SetMembershipBitProgram

set_option autoImplicit false

namespace CountingMatroid.Bridge

open OAI.CommonBasesFPRAS

def exchangeSecondState (q : Fin 12) : Fin 28 :=
  if h : q.val = 11 then ⟨27, by omega⟩
  else if h10 : q.val = 10 then ⟨16, by omega⟩
  else ⟨q.val + 17, by have := q.isLt; omega⟩

def exchangeSecondInstruction (ins : Instruction 2 11) : Instruction 2 27 :=
  match ins with
  | .push i b next => .push i b (exchangeSecondState next)
  | .pop i empty zero one =>
      .pop i (exchangeSecondState empty) (exchangeSecondState zero) (exchangeSecondState one)
  | .coin zero one => .coin (exchangeSecondState zero) (exchangeSecondState one)
  | .query which i no yes =>
      .query which i (exchangeSecondState no) (exchangeSecondState yes)
  | .halt => .halt

def exchangeFirstState (q : Fin 12) : Fin 28 :=
  if h : q.val = 11 then ⟨11, by omega⟩
  else ⟨q.val, by have := q.isLt; omega⟩

def exchangeFirstInstruction (ins : Instruction 2 11) : Instruction 2 27 :=
  match ins with
  | .push i b next => .push i b (exchangeFirstState next)
  | .pop i empty zero one =>
      .pop i (exchangeFirstState empty) (exchangeFirstState zero) (exchangeFirstState one)
  | .coin zero one => .coin (exchangeFirstState zero) (exchangeFirstState one)
  | .query which i no yes =>
      .query which i (exchangeFirstState no) (exchangeFirstState yes)
  | .halt => .halt

/-- A two-stage query constructor for the directed exchange set `insert v (I.erase u)`.
It first clears `u`, moves the separately supplied unary index for `v` from
register 9 to register 7, sets `v`, and queries the resulting vector. -/
def exchangeCandidateQueryProgram (which : Bool) : Program 2 27 := fun pc =>
  if hfirst : pc.val < 11 then
    exchangeFirstInstruction
      (setMembershipBitProgram false ⟨11, by omega⟩ ⟨pc.val, by omega⟩)
  else if pc.val = 11 then
    .pop ⟨9, by omega⟩ ⟨14, by omega⟩ ⟨12, by omega⟩ ⟨12, by omega⟩
  else if pc.val = 12 then
    .push ⟨7, by omega⟩ true ⟨13, by omega⟩
  else if pc.val = 13 then
    .pop ⟨9, by omega⟩ ⟨14, by omega⟩ ⟨12, by omega⟩ ⟨12, by omega⟩
  else if pc.val = 14 then
    .pop ⟨8, by omega⟩ ⟨17, by omega⟩ ⟨17, by omega⟩ ⟨17, by omega⟩
  else if pc.val = 16 then
    exchangeSecondInstruction
      (setMembershipBitProgram true ⟨11, by omega⟩ ⟨10, by omega⟩)
  else if pc.val = 27 then
    .query which ⟨6, by omega⟩ ⟨10, by omega⟩ ⟨11, by omega⟩
  else if hsecond : 17 ≤ pc.val ∧ pc.val < 27 then
    let q : Fin 12 := ⟨pc.val - 17, by omega⟩
    exchangeSecondInstruction
      (setMembershipBitProgram true ⟨11, by omega⟩ q)
  else
    .halt

end CountingMatroid.Bridge


