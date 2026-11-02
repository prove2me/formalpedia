-- Prove2me | Definitions.Def_TwoAgentSched_TotalTotal_StackCompareDigits
-- name    : TwoAgentSched_TotalTotal_StackCompareDigits
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T20:37:56.937558+00:00
-- url     : https://prove2.me/theorems/8c4a3d84-e03b-4f04-ad30-79c11fe0177b
-- title:
--   Finite stack comparator for canonical binary naturals
-- statement:
--   A finite three-stack program for comparing two most-significant-bit-first binary digit strings. It scans paired symbols, maintaining a comparison-state stack, and then uses unmatched input lengths to decide which string is shorter. A separator marker represents equality, zero represents less, and one represents greater.
--
--   On arbitrary symbols the program is still a finite stack program; a separate theorem states its total step bound. Its numerical correctness is stated for canonical binary expansions, for which comparing lengths before equal-length lexicographic order is valid. The program supports the sorting component of the scheduling reduction.
-- source:
--   Supporting implementation for the formalization of Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2, pp. 237–238. This comparator is an additional machine component, not a claim in the paper.

import Mathlib
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding

set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TwoAgentSched.TotalTotal.StackCompareDigits

/-- Left digits, right digits, and a nonempty stack of comparison states.
    The state symbols are separator = equal, zero = less, one = greater. -/
def store (left right states : List BSym) : Fin 3 → List BSym :=
  fun k => if k = 0 then left else if k = 1 then right else states

def digitSym (b : Bool) : BSym := if b then .one else .zero

def nextState (state x y : BSym) : BSym :=
  if state = .sep then
    if x = .zero ∧ y = .one then .zero
    else if x = .one ∧ y = .zero then .one
    else .sep
  else state

def bothNonempty (h : Fin 3 → Option BSym) : Bool :=
  (h 0).isSome && (h 1).isSome

def compareAct (h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 0 ∨ k = 1 then .pop
  else .push (nextState ((h 2).getD .sep) ((h 0).getD .sep) ((h 1).getD .sep))

/-- A finite program for equal-length MSB-first digit comparison. -/
def compareProg : StackProg (Fin 3) BSym := .loop bothNonempty (.act compareAct)

def leftShort (h : Fin 3 → Option BSym) : Bool :=
  !(h 0).isSome && (h 1).isSome
def rightShort (h : Fin 3 → Option BSym) : Bool :=
  (h 0).isSome && !(h 1).isSome
def markAct (a : BSym) (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push a else .keep
def keepAct (_h : Fin 3 → Option BSym) (_k : Fin 3) : StackAct BSym := .keep

/-- At the end of the pair scan, unequal lengths override the lexicographic
    marker; equal lengths leave the previous state unchanged. -/
def finishLength : StackProg (Fin 3) BSym :=
  .branch leftShort (.act (markAct .zero))
    (.branch rightShort (.act (markAct .one)) (.act keepAct))

/-- Pairwise bit comparison followed by its length check. -/
def compareFullProg : StackProg (Fin 3) BSym := .seq compareProg finishLength


end TwoAgentSched.TotalTotal.StackCompareDigits


