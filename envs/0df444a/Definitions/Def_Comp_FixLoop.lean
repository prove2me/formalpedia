-- Prove2me | Definitions.Def_Comp_FixLoop
-- name    : Comp_FixLoop
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:40:16.199675+00:00
-- url     : https://prove2.me/theorems/6bef07aa-c3ec-4f11-9126-95f36bbaa923
-- title:
--   Fix Loop
-- statement:
--   Definitions and structural lemmas for Fix Loop, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
set_option autoImplicit true
namespace Comp
variable {S : Type*} [DecidableEq S]
def fixAux (f : Finset S → Finset S) : ℕ → Finset S → Finset S
  | 0, x => x
  | n + 1, x => if f x = x then x else fixAux f n (f x)
variable [Fintype S]
def fixFrom (f : Finset S → Finset S) (x : Finset S) : Finset S :=
  fixAux f (Fintype.card S) x
end Comp


