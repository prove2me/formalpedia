-- Prove2me | Definitions.Def_UnaryRecordStream
-- name    : UnaryRecordStream
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T21:14:52.846113+00:00
-- url     : https://prove2.me/theorems/991a05b0-57c9-4b24-985e-231d1086394d
-- title:
--   Self-delimiting unary fields in a finite-alphabet stream
-- statement:
--   A positive symbol increments the length of the open field. A zero completes the field, emits its length and resets the open field to zero. An unfinished field at the end contributes nothing. The canonical representation of a natural number is a run of that many ones followed by zero.
-- source:
--   Unary coding with a delimiter and an append-only streaming parser.

import Mathlib

set_option autoImplicit false

namespace UnaryRecordStream

/-- The accumulator keeps the open field and the complete fields in reverse. -/
def step (state : ℕ × List ℕ) (symbol : ℕ) : ℕ × List ℕ :=
  if symbol = 0 then (0, state.1 :: state.2) else (state.1+1,state.2)

def fields (symbols : List ℕ) : List ℕ :=
  (symbols.foldl step (0,[])).2.reverse

def code (n : ℕ) : List ℕ := List.replicate n 1 ++ [0]

def encode (values : List ℕ) : List ℕ := values.flatMap code

end UnaryRecordStream


