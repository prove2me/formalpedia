-- Prove2me | Definitions.Def_StreamReductionResidualRank
-- name    : StreamReductionResidualRank
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-27T05:23:21.711882+00:00
-- url     : https://prove2.me/theorems/70a7df7f-5dd0-4b83-b8d1-630f7945aa15
-- title:
--   Streaming reductions with committed, write-only output
-- statement:
--   A deterministic transducer reads one input symbol at a time, updates its state, and emits a finite output block. Output blocks concatenate, and a final block can depend on the last state.
-- source:
--   Basic operational semantics of a one-way streaming reduction.

import Mathlib

set_option autoImplicit false

namespace PvsNP.StreamReductionRank

universe u v w x y

structure Transducer (A : Type u) (B : Type v) (S : Type w) where
  init : S
  step : S → A → S × List B
  finish : S → List B

variable {A : Type u} {B : Type v} {S : Type w}

def Transducer.run (R : Transducer A B S) : S → List A → S × List B
  | q, [] => (q, [])
  | q, a :: xs =>
      let first := R.step q a
      let rest := R.run first.1 xs
      (rest.1, first.2 ++ rest.2)

def Transducer.output (R : Transducer A B S) (xs : List A) : List B :=
  let reached := R.run R.init xs
  reached.2 ++ R.finish reached.1

end PvsNP.StreamReductionRank


