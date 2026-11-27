-- Prove2me | Definitions.Def_TrimmedNativeWorkTape
-- name    : TrimmedNativeWorkTape
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T22:12:32.262209+00:00
-- url     : https://prove2.me/theorems/03ffa945-532c-5fd8-80a4-50609f6b1587
-- title:
--   Relative work-tape configurations with blank tails removed
-- statement:
--   In each work-tape zipper, keep the relative location of each nonblank symbol, remove trailing blanks on each half, and zero the absolute work-head coordinate. Leave the input-head position and machine state untouched.
-- source:
--   Universal multitape machine and work-tape zipper in the Prove2Me Complexitylib definition library.

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic
import Mathlib

namespace TrimmedWorkTape

open Turing.MultiTapeTM.Universal

/-- On a zipper half, remove blank cells only beyond the last nonblank symbol. -/
def trim : List (Option ℕ) → List (Option ℕ)
  | [] => []
  | none :: xs => if trim xs = [] then [] else none :: trim xs
  | some a :: xs => some a :: trim xs

/-- The transition table observes only the relative placement of nonblank work
symbols. The input-head position is handled separately. -/
def normalizeTape (t : Tape) : Tape := ⟨0,trim t.left,trim t.right⟩

def normalizeConfiguration (c : SCfg) : SCfg :=
  { c with workTapes := c.workTapes.map normalizeTape }

end TrimmedWorkTape


