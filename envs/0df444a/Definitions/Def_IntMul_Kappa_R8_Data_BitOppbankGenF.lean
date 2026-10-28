-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenF
-- name    : IntMul_Kappa_R8_Data_BitOppbankGenF
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:39:16.629881+00:00
-- url     : https://prove2.me/theorems/199f2b09-28d1-41e1-81f8-98ddfc963614
-- title:
--   R8 BitNB genF label generator (NL=31359)
-- statement:
--   # Label generator `genF` for R8 BitNB
--
--   Port of `R6Chk.Bit.Loc.genF` / `mvF` / `genStepF` / `codeOf` from
--   `IntMul_Kappa_R6_Defs51`. Geometry-agnostic fold of `LInstr` into code-state
--   moves and chunks; `ValidOn` / `packCodes` use $N_L=31359$.
-- source:
--   Port of IntMul_Kappa_R6_Defs51 genF (R6BitNBLabGen / R6BitNBChunk).

import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R8 opp-bank label generator (`genF`) @ `NL = 31359`

Port of `R6Chk.Bit.Loc.genF` / `codeOf` / `mvF` / `genStepF` from
`IntMul_Kappa_R6_Defs51` onto R8 geometry (`NR = 27794`, `NL = 31359`).
`genF` itself is geometry-agnostic; `ValidOn` / `packCodes` use `NL`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.Gen

def NL : ℕ := 31359

def fieldOf (X w i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight X (Nat.mul w i)) (Nat.sub (Nat.shiftLeft 1 w) 1)

def catB (B : ℕ) (l : List ℕ) : ℕ :=
  l.foldr (fun x acc => x ||| (acc <<< B)) 0

def packL (l : List Nat) : Nat := catB 65536 l

abbrev LInstr := ℕ × List ℕ × List (ℕ × ℕ)
abbrev LChunk := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)

def mvF (c : ℕ) (acc : (ℕ → ℕ) × List (ℕ × ℕ)) (w : ℕ) :
    (ℕ → ℕ) × List (ℕ × ℕ) :=
  if acc.1 w = c then acc
  else (fun x => if x = w then c else acc.1 x, (w, acc.1 w) :: acc.2)

def genStepF (acc : (ℕ → ℕ) × List LChunk) (i : LInstr) :
    (ℕ → ℕ) × List LChunk :=
  let r := i.2.1.foldl (mvF i.1) (acc.1, [])
  (r.1, (i.1, r.2.reverse, i.2.2) :: acc.2)

/-- Label generator (specification of `genP`). -/
def genF (f : ℕ → ℕ) (W : List LInstr) : (ℕ → ℕ) × List LChunk :=
  let r := W.foldl genStepF (f, [])
  (r.1, r.2.reverse)

def codeOf (S : ℕ) : ℕ → ℕ := fun w => fieldOf S 16 w

def packCodes (f : ℕ → ℕ) : ℕ :=
  catB 16 ((List.range NL).map f)

/-- Codes on local wires fit the R8 label alphabet bound used by R6 Fits-style checks. -/
def ValidOn (f : ℕ → ℕ) : Prop := ∀ w < NL, f w < 65536

end IntMul.Kappa.R8.Bit.Oppbank.Gen


