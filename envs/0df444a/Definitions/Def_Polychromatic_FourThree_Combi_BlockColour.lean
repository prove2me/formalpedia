-- Prove2me | Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
-- name    : Polychromatic_FourThree_Combi_BlockColour
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:40:18.800406+00:00
-- url     : https://prove2.me/theorems/0e30648c-8e5f-43df-88d2-21bce925097c
-- title:
--   Block Colour
-- statement:
--   Definitions and structural lemmas for Block Colour, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Mathlib.Algebra.Ring.AddAut
set_option autoImplicit true
open Finset Pointwise
def zmod_set (m : ℕ) (a b : ℤ) : Finset (ZMod m) :=
  ({0, b - a, b, 2 * b - a} : Finset ℤ).image Int.cast
section BlockColorInfra
def checkLinearPolychrom (offsets : List ℕ) (L : List (Fin 3)) : Bool :=
  let maxOff := offsets.foldr max 0
  (List.range (L.length - maxOff)).all fun i => ([0, 1, 2] : List (Fin 3)).all fun c =>
      offsets.any fun s => L[i + s]? == some c
def checkBlockPairs (offsets : List ℕ) (A B : List (Fin 3)) : Bool :=
  checkLinearPolychrom offsets (A ++ A) &&
  checkLinearPolychrom offsets (A ++ B) &&
  checkLinearPolychrom offsets (B ++ A) &&
  checkLinearPolychrom offsets (B ++ B)
def blockColorVal (A B : List (Fin 3)) (h : ℕ) (p : ℕ) : Fin 3 :=
  if p < A.length * h then (A[p % A.length]?).getD 0
  else (B[(p - A.length * h) % B.length]?).getD 0
def CaseGoal (A B : List (Fin 3)) (offsets : List ℕ) (h m i : ℕ) : Prop :=
  ∃ (XY : List (Fin 3)) (j : ℕ),
    checkLinearPolychrom offsets XY = true ∧
    j + offsets.foldr max 0 < XY.length ∧
    ∀ s, s ≤ offsets.foldr max 0 → XY[j + s]? = some (blockColorVal A B h ((i + s) % m))
end BlockColorInfra
section Table1
variable (m : ℕ)
end Table1


