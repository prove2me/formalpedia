-- Prove2me | Definitions.Def_MazurTransfer_ThirteenToNineteenOriginalCharacterDataAndConstructorCertificates20261018
-- name    : MazurTransfer_ThirteenToNineteenOriginalCharacterDataAndConstructorCertificates20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T23:30:12.034568+00:00
-- url     : https://prove2.me/theorems/b20e5b34-9cc0-412f-b802-008357d7e683
-- title:
--   Original explicit characters from thirteenth cyclotomic units to F19 units
-- statement:
--   The original generator two, explicit character value table, multiplicative character, inverse character and scalar twelve. Five full declaration types, five whole values and both original prime-provider propositions are checked. Named downstream consumer: the actual arithmetic13 norm-kernel characters. Exact order and generator evaluations remain separate theorem contracts.
-- source:
--   MazurTheorem ThirteenToNineteenCharacters, original definitions and immediate multiplicativity constructor certificates; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: explicit inverse order-six characters from the thirteenth
cyclotomic Galois group (ZMod 13)^* to F19^*, normalized at two.
Named downstream consumer: the two actual norm-factor arithmetic13 lines.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

namespace MazurTransfer.ThirteenToNineteenCharacters
local instance characterOriginalPrime13Provider20261018 : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance characterOriginalPrime19Provider20261018 : Fact (Nat.Prime 19) := ⟨by decide⟩

def generator : (ZMod 13)ˣ := Units.mk0 2 (by decide)

def characterValue (u : (ZMod 13)ˣ) : ZMod 19 :=
  match (u : ZMod 13).val with
  | 1 => 1
  | 2 => 12
  | 3 => 7
  | 4 => 11
  | 5 => 18
  | 6 => 8
  | 7 => 8
  | 8 => 18
  | 9 => 11
  | 10 => 7
  | 11 => 12
  | _ => 1

def character : (ZMod 13)ˣ →* (ZMod 19)ˣ where
  toFun u := Units.mk0 (characterValue u) (by unfold characterValue; split <;> decide)
  map_one' := by decide
  map_mul' := by decide

def conjugateCharacter : (ZMod 13)ˣ →* (ZMod 19)ˣ := character⁻¹

def scalarTwelve : (ZMod 19)ˣ := ⟨12, 8, by decide, by decide⟩
end MazurTransfer.ThirteenToNineteenCharacters
#print axioms MazurTransfer.ThirteenToNineteenCharacters.generator
#print axioms MazurTransfer.ThirteenToNineteenCharacters.characterValue
#print axioms MazurTransfer.ThirteenToNineteenCharacters.character
#print axioms MazurTransfer.ThirteenToNineteenCharacters.conjugateCharacter
#print axioms MazurTransfer.ThirteenToNineteenCharacters.scalarTwelve


