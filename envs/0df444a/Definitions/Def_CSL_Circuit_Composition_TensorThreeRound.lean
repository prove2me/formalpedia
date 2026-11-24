-- Prove2me | Definitions.Def_CSL_Circuit_Composition_TensorThreeRound
-- name    : CSL_Circuit_Composition_TensorThreeRound
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:55:12.932086+00:00
-- url     : https://prove2.me/theorems/98880f34-f5d7-476c-8223-a84b345f1bc5
-- title:
--   Coded sorting library: Circuit / Composition / TensorThreeRound
-- statement:
--   Module `CodedSorting.Circuit.Composition.TensorThreeRound` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Three executable XOR rounds swap all original data and restore helpers
--
--   The rounds accept separate physical local words. In particular, the middle
--   round may use the paper's reversed and complemented word; payload correctness
--   alone does not identify its frame sequence with that of the first round.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Composition.TensorThreeRound

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Composition_TensorLiftProgram

/-!
# Three executable XOR rounds swap all original data and restore helpers

The rounds accept separate physical local words. In particular, the middle
round may use the paper's reversed and complemented word; payload correctness
alone does not identify its frame sequence with that of the first round.
-/

set_option autoImplicit false

namespace CSL.Construction.TensorThreeRound

open CSL.Circuit CSL.CircuitProgram
open CSL.Construction.ThreeCopySchedule CSL.Construction.TensorLiftProgram

def dataRegister (i : Copy) (bank : Fin 2) (coordinates : Coordinates) : GlobalReg :=
  .inl (.inl (i, bank, coordinates))

def helperRegister (pool : Pool) (h : Fin 439) : GlobalReg := .inl (.inr (pool,h))

theorem fiberEmbedding_data_at (round : Round) (assignment : Pool ≃ Block)
    (i : Copy) (bank : Fin 2) (coordinates : Coordinates) :
    fiberEmbedding round assignment (i, (coordinateView round coordinates).2)
      (.inl (bank, (coordinateView round coordinates).1)) =
    dataRegister i (bankView round bank) coordinates := by
  simp [fiberEmbedding, fiberMap, fiberDataEquiv, dataRegister]

theorem round_data_source (word : List (XorGate LocalReg)) (hc : LocalCorrect word)
    (round : Round) (assignment : Pool ≃ Block) (state : GlobalReg → Bit)
    (i : Copy) (coordinates : Coordinates) :
    runProgram (roundProgram word round assignment) state
      (dataRegister i (bankView round 0) coordinates) =
    state (dataRegister i (bankView round 0) coordinates) := by
  have h := roundProgram_source word hc round assignment state
    (i, (coordinateView round coordinates).2) (coordinateView round coordinates).1
  simpa only [fiberEmbedding_data_at] using h

theorem round_data_target (word : List (XorGate LocalReg)) (hc : LocalCorrect word)
    (round : Round) (assignment : Pool ≃ Block) (state : GlobalReg → Bit)
    (i : Copy) (coordinates : Coordinates) :
    runProgram (roundProgram word round assignment) state
      (dataRegister i (bankView round 1) coordinates) =
    state (dataRegister i (bankView round 1) coordinates) +
      state (dataRegister i (bankView round 0) coordinates) := by
  have h := roundProgram_target word hc round assignment state
    (i, (coordinateView round coordinates).2) (coordinateView round coordinates).1
  simpa only [fiberEmbedding_data_at] using h

theorem round_data_zero (word : List (XorGate LocalReg)) (hc : LocalCorrect word)
    (round : Round) (assignment : Pool ≃ Block) (state : GlobalReg → Bit)
    (i : Copy) (coordinates : Coordinates) :
    runProgram (roundProgram word round assignment) state (dataRegister i 0 coordinates) =
    match round with
    | .first => state (dataRegister i 0 coordinates)
    | .second => state (dataRegister i 0 coordinates) + state (dataRegister i 1 coordinates)
    | .third => state (dataRegister i 0 coordinates) := by
  cases round with
  | first => exact round_data_source word hc .first assignment state i coordinates
  | second =>
    simpa [bankView] using round_data_target word hc .second assignment state i coordinates
  | third => exact round_data_source word hc .third assignment state i coordinates

theorem round_data_one (word : List (XorGate LocalReg)) (hc : LocalCorrect word)
    (round : Round) (assignment : Pool ≃ Block) (state : GlobalReg → Bit)
    (i : Copy) (coordinates : Coordinates) :
    runProgram (roundProgram word round assignment) state (dataRegister i 1 coordinates) =
    match round with
    | .first => state (dataRegister i 1 coordinates) + state (dataRegister i 0 coordinates)
    | .second => state (dataRegister i 1 coordinates)
    | .third => state (dataRegister i 1 coordinates) + state (dataRegister i 0 coordinates) := by
  cases round with
  | first => exact round_data_target word hc .first assignment state i coordinates
  | second =>
    simpa [bankView] using round_data_source word hc .second assignment state i coordinates
  | third => exact round_data_target word hc .third assignment state i coordinates

/-- The exact assignments from the proved three-copy reuse schedule. -/
def roundAssignment (pi : Equiv.Perm Line) : Round → Pool ≃ Block
  | .first => roundOne
  | .second => roundTwo pi
  | .third => roundThree pi

/-- Actual three-round gate list. Each round has its own physical local word
so the middle round can use the reversed-complemented construction. -/
noncomputable def threeRoundProgram (wordOne wordTwo wordThree : List (XorGate LocalReg))
    (pi : Equiv.Perm Line) : List (XorGate GlobalReg) :=
  roundProgram wordOne .first (roundAssignment pi .first) ++
    roundProgram wordTwo .second (roundAssignment pi .second) ++
    roundProgram wordThree .third (roundAssignment pi .third)

private theorem bit_add_self (a : Bit) : a + a = 0 :=
  (by decide : ∀ b : Bit, b + b = 0) a

theorem threeRound_data_zero (wordOne wordTwo wordThree : List (XorGate LocalReg))
    (hOne : LocalCorrect wordOne) (hTwo : LocalCorrect wordTwo) (hThree : LocalCorrect wordThree)
    (pi : Equiv.Perm Line) (state : GlobalReg → Bit) (i : Copy) (coordinates : Coordinates) :
    runProgram (threeRoundProgram wordOne wordTwo wordThree pi) state
      (dataRegister i 0 coordinates) = state (dataRegister i 1 coordinates) := by
  simp only [threeRoundProgram, runProgram_append]
  rw [round_data_zero wordThree hThree, round_data_zero wordTwo hTwo,
    round_data_zero wordOne hOne, round_data_one wordOne hOne]
  rw [add_left_comm, bit_add_self, add_zero]

theorem threeRound_data_one (wordOne wordTwo wordThree : List (XorGate LocalReg))
    (hOne : LocalCorrect wordOne) (hTwo : LocalCorrect wordTwo) (hThree : LocalCorrect wordThree)
    (pi : Equiv.Perm Line) (state : GlobalReg → Bit) (i : Copy) (coordinates : Coordinates) :
    runProgram (threeRoundProgram wordOne wordTwo wordThree pi) state
      (dataRegister i 1 coordinates) = state (dataRegister i 0 coordinates) := by
  simp only [threeRoundProgram, runProgram_append]
  rw [round_data_one wordThree hThree, round_data_one wordTwo hTwo,
    round_data_zero wordTwo hTwo, round_data_zero wordOne hOne,
    round_data_one wordOne hOne]
  rw [add_left_comm, bit_add_self, add_zero]

theorem threeRound_helper (wordOne wordTwo wordThree : List (XorGate LocalReg))
    (hOne : LocalCorrect wordOne) (hTwo : LocalCorrect wordTwo) (hThree : LocalCorrect wordThree)
    (pi : Equiv.Perm Line) (state : GlobalReg → Bit) (pool : Pool) (h : Fin 439) :
    runProgram (threeRoundProgram wordOne wordTwo wordThree pi) state (helperRegister pool h) =
      state (helperRegister pool h) := by
  simp only [threeRoundProgram, runProgram_append, helperRegister]
  rw [roundProgram_helper wordThree hThree, roundProgram_helper wordTwo hTwo,
    roundProgram_helper wordOne hOne]

def originalSwap : Equiv.Perm IndependentStream :=
  Equiv.sumCongr
    (Equiv.prodCongr (Equiv.refl Copy)
      (Equiv.prodCongr (Equiv.swap (0 : Fin 2) 1) (Equiv.refl Coordinates)))
    (Equiv.refl HelperStream)

def physicalSwap : Equiv.Perm GlobalReg :=
  Equiv.sumCongr originalSwap (Equiv.refl TemporaryStream)

/-- The whole original message vector is permuted, including preservation
of every dirty helper. No temporary restoration is claimed or needed. -/
theorem threeRound_original (wordOne wordTwo wordThree : List (XorGate LocalReg))
    (hOne : LocalCorrect wordOne) (hTwo : LocalCorrect wordTwo) (hThree : LocalCorrect wordThree)
    (pi : Equiv.Perm Line) (state : GlobalReg → Bit) (r : IndependentStream) :
    runProgram (threeRoundProgram wordOne wordTwo wordThree pi) state (.inl r) =
      state (.inl (originalSwap r)) := by
  rcases r with ⟨i,bank,coordinates⟩ | ⟨pool,h⟩
  · have hbank : bank = 0 ∨ bank = 1 := by omega
    rcases hbank with rfl | rfl
    · simpa [dataRegister, originalSwap] using
        threeRound_data_zero wordOne wordTwo wordThree hOne hTwo hThree pi state i coordinates
    · simpa [dataRegister, originalSwap] using
        threeRound_data_one wordOne wordTwo wordThree hOne hTwo hThree pi state i coordinates
  · exact threeRound_helper wordOne wordTwo wordThree hOne hTwo hThree pi state pool h

end CSL.Construction.TensorThreeRound


