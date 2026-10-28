-- Prove2me | Definitions.Def_OAICommonBasesFPRASNaturalMultiplierMachineV2
-- name    : OAICommonBasesFPRASNaturalMultiplierMachineV2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T20:40:19.961634+00:00
-- url     : https://prove2.me/theorems/343150ef-9814-481d-9a00-77049a7e3424
-- title:
--   Natural inputs for the verified binary multiplier
-- statement:
--   The fixed shift-and-add register program accepts ordinary little-endian Nat.bits operands, returns their exact product, makes no oracle calls, and uses at most a quadratic number of bit operations.
-- source:
--   Lean 4.33.1 binary-register implementation verified locally; source definitions and proofs are included in the published module.

import Definitions.Def_OAICommonBasesFPRASBinaryStackAdderContinuationV3
import Definitions.Def_CountingMatroidBridgeBinarySampler

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Fixed binary multiplier on natural inputs

This package connects the reusable shift-and-add program to ordinary `Nat.bits`
inputs and records its exact result, oracle behavior, and quadratic bit cost.
It uses the local binary-stack machine and does not import Arlib.
-/

namespace OAI.CommonBasesFPRAS

/-- Load two natural operands into the fixed multiplication program. -/
def naturalMultiplierConfig (a b : ℕ) : MachineConfig 2 37 where
  registers := fun i =>
    match i.val with
    | 5 => a.bits
    | 7 => [true]
    | 9 => b.bits
    | _ => []
  control := ⟨25, by omega⟩
  output := none
  oracleCalls := 0
  bitOperations := 0

/-- The fixed shift-and-add machine returns the product of its natural inputs. -/
theorem naturalMultiplierConfig_correct {n : ℕ} (O : IndependenceOracle n)
    (coins : ℕ → Bool) (a b : ℕ) :
    let c := naturalMultiplierConfig a b
    let out := execution binaryStackMultiplierProgram O c coins
      (binaryStackMultiplierLoopSteps [] a.bits b.bits)
    out.output = some ((a * b : ℕ) : ℚ) := by
  let c := naturalMultiplierConfig a b
  have h := binaryStackMultiplierProgram_loop_product_output O coins c
    a.bits b.bits (by simp [c, naturalMultiplierConfig])
    (by simp [c, naturalMultiplierConfig])
    (by simp [c, naturalMultiplierConfig, adderReg])
    (by simp [c, naturalMultiplierConfig, adderReg])
    (by simp [c, naturalMultiplierConfig, adderReg])
    (by simp [c, naturalMultiplierConfig, adderReg])
    (by simp [c, naturalMultiplierConfig, adderReg])
    (by simp [c, naturalMultiplierConfig, adderReg])
    (by simp [c, naturalMultiplierConfig, adderReg])
  simpa [c, CountingMatroid.Bridge.machineBinaryValue_bits] using h

/-- The same multiplication run uses no oracle calls and has quadratic bit cost. -/
theorem naturalMultiplierConfig_resources {n : ℕ} (O : IndependenceOracle n)
    (coins : ℕ → Bool) (a b : ℕ) :
    let c := naturalMultiplierConfig a b
    let out := execution binaryStackMultiplierProgram O c coins
      (binaryStackMultiplierLoopSteps [] a.bits b.bits)
    out.oracleCalls = 0 ∧
      out.bitOperations ≤ 100 * (b.bits.length + 1) *
        (a.bits.length + b.bits.length + 5) := by
  let c := naturalMultiplierConfig a b
  have h := binaryStackMultiplierProgram_loop_correct O coins c [] a.bits b.bits
    (by simp [c, naturalMultiplierConfig])
    (by simp [c, naturalMultiplierConfig])
    (by simp [c, naturalMultiplierConfig, adderReg])
    (by simp [c, naturalMultiplierConfig, adderReg])
    (by simp [c, naturalMultiplierConfig, adderReg])
    (by simp [c, naturalMultiplierConfig, adderReg])
    (by simp [c, naturalMultiplierConfig, adderReg])
    (by simp [c, naturalMultiplierConfig, adderReg])
    (by simp [c, naturalMultiplierConfig, adderReg])
  rcases h with ⟨_, _, hcalls, hbits⟩
  constructor
  · simpa [c, naturalMultiplierConfig] using hcalls
  · calc
      (execution binaryStackMultiplierProgram O c coins
        (binaryStackMultiplierLoopSteps [] a.bits b.bits)).bitOperations =
          c.bitOperations + binaryStackMultiplierLoopBitOperations [] a.bits b.bits :=
            hbits
      _ = binaryStackMultiplierLoopBitOperations [] a.bits b.bits := by
        simp [c, naturalMultiplierConfig]
      _ ≤ 100 * (b.bits.length + 1) *
          (a.bits.length + b.bits.length + 5) := by
        simpa using binaryStackMultiplierLoopBitOperations_le_quadratic
          [] a.bits b.bits

end OAI.CommonBasesFPRAS


