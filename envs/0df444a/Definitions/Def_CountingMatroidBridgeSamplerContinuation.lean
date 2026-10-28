-- Prove2me | Definitions.Def_CountingMatroidBridgeSamplerContinuation
-- name    : CountingMatroidBridgeSamplerContinuation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T04:32:30.739137+00:00
-- url     : https://prove2.me/theorems/4a64fb91-9d5c-42aa-9b29-87909735de31
-- title:
--   Sampler loop and estimator continuation configuration
-- statement:
--   The machine configuration after m iterations of the fixed sampler, together with the exact continuation configuration after its final empty-counter test. The first stores the remaining unary counter and the sampled bits in reverse order; the second enters the estimator at its designated control state with the sampler cost included.
-- source:
--   Lean 4.33.1 machine-composition contribution to the existing counting-matroid mission; no Arlib dependency.

import Definitions.Def_CountingMatroidBridgeProgramAppend
set_option autoImplicit false

namespace CountingMatroid.Bridge
open OAI.CommonBasesFPRAS

/-- Configuration after m iterations of the fixed sampling prefix. -/
def appendedSamplingConfig {s : ℕ} (c : MachineConfig 2 (s + 5))
    (bits : ℕ → Bool) (K m : ℕ) : MachineConfig 2 (s + 5) :=
  { c with
    registers := Function.update
      (Function.update c.registers 8 (List.replicate (K - m) false)) 9
      (sampledStack bits m ++ c.registers 9)
    control := 0
    output := none
    bitOperations := c.bitOperations + 3 * m }

/-- The exact continuation configuration after the sampler's final empty test. -/
def appendedSamplerBoundary {s : ℕ} (c : MachineConfig 2 (s + 5))
    (bits : ℕ → Bool) (K : ℕ) : MachineConfig 2 (s + 5) :=
  { appendedSamplingConfig c bits K K with
    control := 4
    bitOperations := c.bitOperations + (3 * K + 1) }

end CountingMatroid.Bridge


