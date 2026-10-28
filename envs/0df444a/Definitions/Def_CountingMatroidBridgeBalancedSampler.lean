-- Prove2me | Definitions.Def_CountingMatroidBridgeBalancedSampler
-- name    : CountingMatroidBridgeBalancedSampler
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T03:59:21.854909+00:00
-- url     : https://prove2.me/theorems/7e679f85-5a4a-4bf1-9dda-a0c17c47829f
-- title:
--   Fixed-cost finite-bit sampler
-- statement:
--   A fixed machine program that samples K fair bits at deterministic, pairwise distinct random-tape positions and stores the samples on its work stack. Each sample uses exactly three machine steps, followed by a one-step loop exit.
-- source:
--   Lean 4.33.1 finite-randomness machine contribution to the existing counting-matroid mission; uses the local CommonBasesFPRAS instruction model and no Arlib definitions.

import Definitions.Def_CommonBasesFPRAS
set_option autoImplicit false

namespace CountingMatroid.Bridge
open OAI.CommonBasesFPRAS

/-- Fixed-cost sampler: one counter pop, fair coin, and sample-stack push per bit. -/
def balancedSampler : Program 2 4 := fun q =>
  match q.val with
  | 0 => .pop 8 4 1 1
  | 1 => .coin 2 3
  | 2 => .push 9 false 0
  | 3 => .push 9 true 0
  | _ => .halt

def sampledStack (bits : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | m + 1 => bits (3 * m + 1) :: sampledStack bits m

def samplingConfig (c : MachineConfig 2 4) (bits : ℕ → Bool) (K m : ℕ) :
    MachineConfig 2 4 :=
  { c with
    registers := Function.update
      (Function.update c.registers 8 (List.replicate (K - m) false)) 9
      (sampledStack bits m ++ c.registers 9)
    control := 0
    output := none
    bitOperations := c.bitOperations + 3 * m }

def samplingPositions (K : ℕ) : Fin K ↪ Fin (3 * K + 1) where
  toFun i := ⟨3 * i.val + 1, by have := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

end CountingMatroid.Bridge


