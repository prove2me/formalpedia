-- Prove2me | Definitions.Def_CountingMatroidProgramShift
-- name    : CountingMatroidProgramShift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T02:16:50.483694+00:00
-- url     : https://prove2.me/theorems/f8e69fc6-b56a-4535-8a53-ba5c67e2fe1a
-- title:
--   Sampler followed by a control-state-shifted evaluator
-- statement:
--   A concrete two-register-stack program that first samples K fair bits into register 9 and then runs a given evaluator after shifting its control states by four. The sampler uses a unary counter in register 8 and consumes exactly 3K+1 machine instructions.
-- source:
--   Verified local Lean 4.33.1 bridge contribution to the existing Approximate counting of common bases of two matroids mission. Adds no duplicate mission.

import Definitions.Def_CommonBasesFPRAS
set_option autoImplicit false

namespace OAI.CommonBasesFPRAS

def shiftState {s : ℕ} (q : Fin (s+1)) : Fin (s+5) := ⟨q.val+4, by omega⟩
def shiftInstruction {k s : ℕ} : Instruction k s → Instruction k (s+4)
 | .push r b q => .push r b (shiftState q)
 | .pop r e z o => .pop r (shiftState e) (shiftState z) (shiftState o)
 | .coin z o => .coin (shiftState z) (shiftState o)
 | .query w r no yes => .query w r (shiftState no) (shiftState yes)
 | .halt => .halt

def shiftProgram {k s : ℕ} (P : Program k s) : Program k (s+4) := fun q =>
 if h : q.val < 4 then .halt else shiftInstruction (P ⟨q.val-4, by omega⟩)

def embedConfig {k s : ℕ} (c : MachineConfig k s) : MachineConfig k (s+4) :=
 { c with control := shiftState c.control }

/-- The four-state sampler followed by the evaluator with shifted control. -/
def sampleThenProgram {s : ℕ} (P : Program 2 s) : Program 2 (s+4) := fun q =>
 if h : q.val < 4 then
  match q.val with
  | 0 => .pop 8 ⟨4, by omega⟩ ⟨1, by omega⟩ ⟨1, by omega⟩
  | 1 => .coin ⟨2, by omega⟩ ⟨3, by omega⟩
  | 2 => .push 9 false ⟨0, by omega⟩
  | _ => .push 9 true ⟨0, by omega⟩
 else shiftInstruction (P ⟨q.val-4, by omega⟩)

/-- The sampled bits in reverse order, as held on a stack after `m` pushes. -/
def programSampledStack (bits : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | m+1 => bits (3*m+1) :: programSampledStack bits m

/-- Register contents after `m` three-instruction sampling cycles. -/
def sampledProgramConfig {s : ℕ} (c : MachineConfig 2 s)
    (bits : ℕ → Bool) (K m : ℕ) : MachineConfig 2 (s+4) where
  registers := Function.update
    (Function.update c.registers 8 (List.replicate (K-m) false)) 9
    (programSampledStack bits m ++ c.registers 9)
  control := 0
  output := none
  oracleCalls := c.oracleCalls
  bitOperations := c.bitOperations + 3*m

/-- Evaluator configuration after sampling: register nine contains the sampled
bits in reverse stack order, and register eight is empty. -/
def afterSampleConfig {s : ℕ} (c : MachineConfig 2 s)
    (bits : ℕ → Bool) (K : ℕ) : MachineConfig 2 s :=
  { c with
    registers := Function.update (Function.update c.registers 8 []) 9
      (programSampledStack bits K ++ c.registers 9)
    control := 0
    output := none
    bitOperations := c.bitOperations + (3*K+1) }

end OAI.CommonBasesFPRAS


