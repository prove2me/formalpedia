-- Prove2me | Definitions.Def_CountingMatroidBridgeProgramAppend
-- name    : CountingMatroidBridgeProgramAppend
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T04:26:15.885432+00:00
-- url     : https://prove2.me/theorems/06d56872-6180-4d5e-ba5f-f97f39798f40
-- title:
--   Fixed sampler followed by a shifted machine program
-- statement:
--   A fixed register-machine program that reserves five control states for finite-bit sampling and shifts the control states of a supplied estimator program. Its decoder maps the continuation state and every shifted estimator state back to the corresponding state of the supplied program, allowing the sampler and estimator to share one fixed program.
-- source:
--   Lean 4.33.1 machine-composition contribution to the existing counting-matroid mission; no Arlib dependency.

import Definitions.Def_CountingMatroidBridgeBalancedSampler
set_option autoImplicit false

namespace CountingMatroid.Bridge
open OAI.CommonBasesFPRAS

def liftedSampleState {s : ℕ} (q : Fin 5) : Fin (s + 6) :=
  ⟨q.val, by have := q.isLt; omega⟩

def shiftedProgramState {s : ℕ} (q : Fin (s + 1)) : Fin (s + 6) :=
  ⟨q.val + 5, by have := q.isLt; omega⟩

def shiftInstruction {s : ℕ} : Instruction 2 s → Instruction 2 (s + 5)
  | .push i b q => .push i b (shiftedProgramState q)
  | .pop i empty zero one =>
      .pop i (shiftedProgramState empty) (shiftedProgramState zero) (shiftedProgramState one)
  | .coin zero one => .coin (shiftedProgramState zero) (shiftedProgramState one)
  | .query which i no yes =>
      .query which i (shiftedProgramState no) (shiftedProgramState yes)
  | .halt => .halt

def liftSampleInstruction {s : ℕ} : Instruction 2 4 → Instruction 2 (s + 5)
  | .push i b q => .push i b (liftedSampleState q)
  | .pop i empty zero one =>
      .pop i (liftedSampleState empty) (liftedSampleState zero) (liftedSampleState one)
  | .coin zero one => .coin (liftedSampleState zero) (liftedSampleState one)
  | .query which i no yes =>
      .query which i (liftedSampleState no) (liftedSampleState yes)
  | .halt => .halt

def sampleThenProgram {s : ℕ} (P : Program 2 s) : Program 2 (s + 5) := fun q =>
  match h : q.val with
  | 0 => liftSampleInstruction (balancedSampler 0)
  | 1 => liftSampleInstruction (balancedSampler 1)
  | 2 => liftSampleInstruction (balancedSampler 2)
  | 3 => liftSampleInstruction (balancedSampler 3)
  | 4 => shiftInstruction (P 0)
  | v + 5 => shiftInstruction (P ⟨v, by have hq := q.isLt; rw [h] at hq; omega⟩)

def decodeProgramState {s : ℕ} (q : Fin (s + 6)) : Fin (s + 1) :=
  ⟨if q.val < 5 then 0 else q.val - 5, by
    split
    · have := q.isLt; omega
    · have := q.isLt; omega⟩

def decodeProgramConfig {s : ℕ} (c : MachineConfig 2 (s + 5)) : MachineConfig 2 s where
  registers := c.registers
  control := decodeProgramState c.control
  output := c.output
  oracleCalls := c.oracleCalls
  bitOperations := c.bitOperations

def programStartConfig {s : ℕ} (c : MachineConfig 2 (s + 5)) : MachineConfig 2 s where
  registers := c.registers
  control := 0
  output := c.output
  oracleCalls := c.oracleCalls
  bitOperations := c.bitOperations


