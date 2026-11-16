-- Prove2me | Definitions.Def_GaussMixGated_ExactReal_Supplement_BitMachine
-- name    : GaussMixGated_ExactReal_Supplement_BitMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:07:34.803075+00:00
-- url     : https://prove2.me/theorems/a5b4874d-c953-48fa-8594-d15b9cfa6f56
-- title:
--   Finite-bit trainer with a charged quantized-observation instruction
-- statement:
--   The finite-bit trainer extends the published log-cost rational RAM by one instruction fetching a fresh quantized observation. A state contains the core rational registers, rational memory, input and output positions, fair-coin counter, bit-cost counter and halted flag, together with an input bit string and an observation counter. An observation instruction appends the self-delimiting encoding of one quantized vector to the input and costs one plus its encoding length. The number of observations is exactly the number of executed observation instructions.
--
--   Core instructions retain the published arithmetic, floor, gcd, indirect addressing, comparisons, binary input/output and fair-coin semantics and operand-length charges. Rational division by zero returns zero. A halted state stays fixed; an invalid program counter never halts. Runs begin from zero registers and memory with the specified binary input. The first halted state defines the output and costs, and halting is a separate predicate. The sampler uses the original RAM without the observation instruction. This extension gives operational sample and bit-cost counts without granting exact-real arithmetic or ideal Gaussian draws.
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, Appendix A computational model, PDF p. 23 (printed p. 21)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_BitRAM

open BlottoFPTAS.Main

noncomputable section

namespace GaussMixGated.ExactReal.Supplement

/-- Appendix A's trainer instruction set: the published rational bit RAM, plus a single
fresh-observation instruction. There are no real literals or elementary-function or Gaussian
instructions. The sampler uses `BitRAM.Program` itself and has no observation instruction. -/
inductive BitInstr where
  | core (op : BitRAM.Instr)
  | obs

abbrev BitProgram := List BitInstr

/-- The rational RAM state together with the binary input stream and the number of oracle
answers fetched. Each answer is appended to the stream in the self-delimiting rational code. -/
structure BitState where
  core : BitRAM.State
  input : List Bool
  observations : ℕ

/-- Initial trainer state. -/
def bitStart (input : List Bool) : BitState := ⟨BitRAM.initState, input, 0⟩

/-- One trainer step. `answers n` is the encoded quantized vector returned by oracle call n.
Fetching it costs one plus its entire encoded length; subsequent input reads are charged by
the core machine. Core jumps keep their absolute targets. An invalid pc never halts. -/
def bitStep (T : BitProgram) (answers : ℕ → List Bool) (coins : ℕ → Bool)
    (s : BitState) : BitState :=
  if s.core.halted then s else
    match T[s.core.pc]? with
    | none => { s with core := { s.core with cost := s.core.cost + 1 } }
    | some (.core op) =>
        { s with core := (BitRAM.step (List.replicate s.core.pc .halt ++ [op])
            s.input coins s.core) }
    | some .obs =>
        let a := answers s.observations
        { core := { s.core with pc := s.core.pc + 1, cost := s.core.cost + 1 + a.length },
          input := s.input ++ a, observations := s.observations + 1 }

/-- The state after n steps, with the input, answers and coins fixed. -/
def bitRun (T : BitProgram) (input : List Bool) (answers : ℕ → List Bool)
    (coins : ℕ → Bool) (n : ℕ) : BitState :=
  (bitStep T answers coins)^[n] (bitStart input)

/-- Actual halting, required before any final-state cost is used. -/
def BitHalts (T : BitProgram) (input : List Bool) (answers : ℕ → List Bool)
    (coins : ℕ → Bool) : Prop :=
  ∃ n, (bitRun T input answers coins n).core.halted = true

/-- First halted state, or the initial state on nontermination (the theorem excludes that case). -/
def bitFinal (T : BitProgram) (input : List Bool) (answers : ℕ → List Bool)
    (coins : ℕ → Bool) : BitState :=
  open Classical in
  if h : ∃ n, (bitRun T input answers coins n).core.halted = true then
    bitRun T input answers coins (Nat.find h)
  else bitStart input

end GaussMixGated.ExactReal.Supplement


