-- Prove2me | Definitions.Def_LogSupermodularBIS_Main_Supplement_BitMachine
-- name    : LogSupermodularBIS_Main_Supplement_BitMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:32:02.140572+00:00
-- url     : https://prove2.me/theorems/7a4c27d1-d7b6-47b5-9075-3e2c9fe8052a
-- title:
--   Finite binary-stack programs, rational encodings and charged fair-bit execution
-- statement:
--   A binary string stores bits with its head on the left. A natural number is encoded by its binary length in unary, a separator, and its little-endian binary digits. A rational is encoded by a sign and the canonical reduced numerator magnitude and positive denominator. Framing changes binary lengths by only a constant factor. The decoder rejects noncanonical strings and zero denominators.
--
--   A program consists of a finite instruction list and a fixed finite collection of binary stacks. Its instructions push a constant bit, pop and branch on empty/zero/one, push one fresh fair bit, jump, query the optional external evaluator, or halt. Stack zero initially contains the input and is the output stack. Only the coin instruction accesses the random tape. Each active instruction costs one bit operation, including a fair-bit read; evaluator queries also pay the evaluator's returned charge. Invalid instruction addresses remain active and continue consuming work. Halting is absorbing. Arithmetic on integers or rationals, comparisons of such numbers, and memory organization must be implemented with these bit instructions.
--
--   For cost bound $T$, the execution is observed after $\lfloor T\rfloor+1$ instructions. Termination means that on every infinite bit tape the program has explicitly halted, its charged cost is at most $T$, and its output meets the specified validity predicate. Observation fuel does not halt the program. Fair-bit probabilities are derived by uniformly averaging the outputs over prefixes of $\lfloor T\rfloor+1$ fair bits:
--   $$
--   \Pr[E]=2^{-k}\sum_{u\in\{0,1\}^k}\mathbf 1_E(\operatorname{output}(u)),\qquad k=\lfloor T\rfloor+1.
--   $$
--   Any observed run reads at most $k$ bits; unused bits leave the output unchanged. Cost, output and probabilities come from this execution semantics, with no correctness or runtime fields assumed in the program.
--
--   This is a reusable operational bit model. The paper-specific exact evaluator is instantiated separately, so ordinary graph algorithms have no external weight access.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 38 (PDF 39), Appendix A conventions; pp. 42–44 (PDF 43–45), Appendix A.3

import Mathlib

set_option autoImplicit false

namespace LogSupermodularBIS.Main.Supplement

/-- Binary strings; stack heads are at the left. -/
abbrev Bits := List Bool

/-- Little-endian binary value, allowing leading zeroes at the high end. -/
def bitsValue : Bits → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsValue bs

/-- A self-delimiting frame with linear overhead in the payload length. -/
def frame (bs : Bits) : Bits := List.replicate bs.length true ++ [false] ++ bs

/-- Canonical self-delimiting binary encoding of a natural number. -/
def encNat (n : ℕ) : Bits := frame n.bits

/-- Parse one framed natural, returning the unused suffix. -/
def readNat (bs : Bits) : Option (ℕ × Bits) :=
  let p := bs.span id
  match p.2 with
  | [] => none
  | _ :: rest =>
    if p.1.length ≤ rest.length then
      some (bitsValue (rest.take p.1.length), rest.drop p.1.length)
    else none

/-- Sign followed by framed numerator magnitude and positive denominator, in reduced form. -/
def encRat (q : ℚ) : Bits :=
  [decide (q.num < 0)] ++ encNat q.num.natAbs ++ encNat q.den

/-- Rational decoder: rejects zero denominators, noncanonical codes and trailing data. -/
def decRat (bs : Bits) : Option ℚ := do
  let sign ← bs.head?
  let (a, rest) ← readNat bs.tail
  let (b, unused) ← readNat rest
  if b = 0 ∨ unused ≠ [] then none else
    let z : ℤ := if sign then -(a : ℤ) else a
    let q : ℚ := (z : ℚ) / b
    if encRat q = bs then some q else none

/-- A finite instruction alphabet for a fixed finite number of binary store. No instruction
carries a function, an arithmetic operation on unbounded integers, or a real primitive. `pop`
branches on empty/false/true, deleting the inspected bit. `query` is the only oracle access. -/
inductive BitInstr (k : ℕ) where
  | push (stack : Fin k) (bit : Bool) (next : ℕ)
  | pop (stack : Fin k) (empty ifFalse ifTrue : ℕ)
  | coin (stack : Fin k) (next : ℕ)
  | jump (next : ℕ)
  | query (src dst : Fin k) (next : ℕ)
  | halt

/-- Finite syntax of a uniform multi-stack bit program; stack 0 is input and output. -/
structure BitProgram where
  extraStacks : ℕ
  code : List (BitInstr (extraStacks + 1))

/-- An optional external evaluator returning a binary answer and its bit cost. Its precise
instantiation for weights is defined separately; `none` provides no external information. -/
abbrev BitOracle := Option (Bits → Bits × ℕ)

/-- Operational configuration. `work` includes every fair bit read and every evaluator charge. -/
structure BitState (k : ℕ) where
  pc : ℕ
  store : Fin k → Bits
  cursor : ℕ
  work : ℕ
  halted : Bool

/-- Initial state: input on stack 0, other store empty, all counters zero. -/
def bitInit (P : BitProgram) (input : Bits) : BitState (P.extraStacks + 1) :=
  ⟨0, fun i => if i.val = 0 then input else [], 0, 0, false⟩

/-- One charged binary-stack step. Invalid instruction addresses keep running and consume work.
Only `coin` reads the random tape. A halted state is absorbing with no additional work. -/
def bitStep (P : BitProgram) (O : BitOracle) (ω : ℕ → Bool)
    (s : BitState (P.extraStacks + 1)) : BitState (P.extraStacks + 1) :=
  if s.halted then s else
    let t := { s with work := s.work + 1 }
    match P.code[s.pc]? with
    | none => t
    | some (.push i b next) =>
      { t with pc := next, store := Function.update s.store i (b :: s.store i) }
    | some (.pop i empty ifFalse ifTrue) =>
      match s.store i with
      | [] => { t with pc := empty }
      | b :: rest =>
        { t with
          pc := (if b then ifTrue else ifFalse)
          store := Function.update s.store i rest }
    | some (.coin i next) =>
      { t with pc := next, cursor := s.cursor + 1,
               store := Function.update s.store i (ω s.cursor :: s.store i) }
    | some (.jump next) => { t with pc := next }
    | some (.query src dst next) =>
      let ans := match O with
        | none => ([], 1)
        | some f => f (s.store src)
      { t with pc := next, work := t.work + ans.2,
               store := Function.update s.store dst ans.1 }
    | some .halt => { t with halted := true }

/-- Execute at most `fuel` instructions. This is observation fuel, not an extra instruction
available to the program. Only an explicit `halt` counts as termination. -/
def bitRun (P : BitProgram) (O : BitOracle) (input : Bits) (ω : ℕ → Bool)
    (fuel : ℕ) : BitState (P.extraStacks + 1) :=
  (bitStep P O ω)^[fuel] (bitInit P input)

/-- Enough observation steps for any computation whose charged cost is at most `T`. -/
noncomputable def observationFuel (T : ℝ) : ℕ := ⌊T⌋₊ + 1

/-- Observed execution, with elapsed cost and number of consumed random bits. -/
noncomputable def execution (P : BitProgram) (O : BitOracle) (input : Bits)
    (T : ℝ) (ω : ℕ → Bool) : BitState (P.extraStacks + 1) :=
  bitRun P O input ω (observationFuel T)

/-- Stack 0 of the observed execution. Validity specifications also require that it has halted. -/
noncomputable def bitOutput (P : BitProgram) (O : BitOracle) (input : Bits)
    (T : ℝ) (ω : ℕ → Bool) : Bits :=
  (execution P O input T ω).store 0

/-- Pathwise halting, charged cost and unconditional output validity on every infinite bit tape. -/
def BitTerminates (P : BitProgram) (O : BitOracle) (input : Bits) (T : ℝ)
    (valid : Bits → Prop) : Prop :=
  ∀ ω : ℕ → Bool,
    (execution P O input T ω).halted = true ∧
    ((execution P O input T ω).work : ℝ) ≤ T ∧ valid (bitOutput P O input T ω)

/-- Extend a finite fair tape by zeroes; any run observed for `k` steps reads at most `k` bits. -/
def extendCoins {k : ℕ} (u : Fin k → Bool) : ℕ → Bool :=
  fun j => if h : j < k then u ⟨j, h⟩ else false

open Classical in
/-- Fair-bit probability of an output event. The finite sum uses a uniform prefix of length
`observationFuel T`; unused bits are immaterial. There is no measure-map default or assumed law. -/
noncomputable def bitProbability (P : BitProgram) (O : BitOracle) (input : Bits)
    (T : ℝ) (event : Bits → Prop) : ℝ :=
  (∑ u : Fin (observationFuel T) → Bool,
    if event (bitOutput P O input T (extendCoins u)) then (1 : ℝ) else 0) /
      (2 : ℝ) ^ observationFuel T

/-- Probability mass of a particular output code, derived from finite execution. -/
noncomputable def bitMass (P : BitProgram) (O : BitOracle) (input : Bits)
    (T : ℝ) (bs : Bits) : ℝ := bitProbability P O input T (fun out => out = bs)

end LogSupermodularBIS.Main.Supplement


