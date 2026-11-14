-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_WordRAM
-- name    : KSATSingleFlip_Connect_WordRAM
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T07:53:38.783089+00:00
-- url     : https://prove2.me/theorems/ff1cc841-dd9e-4f0a-9ad9-a2c15c8bb7f7
-- title:
--   A fixed-width word-RAM for sparse k-SAT algorithms
-- statement:
--   This is an explicit candidate computation model for formalizing the time bounds of Theorem 1.3. A finite deterministic program runs on fixed-width unsigned words with unit-cost arithmetic, comparisons, branches, and indirect memory access; arithmetic wraps modulo $2^w$. Inputs serialize the sparse clauses, initial assignment and either a requested variable or target assignment. A successful output gives a length followed by variable indices, interpreted as a compact flip list starting from the supplied assignment. The width is chosen to represent the input dimensions, input address range, and step budget. The cited paper does not prescribe this specific machine model, and no claim is made here that its algorithms have been implemented or verified on it.
-- source:
--   Formalization choice motivated by Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, Theorem 1.3 (printed p. 4) and compact path representation (printed p. 32, PDF p. 34), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SparseFlip

namespace KSATSingleFlip.Connect

/-- A finite word-RAM instruction. Registers and addressed memory contain
unsigned words; arithmetic wraps modulo 2^w. Each instruction costs one step. -/
inductive WordRAMInstruction where
  | halt
  | constant (dst value : ℕ)
  | copy (dst src : ℕ)
  | add (dst left right : ℕ)
  | sub (dst left right : ℕ)
  | mul (dst left right : ℕ)
  | div (dst left right : ℕ)
  | less (dst left right : ℕ)
  | load (dst addressReg : ℕ)
  | store (addressReg sourceReg : ℕ)
  | jump (target : ℕ)
  | jumpZero (testReg target : ℕ)
  deriving DecidableEq

/-- An ordered finite instruction sequence. -/
abbrev WordRAMProgram := List WordRAMInstruction

/-- Infinite address space is a total map, but only addresses below 2^w can be
addressed by an instruction. Halted states are absorbing. -/
structure WordRAMState where
  pc : ℕ
  registers : ℕ → ℕ
  memory : ℕ → ℕ
  halted : Bool

/-- Read one unsigned w-bit word from a register. -/
def WordRAMState.read (s : WordRAMState) (w r : ℕ) : ℕ := s.registers r % (2^w)

/-- Write a register and advance to the next instruction. -/
def WordRAMState.writeNext (s : WordRAMState) (w dst value : ℕ) : WordRAMState :=
  { s with pc := s.pc + 1, registers := Function.update s.registers dst (value % (2^w)) }

/-- One deterministic unit-cost transition of a fixed-width word RAM.
Reading beyond the program halts. All operands and addresses are w-bit words. -/
def wordRAMStep (program : WordRAMProgram) (w : ℕ) (s : WordRAMState) : WordRAMState :=
  if s.halted then s else
    match program[s.pc]? with
    | none => { s with halted := true }
    | some .halt => { s with halted := true }
    | some (.constant d v) => s.writeNext w d v
    | some (.copy d a) => s.writeNext w d (s.read w a)
    | some (.add d a b) => s.writeNext w d (s.read w a + s.read w b)
    | some (.sub d a b) => s.writeNext w d (s.read w a + 2^w - s.read w b)
    | some (.mul d a b) => s.writeNext w d (s.read w a * s.read w b)
    | some (.div d a b) => s.writeNext w d (s.read w a / s.read w b)
    | some (.less d a b) => s.writeNext w d (if s.read w a < s.read w b then 1 else 0)
    | some (.load d a) => s.writeNext w d (s.memory (s.read w a))
    | some (.store a b) =>
        { s with pc := s.pc + 1, memory := Function.update s.memory (s.read w a) (s.read w b) }
    | some (.jump target) => { s with pc := target }
    | some (.jumpZero a target) => { s with pc := if s.read w a = 0 then target else s.pc + 1 }

/-- Execute at most T unit-cost steps; a halted state remains unchanged. -/
def wordRAMRun (program : WordRAMProgram) (w : ℕ) : ℕ → WordRAMState → WordRAMState
  | 0, s => s
  | T + 1, s => wordRAMRun program w T (wordRAMStep program w s)

/-- Input memory is initialized by a list of words, and every other cell and
register is zero. The caller must choose w large enough for input words. -/
def wordRAMStart (input : List ℕ) : WordRAMState :=
  { pc := 0, registers := fun _ => 0, memory := fun i => input[i]?.getD 0, halted := false }

/-- Sparse formula, initial solution and requested variable as words. Clause
records are k variable indices followed by k signs, preserving clause order. -/
def sparseFlipInput {n k m : ℕ} (F : SparseFormula n k m)
    (x : Fin n → Bool) (v : Fin n) : List ℕ :=
  [n, k, m] ++
    (List.ofFn fun j : Fin m =>
      (List.ofFn fun i : Fin k => ((F j).index i).val) ++
      (List.ofFn fun i : Fin k => ((F j).sign i).toNat)).flatten ++
    List.ofFn (fun i : Fin n => (x i).toNat) ++ [v.val]

/-- Choose a width large enough to address the serialized input and a
T-step computation, and to represent the instance dimensions. -/
def wordRAMWidth (n k m T : ℕ) : ℕ :=
  Nat.log2 (n + k + m + sparseFlipInputWords n k m + T + 2) + 1

/-- Success is encoded by memory word 0 = 1, followed by a length in word 1
and flip indices in words 2,... . The address-range guard prevents wraparound;
an invalid status, non-halting run, invalid index or oversized output fails. -/
def wordRAMDecodeFlips (n w : ℕ) (s : WordRAMState) : Option (List (Fin n)) :=
  if s.halted ∧ s.memory 0 = 1 ∧ s.memory 1 + 2 ≤ 2^w then
    (List.range (s.memory 1)).mapM fun i =>
      if h : s.memory (i + 2) < n then some ⟨s.memory (i + 2), h⟩ else none
  else none

/-- Run a deterministic program on the sparse input for T steps, then decode
a compact path starting at the supplied initial assignment. -/
def wordRAMFlipResult {n k m : ℕ} (program : WordRAMProgram) (T : ℕ)
    (F : SparseFormula n k m) (x : Fin n → Bool) (v : Fin n) : Option (FlipListPath n) :=
  let w := wordRAMWidth n k m T
  let s := wordRAMRun program w T (wordRAMStart (sparseFlipInput F x v))
  (wordRAMDecodeFlips n w s).map fun flips => ⟨x, flips⟩

/-- Sparse formula, start and target assignments as words for local routing. -/
def sparseRouteInput {n k m : ℕ} (F : SparseFormula n k m)
    (x y : Fin n → Bool) : List ℕ :=
  [n, k, m] ++
    (List.ofFn fun j : Fin m =>
      (List.ofFn fun i : Fin k => ((F j).index i).val) ++
      (List.ofFn fun i : Fin k => ((F j).sign i).toNat)).flatten ++
    List.ofFn (fun i : Fin n => (x i).toNat) ++
    List.ofFn (fun i : Fin n => (y i).toNat)

/-- Number of words in the local-routing input. -/
def sparseRouteInputWords (n k m : ℕ) : ℕ := 3 + 2 * k * m + 2 * n

/-- Width sufficient for local-routing input and a T-step computation. -/
def wordRAMRouteWidth (n k m T : ℕ) : ℕ :=
  Nat.log2 (n + k + m + sparseRouteInputWords n k m + T + 2) + 1

/-- Run a deterministic local-routing program and decode its compact flip list. -/
def wordRAMRouteResult {n k m : ℕ} (program : WordRAMProgram) (T : ℕ)
    (F : SparseFormula n k m) (x y : Fin n → Bool) : Option (FlipListPath n) :=
  let w := wordRAMRouteWidth n k m T
  let s := wordRAMRun program w T (wordRAMStart (sparseRouteInput F x y))
  (wordRAMDecodeFlips n w s).map fun flips => ⟨x, flips⟩

end KSATSingleFlip.Connect


