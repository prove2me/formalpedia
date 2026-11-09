-- Prove2me | Definitions.Def_MaoLowDegree_Counterexample_bitRAM
-- name    : MaoLowDegree_Counterexample_bitRAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:03.214616+00:00
-- url     : https://prove2.me/theorems/0b846016-d39f-4266-b90b-45bb7b5f70cd
-- title:
--   Finite bit-RAM programs, execution, fair streams, and exact stopping-time laws
-- statement:
--   A program is a finite list of instructions and a fixed word-width factor $q$. Address and counter registers have $q(\lfloor\log_2(n+2)\rfloor+1)$ bits; data memory holds individual bits. The finite instruction set has bounded counter arithmetic, Boolean operations, direct register access, addressed bit loads and stores, input/advice bit access, one fair-coin read, output of one bit, branches, and halt. It has no algebraic rank, real arithmetic, or arbitrary-function instruction.
--
--   Each executed instruction costs one transition. Registers and memory start at zero; a halted state is absorbing. Graph input is unary $n$, a delimiter, then the lexicographic edge array. The sampler receives unary $n$ and a separate advice tape. Invalid fetch halts, and reading past an input tape returns false.
--
--   Let $\tau$ be the first halting time, with $\tau=\infty$ on nontermination. The definitions use disjoint first-halting cylinders for each exact output and the tail sum
--   $$\mathbb E\tau=\sum_{t\ge0}\Pr(\tau>t).$$
--
--   At time $t$ probabilities average over all $t$ independent fair bits; no conditioning on bounded-time success is used. This is the bit-RAM reading of the source's unnamed field-operation model, justified by Algorithm 1, the strict exponent slack on p.14, and the random-access/full-scan distinction on p.15. It is not a linear-time Turing-machine claim.
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), Theorem 1.2, p.5; Algorithm 1, p.12; runtime and sampling, pp.14–15; computation-model reading

import Definitions.Def_MaoLowDegree_Counterexample_graphModel

open Classical
open scoped ENNReal
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- A finite bit-RAM instruction alphabet. Only address counters use word arithmetic
(copy, addition, subtraction, increment and decrement); data memory holds single bits. No multiplication, rank,
real-number, graph, polynomial, or arbitrary-function instruction is present. -/
inductive BitInstr where
  | constant (dst value : ℕ)
  | copy (dst src : ℕ)
  | add (dst src₁ src₂ : ℕ)
  | sub (dst src₁ src₂ : ℕ)
  | inc (dst : ℕ)
  | dec (dst : ℕ)
  | band (dst src₁ src₂ : ℕ)
  | bxor (dst src₁ src₂ : ℕ)
  | load (dst address : ℕ)
  | store (address src : ℕ)
  | input (dst address : ℕ)
  | advice (dst address : ℕ)
  | coin (dst : ℕ)
  | emit (src : ℕ)
  | jump (label : ℕ)
  | zeroJump (src label : ℕ)
  | halt
  deriving DecidableEq

/-- Fixed code and fixed word-width factor, independent of n and the random coins. -/
structure BitProgram where
  code : List BitInstr
  wordFactor : ℕ

/-- Address/counter words have q·(⌊log₂(n+2)⌋+1) bits; q is fixed with the program.
The bit-RAM uses unit-cost addressing and bounded-address bookkeeping. -/
def addressModulus (A : BitProgram) (n : ℕ) : ℕ :=
  2 ^ (A.wordFactor * (Nat.log2 (n + 2) + 1))

structure BitState where
  pc : ℕ := 0
  reg : ℕ → ℕ := fun _ => 0
  mem : ℕ → Bool := fun _ => false
  output : List Bool := []
  halted : Bool := false

/-- One actual instruction, including halt, costs one step. Invalid fetch halts.
Input/advice are read-only bit arrays; accessing beyond their end returns false. -/
def bitStep (A : BitProgram) (n : ℕ) (input advice : List Bool) (coin : Bool)
    (s : BitState) : BitState := Id.run do
  if s.halted then return s
  let B := addressModulus A n
  let put := fun (dst value : ℕ) =>
    { s with pc := s.pc + 1, reg := Function.update s.reg dst (value % B) }
  let bit := fun (src : ℕ) => s.reg src % 2 == 1
  match A.code.getD s.pc .halt with
  | .constant dst value => return put dst value
  | .copy dst src => return put dst (s.reg src)
  | .add dst u v => return put dst (s.reg u + s.reg v)
  | .sub dst u v => return put dst (s.reg u + B - s.reg v)
  | .inc dst => return put dst (s.reg dst + 1)
  | .dec dst => return put dst ((s.reg dst + B - 1) % B)
  | .band dst u v => return put dst (if bit u && bit v then 1 else 0)
  | .bxor dst u v => return put dst (if xor (bit u) (bit v) then 1 else 0)
  | .load dst addr => return put dst (if s.mem (s.reg addr) then 1 else 0)
  | .store addr src => return { s with pc := s.pc + 1, mem := Function.update s.mem (s.reg addr) (bit src) }
  | .input dst addr => return put dst (if input.getD (s.reg addr) false then 1 else 0)
  | .advice dst addr => return put dst (if advice.getD (s.reg addr) false then 1 else 0)
  | .coin dst => return put dst (if coin then 1 else 0)
  | .emit src => return { s with pc := s.pc + 1, output := s.output ++ [bit src] }
  | .jump label => return { s with pc := label }
  | .zeroJump src label => return { s with pc := if s.reg src = 0 then label else s.pc + 1 }
  | .halt => return { s with halted := true }

/-- The state after exactly t transitions; a halted state stays fixed. A fresh independent
coin is available at each step, used only by the coin instruction. -/
def runBits (A : BitProgram) (n : ℕ) (input advice : List Bool) (coins : ℕ → Bool) : ℕ → BitState
  | 0 => {}
  | t + 1 => bitStep A n input advice (coins t) (runBits A n input advice coins t)

/-- Finite prefixes of an infinite fair stream, extended arbitrarily after the used prefix. -/
def extendCoins {t : ℕ} (c : Fin t → Bool) (i : ℕ) : Bool :=
  if h : i < t then c ⟨i,h⟩ else false

def HasNoCoins (A : BitProgram) : Prop :=
  ∀ dst : ℕ, BitInstr.coin dst ∉ A.code

/-- Exact output mass: disjoint first-halting cylinders, with no bounded-time conditioning.
A nonhalting stream contributes to no output. -/
def outputMass (A : BitProgram) (n : ℕ) (input advice out : List Bool) : ℝ≥0∞ :=
  ∑' t : ℕ, probE (PMF.uniformOfFintype (Fin t → Bool)) (fun c =>
    let coins := extendCoins c
    let s := runBits A n input advice coins t
    s.halted = true ∧ s.output = out ∧
      (t = 0 ∨ (runBits A n input advice coins (t - 1)).halted = false))

/-- E[halting time] = Σ_t Pr[not halted by t], in extended nonnegative reals.
Infinite halting time is not replaced by zero. -/
def expectedSteps (A : BitProgram) (n : ℕ) (input advice : List Bool) : ℝ≥0∞ :=
  ∑' t : ℕ, probE (PMF.uniformOfFintype (Fin t → Bool)) (fun c =>
    (runBits A n input advice (extendCoins c) t).halted = false)

def HaltsWithin (A : BitProgram) (n : ℕ) (input advice : List Bool) (t : ℕ) : Prop :=
  ∀ coins : ℕ → Bool, (runBits A n input advice coins t).halted = true

/-- Output edge bits in lexicographic increasing-endpoint order. -/
def graphBits {n : ℕ} (Y : Graph n) : List Bool :=
  (List.finRange n).flatMap fun i => (List.finRange n).filterMap fun j =>
    if h : i < j then some (Y ⟨(i,j),h⟩) else none

/-- Unary n, a delimiter, then the edge array. Reading the whole input costs Θ(n²). -/
def graphInput {n : ℕ} (Y : Graph n) : List Bool := List.replicate n true ++ [false] ++ graphBits Y

def unaryInput (n : ℕ) : List Bool := List.replicate n true ++ [false]

end MaoLowDegree.Counterexample


