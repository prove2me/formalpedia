-- Prove2me | Definitions.Def_ProportionalTSP_Exact_RAM
-- name    : ProportionalTSP_Exact_RAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:45.188725+00:00
-- url     : https://prove2.me/theorems/fda91777-5915-404d-8227-389e9b33c5c5
-- title:
--   Finite addition-and-comparison RAM and rational bit-cost evaluator
-- statement:
--   A program is a finite list of instructions on natural and scalar registers. Natural instructions perform constants, addition, truncated subtraction, halving, indirect access, input reads, branching, and output. Scalar instructions perform zero, addition, copying, input reads, comparison, and output. There is no scalar-to-natural conversion or scalar multiplication, subtraction, division, or other scalar function.
--
--   The same step evaluator is interpreted over $\mathbb R$ and $\mathbb Q$. Out-of-range input cells return zero; a program counter outside the program is stuck and is not a successful halt. The bit-cost evaluator charges every executed instruction by a cubic polynomial in its accessed operand and address lengths, with numerator/denominator lengths for rational registers and the whole input length for an input read:
--   $$T_{\rm bit}(P,I,t)=\sum_{i<t}(1+|P|+\operatorname{bits}(pc_i)+\operatorname{operandBits}(I,s_i))^3.$$
--   This is an explicit operand-size bit-cost RAM convention covering binary rational arithmetic, normalization, comparison and binary-trie memory access. It is not a unit-cost rational model. The evaluator and bit-cost definition contain no TSP correctness or claimed bound.
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), exact arithmetic convention and signed-sum implementation, PDF p. 2, 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Mathlib

namespace ProportionalTSP.Exact.RAM

/-- Finite uniform programs. Real data have only copying, addition and comparison instructions.
Natural registers hold combinatorial data, never a conversion from a real register. -/
inductive Instruction where
  | nconst (d value : ℕ)
  | nadd (d a b : ℕ)
  | nsub (d a b : ℕ)
  | nhalf (d a : ℕ)
  | nload (d address : ℕ)
  | nstore (address a : ℕ)
  | nread (d address : ℕ)
  | rzero (d : ℕ)
  | radd (d a b : ℕ)
  | rload (d address : ℕ)
  | rstore (address a : ℕ)
  | rread (d address : ℕ)
  | nle (a b target : ℕ)
  | rle (a b target : ℕ)
  | jump (target : ℕ)
  | emit (a : ℕ)
  | emitR (a : ℕ)
  | halt
  deriving DecidableEq

abbrev Program := List Instruction

structure Input (K : Type) where
  naturals : List ℕ
  values : List K

structure Config (K : Type) where
  pc : ℕ := 0
  nat : ℕ → ℕ := fun _ => 0
  reg : ℕ → K
  out : List ℕ := []
  realOut : List K := []

def initial {K : Type} [Zero K] : Config K := ⟨0, fun _ => 0, fun _ => 0, [], []⟩

def step {K : Type} [Zero K] [Add K] [LE K] [DecidableLE K]
    (P : Program) (I : Input K) (s : Config K) : Config K :=
  let next := {s with pc := s.pc + 1}
  match P[s.pc]? with
  | none => s
  | some .halt => s
  | some (.nconst d x) => {next with nat := Function.update s.nat d x}
  | some (.nadd d a b) => {next with nat := Function.update s.nat d (s.nat a + s.nat b)}
  | some (.nsub d a b) => {next with nat := Function.update s.nat d (s.nat a - s.nat b)}
  | some (.nhalf d a) => {next with nat := Function.update s.nat d (s.nat a / 2)}
  | some (.nload d a) => {next with nat := Function.update s.nat d (s.nat (s.nat a))}
  | some (.nstore a b) => {next with nat := Function.update s.nat (s.nat a) (s.nat b)}
  | some (.nread d a) => {next with nat := Function.update s.nat d (I.naturals.getD (s.nat a) 0)}
  | some (.rzero d) => {next with reg := Function.update s.reg d 0}
  | some (.radd d a b) => {next with reg := Function.update s.reg d (s.reg a + s.reg b)}
  | some (.rload d a) => {next with reg := Function.update s.reg d (s.reg (s.nat a))}
  | some (.rstore a b) => {next with reg := Function.update s.reg (s.nat a) (s.reg b)}
  | some (.rread d a) => {next with reg := Function.update s.reg d (I.values.getD (s.nat a) 0)}
  | some (.nle a b t) => if s.nat a ≤ s.nat b then {next with pc := t} else next
  | some (.rle a b t) => if s.reg a ≤ s.reg b then {next with pc := t} else next
  | some (.jump t) => {next with pc := t}
  | some (.emit a) => {next with out := s.nat a :: s.out}
  | some (.emitR a) => {next with realOut := s.reg a :: s.realOut}

def run {K : Type} [Zero K] [Add K] [LE K] [DecidableLE K]
    (P : Program) (I : Input K) (t : ℕ) : Config K := (step P I)^[t] initial

def Halts {K : Type} [Zero K] [Add K] [LE K] [DecidableLE K]
    (P : Program) (I : Input K) (t : ℕ) : Prop := P[(run P I t).pc]? = some .halt

/-- Canonical binary numerator/positive denominator length (including sign and delimiters). -/
def ratBits (x : ℚ) : ℕ := 2 + x.num.natAbs.size + x.den.size

def inputBits (I : Input ℚ) : ℕ :=
  1 + (I.naturals.map (fun x => 1 + x.size)).sum + (I.values.map ratBits).sum

/-- Sizes of all natural and rational operands accessed by a single instruction. Indirect
addresses and target addresses are included. Input reads are charged the whole input length.
The cubic charge covers binary addition, cross multiplication for rational comparison,
normalization, and binary-trie memory access; it is a bit-cost RAM, not unit-cost rationals. -/
def operandBits (I : Input ℚ) (s : Config ℚ) : Instruction → ℕ
  | .nconst d x => d.size + x.size
  | .nadd d a b | .nsub d a b => d.size + a.size + b.size + (s.nat a).size + (s.nat b).size
  | .nhalf d a => d.size + a.size + (s.nat a).size
  | .nload d a => d.size + a.size + (s.nat a).size + (s.nat (s.nat a)).size
  | .nstore a b => a.size + b.size + (s.nat a).size + (s.nat b).size
  | .nread d a => d.size + a.size + (s.nat a).size + inputBits I
  | .rzero d => d.size
  | .radd d a b => d.size + a.size + b.size + ratBits (s.reg a) + ratBits (s.reg b)
  | .rload d a => d.size + a.size + (s.nat a).size + ratBits (s.reg (s.nat a))
  | .rstore a b => a.size + b.size + (s.nat a).size + ratBits (s.reg b)
  | .rread d a => d.size + a.size + (s.nat a).size + inputBits I
  | .nle a b t => a.size + b.size + t.size + (s.nat a).size + (s.nat b).size
  | .rle a b t => a.size + b.size + t.size + ratBits (s.reg a) + ratBits (s.reg b)
  | .jump t => t.size
  | .emit a => a.size + (s.nat a).size
  | .emitR a => a.size + ratBits (s.reg a)
  | .halt => 0

def stepBitCost (P : Program) (I : Input ℚ) (s : Config ℚ) : ℕ :=
  match P[s.pc]? with
  | none => 1
  | some ins => (1 + P.length + s.pc.size + operandBits I s ins) ^ 3

def bitTime (P : Program) (I : Input ℚ) (t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range t, stepBitCost P I (run P I i)

end ProportionalTSP.Exact.RAM


