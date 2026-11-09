-- Prove2me | Definitions.Def_FourBlockIP_FPT_Machine
-- name    : FourBlockIP_FPT_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:52.247597+00:00
-- url     : https://prove2.me/theorems/15d99d92-1bc4-479b-a5d1-507d4a71ce9f
-- title:
--   Arithmetic RAM with unit-cost vector comparisons
-- statement:
--   A program is a finite list of restricted integer and real register instructions. Integer registers support constants, copying, arithmetic, Euclidean quotient and remainder, comparison branches, and indirect reads and writes. Real registers support rational constants, copying, arithmetic, comparison branches, indirect reads and writes, integer casts and floor. Indirect real memory is needed to access real inputs of variable length in Lemmas 6–7. Negative indirect addresses denote register zero. Division by zero returns zero; integer remainder modulo zero returns the dividend.
--
--   A comparison instruction reads two integer-memory blocks, whose addresses and common length are held in integer registers, and writes only a comparison bit. It charges one unit, independently of block length. Preparing the blocks uses ordinary charged instructions. There is no objective-value instruction. Every active instruction costs one; states on halt or outside the program remain fixed with no further charge. An integer input list is stored with its length in register zero and its entries starting at register one. Real input starts at real register zero. Output is the integer block starting at register one with length given by integer register zero.
--
--   This implements the arithmetic-operation/query convention of p. 3 under reading R2, including rounding for the arbitrary real framework data. It makes no bit-size claim. The execution interpreter is defined from the instruction list, not from a solver specification.
-- source:
--   Martin Koutecký, Alexandra Lassota, Koen Ligthart, 4-Block Integer Programming is in FPT, STOC 2027 submission #392 (October 2026), p. 3, running-time convention; p. 7, Lemma 6 real data; p. 10, unit-cost rounding convention (reading R2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/392.pdf

import Mathlib

namespace FourBlockIP.FPT

/-- Restricted two-sorted arithmetic RAM (p. 3, time convention; reading R2).
Integer literals and rational real literals are the only program constants.
All active instructions cost one; halted states are fixed. Real indirect memory
access is included, since the framework has variable-length exact real input. -/
inductive Instr where
  | const (d : ℕ) (v : ℤ)
  | copy (d a : ℕ)
  | add (d a b : ℕ) | sub (d a b : ℕ) | mul (d a b : ℕ)
  | div (d a b : ℕ) | mod (d a b : ℕ)
  | jle (a b target : ℕ)
  | load (d a : ℕ) | store (a s : ℕ)
  | rconst (d : ℕ) (v : ℚ)
  | rcopy (d a : ℕ)
  | radd (d a b : ℕ) | rsub (d a b : ℕ)
  | rmul (d a b : ℕ) | rdiv (d a b : ℕ)
  | rjle (a b target : ℕ)
  | rload (d a : ℕ) | rstore (a s : ℕ)
  | cast (d a : ℕ) | floor (d a : ℕ)
  /-- a,b,len name integer registers holding two base addresses and the length. -/
  | cmp (d a b len : ℕ)
  | halt
  deriving DecidableEq

abbrev Program := List Instr
abbrev ComparisonOracle := List ℤ → List ℤ → Bool

def noOracle : ComparisonOracle := fun _ _ => false

structure State where
  pc : ℕ
  reg : ℕ → ℤ
  realReg : ℕ → ℝ
  cost : ℕ

def readBlock (reg : ℕ → ℤ) (base len : ℕ) : List ℤ :=
  (List.range len).map (fun j => reg (base + j))

def initState (input : List ℤ) (realInput : List ℝ) : State where
  pc := 0
  reg := fun j => if j = 0 then input.length else input.getD (j - 1) 0
  realReg := fun j => realInput.getD j 0
  cost := 0

def halted (P : Program) (s : State) : Bool :=
  match P[s.pc]? with
  | none | some .halt => true
  | _ => false

def State.writeInt (s : State) (d : ℕ) (v : ℤ) : State :=
  { s with reg := Function.update s.reg d v, pc := s.pc + 1, cost := s.cost + 1 }

noncomputable def State.writeReal (s : State) (d : ℕ) (v : ℝ) : State :=
  { s with realReg := Function.update s.realReg d v, pc := s.pc + 1, cost := s.cost + 1 }

/-- Negative indirect addresses denote register zero. Integer division and remainder
are Euclidean, including a/0=0 and a%0=a; real division by zero is zero.
Only cmp calls the oracle: it receives two lists and returns one comparison bit.
The instruction writes only its destination, leaving the query cells unchanged
unless the program itself aliases its destination with a query cell. -/
noncomputable def step (P : Program) (O : ComparisonOracle) (s : State) : State := by
  classical
  exact match P[s.pc]? with
  | none | some .halt => s
  | some (.const d v) => s.writeInt d v
  | some (.copy d a) => s.writeInt d (s.reg a)
  | some (.add d a b) => s.writeInt d (s.reg a + s.reg b)
  | some (.sub d a b) => s.writeInt d (s.reg a - s.reg b)
  | some (.mul d a b) => s.writeInt d (s.reg a * s.reg b)
  | some (.div d a b) => s.writeInt d (s.reg a / s.reg b)
  | some (.mod d a b) => s.writeInt d (s.reg a % s.reg b)
  | some (.jle a b t) =>
      { s with pc := if s.reg a ≤ s.reg b then t else s.pc + 1, cost := s.cost + 1 }
  | some (.load d a) => s.writeInt d (s.reg (s.reg a).toNat)
  | some (.store a v) => s.writeInt (s.reg a).toNat (s.reg v)
  | some (.rconst d v) => s.writeReal d (v : ℝ)
  | some (.rcopy d a) => s.writeReal d (s.realReg a)
  | some (.radd d a b) => s.writeReal d (s.realReg a + s.realReg b)
  | some (.rsub d a b) => s.writeReal d (s.realReg a - s.realReg b)
  | some (.rmul d a b) => s.writeReal d (s.realReg a * s.realReg b)
  | some (.rdiv d a b) => s.writeReal d (s.realReg a / s.realReg b)
  | some (.rjle a b t) =>
      { s with pc := if s.realReg a ≤ s.realReg b then t else s.pc + 1, cost := s.cost + 1 }
  | some (.rload d a) => s.writeReal d (s.realReg (s.reg a).toNat)
  | some (.rstore a v) => s.writeReal (s.reg a).toNat (s.realReg v)
  | some (.cast d a) => s.writeReal d (s.reg a : ℝ)
  | some (.floor d a) => s.writeInt d ⌊s.realReg a⌋
  | some (.cmp d a b len) =>
      s.writeInt d (if O (readBlock s.reg (s.reg a).toNat (s.reg len).toNat)
        (readBlock s.reg (s.reg b).toNat (s.reg len).toNat) then 1 else 0)

noncomputable def run (P : Program) (O : ComparisonOracle)
    (input : List ℤ) (realInput : List ℝ) : ℕ → State
  | 0 => initState input realInput
  | t + 1 => step P O (run P O input realInput t)

def output (s : State) : List ℤ := readBlock s.reg 1 (s.reg 0).toNat

noncomputable def RunBounded (P : Program) (O : ComparisonOracle)
    (input : List ℤ) (realInput : List ℝ) (B : ℕ) : Prop :=
  ∃ t, halted P (run P O input realInput t) = true ∧
    (run P O input realInput t).cost ≤ B

end FourBlockIP.FPT


