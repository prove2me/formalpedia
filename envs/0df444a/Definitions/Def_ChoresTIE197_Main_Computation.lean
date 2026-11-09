-- Prove2me | Definitions.Def_ChoresTIE197_Main_Computation
-- name    : ChoresTIE197_Main_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T02:15:36.01997+00:00
-- url     : https://prove2.me/theorems/fa05306a-bfe2-4971-8ca5-e452fc39ee74
-- title:
--   Uniform binary computation and exact fair-bit sampling
-- statement:
--   The input explicitly encodes $n,m,k$ and every rational singleton cost using self-delimiting binary numerators and denominators. Deterministic partition algorithms use the published finite-stack bit-machine and polynomial-time interface. A streaming fair-bit Post machine provides the expected-time extension needed for exact rejection sampling; each transition writes one tape symbol, moves one square, and changes a finite control state. There is no unit-cost arithmetic oracle.
--
--   For a randomized run, first-halting masses count finite independent fair-bit words and carry weight $2^{-t}$. Summing these masses must give one; the tail sum of actual nontermination probabilities is its expected number of charged steps. One program and one polynomial precede every dimension and rational table. The output word must encode precisely the real-semantic allocation, with exactly the same probability. Mechanism 3 additionally has a bound on every tape.
--
--   These predicates concern implementation on rational input only. Every fairness and incentive statement separately quantifies over all nonnegative real rows.
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), computational clauses, pp.12,23,35–37, printed p.12, PDF p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Setting
import Definitions.Def_HypergraphUnreliability_FPRAS_Machine

open Finset Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

/-- Self delimiting little endian binary natural numbers. -/
def binaryNat (n : ℕ) : List Bool := HypergraphUnreliability.FPRAS.natCode n

def binaryRat (q : ℚ) : List Bool :=
  [decide (q < 0)] ++ binaryNat q.num.natAbs ++ binaryNat q.den

def inputCode (n m k : ℕ) (q : Fin n → Fin m → ℚ) : List Bool :=
  binaryNat n ++ binaryNat m ++ binaryNat k ++
    ((List.finRange n).flatMap (fun i => (List.finRange m).flatMap (fun e => binaryRat (q i e))))

def allocationCode {n m : ℕ} (A : Allocation n m) : List Bool :=
  (List.finRange m).flatMap (fun e => binaryNat (A e).val)

def subsetCode {m : ℕ} (S : Finset (Fin m)) : List Bool :=
  (List.finRange m).map (fun e => decide (e ∈ S))

def rationalProfile {n m : ℕ} (q : Fin n → Fin m → ℚ) : Profile n m :=
  fun i e => Real.toNNReal (q i e : ℝ)

/-- A finite fair-bit Post machine. Tape alphabet: blank, binary 0, binary 1.
Every transition writes one symbol, moves one square, and changes finite control.
There is no arithmetic oracle, free input-dependent state, or assumed runtime. -/
structure BitProgram where
  states : ℕ
  code : Fin (states+1) → Fin 3 → Bool → Option (Fin 3 × Bool × Fin (states+1))

structure BitConfig (p : BitProgram) where
  state : Fin (p.states+1)
  tape : ℤ → Fin 3
  head : ℤ
  halted : Bool

def bitInit (p : BitProgram) (input : List Bool) : BitConfig p :=
  ⟨0, (fun z => if z < 0 then 0 else
    match input[z.toNat]? with | none => 0 | some false => 1 | some true => 2), 0, false⟩

def bitStep (p : BitProgram) (s : BitConfig p) (bit : Bool) : BitConfig p :=
  if s.halted then s else
    match p.code s.state (s.tape s.head) bit with
    | none => {s with halted := true}
    | some (sym,dir,next) =>
      ⟨next, Function.update s.tape s.head sym, s.head + (if dir then 1 else -1), false⟩

def bitRun (p : BitProgram) (input bits : List Bool) : BitConfig p :=
  bits.foldl (bitStep p) (bitInit p input)

def bitOutput (p : BitProgram) (input bits : List Bool) : List Bool :=
  let s := bitRun p input bits
  (((List.range (input.length + bits.length + 1)).map (fun j => s.tape (j:ℤ))).takeWhile
    (fun a => a != 0)).map (fun a => a == 2)

def bitWords (t : ℕ) : Finset (List Bool) :=
  univ.image (fun b : Fin t → Bool => (List.finRange t).map b)

/-- Exact probability of first halting after t+1 charged steps, with output w. -/
def firstHaltMass (p : BitProgram) (input w : List Bool) (t : ℕ) : ℝ≥0∞ :=
  ((bitWords (t+1)).filter (fun bits =>
    (bitRun p input bits).halted = true ∧
    (bitRun p input (bits.take t)).halted = false ∧ bitOutput p input bits = w)).card *
      (2:ℝ≥0∞)⁻¹ ^ (t+1)

def haltMass (p : BitProgram) (input : List Bool) (t : ℕ) : ℝ≥0∞ :=
  ((bitWords (t+1)).filter (fun bits =>
    (bitRun p input bits).halted = true ∧
    (bitRun p input (bits.take t)).halted = false)).card * (2:ℝ≥0∞)⁻¹ ^ (t+1)

/-- Tail sum of the actual halting time, not an assigned cost annotation. -/
def expectedSteps (p : BitProgram) (input : List Bool) : ℝ≥0∞ :=
  ∑' t, ((bitWords t).filter (fun bits => (bitRun p input bits).halted = false)).card *
    (2:ℝ≥0∞)⁻¹ ^ t

def Deterministic (p : BitProgram) : Prop :=
  ∀ q a, p.code q a false = p.code q a true

/-- One machine and one polynomial, uniform in the table dimensions and reports.
The decoded outcome probabilities agree with the real-semantic procedure exactly. -/
def PolySampler (D : (n m k : ℕ) → Profile n m → Prop)
    (F : (n m k : ℕ) → Profile n m → Allocation n m → ℝ≥0∞) : Prop :=
  ∃ p : BitProgram, ∃ C d : ℕ, 0 < C ∧
    ∀ n m k (q : Fin n → Fin m → ℚ), (∀ i e, 0 ≤ q i e) → D n m k (rationalProfile q) →
      let input := inputCode n m k q
      (∑' t, haltMass p input t) = 1 ∧
      expectedSteps p input ≤ (C * (input.length+1)^d : ℕ) ∧
      ∀ A, (∑' t, firstHaltMass p input (allocationCode A) t) = F n m k (rationalProfile q) A

/-- Bounded time is retained for Mechanism 3 (one final fair coin).
This additionally bounds every random tape, unlike the rejection samplers. -/
def PolyBoundedSampler (D : (n m k : ℕ) → Profile n m → Prop)
    (F : (n m k : ℕ) → Profile n m → Allocation n m → ℝ≥0∞) : Prop :=
  ∃ p : BitProgram, ∃ C d : ℕ, 0 < C ∧
    ∀ n m k (q : Fin n → Fin m → ℚ), (∀ i e, 0 ≤ q i e) → D n m k (rationalProfile q) →
      let input := inputCode n m k q
      let B := C * (input.length+1)^d
      (∀ bits ∈ bitWords B, (bitRun p input bits).halted = true) ∧
      ∀ A, (∑' t, firstHaltMass p input (allocationCode A) t) = F n m k (rationalProfile q) A

/-- Deterministic algorithms for subsets use the published finite-stack bit-machine interface.
The size/deviation side conditions are the source domains, not correctness assumptions. -/
def PolyPartition (D : (m : ℕ) → Profile 2 m → Prop)
    (f : (m : ℕ) → Profile 2 m → Finset (Fin m)) : Prop :=
  HypergraphUnreliability.FPRAS.PolyComputesIn
    (fun z : (Σ m : ℕ, Fin 2 → Fin m → ℚ) =>
      (∀ i e, 0 ≤ z.2 i e) ∧ D z.1 (rationalProfile z.2))
    (fun z => inputCode 2 z.1 0 z.2)
    (fun z => subsetCode (f z.1 (rationalProfile z.2)))
    (fun z => (inputCode 2 z.1 0 z.2).length)

end ChoresTIE197.Main


