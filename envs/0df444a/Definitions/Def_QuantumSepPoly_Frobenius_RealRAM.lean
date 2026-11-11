-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_RealRAM
-- name    : QuantumSepPoly_Frobenius_RealRAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:26.367913+00:00
-- url     : https://prove2.me/theorems/b0379fc8-de77-406d-91f0-51c379dbd58d
-- title:
--   Finite exact-arithmetic RAM programs and random tapes
-- statement:
--   A program is a finite instruction list using rational constants, scalar arithmetic, square roots, comparisons, jumps, natural counters, indexed reads and writes for both real and natural-number memory, real Gaussian draws, and finite uniform draws. Initial real register zero holds accuracy; natural register zero holds dimension. Other real inputs are explicitly loaded. Independent product tapes carry the specified Gaussian and uniform laws.
--   $$\operatorname{cost}(s_{t+1})\ge\operatorname{cost}(s_t)+1$$
--   for each nonhalting instruction, with extra charges for indexed access, loading, natural constants, and the index bit length of finite draws. Runtime means a halting execution whose accumulated cost satisfies its bound. First-halting output is computed from execution; nontermination has the initial-state default. There is no instruction for separability, an optimizer, an arbitrary function, or a desired answer. Division and square root are total real operations; mathematical singular cases must be handled in algorithms.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), §§2–5, p. 8 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Mathlib

noncomputable section

namespace QuantumSepPoly.Frobenius

/-- A finite scalar RAM instruction set. Addresses are held in natural registers.
No mathematical functions, oracles, or arbitrary real constants are instructions. -/
inductive RAMInstruction where
  | rational (dst : ℕ) (value : ℚ)
  | copy (dst src : ℕ)
  | add (dst a b : ℕ)
  | sub (dst a b : ℕ)
  | mul (dst a b : ℕ)
  | div (dst a b : ℕ)
  | sqrt (dst src : ℕ)
  | load (dst address : ℕ)
  | store (address src : ℕ)
  | natConst (dst value : ℕ)
  | natSucc (dst src : ℕ)
  | natPred (dst src : ℕ)
  | natLoad (dst address : ℕ)
  | natStore (address src : ℕ)
  | natToReal (dst src : ℕ)
  | jump (target : ℕ)
  | branchLE (a b yes no : ℕ)
  | branchNatZero (src yes no : ℕ)
  | gaussian (dst : ℕ)
  | uniform (dst bound : ℕ)
  | halt
  deriving Inhabited

abbrev RAMProgram := List RAMInstruction
abbrev RandomTape := (ℕ → ℝ) × ((ℕ × ℕ) → ℕ)

/-- Independent N(0,1) draws and independent uniform draws for each positive bound.
The n-th family supplies uniform choices from {0,...,n}; it is not an oracle. -/
def tapeLaw : MeasureTheory.Measure RandomTape :=
  (MeasureTheory.Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.gaussianReal 0 1)).prod
    (MeasureTheory.Measure.infinitePi (fun i : ℕ × ℕ =>
      (PMF.uniformOfFintype (Fin (i.2 + 1))).toMeasure.map (fun j => j.val)))

structure RAMState where
  pc : ℕ
  real : ℕ → ℝ
  nat : ℕ → ℕ
  randomIndex : ℕ
  cost : ℕ
  stopped : Bool

/-- Input loading is charged. r[0] is accuracy, r[1..] the scalar input;
n[0] is dimension, other natural registers initially zero. -/
def ramInitial (accuracy : ℝ) (dimension : ℕ) (input : List ℝ) : RAMState where
  pc := 0
  real := fun a => if a = 0 then accuracy else input[a-1]?.getD 0
  nat := fun a => if a = 0 then dimension else 0
  randomIndex := 0
  cost := input.length + 1
  stopped := false

/-- Division by zero and square roots of negatives use Lean's total real operations.
Algorithms must branch explicitly if those cases carry mathematical meaning. -/
def ramStep (P : RAMProgram) (tape : RandomTape) (s : RAMState) : RAMState := by
  classical
  let next := {s with pc := s.pc + 1, cost := s.cost + 1}
  let put := fun (dst : ℕ) (v : ℝ) => {next with real := Function.update s.real dst v}
  let putN := fun (dst v : ℕ) => {next with nat := Function.update s.nat dst v}
  exact if s.stopped then s else
    match P[s.pc]?.getD .halt with
    | .rational dst v => put dst v
    | .copy dst src => put dst (s.real src)
    | .add dst a b => put dst (s.real a + s.real b)
    | .sub dst a b => put dst (s.real a - s.real b)
    | .mul dst a b => put dst (s.real a * s.real b)
    | .div dst a b => put dst (s.real a / s.real b)
    | .sqrt dst src => put dst (Real.sqrt (s.real src))
    | .load dst a => { (put dst (s.real (s.nat a))) with cost := s.cost + 2 }
    | .store a src => { (put (s.nat a) (s.real src)) with cost := s.cost + 2 }
    | .natConst dst v => { (putN dst v) with cost := s.cost + v.log2 + 1 }
    | .natSucc dst src => putN dst (s.nat src + 1)
    | .natPred dst src => putN dst (s.nat src - 1)
    | .natLoad dst a => { (putN dst (s.nat (s.nat a))) with cost := s.cost + 2 }
    | .natStore a src => { (putN (s.nat a) (s.nat src)) with cost := s.cost + 2 }
    | .natToReal dst src => put dst (s.nat src : ℝ)
    | .jump target => {next with pc := target}
    | .branchLE a b yes no => {next with pc := if s.real a ≤ s.real b then yes else no}
    | .branchNatZero src yes no => {next with pc := if s.nat src = 0 then yes else no}
    | .gaussian dst => {(put dst (tape.1 s.randomIndex)) with randomIndex := s.randomIndex + 1}
    | .uniform dst bound =>
        let n := s.nat bound
        {(putN dst (if n = 0 then 0 else tape.2 (s.randomIndex, n-1))) with
          randomIndex := s.randomIndex + 1, cost := s.cost + n.log2 + 1}
    | .halt => {next with stopped := true}

/-- A finite trace; cost is accumulated by instructions, including memory and draws. -/
def ramRun (P : RAMProgram) (tape : RandomTape) (initial : RAMState) (steps : ℕ) : RAMState :=
  (ramStep P tape)^[steps] initial

/-- Halting by an actual charged-operation bound. -/
def RAMTerminates (P : RAMProgram) (initial : RAMState) (bound : ℝ) (tape : RandomTape) : Prop :=
  ∃ steps, (ramRun P tape initial steps).stopped = true ∧
    ((ramRun P tape initial steps).cost : ℝ) ≤ bound

/-- First halting state, with the initial state as the explicit nontermination default. -/
def ramResult (P : RAMProgram) (initial : RAMState) (tape : RandomTape) : RAMState := by
  classical
  exact if h : ∃ steps, (ramRun P tape initial steps).stopped = true then
    ramRun P tape initial (Nat.find h) else initial

end QuantumSepPoly.Frobenius


