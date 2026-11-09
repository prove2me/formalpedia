-- Prove2me | Definitions.Def_DetPermanentApprox_Main_Computation
-- name    : DetPermanentApprox_Main_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:22.900901+00:00
-- url     : https://prove2.me/theorems/a47ac843-d16d-4f24-bb59-7edbd098506c
-- title:
--   Guarded arithmetic programs and rational execution traces
-- statement:
--   A program is a finite list of the published real pointer-machine instructions. Its literals must be rational. Runs start with zero registers and pointers and the given input in memory. The output is memory cell $-1$ at a halted state. A valid run reaches the accepting instruction and has a nonzero divisor at every executed division. There are no permanent, matching, logarithm, exponential, floor, or optimization instructions.
--
--   For rational input, a trace bound requires every real register and memory cell at every time through termination to equal a rational with bounded reduced numerator-plus-denominator binary length. Integer pointer values and the program counter are also bounded. Matrix inputs consist of the dimension followed by the row-major entry table. These are execution predicates independent of any approximation guarantee or assigned cost.
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), §1.1, p. 2 (PDF p. 2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

namespace DetPermanentApprox.Main

/-! Exact arithmetic computation, §1.1, p.2 of STOC 2027 submission #704.
The published pointer machine supplies finite syntax and operational semantics.
This interface restricts literals to rationals, forbids division by zero along a run,
and reads a numerical output from memory cell -1. There are no elementary-function
or counting instructions. No correctness or complexity claim is part of a program. -/

abbrev Program := SmaleNinth.RAMProgram
abbrev Configuration := SmaleNinth.RAMConfig

def RationalProgram (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .const _ c => ∃ q : ℚ, c = (q : ℝ)
    | _ => True

noncomputable def run (P : Program) (input : List ℝ) (k : ℕ) : Configuration :=
  SmaleNinth.RAMRun P (fun a => if 0 ≤ a then input.getD a.toNat 0 else 0) k

def halted (P : Program) (c : Configuration) : Prop :=
  P[c.pc]? = some .accept

def legalDivision (P : Program) (c : Configuration) : Prop :=
  ∀ d a b, P[c.pc]? = some (.div d a b) → c.regs b ≠ 0

def validRun (P : Program) (input : List ℝ) (T : ℕ) : Prop :=
  halted P (run P input T) ∧ ∀ k < T, legalDivision P (run P input k)

noncomputable def output (P : Program) (input : List ℝ) (T : ℕ) : ℝ :=
  (run P input T).mem (-1)

def rationalLength (q : ℚ) : ℕ := max 1 q.num.natAbs.size + max 1 q.den.size

def inputLength (input : List ℚ) : ℕ :=
  input.length + (input.map rationalLength).sum

/-- All real registers and memory cells in the same real execution have rational
representatives of bounded reduced numerator/denominator length. The finite control
and integer pointers are bounded too; this rules out uncharged large integer data. -/
def traceBound (P : Program) (input : List ℚ) (T B : ℕ) : Prop :=
  ∀ k ≤ T,
    (∀ r, ∃ q : ℚ, (run P (input.map (fun q => (q : ℝ))) k).regs r = (q : ℝ) ∧
      rationalLength q ≤ B) ∧
    (∀ a, ∃ q : ℚ, (run P (input.map (fun q => (q : ℝ))) k).mem a = (q : ℝ) ∧
      rationalLength q ≤ B) ∧
    (∀ p, ((run P (input.map (fun q => (q : ℝ))) k).ptrs p).natAbs.size ≤ B) ∧
    (run P (input.map (fun q => (q : ℝ))) k).pc.size ≤ B

def matrixInput {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : List ℝ :=
  (n : ℝ) :: (List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => A i j).flatten

def rationalMatrixInput {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : List ℚ :=
  (n : ℚ) :: (List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => A i j).flatten

end DetPermanentApprox.Main


