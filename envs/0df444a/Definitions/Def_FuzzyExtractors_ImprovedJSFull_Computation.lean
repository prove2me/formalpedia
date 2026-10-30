-- Prove2me | Definitions.Def_FuzzyExtractors_ImprovedJSFull_Computation
-- name    : FuzzyExtractors_ImprovedJSFull_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:33:56.302284+00:00
-- url     : https://prove2.me/theorems/d33223b9-7107-4109-bdb3-b73453e661f0
-- title:
--   Finite binary programs, fair coins, output laws and expected stopping time
-- statement:
--   A program is a finite instruction list operating on three Mathlib binary tapes, with a separate blank symbol. Read, write, move, fair-bit branch and halt instructions cost one transition. Invalid labels loop. Input starts on tape zero, output is read from tape one at halting, and tape two is scratch. Output ends at the first blank to the right of the final output head. The trace determines the step count.
--
--   Independent uniform bit prefixes determine exact first-halting probabilities. The output law is the sum of those masses over all first-halting times; it is a subprobability law until almost-sure termination is established. A realization requires total output mass one and every positive-mass output to satisfy the stated relation.
--
--   $$\mathbb E[T]=\sum_{j\ge0}\Pr[T>j].$$
--
--   Stopping time is infinite on a divergent run. Expected time is this nonnegative extended tail sum, so a positive probability of divergence has infinite cost. No real-valued integral can default to zero. Syntactically deterministic programs contain no fair-bit instruction.
--
--   This operational layer supplies the expected-time meaning of Definition 3. It contains no assumed field arithmetic, decoder, root finder, cost bound or correctness certificate.
-- source:
--   Dodis, Ostrovsky, Reyzin and Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4 (1 Apr 2008), https://arxiv.org/abs/cs/0602007v4, Definition 3, printed p.11 / PDF p.12; Construction 5 and Theorem 6.1, printed pp.21–22 / PDF pp.22–23; concrete machine representation is an encoding convention

import Mathlib
import Mathlib.Computability.TuringMachine.Tape

namespace FuzzyExtractors.ImprovedJSFull

/-! Finite binary programs and exact fair-coin execution. Definition 3,
arXiv:cs/0602007v4, printed p.11 / PDF 12. The Mathlib tape operations
are local operations, not arithmetic or decoding oracles. -/

abbrev Bits := List Bool

/-- Each instruction performs one local tape action or one fair-bit branch.
Labels outside the finite program loop forever. Tape 0 initially holds input;
tape 1 is output; tape 2 is scratch. Blank is distinct from both bits. -/
inductive Instruction where
  | read (tape : Fin 3) (blank onZero one : ℕ)
  | write (tape : Fin 3) (symbol : Option Bool) (next : ℕ)
  | move (tape : Fin 3) (direction : Turing.Dir) (next : ℕ)
  | coin (onZero one : ℕ)
  | halt

abbrev Program := List Instruction

structure Configuration where
  pc : Option ℕ
  tapes : Fin 3 → Turing.Tape (Option Bool)

/-- No input encoding, arithmetic, or parsing is performed for free here. -/
def initial (input : Bits) : Configuration :=
  ⟨some 0, fun i => Turing.Tape.mk₁ (if i = 0 then input.map some else [])⟩

/-- A fresh bit is supplied each step, and only the coin instruction uses it. -/
def step (P : Program) (bit : Bool) (c : Configuration) : Configuration :=
  match c.pc with
  | none => c
  | some q =>
    match P[q]? with
    | none => c
    | some .halt => { c with pc := none }
    | some (.coin onZero one) => { c with pc := some (if bit then one else onZero) }
    | some (.read i blank onZero one) =>
      { c with pc := some (match (c.tapes i).head with
        | none => blank | some false => onZero | some true => one) }
    | some (.write i symbol next) =>
      ⟨some next, Function.update c.tapes i ((c.tapes i).write symbol)⟩
    | some (.move i dir next) =>
      ⟨some next, Function.update c.tapes i ((c.tapes i).move dir)⟩

/-- Trace index is the number of actual instructions executed. -/
def run (P : Program) (input : Bits) (coins : ℕ → Bool) : ℕ → Configuration
  | 0 => initial input
  | n + 1 => step P (coins n) (run P input coins n)

/-- The output head must point to the start of the output at halting.
At most t+1 cells to its right can have been visited in t steps on a blank
output tape. Output ends at the first blank. -/
def readOutput (c : Configuration) (t : ℕ) : Bits :=
  ((List.ofFn fun i : Fin (t + 1) => (c.tapes 1).right₀.nth i.val).takeWhile
    Option.isSome).filterMap id

/-- Nontermination has stopping time infinity, never a default zero. -/
noncomputable def stoppingTime (P : Program) (input : Bits) (coins : ℕ → Bool) : ℕ∞ := by
  classical
  exact if h : ∃ t, (run P input coins t).pc = none then (Nat.find h : ℕ∞) else ⊤

def firstHalt (P : Program) (input : Bits) (coins : ℕ → Bool) (t : ℕ) : Prop :=
  (run P input coins t).pc = none ∧ ∀ j < t, (run P input coins j).pc ≠ none

/-- Independent uniform length-t bit prefixes. Unused fair bits do not change
an execution; padding after time t cannot influence the first t steps. -/
def extendCoins {t : ℕ} (v : Fin t → Bool) : ℕ → Bool :=
  fun j => if h : j < t then v ⟨j, h⟩ else false

noncomputable def haltMass (P : Program) (input : Bits) (t : ℕ) (out : Bits) : ENNReal := by
  classical
  exact ((PMF.uniformOfFintype (Fin t → Bool)).map fun v =>
    decide (firstHalt P input (extendCoins v) t ∧
      readOutput (run P input (extendCoins v) t) t = out)) true

/-- Subprobability output law: divergent histories contribute no output. -/
noncomputable def outputMass (P : Program) (input out : Bits) : ENNReal :=
  ∑' t, haltMass P input t out

noncomputable def survivalMass (P : Program) (input : Bits) (t : ℕ) : ENNReal := by
  classical
  exact ((PMF.uniformOfFintype (Fin t → Bool)).map fun v =>
    decide ((run P input (extendCoins v) t).pc ≠ none)) true

/-- Tail-sum expectation of the actual stopping time. In particular a positive
probability of nontermination makes this infinity. No Bochner integral or
integrability-dependent real default is used. -/
noncomputable def expectedSteps (P : Program) (input : Bits) : ENNReal :=
  ∑' t : ℕ, survivalMass P input t

def AlmostSureHalts (P : Program) (input : Bits) : Prop :=
  ∑' out : Bits, outputMass P input out = 1

/-- Every terminating observation obeys R, and termination has total mass one. -/
def Realizes (P : Program) (input : Bits) (R : Bits → Prop) : Prop :=
  AlmostSureHalts P input ∧ ∀ out, outputMass P input out ≠ 0 → R out

/-- A syntactically deterministic program, with no fair-bit instructions. -/
def Deterministic (P : Program) : Prop :=
  ∀ i ∈ P, match i with | .coin _ _ => False | _ => True

end FuzzyExtractors.ImprovedJSFull


