-- Prove2me | Definitions.Def_FasterExactColoring_ThreeColor_Execution
-- name    : FasterExactColoring_ThreeColor_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:07:06.241355+00:00
-- url     : https://prove2.me/theorems/0f55b4c6-85cf-42b6-bd10-8f3a72fa1bf0
-- title:
--   Finite programs, charged executions and one-sided randomization
-- statement:
--   A program is a finite list of instructions of the published logarithmic-cost RAM, with an optional instruction that writes a fresh fair bit to a specified memory cell. The base instructions are constants, addition, truncated subtraction, halving, indirect loads and stores, conditional jumps and halting. No instruction solves a combinatorial problem or evaluates an arbitrary function.
--
--   Every execution produces both its final memory and its charged work. Step costs count the binary lengths of accessed addresses and values; input loading and output extraction are also charged. Cell $0$ initially stores the input-word count; input words start at address $16$. At termination cell $1$ stores the output length and output words begin at address $16$.
--
--   For input $x$, the polynomial envelope is
--   $$\operatorname{poly}_{C,d}(x)=C(\operatorname{inputCost}(x)+1)^d.$$
--   The predicate $\operatorname{runWithin}(A,x,B,Q)$ asserts an actual halted execution with total charged cost at most $B$ and an output satisfying $Q$. Decision outputs are the singleton words $[1]$ and $[0]$.
--
--   A one-sided Monte Carlo execution halts within the same worst-case bound for every coin tape, accepts only true instances, and accepts each true instance with probability at least $1/2$. The probability is counted exactly over all equally likely finite bit strings of a sufficiently large length. Independent constant repetition gives this threshold from the source's fixed positive success probability. This definition supplies semantics, not an assumed correct or fast solver. The log-cost model is a conventional encoding of the source's finite algorithms; polynomial operand costs are absorbed into $O^*$.
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Section 2, pp. 2–3 (PDF pp. 4–5), deterministic and one-sided Monte Carlo conventions

import Mathlib
import Definitions.Def_MinrankTW_RAM

namespace FasterExactColoring.ThreeColor

/-- A finite oracle-free program: the published log-cost RAM plus fair bits. -/
abbrev Program := List (Sum MinrankTW.Instr ℕ)

def coreProgram (A : Program) : List MinrankTW.Instr :=
  A.map (fun i => match i with | .inl j => j | .inr _ => .halt)

def deterministic (A : Program) : Prop := ∀ i ∈ A, ∃ j, i = Sum.inl j

def initialMemory (x : List ℕ) (a : ℕ) : ℕ :=
  if a = 0 then x.length else if 16 ≤ a then x.getD (a - 16) 0 else 0

def halted (A : Program) (c : MinrankTW.Config) : Prop :=
  A[c.pc]? = none ∨ A[c.pc]? = some (.inl .halt)

def step (A : Program) (bit : Bool) (c : MinrankTW.Config) : MinrankTW.Config :=
  match A[c.pc]? with
  | some (.inr a) => ⟨c.pc + 1, Function.update c.mem a bit.toNat⟩
  | _ => MinrankTW.step (coreProgram A) c

def stepCost (A : Program) (c : MinrankTW.Config) : ℕ :=
  match A[c.pc]? with
  | some (.inr a) => 2 + MinrankTW.logLen a
  | _ => MinrankTW.stepCost (coreProgram A) c

/-- State and charged work are generated together, with one fresh bit per step. -/
def execute (A : Program) (x : List ℕ) (bits : ℕ → Bool) : ℕ → MinrankTW.Config × ℕ
  | 0 => (⟨0, initialMemory x⟩, 0)
  | t + 1 => let prev := execute A x bits t
             (step A (bits t) prev.1, prev.2 + stepCost A prev.1)

def inputCost (x : List ℕ) : ℕ :=
  1 + MinrankTW.logLen x.length +
    ((List.range x.length).map (fun i =>
      1 + MinrankTW.logLen (16+i) + MinrankTW.logLen (x.getD i 0))).sum

/-- Output length in cell 1; output words in cells 16,17,... . -/
def output (c : MinrankTW.Config) : List ℕ :=
  (List.range (c.mem 1)).map (fun i => c.mem (16 + i))

def outputCost (c : MinrankTW.Config) : ℕ :=
  MinrankTW.logLen (c.mem 1) +
    ((List.range (c.mem 1)).map (fun i =>
      1 + MinrankTW.logLen (16 + i) + MinrankTW.logLen (c.mem (16 + i)))).sum

def runWithin (A : Program) (x : List ℕ) (B : ℝ) (Q : List ℕ → Prop) : Prop :=
  ∃ t, let e := execute A x (fun _ => false) t
       halted A e.1 ∧ (inputCost x + e.2 + outputCost e.1 : ℕ) ≤ B ∧ Q (output e.1)

def polynomial (C : ℝ) (d : ℕ) (x : List ℕ) : ℝ := C * (inputCost x + 1 : ℕ) ^ d

def answers (P : Prop) (y : List ℕ) : Prop :=
  (y = [1] ∧ P) ∨ (y = [0] ∧ ¬ P)

/-- Every coin tape halts within the same bound. Counting uniform T-bit tapes
is exact; step t uses bit t, whether or not the instruction is random. -/
noncomputable def monteCarlo (A : Program) (x : List ℕ) (B : ℝ) (P : Prop) : Prop :=
  ∃ T : ℕ,
    (∀ bits : Fin T → Bool, ∃ t ≤ T,
      let e := execute A x (fun i => if h : i < T then bits ⟨i,h⟩ else false) t
      halted A e.1 ∧ (inputCost x + e.2 + outputCost e.1 : ℕ) ≤ B ∧
        (output e.1 = [0] ∨ output e.1 = [1]) ∧ (output e.1 = [1] → P)) ∧
    (P → 2 * (Finset.univ.filter (fun bits : Fin T → Bool =>
      output (execute A x (fun i => if h : i < T then bits ⟨i,h⟩ else false) T).1 = [1])).card
      ≥ Fintype.card (Fin T → Bool))

end FasterExactColoring.ThreeColor


