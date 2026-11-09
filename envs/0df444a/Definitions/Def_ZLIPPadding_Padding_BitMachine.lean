-- Prove2me | Definitions.Def_ZLIPPadding_Padding_BitMachine
-- name    : ZLIPPadding_Padding_BitMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:45.599308+00:00
-- url     : https://prove2.me/theorems/76ecdb94-7db6-4250-ba00-89fdce165ec8
-- title:
--   Finite bit-stack oracle programs and execution traces
-- statement:
--   A program is a finite list of instructions acting on bit stacks. Instructions push a constant bit, pop and branch on an empty stack or a bit, draw one fresh fair bit, query an oracle with a decoded Gram matrix, or halt with an output stack. All labels and register indices are constants in the code. There are no arbitrary function instructions.
--
--   Execution is a probability law on traces. Each internal step is charged its finite code lookup cost; query decoding is charged a cubic upper bound in message length and reading an oracle response is charged its binary length. Traces count
--   $$\text{internal bit cost},\quad\text{random bits},\quad\text{peak stored bits},\quad\text{oracle requests}.$$
--   Two bit stacks can simulate an ordinary tape, so this is a uniform executable bit model. A fuel cutoff is explicit, and complexity conclusions must prove all branches halt before it; a timeout cannot be treated as ordinary successful execution. Oracle kernels receive only the decoded dimension and $H$.
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed pp. 7, 28–32 (PDF pp. 8, 29–33), bit-complexity conventions, §§7.1–7.7

import Definitions.Def_ZLIPPadding_Padding_Binary
import Definitions.Def_ZLIPPadding_Padding_Laws

namespace ZLIPPadding.Padding
/-- Finite bit-stack code. `pop` branches on empty, zero, one and removes the head.
All indices and labels are constants in the finite code. -/
inductive Instruction where
  | push (reg : ℕ) (bit : Bool) (next : ℕ)
  | pop (reg onEmpty onZero onOne : ℕ)
  | coin (reg next : ℕ)
  | query (src dst next : ℕ)
  | halt (reg : ℕ)
  deriving DecidableEq

abbrev Program := List Instruction

structure Configuration where
  pc : ℕ := 0
  tapes : ℕ → Bits
  running : Bool := true
  output : Bits := []
  ticks : ℕ := 0
  bitCost : ℕ := 0
  randomBits : ℕ := 0
  cells : ℕ := 0
  peakCells : ℕ := 0
  requests : List (Σ n : ℕ, ZMat n) := []

def initial (input : Bits) : Configuration where
  tapes := fun i => if i = 0 then input else []
  cells := input.length
  peakCells := input.length

def store (c : Configuration) (r : ℕ) (w : Bits) : Configuration :=
  let cells := c.cells - (c.tapes r).length + w.length
  { c with tapes := Function.update c.tapes r w, cells := cells, peakCells := max c.peakCells cells }

noncomputable section
/-- Every draw is fresh. The query kernel receives only a decoded H, never machine state. -/
def step (P : Program) (A : Oracle) (c : Configuration) : PMF Configuration :=
  if !c.running then PMF.pure c else
    let c := { c with ticks := c.ticks + 1, bitCost := c.bitCost + P.length + 1 }
    match (P[c.pc]? : Option Instruction) with
    | none => PMF.pure { c with running := false, output := [] }
    | some (Instruction.halt r) => PMF.pure { c with running := false, output := c.tapes r }
    | some (Instruction.push r b j) => PMF.pure { store c r (b :: c.tapes r) with pc := j }
    | some (Instruction.pop r e z o) =>
        match c.tapes r with
        | [] => PMF.pure { c with pc := e }
        | b :: w => PMF.pure { store c r w with pc := if b then o else z }
    | some (Instruction.coin r j) =>
        (PMF.bernoulli (1/2) (by norm_num)).map fun b =>
          { store c r (b :: c.tapes r) with pc := j, randomBits := c.randomBits + 1 }
    | some (Instruction.query src dst j) =>
        let w := c.tapes src
        match decGram w with
        | none => PMF.pure { store c dst [] with pc := j, bitCost := c.bitCost + (w.length + 1)^3 }
        | some H => (A H.1 H.2).map fun q =>
            let v := encVec q
            { store c dst v with pc := j, requests := H :: c.requests, bitCost := c.bitCost + (w.length + 1)^3 + v.length }

/-- Fuel counts machine steps. Theorems must separately rule out timeouts and bound bitCost. -/
def executeFrom (P : Program) (A : Oracle) : ℕ → Configuration → PMF Configuration
  | 0, c => PMF.pure c
  | t+1, c => (step P A c).bind (executeFrom P A t)

def execute (P : Program) (A : Oracle) (fuel : ℕ) (input : Bits) : PMF Configuration :=
  executeFrom P A fuel (initial input)

def noOracle : Oracle := fun _ _ => PMF.pure 0

def NoQueries (P : Program) : Prop :=
  ∀ src dst next, Instruction.query src dst next ∉ P

def NoCoins (P : Program) : Prop := ∀ r j, Instruction.coin r j ∉ P

/-- Structural bit complexity, not assumed algebraic-operation unit costs. -/
def TraceBound (B : ℕ) (c : Configuration) : Prop :=
  c.running = false ∧ c.bitCost + c.randomBits + c.peakCells ≤ B

def decodedRun {α : Type} (D : Bits → Option α) (P : Program) (A : Oracle)
    (fuel : ℕ) (input : Bits) : PMF (Option α) :=
  (execute P A fuel input).map fun c => if c.running then none else D c.output

end
end ZLIPPadding.Padding


