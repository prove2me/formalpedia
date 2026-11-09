-- Prove2me | Definitions.Def_EditMulticoloring_Code_Machine
-- name    : EditMulticoloring_Code_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T18:48:45.702894+00:00
-- url     : https://prove2.me/theorems/c3fb0e30-3fe2-40f3-ac84-b9e72bfc4e60
-- title:
--   Finite deterministic RAM programs and accumulated bit costs
-- statement:
--   A program is a finite list of instructions for natural-number registers and random-access working memory. Its instructions load literals, copy, perform integer arithmetic and comparisons, access working memory, branch, inspect the next input symbol, emit a symbol, or halt with acceptance or rejection. There are no instructions carrying arbitrary functions, precomputed code tables, or field or prime oracles.
--
--   Each transition adds the bit lengths of the addresses and data it uses. Addition, subtraction, comparison and exclusive-or have linear bit charges; multiplication, division and remainder use schoolbook product-of-bit-length charges. Fetch, initialization, input inspection and output writing are charged. Working memory starts at zero, register zero contains $n$, and the input is already available as a read-only tape. Symbols $a$ are read as $a+1$, reserving zero for the end marker. Emitted output symbols use their ordinary alphabet labels.
--
--   $$\operatorname{SoftBound}(C,a,d,n)=C n^a(1+\log n)^d.$$
--
--   A bounded execution means that some finite number of deterministic transitions reaches the specified halt result and accumulated cost at most the bound. It does not accept a running-time function or an assumed correctness certificate. Public setup must be executed from the initial state on each first-operation bound.
-- source:
--   Huiling Xie, Zitan Chen, Explicit Edit Codes via Multicoloring, STOC 2027 submission #819 (October 2026), Appendix D preamble and D.1–D.3, printed pp. 17–21 (PDF pp. 18–22); pinned repository artifact papers/stoc2027-819/source.pdf, SHA256 00172d5da76bf6bc886b8a1f87450befb76480107f54cb367988a065737eb376.

import Definitions.Def_EditMulticoloring_Code_Words

namespace EditMulticoloring.Code
namespace RAM

/-- Positive bit length, also charging the representation of zero. -/
def bits (a : ℕ) : ℕ := a.log2 + 1

inductive Arithmetic where
  | add | sub | mul | div | mod | xor | lt
  deriving DecidableEq

/-- A finite instruction language: no oracle calls, field operations or code tables are primitives. -/
inductive Instruction where
  | literal (dst value : ℕ)
  | copy (dst src : ℕ)
  | arithmetic (op : Arithmetic) (dst left right : ℕ)
  | load (dst addressReg : ℕ)
  | store (addressReg src : ℕ)
  | read (dst : ℕ)
  | emit (src : ℕ)
  | jump (pc : ℕ)
  | jumpZero (src pc : ℕ)
  | accept
  | reject
  deriving DecidableEq

abbrev Program := List Instruction

structure State where
  pc : ℕ
  registers : ℕ → ℕ
  memory : ℕ → ℕ
  cursor : ℕ
  output : List ℕ
  status : Option Bool
  cost : ℕ

def initial (n : ℕ) : State :=
  ⟨0, fun r => if r = 0 then n else 0, fun _ => 0, 0, [], none, bits n⟩

def arithmeticValue : Arithmetic → ℕ → ℕ → ℕ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .xor, a, b => Nat.xor a b
  | .lt, a, b => if a < b then 1 else 0

def arithmeticCost (op : Arithmetic) (a b : ℕ) : ℕ :=
  match op with
  | .mul | .div | .mod => (bits a + 1) * (bits b + 1)
  | _ => bits a + bits b + 1

/-- Source tape is already available, with symbol a encoded as a+1 and EOF as zero.
A read inspects exactly one position; it never computes the input length or copies the input. -/
def inputAt {q : ℕ} (input : Word q) (i : ℕ) : ℕ :=
  ((input[i]?).map (fun a => a.val + 1)).getD 0

def setReg (s : State) (r v : ℕ) : ℕ → ℕ :=
  fun i => if i = r then v else s.registers i

def step {q : ℕ} (P : Program) (input : Word q) (s : State) : State :=
  if s.status.isSome then s else
  let fetchCost := bits s.pc + 1
  let base := { s with pc := s.pc + 1, cost := s.cost + fetchCost }
  match P[s.pc]? with
  | none => { base with status := some false }
  | some (.literal d a) =>
      { base with registers := setReg s d a, cost := base.cost + bits d + bits a }
  | some (.copy d a) =>
      { base with registers := setReg s d (s.registers a), cost := base.cost + bits d + bits a + bits (s.registers a) }
  | some (.arithmetic op d a b) =>
      { base with registers := setReg s d (arithmeticValue op (s.registers a) (s.registers b)), cost := base.cost + bits d + bits a + bits b + arithmeticCost op (s.registers a) (s.registers b) }
  | some (.load d a) =>
      let address := s.registers a
      let v := s.memory address
      { base with registers := setReg s d v, cost := base.cost + bits d + bits a + bits address + bits v }
  | some (.store a r) =>
      let address := s.registers a
      let v := s.registers r
      { base with memory := fun i => if i = address then v else s.memory i, cost := base.cost + bits a + bits r + bits address + bits v }
  | some (.read d) =>
      let v := inputAt input s.cursor
      { base with registers := setReg s d v, cursor := s.cursor + 1, cost := base.cost + bits d + bits s.cursor + bits v }
  | some (.emit a) =>
      let v := s.registers a
      { base with output := s.output ++ [v], cost := base.cost + bits a + bits s.output.length + bits v }
  | some (.jump pc) => { base with pc := pc, cost := base.cost + bits pc }
  | some (.jumpZero a pc) =>
      { base with pc := if s.registers a = 0 then pc else s.pc + 1, cost := base.cost + bits a + bits pc + bits (s.registers a) }
  | some .accept => { base with status := some true }
  | some .reject => { base with status := some false }

/-- Fuel counts transitions; the separately accumulated bit cost is fixed by step. -/
def run {q : ℕ} (P : Program) (input : Word q) : ℕ → State → State
  | 0, s => s
  | fuel + 1, s => run P input fuel (step P input s)

/-- Finite deterministic halting execution, including initialization, input and output work.
No caller supplies a running-time function or correctness certificate. -/
def Executes {q : ℕ} (P : Program) (n : ℕ) (input : Word q)
    (result : Option (List ℕ)) (bound : ℝ) : Prop :=
  ∃ fuel : ℕ, let s := run P input fuel (initial n)
    (match result with
      | none => s.status = some false
      | some z => s.status = some true ∧ s.output = z) ∧ (s.cost : ℝ) ≤ bound

end RAM

noncomputable def softBound (C : ℝ) (a d n : ℕ) : ℝ :=
  C * (n : ℝ) ^ a * (1 + Real.log (n : ℝ)) ^ d

end EditMulticoloring.Code


