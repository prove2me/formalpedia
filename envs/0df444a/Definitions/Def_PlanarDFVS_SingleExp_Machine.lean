-- Prove2me | Definitions.Def_PlanarDFVS_SingleExp_Machine
-- name    : PlanarDFVS_SingleExp_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:23.515886+00:00
-- url     : https://prove2.me/theorems/b7f15a15-fb0c-472c-86d5-128449f77140
-- title:
--   §4–§5 — finite programs with charged work and live workspace
-- statement:
--   A program is a finite list of instructions. Its state has a program counter, finitely allocated natural registers and memory, finitely allocated real registers and memory, a random-bit cursor, a work counter and a distinct halted output flag. Instructions provide literals, copies, arithmetic, indirect loads/stores, comparison jumps, a fair-bit instruction and halt. Natural operations charge binary operand lengths using a schoolbook bound; allocation of a new memory interval is charged. Real arithmetic and comparisons have unit arithmetic cost and are used only for the real-weight subroutine. There is no optimization, graph, planarity or biased-sampling oracle.
--
--   Every executed instruction adds a positive work charge. A missing instruction never produces an answer. A halted state stutters. Live space counts allocated natural cells and their bit lengths, the program counter and random cursor lengths, and real cells in the arithmetic model. Binary programs exclude real operations; deterministic programs exclude random flips. Random bits are independent and fair. For a horizon $t$, semantic success probability counts the $2^t$ bit prefixes resulting in success and divides by $2^t$; enumeration of these prefixes is not an operation available to a program.
--
--   $$\operatorname{BoundedRun}(P,\omega,s,t,T,S)\iff\text{the run halts by }t,\quad\operatorname{work}(t)\le T,\quad\max_{j\le t}\operatorname{space}(j)\le S.$$
--
--   These definitions tie output, time, randomness and space to the same operational execution. No correctness or resource bound is stored in a program's type. The paper leaves the elementary computational model unspecified; this is the declared bit-cost/arithmetic-cost reading.
--   The binary interpreter is a separate executable definition; it never evaluates a real comparison or real arithmetic operation. The arithmetic interpreter is used only for arbitrary real-weight inputs. The source does not prescribe an instruction set, so this distinction is part of the declared computational-model reading.
-- source:
--   Daniel Lokshtanov, Saket Saurabh, Jie Xue, STOC 2027 submission #1569 (October 2026), pp. 7, 10–13 (PDF pp. 7, 10–13), Theorem 3.5, Theorem 4.2 and Theorem 5.2 (computational-model reading)

import Mathlib

namespace PlanarDFVS.SingleExp

/-- A finite instruction language, without graph, optimization or sampling oracles.
    Natural operations are bit charged. Real operations are used only by the real-weight
    subroutine. A rational-weight algorithm uses the natural fragment instead. -/
inductive Instruction where
  | literal (d v : ℕ)
  | copy (d s : ℕ)
  | add (d x y : ℕ)
  | sub (d x y : ℕ)
  | mul (d x y : ℕ)
  | div (d x y : ℕ)
  | load (d a : ℕ)
  | store (a s : ℕ)
  | leJump (x y target : ℕ)
  | jump (target : ℕ)
  | flip (d : ℕ)
  | realLiteral (d : ℕ) (q : ℚ)
  | realCopy (d s : ℕ)
  | realAdd (d x y : ℕ)
  | realSub (d x y : ℕ)
  | realMul (d x y : ℕ)
  | realDiv (d x y : ℕ)
  | realLoad (d a : ℕ)
  | realStore (a s : ℕ)
  | realLeJump (x y target : ℕ)
  | castReal (d s : ℕ)
  | halt (success : Bool)
  deriving DecidableEq

abbrev Program := List Instruction

/-- Finite memories; zero cells beyond the allocated list. All list lengths and
    all natural values count toward live workspace. -/
structure Configuration where
  pc : ℕ := 0
  registers : List ℕ := []
  memory : List ℕ := []
  realRegisters : List ℝ := []
  realMemory : List ℝ := []
  cursor : ℕ := 0
  work : ℕ := 0
  result : Option Bool := none

/-- A random-access store allocates its full address interval. -/
def put {α : Type} (zero : α) (xs : List α) (i : ℕ) (x : α) : List α :=
  (xs ++ List.replicate (i + 1 - xs.length) zero).set i x

def Configuration.reg (s : Configuration) (i : ℕ) : ℕ := s.registers.getD i 0

def Configuration.rreg (s : Configuration) (i : ℕ) : ℝ := s.realRegisters.getD i 0

def Configuration.write (s : Configuration) (d v : ℕ) : Configuration :=
  { s with registers := put 0 s.registers d v }

def Configuration.rwrite (s : Configuration) (d : ℕ) (v : ℝ) : Configuration :=
  { s with realRegisters := put 0 s.realRegisters d v }

/-- Schoolbook upper cost for an operation on two binary naturals. Address/operand
    lengths are charged also for load, store, comparison and jumps. -/
def binaryCharge (x y : ℕ) : ℕ := (1 + Nat.size x + Nat.size y)^2

def Configuration.space (s : Configuration) : ℕ :=
  1 + Nat.size s.pc + Nat.size s.cursor +
    (s.registers.map (fun x => 1 + Nat.size x)).sum +
    (s.memory.map (fun x => 1 + Nat.size x)).sum +
    s.realRegisters.length + s.realMemory.length

/-- Execute a single instruction. The continuation charges at least one step;
    no output can be obtained through a missing instruction. -/
noncomputable def execute (ω : ℕ → Bool) (s : Configuration) (i : Instruction) : Configuration :=
  let next (v : Configuration) (c : ℕ) : Configuration :=
    { v with pc := s.pc + 1, work := s.work + 1 + c }
  let r := s.reg
  let R := s.rreg
  match i with
  | .literal d v => next (s.write d v) (Nat.size d + Nat.size v)
  | .copy d x => next (s.write d (r x)) (binaryCharge d (r x))
  | .add d x y => next (s.write d (r x + r y)) (binaryCharge (r x) (r y))
  | .sub d x y => next (s.write d (r x - r y)) (binaryCharge (r x) (r y))
  | .mul d x y => next (s.write d (r x * r y)) (binaryCharge (r x) (r y))
  | .div d x y => next (s.write d (r x / r y)) (binaryCharge (r x) (r y))
  | .load d a => next (s.write d (s.memory.getD (r a) 0))
      (binaryCharge (r a) (s.memory.getD (r a) 0))
  | .store a x => next { s with memory := put 0 s.memory (r a) (r x) }
      (binaryCharge (r a) (r x) + (r a + 1 - s.memory.length))
  | .leJump x y t =>
      { next s (binaryCharge (r x) (r y) + Nat.size t) with pc := if r x ≤ r y then t else s.pc + 1 }
  | .jump t => { next s (Nat.size t) with pc := t }
  | .flip d => next { s.write d (if ω s.cursor then 1 else 0) with cursor := s.cursor + 1 }
      (Nat.size d + Nat.size s.cursor)
  | .realLiteral d q => next (s.rwrite d (q : ℝ)) (Nat.size d)
  | .realCopy d x => next (s.rwrite d (R x)) (binaryCharge d x)
  | .realAdd d x y => next (s.rwrite d (R x + R y)) 1
  | .realSub d x y => next (s.rwrite d (R x - R y)) 1
  | .realMul d x y => next (s.rwrite d (R x * R y)) 1
  | .realDiv d x y => next (s.rwrite d (R x / R y)) 1
  | .realLoad d a => next (s.rwrite d (s.realMemory.getD (r a) 0)) (Nat.size (r a))
  | .realStore a x => next { s with realMemory := put 0 s.realMemory (r a) (R x) }
      (Nat.size (r a) + (r a + 1 - s.realMemory.length))
  | .realLeJump x y t => { next s (Nat.size t) with pc := if R x ≤ R y then t else s.pc + 1 }
  | .castReal d x => next (s.rwrite d (r x : ℝ)) (Nat.size (r x))
  | .halt success => { next s 0 with result := some success }

noncomputable def step (P : Program) (ω : ℕ → Bool) (s : Configuration) : Configuration :=
  if s.result.isSome then s else
    match P[s.pc]? with
    | none => { s with work := s.work + 1 }
    | some i => execute ω s i

noncomputable def run (P : Program) (ω : ℕ → Bool) (s : Configuration) (t : ℕ) : Configuration :=
  (step P ω)^[t] s

/-- Executable interpreter of the binary fragment. Unsupported real instructions
    are stuck and charged; theorem guarantees exclude them. -/
def executeBinary (ω : ℕ → Bool) (s : Configuration) (i : Instruction) : Configuration :=
  let next (v : Configuration) (c : ℕ) : Configuration :=
    { v with pc := s.pc + 1, work := s.work + 1 + c }
  let r := s.reg
  match i with
  | .literal d v => next (s.write d v) (Nat.size d + Nat.size v)
  | .copy d x => next (s.write d (r x)) (binaryCharge d (r x))
  | .add d x y => next (s.write d (r x + r y)) (binaryCharge (r x) (r y))
  | .sub d x y => next (s.write d (r x - r y)) (binaryCharge (r x) (r y))
  | .mul d x y => next (s.write d (r x * r y)) (binaryCharge (r x) (r y))
  | .div d x y => next (s.write d (r x / r y)) (binaryCharge (r x) (r y))
  | .load d a => next (s.write d (s.memory.getD (r a) 0))
      (binaryCharge (r a) (s.memory.getD (r a) 0))
  | .store a x => next { s with memory := put 0 s.memory (r a) (r x) }
      (binaryCharge (r a) (r x) + (r a + 1 - s.memory.length))
  | .leJump x y t =>
      { next s (binaryCharge (r x) (r y) + Nat.size t) with pc := if r x ≤ r y then t else s.pc + 1 }
  | .jump t => { next s (Nat.size t) with pc := t }
  | .flip d => next { s.write d (if ω s.cursor then 1 else 0) with cursor := s.cursor + 1 }
      (Nat.size d + Nat.size s.cursor)
  | .halt success => { next s 0 with result := some success }
  | _ => { s with work := s.work + 1 }

def stepBinary (P : Program) (ω : ℕ → Bool) (s : Configuration) : Configuration :=
  if s.result.isSome then s else
    match P[s.pc]? with
    | none => { s with work := s.work + 1 }
    | some i => executeBinary ω s i

def runBinary (P : Program) (ω : ℕ → Bool) (s : Configuration) (t : ℕ) : Configuration :=
  (stepBinary P ω)^[t] s

/-- Deterministic programs have no flip. Binary programs have no real operations. -/
def Deterministic (P : Program) : Prop := ∀ d, Instruction.flip d ∉ P

def BinaryProgram (P : Program) : Prop :=
  ∀ i ∈ P, match i with
    | .realLiteral _ _ | .realCopy _ _ | .realAdd _ _ _ | .realSub _ _ _ |
      .realMul _ _ _ | .realDiv _ _ _ | .realLoad _ _ | .realStore _ _ |
      .realLeJump _ _ _ | .castReal _ _ => False
    | _ => True

/-- A finite prefix of independent fair bits; the stream beyond the prefix is
    irrelevant to a run of at most `t` steps. This is semantic enumeration only. -/
def bitStream {t : ℕ} (ω : Fin t → Bool) (i : ℕ) : Bool :=
  if h : i < t then ω ⟨i, h⟩ else false

noncomputable def successProbability (P : Program) (s : Configuration) (t : ℕ) : ℚ := by
  classical
  exact ((Finset.univ.filter fun ω : Fin t → Bool =>
    (runBinary P (bitStream ω) s t).result = some true).card : ℚ) / (2 : ℚ)^t

/-- The output is the binary subset mask in register zero; halt-false is Fail.
    Resource claims concern the actual run, including every intermediate state. -/
def BoundedRun (P : Program) (ω : ℕ → Bool) (s : Configuration)
    (t : ℕ) (time space : ℝ) : Prop :=
  (runBinary P ω s t).result.isSome ∧
    ((runBinary P ω s t).work : ℝ) ≤ time ∧
    ∀ j ≤ t, ((runBinary P ω s j).space : ℝ) ≤ space

end PlanarDFVS.SingleExp


