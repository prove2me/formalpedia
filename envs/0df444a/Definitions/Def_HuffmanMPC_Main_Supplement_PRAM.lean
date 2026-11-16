-- Prove2me | Definitions.Def_HuffmanMPC_Main_Supplement_PRAM
-- name    : HuffmanMPC_Main_Supplement_PRAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:17:06.835482+00:00
-- url     : https://prove2.me/theorems/4a3e36b2-b459-4c10-bae5-7b0656a16eb9
-- title:
--   Section 9 — finite word common-CRCW PRAM with measured time and work
-- statement:
--   A program is a finite list of instructions using finitely many private word registers, processor identifiers, program counters and shared memory. Instructions provide constants, copies, arithmetic, comparisons, bit operations, indirect reads and writes, branches, output, parallel activation control and termination. No instruction performs sorting, prefix summation or optimization.
--
--   For a fixed positive integer $k$ and frequency total $n$, the word width is
--   $$w=k(\lfloor\log_2(2+n)\rfloor+1).$$
--   All values, addresses, live control states and processor identifiers lie below $2^w$. Code is finite read-only syntax, independent of input values. Every synchronous step executes one instruction per active processor. Activating an idle range is the parallel-loop control convention: it has constant depth, and each newly activated processor is charged one additional operation. Initial input occurrences each receive one processor with zero private registers. Time is the number of synchronous steps; work is the sum of executed instructions and activation operations.
--
--   All reads use the old memory. Every pair of writes to the same shared or output cell must agree; conflicts, invalid instruction fetches, negative unsigned subtraction, division by zero and oversized words fault. Output cells start unwritten. Solvability requires one terminating fault-free execution that explicitly writes every requested word and simultaneously meets both resource bounds. This is a predicate derived from operational semantics, never a field of a program.
-- source:
--   Masoud Seddighin, Saeed Seddighin, STOC 2027 submission #377 (October 2026), Massively Parallel Algorithms for Huffman Coding, p. 41 (PDF 42), Section 9, PRAM model

import Mathlib

set_option autoImplicit false

namespace HuffmanMPC.Main.Supplement

/-- Finite word instruction syntax. No aggregate, optimization or real-number oracle. -/
inductive Op where
  | add | sub | mul | div | mod | lt | eq | band | bor | xor | shl | shr
  deriving DecidableEq

def Op.eval : Op → ℕ → ℕ → ℕ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .lt, a, b => if a < b then 1 else 0
  | .eq, a, b => if a = b then 1 else 0
  | .band, a, b => Nat.land a b
  | .bor, a, b => Nat.lor a b
  | .xor, a, b => Nat.xor a b
  | .shl, a, b => Nat.shiftLeft a b
  | .shr, a, b => Nat.shiftRight a b

inductive Instruction (R : ℕ) where
  | literal (dst : Fin R) (value : ℕ)
  | copy (dst src : Fin R)
  | arithmetic (op : Op) (dst a b : Fin R)
  | load (dst addr : Fin R)
  | store (addr src : Fin R)
  | output (addr src : Fin R)
  | pid (dst : Fin R)
  | branch (src : Fin R) (ifZero ifNonzero : ℕ)
  | jump (target : ℕ)
  /-- Parallel control: activate the idle processors in [base,base+count).
  Each newly activated processor costs one operation in the same synchronous step.
  No arithmetic, reading, writing or reduction is performed by activation. -/
  | activate (base count : Fin R) (entry : ℕ)
  | halt

structure Program where
  registers : ℕ
  code : List (Instruction registers)

structure Thread (R : ℕ) where
  pc : Option ℕ
  reg : Fin R → ℕ

def idle (R : ℕ) : Thread R := ⟨none, fun _ => 0⟩
def start (R entry : ℕ) : Thread R := ⟨some entry, fun _ => 0⟩

structure Configuration (R : ℕ) where
  thread : ℕ → Thread R
  memory : ℕ → ℕ
  result : ℕ → Option ℕ
  work : ℕ

structure Effect (R : ℕ) where
  next : Thread R
  write : Option (ℕ × ℕ) := none
  emit : Option (ℕ × ℕ) := none
  forks : List (ℕ × ℕ) := []
  addresses : List ℕ := []

def put {R : ℕ} (t : Thread R) (d : Fin R) (v : ℕ) : Thread R :=
  {t with reg := Function.update t.reg d v}

/-- All reads see the preceding shared-memory snapshot. Division by zero,
negative unsigned subtraction, and later any word overflow are faults. -/
def effect (P : Program) (pid : ℕ) (t : Thread P.registers) (mem : ℕ → ℕ) :
    Option (Effect P.registers) := do
  match t.pc with
  | none => pure ⟨t, none, none, [], []⟩
  | some pc =>
    let ins ← P.code[pc]?
    let nt := {t with pc := some (pc + 1)}
    match ins with
    | .literal d v => pure ⟨put nt d v, none, none, [], []⟩
    | .copy d a => pure ⟨put nt d (t.reg a), none, none, [], []⟩
    | .arithmetic op d a b =>
      if ((op = .div ∨ op = .mod) ∧ t.reg b = 0) ∨
          (op = .sub ∧ t.reg a < t.reg b) then none
      else pure ⟨put nt d (op.eval (t.reg a) (t.reg b)), none, none, [], []⟩
    | .load d a => pure ⟨put nt d (mem (t.reg a)), none, none, [], [t.reg a]⟩
    | .store a b => pure ⟨nt, some (t.reg a, t.reg b), none, [], [t.reg a]⟩
    | .output a b => pure ⟨nt, none, some (t.reg a, t.reg b), [], [t.reg a]⟩
    | .pid d => pure ⟨put nt d pid, none, none, [], []⟩
    | .branch a z nz => pure ⟨{t with pc := some (if t.reg a = 0 then z else nz)}, none, none, [], []⟩
    | .jump target => pure ⟨{t with pc := some target}, none, none, [], []⟩
    | .activate b c entry => pure ⟨nt, none, none,
        (List.range (t.reg c)).map (fun j => (t.reg b + j, entry)), []⟩
    | .halt => pure ⟨{t with pc := none}, none, none, [], []⟩

/-- Finite address, processor and word universe; the exponent is an actual bit count. -/
def wordBits (k n : ℕ) : ℕ := k * (Nat.log 2 (2 + n) + 1)
def capacity (k n : ℕ) : ℕ := 2 ^ wordBits k n

/-- The input has one initial processor per input occurrence; zero occurrences
need no processor. All private storage starts at zero. The supplied input is the
only nonzero initial shared storage, and output starts unwritten. -/
def initial (P : Program) (processors : ℕ) (input : List ℕ) : Configuration P.registers :=
  ⟨fun pid => if pid < processors then start P.registers 0 else idle P.registers,
    fun a => input.getD a 0, fun _ => none, 0⟩

noncomputable def active {R : ℕ} (cap : ℕ) (c : Configuration R) : Finset ℕ :=
  (Finset.range cap).filter (fun pid => (c.thread pid).pc.isSome)

def Bounded {R : ℕ} (cap : ℕ) (c : Configuration R) : Prop :=
  (∀ pid < cap, (∀ j, (c.thread pid).reg j < cap) ∧
    ∀ pc, (c.thread pid).pc = some pc → pc < cap) ∧
  (∀ pid, cap ≤ pid → (c.thread pid).pc = none) ∧
  (∀ a, c.memory a < cap ∧ (cap ≤ a → c.memory a = 0)) ∧
  (∀ a v, c.result a = some v → a < cap ∧ v < cap)

/-- Common-CRCW: agreement is checked on every attempted write, even a write
that leaves the memory unchanged. A conflicting step faults; it never chooses
a winning writer. Activation ranges must be disjoint and previously idle. -/
noncomputable def step (P : Program) (cap : ℕ) (c : Configuration P.registers) :
    Option (Configuration P.registers) := by
  classical
  let ids := Finset.range cap
  let es := fun pid => effect P pid (c.thread pid) c.memory
  let get := fun pid => (es pid).getD ⟨idle P.registers, none, none, [], []⟩
  let writes := fun a => ids.filter (fun pid => ∃ v, (get pid).write = some (a, v))
  let emits := fun a => ids.filter (fun pid => ∃ v, (get pid).emit = some (a, v))
  let forks := fun target => ids.filter (fun pid => ∃ entry, (target, entry) ∈ (get pid).forks)
  let ready : Prop := Bounded cap c ∧ P.registers < cap ∧
    (∀ pid < cap, (es pid).isSome = true) ∧
    (∀ pid < cap, ∀ a ∈ (get pid).addresses, a < cap) ∧
    (∀ i < cap, ∀ j < cap, ∀ a x y,
      (get i).write = some (a,x) → (get j).write = some (a,y) → x = y) ∧
    (∀ i < cap, ∀ j < cap, ∀ a x y,
      (get i).emit = some (a,x) → (get j).emit = some (a,y) → x = y) ∧
    (∀ pid < cap, ∀ target entry, (target,entry) ∈ (get pid).forks →
      target < cap ∧ (c.thread target).pc = none ∧ entry < P.code.length ∧
        ∀ other ∈ forks target, other = pid)
  let after : Configuration P.registers :=
    ⟨fun pid => if pid < cap then
        if h : (forks pid).Nonempty then
          let parent := (forks pid).min' h
          let entry := ((get parent).forks.find? (fun x => x.1 = pid)).getD (0,0)
          start P.registers entry.2
        else (get pid).next
      else idle P.registers,
     fun a => if h : (writes a).Nonempty then
        (((get ((writes a).min' h)).write).getD (0,0)).2
      else c.memory a,
     fun a => if h : (emits a).Nonempty then
        some ((((get ((emits a).min' h)).emit).getD (0,0)).2)
      else c.result a,
     c.work + (active cap c).card + ∑ pid ∈ ids, (get pid).forks.length⟩
  exact if ready ∧ Bounded cap after then some after else none

/-- The mathematical evaluator records only primitive synchronous steps. Its
own host-language evaluation time is not a PRAM resource. Fault is absorbing. -/
noncomputable def run (P : Program) (cap processors : ℕ) (input : List ℕ) :
    ℕ → Option (Configuration P.registers)
  | 0 => some (initial P processors input)
  | t + 1 => do
    let c ← run P cap processors input t
    step P cap c

/-- One deterministic execution supplies both bounds and all output words.
No instruction or program field contains this predicate or its specification. -/
def Solves (P : Program) (k n processors : ℕ) (input : List ℕ)
    (output : List ℕ) (timeBound workBound : ℝ) : Prop :=
  ∃ t c, run P (capacity k n) processors input t = some c ∧
    Bounded (capacity k n) c ∧ active (capacity k n) c = ∅ ∧
    (∀ j < output.length, c.result j = some (output.getD j 0)) ∧
    (t : ℝ) ≤ timeBound ∧ (c.work : ℝ) ≤ workBound

end HuffmanMPC.Main.Supplement


