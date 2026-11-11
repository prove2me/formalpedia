-- Prove2me | Definitions.Def_ProductObjectiveRounding_Main_PRAM
-- name    : ProductObjectiveRounding_Main_PRAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:25.12987+00:00
-- url     : https://prove2.me/theorems/ab9ff5da-9124-4056-b6be-054228bab7bd
-- title:
--   Finite exact-arithmetic arbitrary-CRCW PRAM programs and execution
-- statement:
--   A program is a finite list of primitive instructions over finitely many real and word registers. It provides rational numerical constants, exact arithmetic and comparisons, word arithmetic and bit operations, indirect loads and stores, branches, processor identifiers, single-processor activation, explicit output writes and termination. There are no input-dependent program tables or answer oracles.
--
--   Each synchronous step executes one primitive per active processor and adds their number to total work. All reads see the previous memory. Every concurrent write retains a submitted value, and arbitration must choose a member of every nonempty set of writers. A fork activates one previously idle processor, with zero registers. All output slots start unwritten. Invalid typed loads and zero divisions fault. All indices and addresses, and all computed word values, stay below $(n+2)^{r+1}$ for a fixed exponent $r$; numeric real values have no magnitude restriction.
--
--   The predicate for solving an input requires termination, all output bits actually written, the requested mathematical output relation, and the work and synchronous-depth bounds under every legal arbitration. It is an expanded specification of execution, not a field of the program or a correctness assumption. Synchronous time bounds the longest chain of dependent primitives. This independent machine package underlies all algorithmic targets.
-- source:
--   Chase Hutton, Adam Melrod, STOC 2027 submission #1466 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1466.pdf, §2, parallel model, pp.6–7; explicit operational encoding of that model

import Mathlib

open scoped BigOperators
noncomputable section

namespace ProductObjectiveRounding.Main.PRAM

/-- A finite instruction set for §2, pp.6–7. There are no aggregate or oracle instructions. -/
inductive Cell where
  | blank
  | num (x : ℝ)
  | word (x : ℕ)
  deriving Inhabited

inductive NumOp where
  | add | sub | mul | div
  deriving DecidableEq

inductive WordOp where
  | add | sub | mul | div | mod | band | bor | xor | shl | shr | lt | eq
  deriving DecidableEq

inductive Instruction (registers : ℕ) where
  | constantNum (dst : Fin registers) (x : ℚ)
  | constantWord (dst : Fin registers) (x : ℕ)
  | copyNum (dst src : Fin registers)
  | copyWord (dst src : Fin registers)
  | arithmeticNum (op : NumOp) (dst a b : Fin registers)
  | arithmeticWord (op : WordOp) (dst a b : Fin registers)
  | compareNum (dst a b : Fin registers)
  | wordToNum (dst src : Fin registers)
  | loadNum (dst address : Fin registers)
  | loadWord (dst address : Fin registers)
  | storeNum (address src : Fin registers)
  | storeWord (address src : Fin registers)
  | processorId (dst : Fin registers)
  | branchZero (src : Fin registers) (ifZero ifNonzero : ℕ)
  | jump (target : ℕ)
  | spawn (processor : Fin registers) (entry : ℕ)
  | output (address src : Fin registers)
  | halt

structure Program where
  registers : ℕ
  code : List (Instruction registers)

structure Thread (registers : ℕ) where
  pc : Option ℕ
  num : Fin registers → ℝ
  word : Fin registers → ℕ

def idle (R : ℕ) : Thread R := ⟨none, fun _ => 0, fun _ => 0⟩
def start (R entry : ℕ) : Thread R := ⟨some entry, fun _ => 0, fun _ => 0⟩

structure Configuration (R : ℕ) where
  thread : ℕ → Thread R
  memory : ℕ → Cell
  result : ℕ → Option Bool
  work : ℕ

structure Effect (R : ℕ) where
  next : Thread R
  store : Option (ℕ × Cell) := none
  emit : Option (ℕ × Bool) := none
  fork : Option (ℕ × ℕ) := none
  addresses : List ℕ := []

def nextPC {R : ℕ} (t : Thread R) (p : ℕ) : Thread R := {t with pc := some (p + 1)}
def putNum {R : ℕ} (t : Thread R) (d : Fin R) (x : ℝ) : Thread R :=
  {t with num := Function.update t.num d x}
def putWord {R : ℕ} (t : Thread R) (d : Fin R) (x : ℕ) : Thread R :=
  {t with word := Function.update t.word d x}

def NumOp.eval : NumOp → ℝ → ℝ → ℝ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b

def WordOp.eval : WordOp → ℕ → ℕ → ℕ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .band, a, b => Nat.land a b
  | .bor, a, b => Nat.lor a b
  | .xor, a, b => Nat.xor a b
  | .shl, a, b => Nat.shiftLeft a b
  | .shr, a, b => Nat.shiftRight a b
  | .lt, a, b => if a < b then 1 else 0
  | .eq, a, b => if a = b then 1 else 0

/-- One active processor executes one primitive. Invalid loads and zero divisors fault. -/
def effect (P : Program) (pid : ℕ) (t : Thread P.registers) (mem : ℕ → Cell) :
    Option (Effect P.registers) := by
  classical
  exact match t.pc with
  | none => some ⟨t, none, none, none, []⟩
  | some pc => do
    let ins ← P.code[pc]?
    let nt := nextPC t pc
    match ins with
    | .constantNum d x => pure ⟨putNum nt d x, none, none, none, []⟩
    | .constantWord d x => pure ⟨putWord nt d x, none, none, none, []⟩
    | .copyNum d a => pure ⟨putNum nt d (t.num a), none, none, none, []⟩
    | .copyWord d a => pure ⟨putWord nt d (t.word a), none, none, none, []⟩
    | .arithmeticNum op d a b =>
      if op = .div ∧ t.num b = 0 then none
      else pure ⟨putNum nt d (op.eval (t.num a) (t.num b)), none, none, none, []⟩
    | .arithmeticWord op d a b =>
      if (op = .div ∨ op = .mod) ∧ t.word b = 0 then none
      else pure ⟨putWord nt d (op.eval (t.word a) (t.word b)), none, none, none, []⟩
    | .compareNum d a b =>
      pure ⟨putWord nt d (if t.num a ≤ t.num b then 1 else 0), none, none, none, []⟩
    | .wordToNum d a => pure ⟨putNum nt d (t.word a), none, none, none, []⟩
    | .loadNum d a => match mem (t.word a) with
      | .num x => pure ⟨putNum nt d x, none, none, none, [t.word a]⟩
      | _ => none
    | .loadWord d a => match mem (t.word a) with
      | .word x => pure ⟨putWord nt d x, none, none, none, [t.word a]⟩
      | _ => none
    | .storeNum a b => pure ⟨nt, some (t.word a, .num (t.num b)), none, none, [t.word a]⟩
    | .storeWord a b => pure ⟨nt, some (t.word a, .word (t.word b)), none, none, [t.word a]⟩
    | .processorId d => pure ⟨putWord nt d pid, none, none, none, []⟩
    | .branchZero a z nz => pure ⟨{t with pc := some (if t.word a = 0 then z else nz)}, none, none, none, []⟩
    | .jump target => pure ⟨{t with pc := some target}, none, none, none, []⟩
    | .spawn a entry => pure ⟨nt, none, none, some (t.word a, entry), [t.word a]⟩
    | .output a b =>
      if t.word b ≤ 1 then pure ⟨nt, none, some (t.word a, t.word b = 1), none, [t.word a]⟩
      else none
    | .halt => pure ⟨{t with pc := none}, none, none, none, []⟩

/-- Every nonempty set of simultaneous writers is resolved to one of those writers.
The time, address space and address can all influence arbitration. -/
abbrev Arbitration := ℕ → Bool → ℕ → Finset ℕ → ℕ

def LegalArbitration (choose : Arbitration) : Prop :=
  ∀ t space a S, S.Nonempty → choose t space a S ∈ S

/-- Polynomial ranges give Θ(log(n+2))-bit words, for each fixed exponent r. -/
def capacity (n r : ℕ) : ℕ := (n + 2) ^ (r + 1)

def initial (P : Program) (input : List Cell) : Configuration P.registers :=
  ⟨fun pid => if pid = 0 then start P.registers 0 else idle P.registers,
    fun a => input[a]?.getD .blank, fun _ => none, 0⟩

def active {R : ℕ} (cap : ℕ) (c : Configuration R) : Finset ℕ :=
  (Finset.range cap).filter (fun pid => (c.thread pid).pc.isSome)

def Halted {R : ℕ} (cap : ℕ) (c : Configuration R) : Prop := active cap c = ∅

def Bounded {R : ℕ} (cap : ℕ) (c : Configuration R) : Prop :=
  (∀ pid < cap, ∀ j, (c.thread pid).word j < cap) ∧
  (∀ a z, c.memory a = .word z → a < cap ∧ z < cap) ∧
  (∀ a x, c.memory a = .num x → a < cap) ∧
  (∀ a b, c.result a = some b → a < cap)

/-- Synchronous PRAM step; reads see the old memory. No processor can perform a reduction,
sort or subroutine call as a single instruction. A fork activates one idle processor. -/
def step (P : Program) (cap time : ℕ) (choose : Arbitration)
    (c : Configuration P.registers) : Option (Configuration P.registers) := by
  classical
  let es := fun pid => effect P pid (c.thread pid) c.memory
  let get := fun pid => (es pid).getD ⟨idle P.registers, none, none, none, []⟩
  let forks := fun target => (Finset.range cap).filter
    (fun pid => ∃ entry, (get pid).fork = some (target, entry))
  let ready : Prop := Bounded cap c ∧
    (∀ pid < cap, (es pid).isSome = true) ∧
    (∀ pid < cap, ∀ a ∈ (get pid).addresses, a < cap) ∧
    (∀ pid < cap, ∀ target entry, (get pid).fork = some (target, entry) →
      target < cap ∧ (c.thread target).pc = none ∧ entry < P.code.length ∧
        ∀ other ∈ forks target, other = pid)
  let memWriters := fun a => (Finset.range cap).filter
    (fun pid => ∃ x, (get pid).store = some (a, x))
  let outWriters := fun a => (Finset.range cap).filter
    (fun pid => ∃ b, (get pid).emit = some (a, b))
  let after : Configuration P.registers :=
    ⟨fun pid => if pid < cap then
        if h : (forks pid).Nonempty then
          let parent := (forks pid).min' h
          start P.registers (((get parent).fork).getD (0, 0)).2
        else (get pid).next
      else idle P.registers,
     fun a => if (memWriters a).Nonempty then
        (((get (choose time false a (memWriters a))).store).getD (a, .blank)).2
      else c.memory a,
     fun a => if (outWriters a).Nonempty then
        some ((((get (choose time true a (outWriters a))).emit).getD (a, false)).2)
      else c.result a,
     c.work + (active cap c).card⟩
  exact if ready ∧ Bounded cap after then some after else none

/-- A fault is absorbing; a halted machine incurs no more work. Time is synchronous depth. -/
def run (P : Program) (cap : ℕ) (choose : Arbitration) (input : List Cell) :
    ℕ → Option (Configuration P.registers)
  | 0 => some (initial P input)
  | t + 1 => do
    let c ← run P cap choose input t
    step P cap t choose c

/-- Universal arbitration, actual termination, explicit written output, and execution costs.
No program field assumes correctness or supplies cost labels. -/
def Solves (P : Program) (n r outputs : ℕ) (input : List Cell)
    (spec : (Fin outputs → Bool) → Prop) (workBound depthBound : ℝ) : Prop :=
  ∀ choose, LegalArbitration choose → ∃ t c x,
    run P (capacity n r) choose input t = some c ∧
    Halted (capacity n r) c ∧
    (∀ j : Fin outputs, c.result j.val = some (x j)) ∧ spec x ∧
    (c.work : ℝ) ≤ workBound ∧ (t : ℝ) ≤ depthBound

end ProductObjectiveRounding.Main.PRAM


