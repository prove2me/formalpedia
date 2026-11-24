-- Prove2me | Definitions.Def_CSL_Shared_Programs_FixedPolicyNormalization
-- name    : CSL_Shared_Programs_FixedPolicyNormalization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:08:41.681479+00:00
-- url     : https://prove2.me/theorems/19bf3468-8bfe-4247-a26d-ab6359af6694
-- title:
--   Coded sorting library: Shared / Programs / FixedPolicyNormalization
-- statement:
--   Module `CodedSorting.Shared.Programs.FixedPolicyNormalization` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Physical execution of fixed instructions and memory-dependent I/O policies. The first section gives a counterexample showing when a selected continuation needs additional stored data. The interpreters below keep the data needed to select the next instruction in counted memory. Only fetch and flush access disk, each costing one I/O. Programs are fixed before inputs are chosen; applications specify how the finite addresses are represented by machine words.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.FixedPolicyNormalization

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Programs_ControlledNormalization

section FixedControlNormalization
/-! Physical execution of fixed instructions and memory-dependent I/O policies. The first section gives a counterexample showing when a selected continuation needs additional stored data. The interpreters below keep the data needed to select the next instruction in counted memory. Only fetch and flush access disk, each costing one I/O. Programs are fixed before inputs are chosen; applications specify how the finite addresses are represented by machine words. 














-/

set_option autoImplicit false
namespace CSL.FixedControlNormalization
open Normalization

namespace CaptureCounterexample

def window : Window 1 1 := ⟨0, by decide⟩

def initial (old : Bool) : PhysicalState 1 1 1 Bool :=
  ⟨fun _ => old, fun _ => false, fun _ _ => false⟩

def instruction (old : Bool) : ControlledNormalization.Instruction 1 1 1 Bool :=
  ⟨.read 0 window, fun _ _ => old⟩

def overwritten (old : Bool) : PhysicalState 1 1 1 Bool :=
  Normalization.physicalStep (by decide : 1 ≤ 1) false (.read 0 window) (initial old)

def restored (old : Bool) : PhysicalState 1 1 1 Bool :=
  ControlledNormalization.physicalStep (by decide : 1 ≤ 1) false
    (instruction old) (initial old)

theorem overwritten_equal : overwritten false = overwritten true := by
  simp only [overwritten, Normalization.physicalStep, initial]
  congr 1
  funext j
  have hj : j.val = 0 := by omega
  simp [load, window, hj, blockPrefix]

@[simp] theorem restored_word (old : Bool) : (restored old).ram 0 = old := by
  rfl

/-- The post-read physical state cannot determine this alleged continuation.
The missing discriminator is precisely the old word captured in the closure.
This refutes the stated Markov boundary, not all possible implementations of
the same input/output function (which could, for example, omit the read). -/
theorem no_post_read_state_function :
    ¬ ∃ resume : PhysicalState 1 1 1 Bool → PhysicalState 1 1 1 Bool,
      ∀ old, resume (overwritten old) = restored old := by
  rintro ⟨resume, h⟩
  have he : restored false = restored true :=
    (h false).symm.trans ((congrArg resume overwritten_equal).trans (h true))
  have hc := congrArg (fun s : PhysicalState 1 1 1 Bool => s.ram 0) he
  simp only [restored_word] at hc
  cases hc

end CaptureCounterexample

variable {L b B D K w : ℕ}

abbrev Word (w : ℕ) := Fin (2^w)
abbrev Ram (L w : ℕ) := Words L (Word w)
abbrev State (L B D w : ℕ) := PhysicalState L B D (Word w)

/-- The instruction's functions are static members of the program table.
The local operation sees exactly the counted RAM and transfer buffer. -/
inductive Instruction (L b B D K w : ℕ) where
  | localOp (operation : Ram L w × Words B (Word w) → Ram L w × Words B (Word w))
      (next : Fin K)
  | fetch (address : Ram L w → Fin D) (next : Fin K)
  | copyPrefix (window : Window L b) (next : Fin K)
  | stageWrite (window : Window L b) (next : Fin K)
  | flush (address : Ram L w → Fin D) (next : Fin K)
  | halt

/-- A PC is a genuine word in one of the L existing RAM cells. Program
labels must fit that word. Invalid label words halt; no external PC exists. -/
structure Program (L b B D K w : ℕ) where
  pc : Fin L
  encode : Fin K → Word w
  decode : Word w → Option (Fin K)
  decode_encode : ∀ k, decode (encode k) = some k
  table : Fin K → Instruction L b B D K w

def advance (p : Program L b B D K w) (next : Fin K)
    (s : State L B D w) : State L B D w :=
  {s with ram := Function.update s.ram p.pc (p.encode next)}

@[simp] theorem advance_pc (p : Program L b B D K w) (next : Fin K)
    (s : State L B D w) :
    p.decode ((advance p next s).ram p.pc) = some next := by
  simp [advance, p.decode_encode]

@[simp] theorem advance_disk (p : Program L b B D K w) (next : Fin K)
    (s : State L B D w) : (advance p next s).disk = s.disk := rfl

/-- This is the entire transition state. In particular it has no pending
Instruction, resume function, snapshot, or uncharged data-dependent label. -/
def step (hb : b ≤ B) (padding : Word w) (p : Program L b B D K w)
    (s : State L B D w) : State L B D w × ℕ :=
  match p.decode (s.ram p.pc) with
  | none => (s, 0)
  | some code => match p.table code with
    | .halt => (s, 0)
    | .localOp operation next =>
        let result := operation (s.ram, s.buffer)
        (advance p next {s with ram := result.1, buffer := result.2}, 0)
    | .fetch address next =>
        (advance p next (primitiveStep hb padding (.fetch (address s.ram)) s), 1)
    | .copyPrefix window next =>
        (advance p next (primitiveStep hb padding (.copyPrefix window) s), 0)
    | .stageWrite window next =>
        (advance p next (primitiveStep hb padding (.stageWrite window) s), 0)
    | .flush address next =>
        (advance p next (primitiveStep hb padding (.flush (address s.ram)) s), 1)

/-- A finite observation horizon is ghost state. At each boundary selection
uses only the current RAM PC and the immutable table. -/
def run (hb : b ≤ B) (padding : Word w) (p : Program L b B D K w) :
    ℕ → State L B D w → State L B D w × ℕ
  | 0, s => (s, 0)
  | fuel+1, s =>
      let current := step hb padding p s
      let rest := run hb padding p fuel current.1
      (rest.1, current.2+rest.2)

theorem step_cost_le_one (hb : b ≤ B) (padding : Word w)
    (p : Program L b B D K w) (s : State L B D w) :
    (step hb padding p s).2 ≤ 1 := by
  unfold step
  split
  · simp
  · split <;> simp

theorem run_cost_le_fuel (hb : b ≤ B) (padding : Word w)
    (p : Program L b B D K w) (fuel : ℕ) (s : State L B D w) :
    (run hb padding p fuel s).2 ≤ fuel := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    have hs := step_cost_le_one hb padding p s
    have hr := ih (step hb padding p s).1
    simp only [run]
    omega

/-- Fetch is precisely the existing explicit primitive, followed only by
a PC update to a fixed label. Fetch itself preserves all RAM, including PC. -/
theorem step_fetch (hb : b ≤ B) (padding : Word w)
    (p : Program L b B D K w) (s : State L B D w) (code next : Fin K)
    (address : Ram L w → Fin D)
    (hc : p.decode (s.ram p.pc) = some code)
    (hi : p.table code = .fetch address next) :
    step hb padding p s =
      (advance p next {s with buffer := s.disk (address s.ram)}, 1) := by
  simp [step, hc, hi, primitiveStep]

theorem step_flush (hb : b ≤ B) (padding : Word w)
    (p : Program L b B D K w) (s : State L B D w) (code next : Fin K)
    (address : Ram L w → Fin D)
    (hc : p.decode (s.ram p.pc) = some code)
    (hi : p.table code = .flush address next) :
    step hb padding p s =
      (advance p next {s with disk := Function.update s.disk (address s.ram) s.buffer}, 1) := by
  simp [step, hc, hi, primitiveStep]

/-- At fixed PC, local computation cannot inspect or modify external disk.
Its only operands are the L+B resident words. -/
theorem local_disk_unchanged (hb : b ≤ B) (padding : Word w)
    (p : Program L b B D K w) (s : State L B D w) (code next : Fin K)
    (operation : Ram L w × Words B (Word w) → Ram L w × Words B (Word w))
    (hc : p.decode (s.ram p.pc) = some code)
    (hi : p.table code = .localOp operation next) :
    (step hb padding p s).1.disk = s.disk := by
  simp [step, hc, hi]

/-- Changing a PC before a payload copy makes no observable difference once
that PC is set to the next fixed label. All other RAM cells agree exactly. -/
theorem update_load_update {Value : Type*} (ram : Words L Value)
    (pc : Fin L) (x y : Value) (window : Window L b) (block : Words b Value) :
    Function.update (load (Function.update ram pc x) window block) pc y =
      Function.update (load ram window block) pc y := by
  classical
  funext j
  by_cases hj : j=pc
  · subst j
    simp
  · simp only [Function.update_of_ne hj, load]

/-- An actual fixed-table fetch/copy sequence refines the useful readNext
fragment of the old controller. Both its opcode and next label are static.
The intermediate opcode is stored in RAM and costs one of its L words. -/
theorem readNext_refinement (hb : b ≤ B) (padding : Word w)
    (p : Program L b B D K w) (s : State L B D w)
    (first copy next : Fin K) (address : Ram L w → Fin D) (window : Window L b)
    (hc : p.decode (s.ram p.pc) = some first)
    (hf : p.table first = .fetch address copy)
    (hcopy : p.table copy = .copyPrefix window next) :
    run hb padding p 2 s =
      (ControlledNormalization.physicalStep hb padding
        (ControlledNormalization.readNext (address s.ram) window p.pc (p.encode next)) s, 1) := by
  have hfirst := step_fetch hb padding p s first copy address hc hf
  simp only [run, hfirst, Nat.add_zero]
  simp only [step, advance_pc, hcopy]
  simp only [ControlledNormalization.physicalStep_eq, ControlledNormalization.readNext,
    Normalization.physicalStep, primitiveStep, advance]
  congr 2
  exact update_load_update s.ram p.pc (p.encode copy) (p.encode next) window
    (blockPrefix hb (s.disk (address s.ram)))

/-- The write pipeline stages the payload before changing its PC, then
flushes it. A data-address expression ignores only the reserved PC cell;
it may otherwise depend on the current RAM. No address is retained in a
closure across a RAM overwrite. -/
theorem writeNext_refinement (hb : b ≤ B) (padding : Word w)
    (p : Program L b B D K w) (s : State L B D w)
    (first flush next : Fin K) (address : Ram L w → Fin D) (window : Window L b)
    (hc : p.decode (s.ram p.pc) = some first)
    (hf : p.table first = .stageWrite window flush)
    (hflush : p.table flush = .flush address next)
    (ha : ∀ ram value, address (Function.update ram p.pc value) = address ram) :
    run hb padding p 2 s =
      (ControlledNormalization.physicalStep hb padding
        (⟨.write (address s.ram) window,
          fun ram => Function.update ram p.pc (p.encode next)⟩ :
          ControlledNormalization.Instruction L b D (Word w)) s, 1) := by
  have hfirst : step hb padding p s =
      (advance p flush (primitiveStep hb padding (.stageWrite window) s), 0) := by
    simp [step, hc, hf]
  simp only [run, hfirst, Nat.zero_add, Nat.add_zero]
  simp only [step, advance_pc, hflush]
  simp only [ControlledNormalization.physicalStep_eq, Normalization.physicalStep,
    primitiveStep, advance, ha, Function.update_idem]


/-- Concrete slots count the PC exactly once, within RAM. There is no
additional register that carries the selected instruction across I/O. -/
theorem resident_word_count :
    Fintype.card (Fin L ⊕ Fin B) = L+B := by simp

/-- The complete resident configuration has exactly the capacity of L+B
w-bit words; neither functions nor an extra opcode are part of it. -/
theorem resident_configuration_count :
    Fintype.card (Ram L w × Words B (Word w)) = (2^w)^(L+B) := by
  simp [Ram, Words, Word, pow_add]

theorem opcode_capacity (p : Program L b B D K w) : K ≤ 2^w := by
  have hi : Function.Injective p.encode := by
    intro x y h
    have hd := congrArg p.decode h
    simpa only [p.decode_encode, Option.some.injEq] using hd
  simpa [Word] using Fintype.card_le_of_injective p.encode hi

theorem memory_fit (M : ℕ) (h : L+B ≤ M) :
    Fintype.card (Fin L ⊕ Fin B) ≤ M := by simpa using h

theorem normalized_memory_fit (M B : ℕ) (hMB : 2*B ≤ M) :
    Fintype.card (Fin (M/4) ⊕ Fin B) ≤ M := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- Equal complete states cannot diverge due to a retained old continuation.
This property applies at every physical instruction boundary. -/
theorem state_determines_run (hb : b ≤ B) (padding : Word w)
    (p : Program L b B D K w) (fuel : ℕ) (s t : State L B D w) (h : s=t) :
    run hb padding p fuel s = run hb padding p fuel t := congrArg _ h

end CSL.FixedControlNormalization
end FixedControlNormalization

section FixedPolicyNormalization
/-!
# A fixed, counted-state interpreter for adaptive I/O policies

The old controller can choose a continuation depending on the pre-read RAM.
Executing a destructive load and retaining that continuation for free is not
sound as a memory accounting argument. This interpreter instead keeps the old
RAM until the physical transfer has finished. It then recomputes the selected
instruction from that RAM and performs load plus continuation as one fixed
RAM-only map. No selected instruction or closure is stored across a boundary.

A fixed program has four phases, encoded in one counted w-bit control cell.
Two microsteps simulate one logical policy observation, with exactly the same
I/O cost. The immutable policy is fixed before all input states are quantified.
The resident budget is L+B+1 words. These are abstract I/O-machine local maps:
a uniform scalar-word implementation of an arbitrary policy is NOT asserted.
-/

set_option autoImplicit false
namespace CSL.FixedPolicyNormalization
open Normalization

variable {L b B D w : ℕ}
abbrev Word (w : ℕ) := Fin (2^w)

/-- A program is immutable and shared by every input. Its policy is evaluated
afresh from resident RAM; no result of that evaluation is runtime state. -/
structure Program (L b D w : ℕ) where
  policy : ControlledNormalization.Policy L b D (Word w)

/-- All data-dependent resident state: L payload/control words from the source
machine, B transfer words, and ONE additional phase word. -/
structure State (L B D w : ℕ) where
  data : PhysicalState L B D (Word w)
  phase : Word w

/-- Four phase codes fit an ordinary word when 4 ≤ 2^w. -/
def code (hcap : 4 ≤ 2^w) (k : Fin 4) : Word w :=
  ⟨k.val, lt_of_lt_of_le k.isLt hcap⟩

@[simp] theorem code_val (hcap : 4 ≤ 2^w) (k : Fin 4) :
    (code hcap k).val = k.val := rfl

def ready (hcap : 4 ≤ 2^w) (s : PhysicalState L B D (Word w)) : State L B D w :=
  ⟨s, code hcap 0⟩

/-- This fixed transition table has four cases. The pending read/write phases
recompute the policy while the OLD RAM still exists in the counted L cells.
The transfer buffer is the only extra data storage used during that I/O. -/
def step (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) (s : State L B D w) : State L B D w × ℕ :=
  match s.phase.val with
  | 0 => match p.policy s.data.ram with
    | none => (⟨s.data, code hcap 3⟩, 0)
    | some i => match i.operation with
      | .localOp f =>
          (⟨{s.data with ram := i.resume (f s.data.ram)}, code hcap 3⟩, 0)
      | .read address _ =>
          (⟨{s.data with buffer := s.data.disk address}, code hcap 1⟩, 1)
      | .write _ window =>
          (⟨{s.data with buffer := pack padding (slice s.data.ram window)},
            code hcap 2⟩, 0)
  | 1 => match p.policy s.data.ram with
    | some i => match i.operation with
      | .read _ window =>
          (ready hcap {s.data with ram := i.resume (load s.data.ram window (blockPrefix hb s.data.buffer))}, 0)
      | _ => (ready hcap s.data, 0)
    | none => (ready hcap s.data, 0)
  | 2 => match p.policy s.data.ram with
    | some i => match i.operation with
      | .write address _ =>
          (ready hcap {s.data with ram := i.resume s.data.ram, disk := Function.update s.data.disk address s.data.buffer}, 1)
      | _ => (ready hcap s.data, 0)
    | none => (ready hcap s.data, 0)
  | _ => (ready hcap s.data, 0)

def run (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) : ℕ → State L B D w → State L B D w × ℕ
  | 0, s => (s, 0)
  | fuel+1, s =>
      let first := step hb hcap padding p s
      let rest := run hb hcap padding p fuel first.1
      (rest.1, first.2+rest.2)

/-- A proof-only description of one source observation, not an additional
component of the physical machine. -/
def observation (hb : b ≤ B) (padding : Word w) (p : Program L b D w)
    (s : PhysicalState L B D (Word w)) : PhysicalState L B D (Word w) × ℕ :=
  match p.policy s.ram with
  | none => (s, 0)
  | some i => (ControlledNormalization.physicalStep hb padding i s,
      transferCost i.operation)

/-- No I/O is hidden in local computation: the only positive-cost cases are
the actual fetch in phase zero and the actual flush in phase two. -/
theorem step_cost_le_one (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) (s : State L B D w) :
    (step hb hcap padding p s).2 ≤ 1 := by
  unfold step
  split
  · split
    · simp
    · split <;> simp
  · split
    · split <;> simp
    · simp
  · split
    · split <;> simp
    · simp
  · simp

/-- A zero-I/O microstep cannot change external disk. -/
theorem zero_cost_disk_unchanged (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) (s : State L B D w) :
    (step hb hcap padding p s).2 = 0 →
      (step hb hcap padding p s).1.data.disk = s.data.disk := by
  unfold step
  split
  · split
    · simp
    · split <;> simp
  · split
    · split <;> simp [ready]
    · simp [ready]
  · split
    · split <;> simp [ready]
    · simp [ready]
  · simp [ready]

/-- Project the complete internal state, excluding external disk. -/
def resident (s : State L B D w) :
    (Words L (Word w) × Words B (Word w)) × Word w :=
  ((s.data.ram, s.data.buffer), s.phase)

/-- Zero-cost computation cannot inspect external disk either. With the same
resident words it produces the same resident result and costs zero, regardless
of disk contents. Thus arbitrary RAM-local maps do not hide extra disk reads. -/
theorem zero_cost_locality (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) (ram : Words L (Word w)) (buffer : Words B (Word w))
    (phase : Word w) (disk₁ disk₂ : Disk D B (Word w)) :
    (step hb hcap padding p ⟨⟨ram,buffer,disk₁⟩,phase⟩).2 = 0 →
      resident (step hb hcap padding p ⟨⟨ram,buffer,disk₁⟩,phase⟩).1 =
        resident (step hb hcap padding p ⟨⟨ram,buffer,disk₂⟩,phase⟩).1 ∧
      (step hb hcap padding p ⟨⟨ram,buffer,disk₂⟩,phase⟩).2 = 0 := by
  unfold step
  split
  · split
    · simp_all [resident]
    · split <;> simp_all [resident]
  · split
    · split <;> simp_all [resident, ready]
    · simp_all [resident, ready]
  · split
    · split <;> simp_all [resident, ready]
    · simp_all [resident, ready]
  · simp_all [resident, ready]

/-- The actual fetch leaves every old source word resident. Its phase word
identifies the next fixed operation, rather than carrying a continuation. -/
theorem read_fetch_state (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) (s : PhysicalState L B D (Word w))
    (i : ControlledNormalization.Instruction L b D (Word w))
    (address : Fin D) (window : Window L b)
    (hp : p.policy s.ram = some i) (hi : i.operation = .read address window) :
    step hb hcap padding p (ready hcap s) =
      (⟨{s with buffer := s.disk address}, code hcap 1⟩, 1) := by
  simp [step, ready, code, hp, hi]

/-- This second step is one fixed map of counted RAM and buffer. It does not
read disk; it selects the same instruction by recomputing the fixed policy. -/
theorem read_resume_state (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) (s : PhysicalState L B D (Word w))
    (i : ControlledNormalization.Instruction L b D (Word w))
    (address : Fin D) (window : Window L b)
    (hp : p.policy s.ram = some i) (hi : i.operation = .read address window) :
    step hb hcap padding p ⟨s, code hcap 1⟩ =
      (ready hcap {s with ram := i.resume (load s.ram window (blockPrefix hb s.buffer))}, 0) := by
  simp [step, code, hp, hi]

/-- One complete source observation, including a data-dependent continuation,
is implemented by two physical boundaries and the exact transfer count. -/
theorem two_steps (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) (s : PhysicalState L B D (Word w)) :
    run hb hcap padding p 2 (ready hcap s) =
      (ready hcap (observation hb padding p s).1,
        (observation hb padding p s).2) := by
  cases hp : p.policy s.ram with
  | none => simp [run, step, ready, code, observation, hp]
  | some i =>
    rcases i with ⟨operation, resume⟩
    cases operation <;>
      simp [run, step, ready, code, observation, hp,
        ControlledNormalization.physicalStep_eq, Normalization.physicalStep,
        transferCost]

theorem run_add (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) (n m : ℕ) (s : State L B D w) :
    run hb hcap padding p (n+m) s =
      ((run hb hcap padding p m (run hb hcap padding p n s).1).1,
        (run hb hcap padding p n s).2 +
          (run hb hcap padding p m (run hb hcap padding p n s).1).2) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [run, ih]
    simp only [Nat.add_assoc]

/-- Full adaptive execution, not merely a single read or write. The fixed
program p is unchanged throughout, for every possible input and horizon. -/
theorem run_refinement (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) (fuel : ℕ) (s : PhysicalState L B D (Word w)) :
    run hb hcap padding p (2*fuel) (ready hcap s) =
      (ready hcap (ControlledNormalization.runPhysical hb padding p.policy fuel s).1,
        (ControlledNormalization.runPhysical hb padding p.policy fuel s).2) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    rw [show 2*(fuel+1)=2+2*fuel by omega, run_add, two_steps]
    simp only [ih]
    cases hp : p.policy s.ram with
    | none =>
      cases fuel <;> simp [observation, hp, ControlledNormalization.runPhysical]
    | some i =>
      simp only [observation, hp, ControlledNormalization.runPhysical,
        ControlledNormalization.compiled_cost]

/-- Payload semantics and exact physical cost are inherited from the logical
controller, now via an actual counted-state two-phase execution. -/
theorem logical_refinement (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) (fuel : ℕ)
    (s : LogicalState L b D (Word w)) (t : PhysicalState L B D (Word w))
    (h : Represents hb s t) :
    Represents hb (ControlledNormalization.runLogical p.policy fuel s).1
      (run hb hcap padding p (2*fuel) (ready hcap t)).1.data ∧
    (ControlledNormalization.runLogical p.policy fuel s).2 =
      (run hb hcap padding p (2*fuel) (ready hcap t)).2 := by
  rw [run_refinement]
  exact ControlledNormalization.run_represents_and_cost hb padding p.policy fuel s t h

/-- The quantifier order rules out choosing an input-dependent program. This
is an abstract local-map compiler; it asserts no scalar-word running time. -/
theorem one_program_all_inputs (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (policy : ControlledNormalization.Policy L b D (Word w)) :
    ∃ p : Program L b D w, ∀ fuel s t, Represents hb s t →
      Represents hb (ControlledNormalization.runLogical policy fuel s).1
        (run hb hcap padding p (2*fuel) (ready hcap t)).1.data ∧
      (ControlledNormalization.runLogical policy fuel s).2 =
        (run hb hcap padding p (2*fuel) (ready hcap t)).2 := by
  refine ⟨⟨policy⟩, ?_⟩
  intro fuel s t h
  exact logical_refinement hb hcap padding ⟨policy⟩ fuel s t h

open LayoutConversion NormalizationComplete in
/-- The output of THIS physical run is compacted back. The exact charge depends
on live input/output lengths, never on total reserved scratch capacity D.
The expand/compact traces here are the existing layout routines; this theorem
does not add a finite-word controller implementation for those routines. -/
theorem simulation_live_layout (source backing target : BlockReflection.Disk (Word w))
    (padding : Word w) (ram : Words L (Word w)) (D B b nIn nOut : ℕ)
    (hB : 0<B) (hb : b≤B) (hout : nOut≤D) (hcap : 4 ≤ 2^w)
    (p : Program L b D w) (fuel : ℕ) :
    let logical := ControlledNormalization.runLogical p.policy fuel
      (liveLogicalInput source backing ram D B b nIn)
    let physical := run hb hcap padding p (2*fuel)
      (ready hcap (livePhysicalInput source backing padding ram D B b nIn hB))
    let restored := compactRun (flattenBlocks D B hB padding physical.1.data.disk)
      B b hB hb nOut ⟨target,[]⟩
    (∀ j : Fin nOut,∀ i : Fin b,
      restored.disk (j.val*b+i.val)=logical.1.disk (j.castLE hout) i) ∧
    (expandRun source padding B b hB nIn ⟨backing,[]⟩).trace.length+
      physical.2+restored.trace.length=logical.2+3*nIn+5*nOut := by
  try dsimp
  rw [run_refinement]
  exact ControlledNormalization.simulation_live_layout source backing target padding ram
    D B b nIn nOut hB hb hout p.policy fuel

/-- Source RAM, transfer buffer, and the full phase word are all counted. -/
theorem resident_word_count :
    Fintype.card ((Fin L ⊕ Fin B) ⊕ Fin 1) = L+B+1 := by simp

/-- Every resident configuration, including invalid phase words, fits exactly
L+B+1 words. Disk is external and is not included in this count. -/
theorem resident_configuration_count :
    Fintype.card ((Words L (Word w) × Words B (Word w)) × Word w) =
      (2^w)^(L+B+1) := by
  simp [Words, Word, pow_add]

theorem memory_fit (M : ℕ) (h : L+B+1 ≤ M) :
    Fintype.card ((Fin L ⊕ Fin B) ⊕ Fin 1) ≤ M := by simpa using h

/-- For the ordinary normalized branch, the phase word also fits; B=1,M=2
is covered arithmetically, though applications still need source RAM and
word/control encodings suited to their own small-memory algorithm. -/
theorem normalized_memory_fit (M B : ℕ) (hB : 0<B) (hMB : 2*B ≤ M) :
    Fintype.card ((Fin (M/4) ⊕ Fin B) ⊕ Fin 1) ≤ M := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- Equal counted states produce equal futures: neither a prior instruction
nor the pre-read RAM is available anywhere outside the displayed state. -/
theorem state_determines_run (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) (fuel : ℕ) (s t : State L B D w) (h : s=t) :
    run hb hcap padding p fuel s = run hb hcap padding p fuel t := congrArg _ h

end CSL.FixedPolicyNormalization
end FixedPolicyNormalization


