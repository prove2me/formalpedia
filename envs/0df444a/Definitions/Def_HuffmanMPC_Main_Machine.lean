-- Prove2me | Definitions.Def_HuffmanMPC_Main_Machine
-- name    : HuffmanMPC_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:23:12.25102+00:00
-- url     : https://prove2.me/theorems/3639cd49-f579-4472-83ef-7fabdb8bfb10
-- title:
--   §1 and §7 — the MPC machine: word programs, rounds, local and aggregate memory, and work
-- statement:
--   The Massively Parallel Computation model is made operational. A fixed program, a finite list of instructions, runs on every machine. Each machine has a word memory of $w$-bit words, an inbox, an outbox and an output list. The instructions are those of the published word RAM `TrulySubcubicAPSP.Instr` (constant $1$, add, subtract, multiply, indirect load and store, branch on negative, accept, reject), plus send a word to a machine, receive the next inbox word, read the inbox length, emit an output word, free a cell, quotient, remainder, left shift and finish. Accept is the barrier that ends a machine's round.
--
--   A configuration assigns a local state to each machine. A step either executes one instruction of one machine (work $1$) or, when every machine has reached the barrier or halted, delivers all pending messages to their destinations (one round, work proportional to the messages). An execution is a finite sequence of such steps. Local words count allocated cells, queued messages, output words and three control words. The input is distributed in an arbitrary legal placement: any assignment of the indexed input words to machines within the local budget. Each machine starts with $n$, the machine count, its identifier and its local input length.
--
--   A run within budgets $(r,s,M,W)$ is, for every legal placement, an execution that halts everywhere with the required output, at most $r$ rounds and $W$ work, peak local words at most $s$ on every machine and peak total words at most $M$, and addresses within the word range.
--
--   **Formalization Note** Memory cells cost space even when zero; messages in transit count against both sender and receiver budgets. No instruction computes an optimum, sorts or routes for free.
--
--   The local-space budget is at least the eleven words occupied by an empty initial machine. Together with the input-capacity inequality this ensures a legal placement exists even for an empty input.
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, MPC model, §1, p. 1 (PDF 2); word model for frequency input, §7, p. 31 (PDF 32)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM

set_option autoImplicit false

namespace HuffmanMPC.Main

/-- Finite syntax, extending the published RAM instructions with message I/O and
barriers, and the queue-length query `inboxSize`.  No instruction evaluates a mathematical optimum or invokes sorting. -/
inductive MPCInstruction where
  | ram (i : TrulySubcubicAPSP.Instr)
  | send (destination payload : ℤ)
  | receive (target : ℤ)
  | inboxSize (target : ℤ)
  | emit (source : ℤ)
  | free (address : ℤ)
  | quotient (target lhs rhs : ℤ)
  | remainder (target lhs rhs : ℤ)
  | shiftLeft (target lhs rhs : ℤ)
  | finish

abbrev MPCProgram := List MPCInstruction

/-- The finite allocation is independent of the values: zero cells also cost space.
Inbox, outbox and output are counted, and a send retains its payload until exchange. -/
structure LocalState (w : ℕ) where
  pc : ℕ
  allocated : Finset ℤ
  memory : ℤ → BitVec w
  inbox : List (BitVec w)
  outbox : List (ℕ × BitVec w)
  output : List (BitVec w)
  waiting : Bool
  halted : Bool

def readWord {w : ℕ} (s : LocalState w) (a : ℤ) : BitVec w :=
  if a ∈ s.allocated then s.memory a else 0

def writeWord {w : ℕ} (s : LocalState w) (a : ℤ) (v : BitVec w) : LocalState w :=
  { s with
    allocated := insert a s.allocated
    memory := (fun j => if j = a then v else s.memory j), pc := s.pc + 1 }

/-- Exact local one-instruction transition. Accept is the communication barrier;
reject and falling off the program are stuck rather than successful answers. -/
def localStep {w : ℕ} (p : MPCProgram) (s : LocalState w) : Option (LocalState w) :=
  if s.waiting || s.halted then none else
  match p[s.pc]? with
  | none => none
  | some (.ram i) =>
    match i with
    | .one a => some (writeWord s a 1)
    | .add a b c => some (writeWord s a (readWord s b + readWord s c))
    | .sub a b c => some (writeWord s a (readWord s b - readWord s c))
    | .mul a b c => some (writeWord s a (readWord s b * readWord s c))
    | .load a b => some (writeWord s a (readWord s (readWord s b).toInt))
    | .store a b => some (writeWord s (readWord s a).toInt (readWord s b))
    | .bltz a j => some {s with pc := if (readWord s a).toInt < 0 then j else s.pc + 1}
    | .accept => some {s with waiting := true, pc := s.pc + 1}
    | .reject => none
  | some (.send d a) => some {s with
      pc := s.pc + 1
      outbox := s.outbox ++ [((readWord s d).toNat, readWord s a)]}
  | some (.receive a) =>
    match s.inbox with
    | [] => none
    | x :: xs => some {writeWord s a x with inbox := xs}
  | some (.inboxSize a) => some (writeWord s a (BitVec.ofNat w s.inbox.length))
  | some (.emit a) => some {s with
      pc := s.pc + 1
      output := s.output ++ [readWord s a]}
  | some (.free a) => some {s with pc := s.pc + 1, allocated := s.allocated.erase a}
  | some (.quotient a b c) => some (writeWord s a
      (BitVec.ofNat w ((readWord s b).toNat / (readWord s c).toNat)))
  | some (.remainder a b c) => some (writeWord s a
      (BitVec.ofNat w ((readWord s b).toNat % (readWord s c).toNat)))
  | some (.shiftLeft a b c) => some (writeWord s a
      (if (readWord s c).toNat < w then
        BitVec.ofNat w ((readWord s b).toNat * 2^(readWord s c).toNat) else 0))
  | some .finish => some {s with halted := true, pc := s.pc + 1}

/-- Address-value storage, queues, output, and finite control registers in words. -/
def localWords {w : ℕ} (s : LocalState w) : ℕ :=
  2*s.allocated.card + s.inbox.length + 2*s.outbox.length + s.output.length + 3

abbrev Configuration (w machines : ℕ) := Fin machines → LocalState w

/-- Deterministic all-to-all delivery, ordered by sender and its send order. -/
def exchange {w machines : ℕ} (c : Configuration w machines) : Configuration w machines :=
  fun i => {c i with
    waiting := false
    outbox := []
    inbox := (c i).inbox ++ (List.finRange machines).flatMap
      (fun j => ((c j).outbox.filter (fun m => m.1 == i.val)).map Prod.snd)}

/-- One step either executes one local instruction or exchanges all pending
messages at a global barrier. The scheduler serializes independent local actions;
only exchanges count as rounds, and every instruction counts as work. -/
inductive MachineStep {w machines : ℕ} (p : MPCProgram) :
    Configuration w machines → Configuration w machines → ℕ → ℕ → Prop where
  | local (c : Configuration w machines) (i : Fin machines) (s : LocalState w)
      (h : localStep p (c i) = some s) :
      MachineStep p c (Function.update c i s) 0 1
  | communication (c : Configuration w machines)
      (ready : ∀ i, (c i).waiting = true ∨ (c i).halted = true)
      (active : ∃ i, (c i).waiting = true)
      (destinations : ∀ i, ∀ m ∈ (c i).outbox, m.1 < machines) :
      MachineStep p c (exchange c) 1 (∑ i, 2*(c i).outbox.length)

/-- An actual finite execution with all intermediate configurations exposed. -/
structure MPCExecution (w machines : ℕ) (p : MPCProgram) where
  length : ℕ
  states : Fin (length + 1) → Configuration w machines
  rounds : Fin length → ℕ
  work : Fin length → ℕ
  valid : ∀ j : Fin length,
    MachineStep p (states ⟨j.val, by omega⟩) (states ⟨j.val+1, by omega⟩)
      (rounds j) (work j)

def MPCExecution.totalRounds {w machines : ℕ} {p : MPCProgram}
    (e : MPCExecution w machines p) : ℕ := ∑ j, e.rounds j

def MPCExecution.totalWork {w machines : ℕ} {p : MPCProgram}
    (e : MPCExecution w machines p) : ℕ := ∑ j, e.work j

def MPCExecution.spaceBound {w machines : ℕ} {p : MPCProgram}
    (e : MPCExecution w machines p) (localSpace aggregate : ℝ) : Prop :=
  (∀ j i, (localWords (e.states j i) : ℝ) ≤ localSpace) ∧
  (∀ j, ((∑ i, localWords (e.states j i)) : ℝ) ≤ aggregate)

def MPCExecution.wordBound {w machines : ℕ} {p : MPCProgram}
    (e : MPCExecution w machines p) : Prop :=
  ∀ j i, ∀ a ∈ (e.states j i).allocated, a.natAbs < 2^(w-1)

/-- Fixed headers n, machine count, machine id and local input size, followed by
raw words. The list lengths and zero-valued input symbols all count toward storage. -/
def initialLocal (w n machines id : ℕ) (xs : List (ℕ × ℕ)) : LocalState w :=
  let data := [n, machines, id, xs.length] ++ xs.flatMap (fun z => [z.1, z.2])
  { pc := 0, allocated := (Finset.range data.length).image (fun j : ℕ => (j : ℤ)),
    memory := fun a => BitVec.ofNat w (data.getD a.toNat 0),
    inbox := [], outbox := [], output := [], waiting := false, halted := false }

/-- All legal distributions, with no prescribed initial sorting or aggregation. -/
def LegalPlacement (input : List ℕ) {machines : ℕ} (xs : Fin machines → List (ℕ × ℕ))
    (space : ℝ) : Prop :=
  ((List.finRange machines).flatMap xs).Perm (input.zipIdx.map (fun z => (z.2, z.1))) ∧
    ∀ i, (4*(xs i).length + 11 : ℕ) ≤ space

/-- Observable output remains distributed and is charged as part of local space. -/
def finalOutput {w machines : ℕ} (c : Configuration w machines) : List ℕ :=
  (List.finRange machines).flatMap fun i => (c i).output.map BitVec.toNat

/-- Program correctness and all four resources concern the same trace.  The
machine count, word size and budgets are supplied externally by asymptotic binders;
no correctness field is part of the program syntax. -/
def RunsMPC (p : MPCProgram) (input : List ℕ) (output : List ℕ → Prop)
    (n machines w : ℕ) (r s mem work : ℝ) : Prop :=
  0 < machines ∧ 0 < w ∧ 11 ≤ s ∧
  input.length ≤ machines * ((⌊s⌋₊ - 11) / 4) ∧
  n < 2^w ∧ machines < 2^w ∧ input.length < 2^w ∧
  (∀ v ∈ input, v < 2^w) ∧ ∀ xs : Fin machines → List (ℕ × ℕ),
    LegalPlacement input xs s → ∃ e : MPCExecution w machines p,
      e.states 0 = (fun i => initialLocal w n machines i.val (xs i)) ∧
      (∀ i, (e.states (Fin.last e.length) i).halted = true) ∧
      output (finalOutput (e.states (Fin.last e.length))) ∧
      (e.totalRounds : ℝ) ≤ r ∧ (e.totalWork : ℝ) ≤ work ∧
      e.spaceBound s mem ∧ e.wordBound

end HuffmanMPC.Main


