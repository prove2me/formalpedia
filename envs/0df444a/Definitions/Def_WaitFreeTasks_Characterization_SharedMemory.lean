-- Prove2me | Definitions.Def_WaitFreeTasks_Characterization_SharedMemory
-- name    : WaitFreeTasks_Characterization_SharedMemory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:29:40.242468+00:00
-- url     : https://prove2.me/theorems/8f2cde2d-3820-4522-80dd-e6a98b18a149
-- title:
--   Deterministic SWMR state machines and operational wait-free solvability
-- statement:
--   A protocol chooses arbitrary private-state and register-value types, fixed initial register contents, local initialization from the process identifier and its own input, and deterministic read, owner-write and decision transitions. No state or register size bound is imposed. A schedule is any sequence of process identifiers, and each step executes precisely one atomic operation. Nonparticipants and decided processes stutter. For every legal input face and schedule, every finite decided set is legal and respects process identifiers. Termination is
--
--   $$\forall i,\quad i\text{ participates and is scheduled infinitely often}\quad\Longrightarrow\quad\exists k:\ i\text{ has decided by step }k.$$
--
--   A task is wait-free solvable if some such protocol meets correctness and termination. No scheduling fairness is imposed on other processes, and nonparticipants reveal no inputs through shared memory. This is an operational definition, independent of PL maps, subdivisions and the asynchronous computability theorem.
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), pp. 6, 7–8 (PDF pp. 8, 9–10), §§2.1, 2.3

import Definitions.Def_WaitFreeTasks_Characterization_Task

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-! # The asynchronous read/write shared-memory model and wait-free solvability

§2.1 (printed p. 6, PDF p. 8) and §2.3 (printed pp. 7–8, PDF pp. 9–10).

`n` deterministic processes with identifiers `Fin n` (encoding `[n]`) communicate through `n`
atomic single-writer multiple-reader registers, register `i` written only by process `i` and read
by everyone. Local state spaces and register contents are arbitrary types chosen by the
protocol (unbounded memory and computational power). A step of a process is one atomic
operation: write its own register, read one register, or decide an output. The schedule is an
arbitrary infinite sequence of process identifiers (all interleavings; a process scheduled only
finitely often has crashed). -/

/-- The next atomic operation of a process: write a value to its own register, read the
register of process `j`, or decide the output vertex `o` (and halt). -/
inductive Op (n : ℕ) (R VO : Type) where
  | write (r : R)
  | read (j : Fin n)
  | decide (o : VO)

/-- A deterministic protocol for `n` processes with input vertices in `VI` and output vertices in
`VO`. Process `i` starts in state `init i v` where `v` is its own input vertex (its initial state
depends only on its identifier and its input); in state `s` its next operation is `op i s`; after
writing it moves to `afterWrite i s`, after reading the value `r` it moves to `afterRead i s r`.
All registers initially hold the fixed values `regInit`. -/
structure Protocol (n : ℕ) (VI VO : Type) where
  State : Type
  Reg : Type
  regInit : Fin n → Reg
  init : Fin n → VI → State
  op : Fin n → State → Op n Reg VO
  afterWrite : Fin n → State → State
  afterRead : Fin n → State → Reg → State

/-- A global configuration: the local state of each participating process (`none` for a process
without input, which never takes a step), the register contents, and the decision of each
process (`none` while undecided). -/
structure Config {n : ℕ} {VI VO : Type} (P : Protocol n VI VO) where
  loc : Fin n → Option P.State
  reg : Fin n → P.Reg
  dec : Fin n → Option VO

/-- The initial configuration for the input assignment `inp` (`inp i = some v`: process `i`
participates with input vertex `v`). -/
def Config.initial {n : ℕ} {VI VO : Type} (P : Protocol n VI VO) (inp : Fin n → Option VI) :
    Config P where
  loc := fun i => (inp i).map (P.init i)
  reg := P.regInit
  dec := fun _ => none

/-- One atomic step of process `i`. A process without input or that has already decided does
nothing. -/
def Config.step {n : ℕ} {VI VO : Type} {P : Protocol n VI VO} (C : Config P) (i : Fin n) :
    Config P :=
  match C.dec i, C.loc i with
  | some _, _ => C
  | none, none => C
  | none, some s =>
    match P.op i s with
    | Op.write r =>
      { C with reg := Function.update C.reg i r,
               loc := Function.update C.loc i (some (P.afterWrite i s)) }
    | Op.read j =>
      { C with loc := Function.update C.loc i (some (P.afterRead i s (C.reg j))) }
    | Op.decide o =>
      { C with dec := Function.update C.dec i (some o) }

/-- The configuration after the first `k` steps of the schedule `sch`. -/
def run {n : ℕ} {VI VO : Type} (P : Protocol n VI VO) (inp : Fin n → Option VI)
    (sch : ℕ → Fin n) : ℕ → Config P
  | 0 => Config.initial P inp
  | k + 1 => (run P inp sch k).step (sch k)

/-- The input assignment of the input simplex `σ`: process `i` gets the vertex of `σ` coloured
`i`, if any (unique because `I` is chromatic); processes with no vertex in `σ` do not
participate. -/
noncomputable def inputOf {n : ℕ} {VI VO : Type} (T : Task n VI VO) (σ : Finset VI) :
    Fin n → Option VI :=
  fun i => if h : ∃ v ∈ σ, T.idI v = i then some h.choose else none

/-- The set of output vertices decided in a configuration. -/
noncomputable def Config.decided {n : ℕ} {VI VO : Type} {P : Protocol n VI VO} (C : Config P) :
    Finset VO :=
  Finset.univ.biUnion fun i => (C.dec i).toFinset

/-- `P` **solves** the task `T` wait-free (§2.1, §2.3): for every input simplex `σ ∈ I` (its
processes participate, the others do not, and nobody knows the participating set) and every
schedule,
1. (validity) after every finite prefix, each decided process `i` has decided a vertex of colour
   `i`, and the set of decided vertices, if nonempty, is a simplex of `Δ(σ)`;
2. (wait-freedom) every participating process that is scheduled infinitely often decides after
   finitely many steps, whatever the other processes do (including stopping forever). -/
def Solves {n : ℕ} {VI VO : Type} (T : Task n VI VO) (P : Protocol n VI VO) : Prop :=
  (∀ σ ∈ T.I.faces, ∀ sch : ℕ → Fin n, ∀ k : ℕ,
      (∀ i o, (run P (inputOf T σ) sch k).dec i = some o → T.idO o = i) ∧
      ((run P (inputOf T σ) sch k).decided.Nonempty →
        (run P (inputOf T σ) sch k).decided ∈ T.Δ σ)) ∧
  (∀ σ ∈ T.I.faces, ∀ sch : ℕ → Fin n, ∀ i : Fin n, (∃ v ∈ σ, T.idI v = i) →
      (∀ N : ℕ, ∃ k, N ≤ k ∧ sch k = i) →
      ∃ k, (run P (inputOf T σ) sch k).dec i ≠ none)

/-- A task is **wait-free solvable** in the asynchronous read/write model with `n` processes if
some deterministic protocol solves it wait-free. -/
def WaitFreeSolvable {n : ℕ} {VI VO : Type} (T : Task n VI VO) : Prop :=
  ∃ P : Protocol n VI VO, Solves T P

end WaitFreeTasks.Characterization


