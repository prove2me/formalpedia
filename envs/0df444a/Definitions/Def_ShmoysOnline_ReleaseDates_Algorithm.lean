-- Prove2me | Definitions.Def_ShmoysOnline_ReleaseDates_Algorithm
-- name    : ShmoysOnline_ReleaseDates_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:55:11.343374+00:00
-- url     : https://prove2.me/theorems/459a7f61-02ff-4e87-93ba-275aef81124e
-- title:
--   Observable processing and a costed uniform base scheduler
-- statement:
--   Fix a static scheduling environment $E$, a job-data encoding, and an admission-information rule. Full encodings are finite lists of real cells with a left-inverse decoder. The algorithm receives only the admission encodings of the jobs in its current batch, together with fixed environment data. Admission encodings are no longer than full encodings. For parallel machines the specified choices reveal either size and speeds, or speeds alone. Release dates and jobs outside the admitted batch are absent from both the processing port and program input.
--
--   A scheduler is a fixed finite register program with real arithmetic, comparisons, indirect addressing, jumps, local-clock access, feedback access, and processing requests. A request contains a timeout followed by triples giving job identity, operation or attempt tag, and a resource bit mask. A negative timeout means to wait until a completion. A legal request uses distinct unfinished admitted jobs on pairwise disjoint nonempty resource sets. The allocation stays fixed until feedback. An honest processing port executes exactly that allocation until the timeout or the first job or internal-operation completion and reports precisely the newly completed job/operation identities; there can be no earlier completion. An unbounded wait returns no observation exactly when no completion signal ever occurs under that request. It then cannot lead to a halting eligible execution. Adjacent recorded pieces with the same tag and resources are joined into one uninterrupted interval.
--
--   The interpreter starts with public input, zero local time, and no history. Ordinary instructions cost one unit. Processing queries additionally charge the lengths of the request, answer, and recorded pieces. Input initialization charges the admission encoding length. Physical elapsed time is separate from this computation counter. The output schedule is extracted directly from the recorded execution; it is not an arbitrary schedule chosen after computation.
--
--   For a finite batch $B$, let $N(B)$ be one plus the fixed input length plus the sum of two header cells and the full encoding length of every admitted datum. A base scheduler $\mathcal A$ is eligible with factor $\rho$ and constants $c,d$ when $c>0$ and every valid nonempty batch has a halting execution, all requests are legal, its physical completion clock equals its schedule's makespan, and
--   $$\operatorname{cost}_{\mathcal A}(B)\le c(N(B)+1)^d,\qquad C_{\max}^{\mathcal A}(B)\le\rho C_{\max}(U)$$
--   for every feasible zero-release comparator $U$. The same program, $c$, and $d$ work for all batches. A family of resource configurations $v$ may have different data types and protocols, but its uniform algorithm has one code list independent of $v$. Only the termination witness is indexed by $v$; the theorem requires the same polynomial constants across configurations. A denotational finite execution horizon witnesses termination but is never an input to the program.
--
--   This separates the scheduling information model from computational effort and allows the batching transformation to reuse exactly the same processing observations.
--
--   **Formalization Note** The explicit computation convention is a finite-cell real RAM, with unit-cost real arithmetic and addressing and separately metered finite message lengths. It does not claim a bit-complexity bound for arbitrary real numbers. The physical port has no optimization power: the honesty predicate restricts it to requested processing and first-completion feedback (including internal operations where the environment exposes them). Missing registers and feedback cells return zero, a missing instruction advances the program counter, and division by zero has the total real-arithmetic value zero; only legal halting executions satisfying the stated performance conditions qualify.
-- source:
--   Shmoys, Wein and Williamson, Scheduling Parallel Machines On-Line, SIAM J. Comput. 24(6) (1995), DOI https://doi.org/10.1137/S0097539793248317; §1 pp. 1313–1315 (PDF 1–3), Theorem 2.1 p. 1316 (PDF 4), §4.1 p. 1323 (PDF 11), processing/completion primitives.

import Definitions.Def_ShmoysOnline_ReleaseDates_Model

set_option autoImplicit false
open scoped NNReal
noncomputable section

namespace ShmoysOnline.ReleaseDates

abbrev BatchData (D : Type) := List (ℕ × D)

noncomputable def batchData {D : Type} (I : Instance D) (J : Finset ℕ) : BatchData D :=
  (J.sort (· ≤ ·)).map (fun j => (j, I.data j))

def batchInstance {D : Type} [Inhabited D] (B : BatchData D) : Instance D :=
  ⟨(B.map Prod.fst).toFinset,
    fun j => ((B.find? (fun x => x.1 == j)).map Prod.snd).getD default,
    fun _ => 0⟩

def ValidBatch {D : Type} (E : Environment D) (B : BatchData D) : Prop :=
  (B.map Prod.fst).Nodup ∧ ∀ x ∈ B, Admissible E x.2

/-- The physical executor records slices; the algorithm sees only `answer` and the
elapsed local clock. Slices are absolute in the invocation's local time. -/
structure Observation where
  elapsed : ℝ≥0
  answer : List ℝ
  pieces : List (ℕ × Slice)

structure Interaction where
  query : List ℝ
  observation : Observation

/-- An information/physics port, fixed for the base algorithm and wrapper alike.
`observe` is a causal interaction oracle: its arguments are only the admitted batch,
previous interactions and the present request. It is not given any future jobs or
release dates. The oracle implements the chosen environment's processing and
completion feedback; its observations are not unit-cost computational solutions. -/
structure Protocol (D : Type) where
  staticInput : List ℝ
  encode : D → List ℝ
  decode : List ℝ → Option D
  decode_encode : ∀ d, decode (encode d) = some d
  admission : D → List ℝ
  admission_length : ∀ d, (admission d).length ≤ (encode d).length
  observe : BatchData D → List Interaction → List ℝ → Option Observation

/-- Standard admission choices for the parallel-machine instances. Relative
machine speeds are visible in either case; only the size is hidden. -/
inductive SizeInformation where
  | known | hidden
  deriving DecidableEq

def parallelEncoding {m : ℕ} (d : ParallelJob m) : List ℝ :=
  (d.size : ℝ) :: List.ofFn (fun i => (d.speed i : ℝ))

def parallelAdmission {m : ℕ} (info : SizeInformation) (d : ParallelJob m) : List ℝ :=
  match info with
  | .known => parallelEncoding d
  | .hidden => List.ofFn (fun i => (d.speed i : ℝ))

/-- Finite-cell real-RAM input. Full encodings are used to measure cost only;
initial registers contain public encodings. -/
def inputSize {D : Type} (P : Protocol D) (B : BatchData D) : ℕ :=
  1 + P.staticInput.length + (B.map (fun x => 2 + (P.encode x.2).length)).sum

def publicInput {D : Type} (P : Protocol D) (B : BatchData D) : List ℝ :=
  P.staticInput ++ [(B.length : ℝ)] ++
    B.flatMap (fun x => [(x.1 : ℝ), ((P.admission x.2).length : ℝ)] ++ P.admission x.2)

inductive Instruction where
  | constant (dst : ℕ) (value : ℝ)
  | copy (dst src : ℕ)
  | add (dst left right : ℕ)
  | sub (dst left right : ℕ)
  | mul (dst left right : ℕ)
  | div (dst left right : ℕ)
  | load (dst address : ℕ)
  | store (address src : ℕ)
  | branchLE (left right yes no : ℕ)
  | jump (target : ℕ)
  | clock (dst : ℕ)
  | answer (dst index : ℕ)
  | query (lengthRegister : ℕ)
  | halt

structure MachineState where
  pc : ℕ
  reg : ℕ → ℝ
  now : ℝ≥0
  history : List Interaction
  cost : ℕ

noncomputable def initialState {D : Type} (P : Protocol D) (B : BatchData D) : MachineState :=
  ⟨0, fun i => (publicInput P B)[i]?.getD 0, 0, [], (publicInput P B).length⟩

def halted (code : List Instruction) (s : MachineState) : Prop :=
  code[s.pc]? = some .halt

noncomputable def machineStep {D : Type} (P : Protocol D) (B : BatchData D)
    (code : List Instruction) (s : MachineState) : MachineState := by
  classical
  let next := { s with pc := s.pc + 1, cost := s.cost + 1 }
  let put := fun (i : ℕ) (x : ℝ) => { next with reg := Function.update s.reg i x }
  exact match code[s.pc]? with
  | none => next
  | some (.halt) => s
  | some (.constant i x) => put i x
  | some (.copy i j) => put i (s.reg j)
  | some (.add i j k) => put i (s.reg j + s.reg k)
  | some (.sub i j k) => put i (s.reg j - s.reg k)
  | some (.mul i j k) => put i (s.reg j * s.reg k)
  | some (.div i j k) => put i (s.reg j / s.reg k)
  | some (.load i j) => put i (s.reg ⌊s.reg j⌋₊)
  | some (.store i j) => { next with reg := Function.update s.reg ⌊s.reg i⌋₊ (s.reg j) }
  | some (.branchLE i j yes no) => { next with pc := if s.reg i ≤ s.reg j then yes else no }
  | some (.jump target) => { next with pc := target }
  | some (.clock i) => put i s.now
  | some (.answer i j) =>
      put i (((((s.history.getLast?).map (fun x => x.observation.answer)).getD [])[⌊s.reg j⌋₊]?).getD 0)
  | some (.query l) =>
      let q := (List.range ⌊s.reg l⌋₊).map s.reg
      match P.observe B s.history q with
      | none => s
      | some o =>
        { next with
          now := s.now + o.elapsed
          history := s.history ++ [⟨q, o⟩]
          cost := s.cost + 1 + q.length + o.answer.length + o.pieces.length }

noncomputable def machineRun {D : Type} (P : Protocol D) (B : BatchData D)
    (code : List Instruction) : ℕ → MachineState
  | 0 => initialState P B
  | k + 1 => machineStep P B code (machineRun P B code k)

/-- Consecutive pieces with the same resource allocation and attempt/operation tag
are one uninterrupted interval, even if another job generated a completion event. -/
def coalesce : Profile → Profile
  | [] => []
  | a :: rest =>
      match coalesce rest with
      | [] => [a]
      | b :: tail =>
          if a.hi = b.lo ∧ a.resources = b.resources ∧ a.tag = b.tag then
            { a with hi := b.hi } :: tail
          else a :: b :: tail

/-- Actual execution recorded by the physical port. -/
def recordedSchedule (h : List Interaction) : Schedule := fun j =>
  ⟨0, coalesce ((h.flatMap (fun x => x.observation.pieces)).filterMap
    (fun x => if x.1 = j then some x.2 else none))⟩

/-- Each request is a positive timeout (negative means wait until a completion)
followed by triples (job id, operation or
attempt tag, resource bit mask). The allocation stays fixed until feedback. -/
def allocations (resources : Finset ℕ) : List ℝ → List (ℕ × ℕ × Finset ℕ)
  | j :: tag :: mask :: rest =>
      (⌊j⌋₊, ⌊tag⌋₊, resources.filter (fun i => (⌊mask⌋₊).testBit i)) ::
        allocations resources rest
  | _ => []

def requestTime (q : List ℝ) : ℝ≥0 := ((q[0]?.getD (0 : ℝ))).toNNReal

def plannedPieces (resources : Finset ℕ) (now dt : ℝ≥0)
    (q : List ℝ) : List (ℕ × Slice) :=
  (allocations resources (q.drop 1)).map (fun a =>
    (a.1, ⟨now, now + dt, a.2.2, a.2.1⟩))

def completed {D : Type} (E : Environment D) (B : BatchData D)
    (h : List Interaction) : Finset ℕ := by
  classical
  exact (B.filter (fun x =>
    WellFormed E.resources (recordedSchedule h x.1).profile ∧
      E.legal x.2 (recordedSchedule h x.1).profile)).map Prod.fst |>.toFinset

/-- Signal 0 denotes completion of the whole job; signal k+1 denotes completion
of internal operation k. Only progress of executed profiles is observable. -/
def feedback {D : Type} (E : Environment D) (B : BatchData D)
    (h : List Interaction) : Finset (ℕ × ℕ) :=
  (completed E B h).image (fun j => (j, 0)) ∪
    (B.flatMap (fun x => ((E.progress x.2 (recordedSchedule h x.1).profile).toList.map
      (fun k => (x.1, k + 1))))).toFinset

def legalRequest {D : Type} (E : Environment D) (B : BatchData D)
    (h : List Interaction) (q : List ℝ) : Prop :=
  (((q[0]?.getD (0 : ℝ))) < 0 ∨ 0 < requestTime q) ∧ (q.length - 1) % 3 = 0 ∧
  let a := allocations E.resources (q.drop 1)
  (a.map Prod.fst).Nodup ∧
  (∀ x ∈ a, x.1 ∈ (B.map Prod.fst).toFinset ∧ x.1 ∉ completed E B h ∧
    x.2.2.Nonempty) ∧ a.Pairwise (fun x y => Disjoint x.2.2 y.2.2)

def elapsedTime (h : List Interaction) : ℝ≥0 :=
  (h.map (fun x => x.observation.elapsed)).sum

def hypothetical {D : Type} (E : Environment D) (h : List Interaction)
    (q : List ℝ) (dt : ℝ≥0) : List Interaction :=
  h ++ [⟨q, ⟨dt, [], plannedPieces E.resources (elapsedTime h) dt q⟩⟩]

/-- A processing port can only execute the requested allocation until the timeout
or first completion signal, and report exactly the newly completed job/operation identities. This
prevents an oracle from doing hidden scheduling or returning unearned information. -/
def HonestProcessing {D : Type} (E : Environment D) (P : Protocol D) : Prop :=
  ∀ B h q, ValidBatch E B → legalRequest E B h q →
    match P.observe B h q with
    | none => ((q[0]?.getD (0 : ℝ))) < 0 ∧
        ∀ dt : ℝ≥0, 0 < dt →
          feedback E B (hypothetical E h q dt) \ feedback E B h = ∅
    | some o =>
      let new := feedback E B (hypothetical E h q o.elapsed) \ feedback E B h
      0 < o.elapsed ∧
      (0 ≤ (q[0]?.getD (0 : ℝ)) → o.elapsed ≤ requestTime q) ∧
      o.pieces = plannedPieces E.resources (elapsedTime h) o.elapsed q ∧
      o.answer = new.toList.flatMap (fun x => [(x.1 : ℝ), (x.2 : ℝ)]) ∧
      (((q[0]?.getD (0 : ℝ)) < 0 ∨ o.elapsed < requestTime q) → new.Nonempty) ∧
      ∀ dt : ℝ≥0, 0 < dt → dt < o.elapsed →
        feedback E B (hypothetical E h q dt) \ feedback E B h = ∅

structure BaseAlgorithm (D : Type) where
  code : List Instruction
  /-- A denotational execution horizon, never supplied to the running program. -/
  steps : BatchData D → ℕ

/-- Uniformity across visible resource configurations: code, and later its
polynomial constants, do not depend on a configuration such as the machine count.
Only the denotational termination witness is indexed by the configuration. -/
structure UniformAlgorithm (V : Type) (D : V → Type) where
  code : List Instruction
  steps : (v : V) → BatchData (D v) → ℕ

def specialize {V : Type} {D : V → Type} (A : UniformAlgorithm V D)
    (v : V) : BaseAlgorithm (D v) := ⟨A.code, A.steps v⟩

noncomputable def baseState {D : Type} (P : Protocol D) (A : BaseAlgorithm D)
    (B : BatchData D) : MachineState := machineRun P B A.code (A.steps B)

noncomputable def baseSchedule {D : Type} (P : Protocol D) (A : BaseAlgorithm D)
    (B : BatchData D) : Schedule := recordedSchedule (baseState P A B).history

/-- A real polynomial bound on actual interpreted computation. The same program,
constant and degree work for every finite admitted batch. Physical time is excluded. -/
def Eligible {D : Type} [Inhabited D] (E : Environment D) (P : Protocol D)
    (A : BaseAlgorithm D) (ρ : ℝ≥0) (c d : ℕ) : Prop :=
  0 < c ∧ ∀ B, ValidBatch E B → B ≠ [] →
    (∀ k < A.steps B, ∀ l,
      A.code[(machineRun P B A.code k).pc]? = some (.query l) →
      legalRequest E B (machineRun P B A.code k).history
        ((List.range ⌊(machineRun P B A.code k).reg l⌋₊).map
          (machineRun P B A.code k).reg)) ∧
    halted A.code (baseState P A B) ∧
    (baseState P A B).cost ≤ c * (inputSize P B + 1) ^ d ∧
    (baseState P A B).now = makespan (batchInstance B).jobs (baseSchedule P A B) ∧
    Approx E (batchInstance B) ρ (baseSchedule P A B)

end ShmoysOnline.ReleaseDates

/- BEGIN IMPORTED LEAN FOR BLIND AUDIT

import Mathlib

set_option autoImplicit false
open scoped NNReal
noncomputable section

namespace ShmoysOnline.ReleaseDates

/-- A finite piece of a job's local execution; resources may be a whole submesh.
The tag distinguishes operations or attempts within a job. -/
structure Slice where
  lo : ℝ≥0
  hi : ℝ≥0
  resources : Finset ℕ
  tag : ℕ
  deriving DecidableEq

abbrev Profile := List Slice

def span (p : Profile) : ℝ≥0 := (p.map Slice.hi).foldr max 0

def WellFormed (resources : Finset ℕ) (p : Profile) : Prop :=
  p ≠ [] ∧ ∀ s ∈ p, s.lo < s.hi ∧ s.resources.Nonempty ∧ s.resources ⊆ resources

/-- Static, job-local constraints. There are no constraints between different jobs
except exclusive use of the fixed resources. Operations within a shop job, mesh
requirements and restart/preemption rules belong to `legal`. -/
structure Environment (D : Type) where
  resources : Finset ℕ
  legal : D → Profile → Prop
  /-- Completed internal operations observable from actual processing. -/
  progress : D → Profile → Finset ℕ

def Admissible {D : Type} (E : Environment D) (d : D) : Prop :=
  ∃ p, WellFormed E.resources p ∧ E.legal d p

structure Instance (D : Type) where
  jobs : Finset ℕ
  data : ℕ → D
  release : ℕ → ℝ≥0

def Valid {D : Type} (E : Environment D) (I : Instance D) : Prop :=
  ∀ j ∈ I.jobs, Admissible E (I.data j)

structure Placement where
  start : ℝ≥0
  profile : Profile
  deriving Inhabited

abbrev Schedule := ℕ → Placement

def completion (s : Schedule) (j : ℕ) : ℝ≥0 := (s j).start + span (s j).profile

noncomputable def makespan (J : Finset ℕ) (s : Schedule) : ℝ≥0 :=
  J.sup (completion s)

def Feasible {D : Type} (E : Environment D) (I : Instance D) (s : Schedule) : Prop :=
  (∀ j ∈ I.jobs, I.release j ≤ (s j).start ∧
    WellFormed E.resources (s j).profile ∧ E.legal (I.data j) (s j).profile) ∧
  (∀ j ∈ I.jobs, ∀ k ∈ I.jobs, j ≠ k →
    ∀ a ∈ (s j).profile, ∀ b ∈ (s k).profile,
      ¬ Disjoint a.resources b.resources →
      (s j).start + a.hi ≤ (s k).start + b.lo ∨
      (s k).start + b.hi ≤ (s j).start + a.lo)

def zeroInstance {D : Type} (I : Instance D) (J : Finset ℕ) : Instance D :=
  ⟨J, I.data, fun _ => 0⟩

def restrictInstance {D : Type} (I : Instance D) (J : Finset ℕ) : Instance D :=
  { I with jobs := I.jobs ∩ J }

def translate (t : ℝ≥0) (s : Schedule) : Schedule :=
  fun j => { s j with start := t + (s j).start }

/-- Used only when every selected placement starts at or after `t`. -/
def untranslate (t : ℝ≥0) (s : Schedule) : Schedule :=
  fun j => { s j with start := (s j).start - t }

noncomputable def join (J : Finset ℕ) (s u : Schedule) : Schedule :=
  fun j => if j ∈ J then s j else u j

/-- Comparator formulation of the pure multiplicative guarantee. No arbitrary OPT
parameter, no infimum of an empty set, and no additive constant. -/
def Approx {D : Type} (E : Environment D) (I : Instance D)
    (ρ : ℝ≥0) (s : Schedule) : Prop :=
  Feasible E I s ∧ ∀ u, Feasible E I u → makespan I.jobs s ≤ ρ * makespan I.jobs u

inductive Mode where
  | nonpreemptive | restart | preemptive
  deriving DecidableEq

structure ParallelJob (m : ℕ) where
  size : ℝ≥0
  speed : Fin m → ℝ≥0

/-- No job runs on two machines at once, including canceled attempts. -/
def SerialProfile (p : Profile) : Prop :=
  p.Pairwise (fun a b => a.hi ≤ b.lo)

noncomputable def work {m : ℕ} (d : ParallelJob m) (p : Profile) : ℝ≥0 :=
  (p.map fun a => (a.hi - a.lo) * ∑ i : Fin m,
    if a.resources = {i.val} then d.speed i else 0).sum

/-- An uninterrupted successful final attempt. Earlier restart attempts are charged
resource time but contribute no surviving work. -/
def successfulAttempt {m : ℕ} (d : ParallelJob m) (a : Slice) : Prop :=
  ∃ i : Fin m, a.resources = {i.val} ∧
    (a.hi - a.lo) * d.speed i = d.size

noncomputable def parallel (m : ℕ) (mode : Mode) : Environment (ParallelJob m) where
  resources := Finset.range m
  progress _ _ := ∅
  legal d p := 0 < d.size ∧ (∀ i, 0 < d.speed i) ∧ SerialProfile p ∧
    (∀ a ∈ p, ∃ i : Fin m, a.resources = {i.val}) ∧
    match mode with
    | .nonpreemptive => ∃ a, p = [a] ∧ successfulAttempt d a
    | .restart => ∃ canceled a, p = canceled ++ [a] ∧ successfulAttempt d a ∧
        ∀ b ∈ canceled, ∃ i : Fin m, b.resources = {i.val} ∧
          (b.hi - b.lo) * d.speed i < d.size
    | .preemptive => work d p = d.size

def identicalJob {m : ℕ} (p : ℝ≥0) : ParallelJob m := ⟨p, fun _ => 1⟩
def uniformJob {m : ℕ} (p : ℝ≥0) (speed : Fin m → ℝ≥0) : ParallelJob m := ⟨p, speed⟩

structure ShopOperation where
  machine : ℕ
  duration : ℝ≥0

structure ShopJob where
  operations : List ShopOperation
  precedes : ℕ → ℕ → Prop

def finishedOperations (d : ShopJob) (p : Profile) : Finset ℕ := by
  classical
  exact ((p.filter fun a => ∃ o, d.operations[a.tag]? = some o ∧
    a.resources = {o.machine} ∧ a.hi - a.lo = o.duration).map Slice.tag).toFinset

/-- Open shops use no precedence pairs; flow/job shops encode their fixed
within-job operation order. The same finite resource interface handles all three. -/
def shop (m : ℕ) : Environment ShopJob where
  resources := Finset.range m
  progress := finishedOperations
  legal d p := d.operations ≠ [] ∧
    (∀ o ∈ d.operations, o.machine < m ∧ 0 < o.duration) ∧
    SerialProfile p ∧ p.length = d.operations.length ∧
    (∀ k < d.operations.length, ∃ a ∈ p, a.tag = k ∧
      ∃ o, d.operations[k]? = some o ∧ a.resources = {o.machine} ∧
        a.hi - a.lo = o.duration) ∧
    (∀ a ∈ p, ∀ b ∈ p, d.precedes a.tag b.tag → a.hi ≤ b.lo)

structure MeshJob where
  size : ℝ≥0
  allowed : Finset (Finset ℕ)

/-- Permitted submeshes (or other static processor subsets) are part of job data. -/
def mesh (resources : Finset ℕ) : Environment MeshJob where
  resources := resources
  progress _ _ := ∅
  legal d p := 0 < d.size ∧ ∃ a, p = [a] ∧
    a.resources ∈ d.allowed ∧ a.hi - a.lo = d.size

end ShmoysOnline.ReleaseDates

END IMPORTED LEAN FOR BLIND AUDIT -/


