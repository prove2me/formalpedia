-- Prove2me | Definitions.Def_ObliviousAdaptive172_Parallel_PrivateTapeExecution
-- name    : ObliviousAdaptive172_Parallel_PrivateTapeExecution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:04.398717+00:00
-- url     : https://prove2.me/theorems/cd8c7ad5-5ab0-4200-aaa4-226314a15246
-- title:
--   Causal private-tape execution, actual work, storage, and output-only policies
-- statement:
--   A primitive has a private control space $Q$, an arbitrary private random seed $r\in R$, an initial control, and an instruction rule. On initialization or one delivered update, an instruction performs internal work, writes or erases a witness handle at a natural-number address, or finishes with “no” or a configuration in an arbitrary space $W$. The return register is address zero. One delivered action and each executed instruction are charged. The bounded interpreter suspends inside an unfinished action; the unbounded semantic observer selects its first return. Divergence costs $+\infty$ and publishes no answer.
--
--   For a probability measure $\mu$ on the seed space, the assertion of success probability at least $p$ means that there is a measurable event $E$ with
--
--   $$
--   \mu(E)\ge p,\qquad \forall r\in E,\ \text{the stated run property holds}.
--   $$
--
--   An adversary chooses the next update, or stops, from its independent seed, its own past updates, and the public answer history. It sees initialization's answer at time zero. A blocked computation supplies no “no” answer and receives no further updates. Legal policies choose only permitted updates. Neither work, private memory nor unfinished-copy state is observable. Regularity means only that induced length, property, “no”, cost-threshold and computed-certificate events are measurable; it supplies no probability or correctness bound.
--
--   The fixed-output predicate says that once a configuration is published, every legal continuation publishes that identical configuration. The two transfer-event predicates record “no” before the intermediate property and a valid configuration in actual memory at its first hit. These are event specifications, not assumed implementations. This execution layer supplies the common operational meaning of Claim 3.1 and Algorithm 2.
-- source:
--   Shiri Chechik, Inbal Hadad, From Oblivious to Adaptive Adversaries: Black-Box Reductions for Monotone Dynamic Problems with Applications to Cuts, Distances, and Clustering, STOC 2027 submission #172 (October 2026), p. 7, §3 preamble (PDF p. 9); p. 9, Claim 3.1 (PDF p. 11); pp. 27–28, Appendix A.1 (PDF pp. 29–30)

import Mathlib
import Definitions.Def_ObliviousAdaptive172_Parallel_HistoryModel
set_option autoImplicit false

namespace ObliviousAdaptive172.Parallel

open MeasureTheory

/-- One charged primitive instruction: internal work, writing a witness handle, or
finishing the current action. Witness construction is primitive work, never wrapper work. -/
inductive Instruction (Q W : Type)
  | work (next : Q)
  | save (next : Q) (address : ℕ) (witness : W)
  | erase (next : Q) (address : ℕ)
  | finish (next : Q) (answer : Option W)

/-- An interruptible, causal private-tape state machine. `none` is initialization;
`some u` is an update. The instruction can inspect this action and persistent private
control, but cannot inspect a future input or the adversary's tape. One instruction costs
one unit in the primitive's own computational model. No termination or correctness field. -/
structure PrivateTapeExecution (U W R Q : Type) where
  boot : Q
  instruction : R → Option U → Q → Instruction Q W

structure Configuration (Q W : Type) where
  control : Q
  memory : ℕ → Option W

/-- Result of actually taking at most `fuel` instructions. Running out of fuel retains
the suspended control and cannot manufacture an answer. -/
structure Slice (Q W : Type) where
  config : Configuration Q W
  answer : Option W
  returned : Bool
  ticks : ℕ

variable {U W R Q : Type}

def runFor (A : PrivateTapeExecution U W R Q) (r : R) (input : Option U) :
    ℕ → Configuration Q W → Slice Q W
  | 0, s => ⟨s, none, false, 0⟩
  | k + 1, s =>
    match A.instruction r input s.control with
    | .work q =>
      let z := runFor A r input k {s with control := q}
      {z with ticks := z.ticks + 1}
    | .save q a w =>
      let z := runFor A r input k ⟨q, Function.update s.memory a (some w)⟩
      {z with ticks := z.ticks + 1}
    | .erase q a =>
      let z := runFor A r input k ⟨q, Function.update s.memory a none⟩
      {z with ticks := z.ticks + 1}
    | .finish q out =>
      ⟨⟨q, Function.update s.memory 0 out⟩, out, true, 1⟩

/-- Untruncated semantics select the first completed execution, not a supplied cost.
An infinite computation has no result. Only this semantic observer is noncomputable;
the compiler below executes `runFor` with bounded fuel. -/
noncomputable def runToReturn (A : PrivateTapeExecution U W R Q) (r : R)
    (input : Option U) (s : Configuration Q W) : Option (Slice Q W) := by
  classical
  exact if h : ∃ k, (runFor A r input k s).returned = true then
    some (runFor A r input (Nat.find h) s) else none

structure Snapshot (Q W : Type) where
  config : Option (Configuration Q W)
  answer : Option W
  work : ℕ∞

/-- Delivery of an action costs one unit; all its internal instructions are charged.
A divergent update is absorbing and has infinite cost, rather than zero cost. -/
noncomputable def perform (A : PrivateTapeExecution U W R Q) (r : R)
    (input : Option U) (s : Snapshot Q W) : Snapshot Q W :=
  match s.config with
  | none => ⟨none, none, ⊤⟩
  | some q => match runToReturn A r input q with
    | none => ⟨none, none, ⊤⟩
    | some z => ⟨some z.config, z.answer, s.work + (1 + z.ticks : ℕ)⟩

noncomputable def machineRun (A : PrivateTapeExecution U W R Q) (r : R)
    (h : List U) : Snapshot Q W :=
  h.foldl (fun s u => perform A r (some u) s)
    (perform A r none ⟨some ⟨A.boot, fun _ => none⟩, none, 0⟩)

def Snapshot.Stored (s : Snapshot Q W) (w : W) : Prop :=
  ∃ q a, s.config = some q ∧ q.memory a = some w

/-- An outer `none` is a blocked computation, not a published “no”. -/
def Snapshot.observation (s : Snapshot Q W) : Option (Option W) :=
  if s.config.isSome then some s.answer else none

/-- Probability is certified by an actual measurable event contained in the stated
good runs. This avoids treating an outer measure lower bound as a success probability. -/
def WithProbability {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : ℝ) (good : Ω → Prop) : Prop :=
  ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal p ≤ μ E ∧ ∀ r ∈ E, good r

/-- A randomized output-observing policy. It knows its own previous updates and all
published answers (including time zero), but no costs, internal storage, or copy states.
`none` stops the finite stream; thus dead ends do not make policy quantification empty. -/
abbrev OutputPolicy (U W Ξ : Type) := Ξ → List U → List (Option W) → Option U

def AdmissiblePolicy {Ξ : Type}
    (M : HistoryModel U) (π : OutputPolicy U W Ξ) : Prop :=
  ∀ η h o u, M.Legal h → π η h o = some u → M.permitted h u

structure Interaction (U W : Type) where
  history : List U
  observations : List (Option W)
  stopped : Bool

/-- Causal interaction, one public answer per completed action. `observe h` is a
semantic prefix observer: this recurrence does not re-execute any earlier update. -/
def interact {Ξ : Type} (observe : List U → Option (Option W)) (π : OutputPolicy U W Ξ)
    (η : Ξ) : ℕ → Interaction U W
  | 0 => match observe [] with
    | none => ⟨[], [], true⟩
    | some out => ⟨[], [out], false⟩
  | t + 1 =>
    let s := interact observe π η t
    if s.stopped then s else
      match π η s.history s.observations with
      | none => {s with stopped := true}
      | some u =>
        let h := s.history ++ [u]
        match observe h with
        | none => ⟨h, s.observations, true⟩
        | some out => ⟨h, s.observations ++ [out], false⟩

/-- The standing probability convention, made explicit for arbitrary tape and update
spaces: induced property, answer, cost, and computed-certificate events are measurable.
This is solely event regularity: it imposes NO probability bound, runtime bound,
existence of a witness, soundness, or independence after conditioning. `ready` below
is evaluated from actual emitted/stored handles, never supplied as an oracle. -/
def ExecutionEventsMeasurable {Ω : Type} [MeasurableSpace Ω]
    (history : Ω → List U) (answer : Ω → List U → Option W)
    (cost : Ω → List U → ℕ∞) (P : List U → Prop)
    (ready : Ω → List U → Prop) : Prop :=
  (∀ k : ℕ, MeasurableSet {z | (history z).length = k}) ∧
  (∀ t : ℕ, MeasurableSet {z | P ((history z).take t)}) ∧
  (∀ t : ℕ, MeasurableSet {z | answer z ((history z).take t) = none}) ∧
  (∀ t k : ℕ, MeasurableSet {z | cost z ((history z).take t) ≤ k}) ∧
  (∀ t : ℕ, MeasurableSet {z | ready z ((history z).take t)})

/-- Exactly the source's single switch, with an arbitrary structural configuration. -/
def FixedOutput (M : HistoryModel U) (A : PrivateTapeExecution U W R Q) : Prop :=
  ∀ r h e w, M.Legal (h ++ e) → (machineRun A r h).answer = some w →
    (machineRun A r (h ++ e)).answer = some w

def NoEarly (A : PrivateTapeExecution U W R Q) (r : R) (P' : List U → Prop)
    (h : List U) : Prop :=
  ∀ t ≤ h.length, ¬ P' (h.take t) → (machineRun A r (h.take t)).answer = none

def StoredAtHit (A : PrivateTapeExecution U W R Q) (r : R)
    (P' : List U → Prop) (valid : List U → W → Prop) (h : List U) : Prop :=
  ∀ t, firstHit P' h = some t →
    ∃ w, (machineRun A r (h.take t)).Stored w ∧ valid (h.take t) w

end ObliviousAdaptive172.Parallel


