-- Prove2me | Definitions.Def_BipartiteVRM_Competitive_Execution
-- name    : BipartiteVRM_Competitive_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:10.310479+00:00
-- url     : https://prove2.me/theorems/9393e1b8-4d0c-4b18-8e0d-cc8854be70fb
-- title:
--   Observed states and the causal RA/SA/AU event engine
-- statement:
--   Fix $\gamma>1$ and a deterministic tie rule using only observed history. A state contains the current real time, received items and their masked arrival/distance data, inserted vertices of $H$, the auxiliary matching, the immutable output log, and a cached minimum augmenting path for each free request. Readiness and the next alarm are
--
--   $$\varphi_r\le\gamma(t-a_r),\qquad t_r^{\rm rdy}=a_r+\varphi_r/\gamma,$$
--
--   with an infinite alarm when no path exists. RA inserts a request and computes its path. SA inserts a server and recomputes all free requests' paths. AU appends the ready request/terminal-server pair at the current time, augments the auxiliary matching, and recomputes the remaining paths. Every available event is processed immediately; otherwise the environment advances to the next external arrival or readiness threshold. Ties include all simultaneous arrivals and ready requests.
--
--   The local selectors are functions on received data and offered finite nonempty choices. They receive neither the ambient space nor the final input size. The execution is iterated without a size-dependent stopping fuel. Final-output and time-slice projections are defined from the first halt; the correctness statements must prove that this halt exists and gives a feasible perfect output. The module defines prefix equivalence across different metric spaces and final sizes, and the resulting causality property.
--
--   This is an operational definition of the source algorithm, not a record assuming a competitive output. A default tie rule shows that the selector type is inhabited; every theorem quantifies over all such fixed rules.
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), pp. 6–9, §2.1 and §3.1–§3.4, equations (3.2)–(3.4), Definition 3.2

import Definitions.Def_BipartiteVRM_Competitive_Paths

set_option autoImplicit false

universe uVRMexec vVRMexec

namespace BipartiteVRM.Competitive

open Classical

/-! Kuo, §3, pp. 7–9. The algorithm's local interface is View, which contains only
received data. The simulator supplies exogenous arrivals and the clock; it never supplies
an optimum, a final cardinality, future data, or an ambient metric to the local rule.
No feasibility, termination, cost, or negative-cycle result is a field of these records. -/

structure MatchEvent where
  request : ℕ
  server : ℕ
  time : ℝ

structure View where
  clock : ℝ
  visible : Finset Vertex
  inserted : Finset Vertex
  arrival : Vertex → ℝ
  distance : Vertex → Vertex → ℝ
  off : Matching
  output : List MatchEvent
  cache : ℕ → Option (List Vertex)

def initialView : View :=
  ⟨0, ∅, ∅, (fun _ => 0), (fun _ _ => 0), ∅, [], (fun _ => none)⟩

noncomputable def View.edgeTA (b : View) (e : Edge) : ℝ :=
  b.distance (.inl e.1) (.inr e.2) + |b.arrival (.inl e.1) - b.arrival (.inr e.2)|

noncomputable def View.freeRequests (b : View) : Finset ℕ := by
  classical
  exact b.inserted.toList.filterMap (fun v => match v with
    | .inl r => if saturated b.off v then none else some r
    | .inr _ => none) |>.toFinset

noncomputable def View.phi (b : View) (γ : ℝ) (r : ℕ) : WithTop ℝ :=
  match b.cache r with
  | none => ⊤
  | some P => (netCost b.edgeTA γ b.off P : WithTop ℝ)

def View.ready (b : View) (γ : ℝ) (r : ℕ) : Prop :=
  r ∈ b.freeRequests ∧ b.phi γ r ≤ (γ * (b.clock - b.arrival (.inl r)) : ℝ)

noncomputable def View.readyTime (b : View) (γ : ℝ) (r : ℕ) : WithTop ℝ :=
  match b.cache r with
  | none => ⊤
  | some P => (b.arrival (.inl r) + netCost b.edgeTA γ b.off P / γ : ℝ)

inductive EventChoice where
  | arrival (v : Vertex)
  | augmentation (r : ℕ)
  deriving DecidableEq

/-- A fixed rule may depend on all observed history. Its dependent return types say
only that it chooses an offered option, not that the algorithm is valid or competitive. -/
structure TieRule where
  path : List View → View → ℕ → (A : Finset (List Vertex)) →
    A.Nonempty → {P : List Vertex // P ∈ A}
  event : List View → View → (A : Finset EventChoice) →
    A.Nonempty → {e : EventChoice // e ∈ A}

/-- One example establishes that the type of causal tie rules is inhabited. -/
noncomputable def defaultTieRule : TieRule where
  path := fun _ _ _ _A h => ⟨Classical.choose h, Classical.choose_spec h⟩
  event := fun _ _ _A h => ⟨Classical.choose h, Classical.choose_spec h⟩

noncomputable def selectPath (γ : ℝ) (tie : TieRule) (h : List View) (b : View)
    (r : ℕ) : Option (List Vertex) := by
  classical
  let A := minimumPaths b.inserted b.edgeTA γ b.off r
  exact if hn : A.Nonempty then some (tie.path h b r A hn).val else none

noncomputable def recache (γ : ℝ) (tie : TieRule) (h : List View) (b : View) : View := by
  classical
  exact { b with cache := fun r =>
    if r ∈ b.freeRequests then selectPath γ tie h b r else none }

noncomputable def choices (γ : ℝ) (b : View) : Finset EventChoice := by
  classical
  exact ((b.visible \ b.inserted).image EventChoice.arrival) ∪
    ((b.freeRequests.filter (b.ready γ)).image EventChoice.augmentation)

/-- RA inserts only the new request's cache entry. SA and AU recompute every free
request's path. The online output is appended to, never revised. -/
noncomputable def applyEvent (γ : ℝ) (tie : TieRule) (h : List View)
    (b : View) : EventChoice → View
  | .arrival (.inl r) =>
      let b' : View := { b with inserted := insert (Sum.inl r) b.inserted }
      { b' with cache := Function.update b.cache r (selectPath γ tie h b' r) }
  | .arrival (.inr s) =>
      recache γ tie h { b with inserted := insert (.inr s) b.inserted }
  | .augmentation r =>
      match b.cache r with
      | none => b
      | some P => match terminal P with
        | none => b
        | some s => recache γ tie h
            { b with
              off := augment b.off P
              output := b.output ++ [⟨r, s, b.clock⟩] }

/-- The environment reveals precisely the items which have arrived, masking all
off-support data to zero. Revealing simultaneous arrivals does not yet insert them in H. -/
noncomputable def reveal {X : Type*} [MetricSpace X] (I : Input X) (b : View) : View := by
  classical
  let A := I.arrived b.clock
  exact { b with
    visible := A
    arrival := fun v => if v ∈ A then I.arrival v else 0
    distance := fun u v => if u ∈ A ∧ v ∈ A then
      dist (I.location u) (I.location v) else 0 }

noncomputable def nextAlarm (γ : ℝ) (b : View) : WithTop ℝ :=
  b.freeRequests.inf (b.readyTime γ)

/-- Exogenous next-arrival time is used only by the environment's clock driver. -/
noncomputable def nextArrival {X : Type*} (I : Input X) (b : View) : WithTop ℝ :=
  (I.items \ b.visible).inf (fun v => (I.arrival v : WithTop ℝ))

noncomputable def nextTime {X : Type*} (I : Input X) (γ : ℝ) (b : View) : WithTop ℝ :=
  min (nextArrival I b) (nextAlarm γ b)

/-- Internal events are processed immediately. Otherwise the environment advances
to the first external arrival or scheduled readiness threshold, revealing that time's data.
Every simultaneous arrival/AU option is offered to the fixed causal tie rule. -/
noncomputable def prepared {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (b : View) : View := by
  classical
  let b' := reveal I b
  exact if (choices γ b').Nonempty then b' else
    match nextTime I γ b' with
    | ⊤ => b'
    | (t : ℝ) => reveal I { b' with clock := max b'.clock t }

noncomputable def step {X : Type*} [MetricSpace X] (I : Input X) (γ : ℝ)
    (tie : TieRule) (h : List View) (b : View) : View := by
  classical
  let p := prepared I γ b
  let A := choices γ p
  exact if hn : A.Nonempty then applyEvent γ tie h p (tie.event h p A hn).val else p

noncomputable def halted {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (b : View) : Prop :=
  choices γ (reveal I b) = ∅ ∧ nextTime I γ (reveal I b) = ⊤

/-- Unbounded iteration; no fuel or final input size is supplied to the local rule. -/
noncomputable def history {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) : ℕ → List View
  | 0 => [initialView]
  | n + 1 =>
      let h := history I γ tie n
      let b := h.getLastD initialView
      if halted I γ b then h else h ++ [step I γ tie h b]

noncomputable def state {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) (n : ℕ) : View :=
  (history I γ tie n).getLastD initialView

/-- Only an analysis projection. No termination is presumed; the correctness theorem
must establish the existential. The fallback is never used on a valid input with γ>1. -/
noncomputable def stopIndex {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) : ℕ :=
  if h : ∃ n, halted I γ (state I γ tie n) then Nat.find h else 0

noncomputable def finalHistory {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) : List View := history I γ tie (stopIndex I γ tie)

noncomputable def finalView {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) : View :=
  (finalHistory I γ tie).getLastD initialView

noncomputable def output {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) : List MatchEvent := (finalView I γ tie).output

def eventEdges (E : List MatchEvent) : Matching :=
  (E.map (fun e => (e.request, e.server))).toFinset

def FeasibleOutput {X : Type*} (I : Input X) (E : List MatchEvent) : Prop :=
  IsPerfect I (eventEdges E) ∧
    (E.map MatchEvent.request).Nodup ∧ (E.map MatchEvent.server).Nodup ∧
    ∀ e ∈ E, max (I.arrival (.inl e.request)) (I.arrival (.inr e.server)) ≤ e.time

noncomputable def ALG {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) : ℝ :=
  ((output I γ tie).map (fun e =>
    dist (I.location (.inl e.request)) (I.location (.inr e.server)) +
      (e.time - I.arrival (.inl e.request)) + (e.time - I.arrival (.inr e.server)))).sum

noncomputable def requestWaiting {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) : ℝ :=
  ((output I γ tie).map (fun e => e.time - I.arrival (.inl e.request))).sum

noncomputable def stateAt {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) (t : ℝ) : View := by
  classical
  exact ((finalHistory I γ tie).filter (fun b => b.clock ≤ t)).getLastD initialView

noncomputable def freeAt {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) (t : ℝ) : Finset ℕ := by
  classical
  exact I.requests.filter (fun r => I.arrival (.inl r) ≤ t ∧
    ¬ saturated (stateAt I γ tie t).off (.inl r))

def stable {X : Type*} [MetricSpace X] (I : Input X) (γ : ℝ)
    (tie : TieRule) (t : ℝ) : Prop :=
  0 ≤ t ∧ (∀ v ∈ I.items, I.arrival v ≠ t) ∧
    ∀ e ∈ output I γ tie, e.time ≠ t

def SamePrefix {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (I : Input X) (J : Input Y) (t : ℝ) : Prop :=
  I.arrived t = J.arrived t ∧
    (∀ v ∈ I.arrived t, I.arrival v = J.arrival v) ∧
    (∀ u ∈ I.arrived t, ∀ v ∈ I.arrived t,
      dist (I.location u) (I.location v) = dist (J.location u) (J.location v))

noncomputable def outputThrough {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) (t : ℝ) : List MatchEvent := by
  classical
  exact (output I γ tie).filter (fun e => e.time ≤ t)

/-- Online behavior includes comparing different ambient spaces and different final
sizes. The tie rule has exactly the same View-only type on both inputs. -/
def Causal (γ : ℝ) (tie : TieRule) : Prop :=
  ∀ {X : Type uVRMexec} {Y : Type vVRMexec} [MetricSpace X] [MetricSpace Y] (I : Input X) (J : Input Y)
    (t : ℝ), 0 ≤ t → SamePrefix I J t → outputThrough I γ tie t = outputThrough J γ tie t

end BipartiteVRM.Competitive


