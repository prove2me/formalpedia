-- Prove2me | Definitions.Def_BipartiteVRM_Competitive_Supplement_Execution
-- name    : BipartiteVRM_Competitive_Supplement_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:28:23.989288+00:00
-- url     : https://prove2.me/theorems/44d79732-adcb-4e2a-b4e9-38e3ae604434
-- title:
--   Non-bipartite VRM: events RA and AU, Steps 1–2, and the run
-- statement:
--   Fix $\gamma>1$ and a tie rule. Non-bipartite VRM keeps an offline matching $M^{\mathrm{OFF}}$ and an output list $M^{\mathrm{VRM}}$, both initially empty. A request is **free** if it has arrived and is unsaturated by $M^{\mathrm{OFF}}$. After every event the algorithm recomputes, for every free $u$:
--
--   1. **Step 1.** For every unordered pair of distinct free requests $\{u,v\}$, a minimum-weight perfect matching $N_{uv}$ of $G_{uv}$ (chosen by the tie rule), and $Q_{uv}$, the component of $N_{uv}\triangle M^{\mathrm{OFF}}$ containing $u$.
--   2. **Step 2.** A free $v\ne u$ minimizing $\varphi_{M^{\mathrm{OFF}}}(Q_{uv})$ (chosen by the tie rule); then $P_u=Q_{uv}$ and $\varphi_u=\varphi_{M^{\mathrm{OFF}}}(Q_{uv})$, and $\varphi_u=+\infty$ if $u$ is the only free request.
--
--   A free $u$ is **ready** at $t$ when $\gamma(t-a_u)\ge\varphi_u$, with ready time $a_u+\varphi_u/\gamma$. **Event RA**: a request arrives and the paths of all free requests are recomputed. **Event AU**: a ready $u$ with partner $v$ outputs the pair $uv$ at the current time, sets $M^{\mathrm{OFF}}\leftarrow M^{\mathrm{OFF}}\triangle P_u$, and recomputes. The environment reveals arrivals and advances the clock to the next arrival or ready time; simultaneous options go to the tie rule. Here $D(u,v)=d(x_u,x_v)+|a_u-a_v|$ is the TA distance computed from observed data.
--
--   From the run are read off $\mathrm{ALG}$, the distance plus both requests' waiting summed over the output pairs; $W_R$, the waiting $t_r-a_r$ of every matched request; the state and free set at time $t$; stable times (no arrival and no output at $t$); $\mathrm{age}(v,t)=t-a_v$; and causality: inputs, possibly of different sizes in different metric spaces, with identical observations through $t$ give identical output through $t$.
--
--   **Formalization Note** The algorithm's interface `View` contains only received data: no final size, future arrival, optimum or ambient metric. Halting is not presumed; it is a conclusion of Theorem 5.1. The run is an unbounded iteration of the event step.
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), pp. 14–16, §5.1 (Eq. (5.1), Events RA and AU, tie rule, stable time, age), §5.2 (Steps 1–2), §5.3 (W_R)

import Definitions.Def_BipartiteVRM_Competitive_Supplement_Paths

set_option autoImplicit false

universe uNBexec vNBexec

namespace BipartiteVRM.Competitive.Supplement

open Classical
open MatchingDelays.Linear (Instance Edge edge endpoints allPairs spatial)

/-! Kuo, §5.1–§5.2, pp. 14–15: non-bipartite VRM. The algorithm's local interface is
`View`, which contains only received data: no final request count, no future arrival,
no optimum and no ambient metric. The environment supplies arrivals and the clock.
No feasibility, termination, minimality or cycle property is a field of these records. -/

/-- An output pair: the initiating request, its partner, and the matching time. -/
structure MatchEvent where
  initiator : ℕ
  partner : ℕ
  time : ℝ

/-- The cache holds, for each free request u, its chosen partner v and the edge set of
Q_uv (its minimum augmenting path P_u), or `none` (φ_u = +∞). -/
structure View where
  clock : ℝ
  visible : Finset ℕ
  inserted : Finset ℕ
  arrival : ℕ → ℝ
  distance : ℕ → ℕ → ℝ
  off : Matching
  output : List MatchEvent
  cache : ℕ → Option (ℕ × Matching)

def initialView : View :=
  ⟨0, ∅, ∅, (fun _ => 0), (fun _ _ => 0), ∅, [], (fun _ => none)⟩

/-- The TA distance D(u,v) = d(x_u,x_v) + |a_u − a_v| from observed data. -/
noncomputable def View.edgeTA (b : View) (e : Edge) : ℝ :=
  b.distance e.1 e.2 + |b.arrival e.1 - b.arrival e.2|

/-- Arrived (inserted) requests not saturated by M^OFF. -/
noncomputable def View.freeRequests (b : View) : Finset ℕ :=
  b.inserted.filter (fun v => ¬ saturated b.off v)

/-- φ_u: +∞ when no path is cached, a signed real otherwise. -/
noncomputable def View.phi (b : View) (γ : ℝ) (u : ℕ) : WithTop ℝ :=
  match b.cache u with
  | none => ⊤
  | some (_, Q) => (netCost b.edgeTA γ b.off Q : WithTop ℝ)

/-- Readiness (5.1): γ (t − a_u) ≥ φ_u. -/
def View.ready (b : View) (γ : ℝ) (u : ℕ) : Prop :=
  u ∈ b.freeRequests ∧ b.phi γ u ≤ ((γ * (b.clock - b.arrival u) : ℝ) : WithTop ℝ)

/-- Ready time a_u + φ_u / γ, +∞ when φ_u = +∞. -/
noncomputable def View.readyTime (b : View) (γ : ℝ) (u : ℕ) : WithTop ℝ :=
  match b.cache u with
  | none => ⊤
  | some (_, Q) => ((b.arrival u + netCost b.edgeTA γ b.off Q / γ : ℝ) : WithTop ℝ)

inductive EventChoice where
  | arrival (v : ℕ)
  | augmentation (u : ℕ)
  deriving DecidableEq

/-- A fixed tie rule for the choice of N_uv (Step 1), of the partner v (Step 2) and of
the next simultaneous event. It may depend on all observed history; its dependent return
types say only that it picks an offered option. -/
structure TieRule where
  matching : List View → View → ℕ → ℕ → (A : Finset Matching) →
    A.Nonempty → {N : Matching // N ∈ A}
  partner : List View → View → ℕ → (A : Finset ℕ) → A.Nonempty → {v : ℕ // v ∈ A}
  event : List View → View → (A : Finset EventChoice) →
    A.Nonempty → {e : EventChoice // e ∈ A}

/-- One example establishes that the type of tie rules is inhabited. -/
noncomputable def defaultTieRule : TieRule where
  matching := fun _ _ _ _ _A h => ⟨Classical.choose h, Classical.choose_spec h⟩
  partner := fun _ _ _ _A h => ⟨Classical.choose h, Classical.choose_spec h⟩
  event := fun _ _ _A h => ⟨Classical.choose h, Classical.choose_spec h⟩

/-- Step 1: one minimum-weight perfect matching N_uv of G_uv per unordered pair {u,v}. -/
noncomputable def stepOneMatching (γ : ℝ) (tie : TieRule) (h : List View) (b : View)
    (u v : ℕ) : Option Matching :=
  let p := min u v
  let q := max u v
  let A := minWeightPerfect b.edgeTA γ b.off p q
  if hn : A.Nonempty then some (tie.matching h b p q A hn).val else none

/-- Q_uv: the component of N_uv △ M containing u. -/
noncomputable def stepOnePath (γ : ℝ) (tie : TieRule) (h : List View) (b : View)
    (u v : ℕ) : Option Matching :=
  (stepOneMatching γ tie h b u v).map (fun N => component (symmD N b.off) u)

noncomputable def candidateCost (γ : ℝ) (tie : TieRule) (h : List View) (b : View)
    (u v : ℕ) : WithTop ℝ :=
  match stepOnePath γ tie h b u v with
  | none => ⊤
  | some Q => (netCost b.edgeTA γ b.off Q : WithTop ℝ)

/-- Step 2: a free v ≠ u minimizing φ_M(Q_uv); `none` if u is the only free request. -/
noncomputable def stepTwo (γ : ℝ) (tie : TieRule) (h : List View) (b : View) (u : ℕ) :
    Option (ℕ × Matching) :=
  let others := b.freeRequests.erase u
  let A := others.filter (fun v => (stepOnePath γ tie h b u v).isSome ∧
    ∀ w ∈ others, candidateCost γ tie h b u v ≤ candidateCost γ tie h b u w)
  if hn : A.Nonempty then
    let v := (tie.partner h b u A hn).val
    (stepOnePath γ tie h b u v).map (fun Q => (v, Q))
  else none

/-- Recompute P_u and φ_u for every free request. -/
noncomputable def recache (γ : ℝ) (tie : TieRule) (h : List View) (b : View) : View :=
  { b with cache := fun u => if u ∈ b.freeRequests then stepTwo γ tie h b u else none }

noncomputable def choices (γ : ℝ) (b : View) : Finset EventChoice :=
  ((b.visible \ b.inserted).image EventChoice.arrival) ∪
    ((b.freeRequests.filter (b.ready γ)).image EventChoice.augmentation)

/-- RA inserts the request and recomputes all free requests; AU outputs uv at the current
time, sets M^OFF ← M^OFF △ P_u and recomputes. The output is appended to, never revised. -/
noncomputable def applyEvent (γ : ℝ) (tie : TieRule) (h : List View)
    (b : View) : EventChoice → View
  | .arrival v => recache γ tie h { b with inserted := insert v b.inserted }
  | .augmentation u =>
      match b.cache u with
      | none => b
      | some (v, Q) => recache γ tie h
          { b with
            off := symmD b.off Q
            output := b.output ++ [⟨u, v, b.clock⟩] }

/-- Requests of the instance that have arrived by time t. -/
noncomputable def arrivedSet {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (t : ℝ) : Finset ℕ :=
  (Finset.range n).filter (fun v => MatchingDelays.Linear.arrival I v ≤ t)

/-- The environment reveals exactly the arrived requests, masking all other data to 0. -/
noncomputable def reveal {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (b : View) : View :=
  let A := arrivedSet I b.clock
  { b with
    visible := A
    arrival := fun v => if v ∈ A then MatchingDelays.Linear.arrival I v else 0
    distance := fun u v => if u ∈ A ∧ v ∈ A then spatial I u v else 0 }

noncomputable def nextAlarm (γ : ℝ) (b : View) : WithTop ℝ :=
  b.freeRequests.inf (b.readyTime γ)

/-- Exogenous next-arrival time, used only by the environment's clock driver. -/
noncomputable def nextArrival {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (b : View) : WithTop ℝ :=
  (Finset.range n \ b.visible).inf
    (fun v => (MatchingDelays.Linear.arrival I v : WithTop ℝ))

noncomputable def nextTime {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (b : View) : WithTop ℝ :=
  min (nextArrival I b) (nextAlarm γ b)

/-- Pending events are processed at the current time; otherwise the clock advances to
the first arrival or ready time. Every simultaneous option is offered to the tie rule. -/
noncomputable def prepared {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (b : View) : View :=
  let b' := reveal I b
  if (choices γ b').Nonempty then b' else
    match nextTime I γ b' with
    | ⊤ => b'
    | (t : ℝ) => reveal I { b' with clock := max b'.clock t }

noncomputable def step {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X) (γ : ℝ)
    (tie : TieRule) (h : List View) (b : View) : View :=
  let p := prepared I γ b
  let A := choices γ p
  if hn : A.Nonempty then applyEvent γ tie h p (tie.event h p A hn).val else p

def halted {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (b : View) : Prop :=
  choices γ (reveal I b) = ∅ ∧ nextTime I γ (reveal I b) = ⊤

/-- Unbounded iteration; no fuel or final input size is supplied to the local rule. -/
noncomputable def history {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (tie : TieRule) : ℕ → List View
  | 0 => [initialView]
  | k + 1 =>
      let h := history I γ tie k
      let b := h.getLastD initialView
      if halted I γ b then h else h ++ [step I γ tie h b]

noncomputable def state {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (tie : TieRule) (k : ℕ) : View :=
  (history I γ tie k).getLastD initialView

/-- Analysis projection only; halting is a theorem, never presumed. -/
noncomputable def stopIndex {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (tie : TieRule) : ℕ :=
  if h : ∃ k, halted I γ (state I γ tie k) then Nat.find h else 0

noncomputable def finalHistory {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (tie : TieRule) : List View := history I γ tie (stopIndex I γ tie)

noncomputable def finalView {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (tie : TieRule) : View :=
  (finalHistory I γ tie).getLastD initialView

noncomputable def output {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (tie : TieRule) : List MatchEvent := (finalView I γ tie).output

def eventEdges (E : List MatchEvent) : Matching :=
  (E.map (fun e => edge e.initiator e.partner)).toFinset

/-- ALG: distance plus the waiting time of both requests of every output pair. -/
noncomputable def ALG {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (tie : TieRule) : ℝ :=
  ((output I γ tie).map (fun e =>
    spatial I e.initiator e.partner +
      (e.time - MatchingDelays.Linear.arrival I e.initiator) +
      (e.time - MatchingDelays.Linear.arrival I e.partner))).sum

/-- W_R: the waiting time t_r − a_r of every matched request, both endpoints of every pair. -/
noncomputable def totalWaiting {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (tie : TieRule) : ℝ :=
  ((output I γ tie).map (fun e =>
    (e.time - MatchingDelays.Linear.arrival I e.initiator) +
      (e.time - MatchingDelays.Linear.arrival I e.partner))).sum

/-- The algorithm's state at physical time t: the last state of the run with clock ≤ t. -/
noncomputable def stateAt {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (tie : TieRule) (t : ℝ) : View :=
  ((finalHistory I γ tie).filter (fun b => b.clock ≤ t)).getLastD initialView

/-- R_free(t): arrived requests not saturated by the offline matching M_t. -/
noncomputable def freeAt {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (tie : TieRule) (t : ℝ) : Finset ℕ :=
  (Finset.range n).filter (fun r => MatchingDelays.Linear.arrival I r ≤ t ∧
    ¬ saturated (stateAt I γ tie t).off r)

/-- A stable time: no request arrives and no augmentation is performed at t. -/
def stable {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X) (γ : ℝ)
    (tie : TieRule) (t : ℝ) : Prop :=
  0 ≤ t ∧ (∀ v ∈ Finset.range n, MatchingDelays.Linear.arrival I v ≠ t) ∧
    ∀ e ∈ output I γ tie, e.time ≠ t

def age {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X) (v : ℕ) (t : ℝ) : ℝ :=
  t - MatchingDelays.Linear.arrival I v

/-- Two inputs (possibly of different sizes, in different metric spaces) agree through t. -/
def SamePrefix {n m : ℕ} {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (I : Instance n X) (J : Instance m Y) (t : ℝ) : Prop :=
  arrivedSet I t = arrivedSet J t ∧
    (∀ v ∈ arrivedSet I t,
      MatchingDelays.Linear.arrival I v = MatchingDelays.Linear.arrival J v) ∧
    (∀ u ∈ arrivedSet I t, ∀ v ∈ arrivedSet I t, spatial I u v = spatial J u v)

noncomputable def outputThrough {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (tie : TieRule) (t : ℝ) : List MatchEvent :=
  (output I γ tie).filter (fun e => e.time ≤ t)

/-- Online behavior: identical observations through t give identical output through t,
across different metric spaces and different final input sizes. -/
def Causal (γ : ℝ) (tie : TieRule) : Prop :=
  ∀ {n m : ℕ} {X : Type uNBexec} {Y : Type vNBexec} [MetricSpace X] [MetricSpace Y]
    (I : Instance n X) (J : Instance m Y) (t : ℝ), 0 ≤ t → SamePrefix I J t →
      outputThrough I γ tie t = outputThrough J γ tie t

end BipartiteVRM.Competitive.Supplement


