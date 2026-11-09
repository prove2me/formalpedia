-- Prove2me | Definitions.Def_BatchMaxService_Metric_PhaseAlgorithm
-- name    : BatchMaxService_Metric_PhaseAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:31:58.177926+00:00
-- url     : https://prove2.me/theorems/3a2e1d4b-3637-4b6e-b0f5-2ecfe5b0ed8d
-- title:
--   Interruptible retained-maximum phase controller and Algorithm 4
-- statement:
--   The controller stores its anchor $s$, pending away-from-anchor identities $P$, oldest arrival $\alpha$, current tree $F$ and retained maximum $E$. The environment delivers complete arrival epochs. Anchor arrivals are served immediately in a separate zero-cost event. A first away arrival starts a phase; later epochs extend $P$ without resetting $\alpha$ or $E$. After every active-phase update it computes a current tree and installs the deadline
--
--   $$E\leftarrow\max\{E,w(F)\},\qquad c=\alpha+E/\rho.$$
--
--   The environment interrupts waiting for an arrival at or before $c$, processing the entire epoch before any tied trigger. At the trigger the controller chooses the least actual phase identity, traverses the current tree with the path to its location last, serves all $P$ in one event, and moves the anchor there. Only a new phase resets the retained maximum. Algorithm 4 specializes this controller to the concrete Prim routine and $\rho=2$.
--
--   This is an operational schedule generator. OPT, certificates and competitive bounds do not enter its computation. Prefix consistency compares full action logs through a real time for any two inputs with identical revealed histories, allowing their future labels and arrivals to differ.
--
--   **Formalization Note** The environmental driver merges arrival delivery with installed timers; the controller receives no future stream tail or end-of-input signal. A finite evaluation budget of $2|Q|+1$ bounds arrival updates and positive phases; exhaustion is visible in the result and successful completion is a theorem conclusion. Work counters charge finite scans, real arithmetic/comparisons, tree work and traversal construction. Polynomial bounds quantify their coefficient and degree before the site count, metric and input.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), Sections 4.1–4.2 and 5.3, (5.14), (5.17), Algorithm 4, printed pp. 9–11, 17–19 / PDF pp. 10–12, 18–20

import Mathlib
import Definitions.Def_BatchMaxService_Metric_RequestInput
import Definitions.Def_BatchMaxService_Metric_PrimTraversal

namespace BatchMaxService.Metric

variable {n : ℕ}

/-- An environmental arrival message is a whole equal-time epoch. -/
structure ArrivalEpoch where
  time : ℝ
  requests : Finset ℕ

/-- Chronological input delivery, not information made available to the controller.
    The driver below is the environment merging delivered arrivals and installed timers. -/
noncomputable def arrivalStream (I : RequestInput n) : List ArrivalEpoch := by
  classical
  exact ((I.ids.image I.arrival).sort (· ≤ ·)).map fun t =>
    ⟨t, I.ids.filter fun q => I.arrival q = t⟩

structure PhaseState (n : ℕ) where
  anchor : Fin n
  pending : Finset ℕ
  oldest : ℝ
  retained : ℝ
  current : MetricTree n
  log : Schedule n
  work : ℕ

def initialState (I : RequestInput n) : PhaseState n :=
  ⟨I.start, ∅, 0, 0, ⟨∅, ∅⟩, [], 1⟩

/-- Only the arrived epoch and the old state are read. The oldest clock and maximum
    are reset precisely when an empty pending set becomes a new positive phase. -/
noncomputable def receiveEpoch [MetricSpace (Fin n)] (f : TreeProcedure n)
    (I : RequestInput n) (st : PhaseState n) (ep : ArrivalEpoch) : PhaseState n := by
  classical
  let hits := ep.requests.filter fun q => I.location q = st.anchor
  let away := ep.requests \ hits
  let log := if hits = ∅ then st.log else st.log ++ [⟨ep.time, [st.anchor], hits⟩]
  let P := st.pending ∪ away
  let inputWork := 20 * (st.pending.card + ep.requests.card + 1)^2 * (n + 1)^2 +
    4 * st.log.length + 5
  if P = ∅ then
    exact { st with log := log, work := st.work + inputWork }
  else
    let α := if st.pending = ∅ then ep.time else st.oldest
    let oldE := if st.pending = ∅ then 0 else st.retained
    let A := insert st.anchor (P.image I.location)
    let result := f A
    exact ⟨st.anchor, P, α, max oldE (treeWeight result.1), result.1, log,
      st.work + inputWork + result.2 + 6 * (result.1.edges.card + 1)⟩

/-- An idle controller installs no timer. Waiting is not charged computational time. -/
noncomputable def installedDeadline (ρ : ℝ) (st : PhaseState n) : Option ℝ := by
  classical
  exact if st.pending = ∅ then none else some (st.oldest + st.retained / ρ)

/-- Select the least phase identity, an actual away-from-anchor request. Traverse
    the current tree, never a historical maximum-weight tree. Anchor hits are logged separately. -/
noncomputable def fireTimer (ρ : ℝ) (I : RequestInput n) (st : PhaseState n) : PhaseState n := by
  classical
  match (st.pending.sort (· ≤ ·)).head? with
  | none => exact st
  | some q =>
      let tour := openTraversal st.current st.anchor (I.location q)
      let event : ServiceEvent n := ⟨st.oldest + st.retained / ρ, tour.1, st.pending⟩
      exact ⟨I.location q, ∅, 0, 0, ⟨∅, ∅⟩, st.log ++ [event],
        st.work + tour.2 + 10 * (st.pending.card + 1)^2 + 4 * st.log.length + 10⟩

structure RunResult (n : ℕ) where
  state : PhaseState n
  undelivered : List ArrivalEpoch
  finished : Bool

/-- The environment delivers an epoch at equality before letting a timer fire.
    The controller receives neither the stream tail nor an end-of-input signal.
    Fuel is solely a finite semantic evaluation bound; exhaustion remains visible. -/
noncomputable def drive [MetricSpace (Fin n)] (ρ : ℝ) (f : TreeProcedure n)
    (I : RequestInput n) : ℕ → List ArrivalEpoch → PhaseState n → RunResult n
  | 0, eps, st => by
      classical
      exact ⟨st, eps, decide (eps = [] ∧ st.pending = ∅)⟩
  | fuel + 1, eps, st => by
      classical
      let ticked := { st with work := st.work + 6 }
      match installedDeadline ρ st, eps with
      | none, [] => exact ⟨st, [], true⟩
      | none, ep :: rest => exact drive ρ f I fuel rest (receiveEpoch f I ticked ep)
      | some _, [] => exact drive ρ f I fuel [] (fireTimer ρ I ticked)
      | some c, ep :: rest =>
          if ep.time ≤ c then
            exact drive ρ f I fuel rest (receiveEpoch f I ticked ep)
          else
            exact drive ρ f I fuel eps (fireTimer ρ I ticked)

noncomputable def phaseRun [MetricSpace (Fin n)] (ρ : ℝ) (f : TreeProcedure n)
    (I : RequestInput n) : RunResult n :=
  drive ρ f I (2 * I.ids.card + 1) (arrivalStream I) (initialState I)

/-- Algorithm 4: concrete Prim, divisor two, and the retained-maximum controller. -/
noncomputable def algorithm4 [MetricSpace (Fin n)] (I : RequestInput n) : RunResult n :=
  phaseRun 2 primTree I

/-- Identical revealed identities, times and locations through t; future labels may differ. -/
def SameHistory (I J : RequestInput n) (t : ℝ) : Prop :=
  I.start = J.start ∧
  (∀ q, (q ∈ I.ids ∧ I.arrival q ≤ t) ↔ (q ∈ J.ids ∧ J.arrival q ≤ t)) ∧
  (∀ q ∈ I.ids, I.arrival q ≤ t →
    I.arrival q = J.arrival q ∧ I.location q = J.location q)

noncomputable def logThrough (t : ℝ) (σ : Schedule n) : Schedule n := by
  classical
  exact σ.filter fun e => e.time ≤ t

/-- Functional determinism plus explicit nonanticipation: all actions up to and including
    t depend only on the complete epochs revealed by t. -/
noncomputable def DeterministicOnline (run : RequestInput n → RunResult n) : Prop :=
  ∀ I J t, 0 ≤ t → SameHistory I J t →
    logThrough t (run I).state.log = logThrough t (run J).state.log

/-- A single uniform polynomial for all metric weights, time gaps, labels and inputs.
    C,d are outside N and the real metric. Counters charge scans, arithmetic, comparisons,
    Prim and traversal construction; waiting and environmental input delivery are excluded. -/
def PolynomialPhaseWork (ρ : ℝ) (f : ∀ n, MetricSpace (Fin n) → TreeProcedure n) : Prop :=
  ∃ C d : ℕ, 0 < C ∧ ∀ n m (I : RequestInput n),
    letI : MetricSpace (Fin n) := m
    (phaseRun ρ (f n m) I).state.work ≤ C * (I.ids.card + 1)^d * (n + 1)^d

end BatchMaxService.Metric


