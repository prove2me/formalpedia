-- Prove2me | Definitions.Def_BatchMaxService_Metric_Supplement_Interaction
-- name    : BatchMaxService_Metric_Supplement_Interaction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:00:20.244838+00:00
-- url     : https://prove2.me/theorems/6a4ea92c-5089-40a7-99ae-824452c438dd
-- title:
--   Causal feedback policies and finite interaction semantics
-- statement:
--   A deterministic policy has an arbitrary internal state, an initial-state function, an epoch-feedback update, a next-walk/timer choice, and a walk-feedback update. A complete epoch reveals its identities and time; visible feedback also reveals its locations. Blind feedback reveals only pending identities at the parked point or vertices of an executed walk. The callbacks receive no future epoch, stream tail, end-of-input flag, or hidden location.
--
--   $$\operatorname{ALG}_p(I)=\operatorname{cost}_I(\operatorname{execution}(p,I)),\qquad \operatorname{ALG}_p(I)=+\infty\ \text{if the interaction does not finish}.$$
--
--   The environment interrupts timers, delivers arrivals before equal-time actions, and bills each walk separately. Successive walks at the same time can use preceding feedback. Feasibility and termination remain predicates to establish, rather than fields of a policy. Finite evaluation fuel is a semantic device and exhaustion is explicit. This interface admits waiting, revisits, pure repositioning and arbitrary finite schedules under either rule.
-- source:
--   Lu, Ren, Liu, Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), canonical source.pdf sha256 652f1a7bbf08e31c9fd0855a098b7b7439589f55b2df3115db7c34adc0eaec34, Sections 2, 4.1 and 6, printed pp. 4–5, 9, 19–20 / PDF pp. 5–6, 10, 20–21

import Mathlib
import Definitions.Def_BatchMaxService_Metric_Supplement_Automatic
import Definitions.Def_BatchMaxService_Metric_PhaseAlgorithm

namespace BatchMaxService.Metric.Supplement

variable {n : ℕ}

inductive Visibility where
  | visible | blind
  deriving DecidableEq

/-- The complete epoch, revealed pending identities/locations, and actual services.
    A blind epoch contains no other locations. -/
structure Feedback (n : ℕ) where
  time : ℝ
  announced : Finset ℕ
  revealed : List (ℕ × Fin n)
  served : Finset ℕ

/-- A deterministic stateful causal interaction strategy. No future arrival, hidden
    location, stream tail, or end-of-input signal is an argument of these callbacks.
    Arbitrary state types include full history and a fixed private random tape. -/
structure Policy (n : ℕ) (S : Type) where
  initial : Fin n → Charged S
  receive : S → Feedback n → Charged S
  choose : ℝ → Fin n → S → Charged (Option (ServiceEvent n))
  respond : S → ServiceEvent n → Feedback n → Charged S

structure Execution (n : ℕ) (S : Type) where
  control : S
  now : ℝ
  site : Fin n
  delivered : Finset ℕ
  served : Finset ℕ
  log : Schedule n
  work : ℕ
  finished : Bool

noncomputable def reveal (I : RequestInput n) (qs : Finset ℕ) : List (ℕ × Fin n) :=
  (qs.sort (· ≤ ·)).map fun q => (q, I.location q)

/-- The environment alone reads the input locations. Complete arrivals are delivered
    before actions at equality. The forced parked batch precedes any movement. -/
noncomputable def deliver {S : Type} (v : Visibility) (r : Rule) (p : Policy n S)
    (I : RequestInput n) (ep : ArrivalEpoch) (st : Execution n S) : Execution n S := by
  classical
  let delivered := st.delivered ∪ ep.requests
  let pending := delivered \ st.served
  let atAnchor := hits I pending [st.site]
  let forced := if r = .automatic then atAnchor else ∅
  let shown := if v = .visible then ep.requests ∪ atAnchor else atAnchor
  let fb : Feedback n := ⟨ep.time, ep.requests, reveal I shown, forced⟩
  let next := p.receive st.control fb
  let log := if forced = ∅ then st.log else st.log ++ [⟨ep.time, [st.site], forced⟩]
  exact ⟨next.1, ep.time, st.site, delivered, st.served ∪ forced, log,
    st.work + next.2 + 100 * (delivered.card + n + st.log.length + 1)^3, false⟩

/-- One walk is one bill, including an empty batch. Its feedback can determine a
    following walk at the same timestamp, with no intervening arrival. -/
noncomputable def act {S : Type} (r : Rule) (p : Policy n S) (I : RequestInput n)
    (e : ServiceEvent n) (st : Execution n S) : Execution n S := by
  classical
  let found := hits I (st.delivered \ st.served) e.walk
  let batch := if r = .automatic then found else e.batch
  let actual : ServiceEvent n := { e with batch := batch }
  let fb : Feedback n := ⟨e.time, ∅, reveal I found, batch⟩
  let next := p.respond st.control actual fb
  exact ⟨next.1, e.time, e.walk.getLast?.getD st.site, st.delivered,
    st.served ∪ batch, st.log ++ [actual],
    st.work + next.2 + 100 * (st.delivered.card + n + st.log.length + e.walk.length + 1)^3,
    false⟩

/-- Fuel is solely an evaluator bound. Exhaustion is never mistaken for completion.
    Timers are interruptible; a controller never sees whether the stream is exhausted. -/
noncomputable def interact {S : Type} (v : Visibility) (r : Rule) (p : Policy n S)
    (I : RequestInput n) : ℕ → List ArrivalEpoch → Execution n S → Execution n S
  | 0, _, st => { st with finished := false }
  | k + 1, eps, st => by
      classical
      let choice := p.choose st.now st.site st.control
      let tick := { st with work := st.work + choice.2 + 10 }
      match choice.1, eps with
      | none, [] => exact { tick with finished := decide (st.served = I.ids) }
      | none, ep :: rest => exact interact v r p I k rest (deliver v r p I ep tick)
      | some e, [] => exact interact v r p I k [] (act r p I e tick)
      | some e, ep :: rest =>
          if ep.time ≤ e.time then
            exact interact v r p I k rest (deliver v r p I ep tick)
          else
            exact interact v r p I k eps (act r p I e tick)

noncomputable def initialExecution {S : Type} (p : Policy n S) (I : RequestInput n) : Execution n S :=
  let init := p.initial I.start
  ⟨init.1, 0, I.start, ∅, ∅, [], init.2, false⟩

noncomputable def evaluate {S : Type} (v : Visibility) (r : Rule) (p : Policy n S)
    (I : RequestInput n) (fuel : ℕ) : Execution n S :=
  interact v r p I fuel (arrivalStream I) (initialExecution p I)

noncomputable def Terminates {S : Type} (v : Visibility) (r : Rule) (p : Policy n S)
    (I : RequestInput n) : Prop := ∃ k, (evaluate v r p I k).finished = true

/-- The first completed finite interaction; undefined runs remain explicitly unfinished. -/
noncomputable def execution {S : Type} (v : Visibility) (r : Rule) (p : Policy n S)
    (I : RequestInput n) : Execution n S := by
  classical
  exact if h : Terminates v r p I then evaluate v r p I (Nat.find h)
    else initialExecution p I

noncomputable def ValidOn {S : Type} (v : Visibility) (r : Rule) (p : Policy n S)
    (I : RequestInput n) : Prop :=
  Terminates v r p I ∧ RuleFeasible r I (execution v r p I).log

/-- Every finite input from this start, with no laziness or efficiency restriction. -/
noncomputable def ValidPolicy {S : Type} (v : Visibility) (r : Rule) (s : Fin n)
    (p : Policy n S) : Prop := ∀ I, I.start = s → ValidOn v r p I

/-- Incomplete runs cost +∞, including on exceptional random seeds. -/
noncomputable def policyCost {S : Type} [MetricSpace (Fin n)] (v : Visibility) (r : Rule)
    (p : Policy n S) (I : RequestInput n) : ENNReal := by
  classical
  exact if Terminates v r p I then ENNReal.ofReal (cost I (execution v r p I).log) else ⊤

end BatchMaxService.Metric.Supplement


