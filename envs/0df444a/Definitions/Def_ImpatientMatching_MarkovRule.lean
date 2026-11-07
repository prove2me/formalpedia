-- Prove2me | Definitions.Def_ImpatientMatching_MarkovRule
-- name    : ImpatientMatching_MarkovRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:49:30.446258+00:00
-- url     : https://prove2.me/theorems/19bcca63-6994-4bf5-83e4-003c1ad8acdf
-- title:
--   Stationary Markov rules, the queue-length chain and invariant laws
-- statement:
--   A **stationary Markov rule** chooses type-level matches from the current queue lengths, the arrival or abandonment event just observed, and fresh randomization. It is **deterministic** if it ignores its randomization. A policy **follows** a rule if it is admissible and, almost surely, at its $q$-th real event its type-level matches are the rule's decision on the pre-event queue vector, the event, and a private coin reserved for that event.
--
--   Under a rule, the post-decision queue vector is a continuous-time Markov chain on $\mathbb Z_+^n$. Type $i$ arrives at rate $\lambda_i$, and a waiting agent of type $i$ abandons at rate one, so abandonments of type $i$ occur at rate $x_i$ in state $x$. Each event is followed by the rule's decision, and an unmatched zero-patience arrival leaves the state unchanged. An **invariant law** is a stationary probability vector of this generator carried by the class reachable from empty queues.
--
--   These are the objects of Lemma B.1, and the cover policy of the YES-instance bounds is such a rule.
--
--   **Formalization Note** The randomization is one $\mathrm{Exp}(1)$ coin per event. Any randomization over the countable decision set is a measurable function of such a coin. The generator has the form read by the published `holdRate`, `jumpP` and `PositiveRecurrentCT`. Stationary expectations are sums in $[0,\infty]$, so a bound cannot hold through a default value. The published `stationary` is not used, because it lets a rule read arrival order.
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), §2.2, p.8; App. B.2, pp.27–28

import Definitions.Def_ImpatientMatching_Value
import Definitions.Def_MatrixAnalytic_ProductForm_Chain

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DynStochMatching.Reward MatrixAnalytic.ProductForm

namespace ImpatientMatching

/-- A queue-length vector: one count per type (`Q(t)`, §2.1, p.7). -/
abbrev State (n : ℕ) := Fin n → ℕ

/-- A type-level decision: `d i j` for `i < j` is the number of matches between a type-`i` and a
type-`j` agent. Entries with `i ≥ j` are not read. -/
abbrev Decision (n : ℕ) := Fin n → Fin n → ℕ

/-- The number of type-`i` agents a decision uses. -/
def load {n : ℕ} (d : Decision n) (i : Fin n) : ℕ :=
  ∑ j, ((if i < j then d i j else 0) + (if j < i then d j i else 0))

/-- The queue vector just after the event and before any match: an arrival adds its agent, and an
abandonment removes its agent. -/
def preState {n : ℕ} (q : State n) : Event n → State n
  | .arrival i => Function.update q i (q i + 1)
  | .abandon i => Function.update q i (q i - 1)

/-- Whether a lifetime is zero patience. -/
def isImmediate : Lifetime → Bool
  | .immediate => true
  | .exponential _ _ => false

/-- The post-decision queue vector. A zero-patience type is never stored: an arriving agent who is
not matched at once leaves the state unchanged (§2.1, p.6; Lemma B.1, p.27). -/
def postState {n : ℕ} (D : Instance n) (q : State n) (ev : Event n) (d : Decision n) : State n :=
  fun i => if isImmediate (D.lifetime i) then 0 else preState q ev i - load d i

/-- A **stationary Markov rule** (Yan–Varma, manuscript (sha256 7b1051b6…), §2.2, p.8): it "chooses
matches using the current queue lengths, the arrival or abandonment event just observed, and fresh
randomization".

**Formalization Note.** The fresh randomization is one `Exp(1)` coin per event, the distribution
of a private coordinate of the published seed space; any randomization over the countable set of
decisions is a measurable function of such a coin. -/
structure MarkovRule (n : ℕ) where
  decide : State n → Event n → ℝ → Decision n
  measurable : ∀ q ev, Measurable (decide q ev)

/-- A deterministic stationary Markov rule (Proposition 4.4, p.12): it ignores its coin. -/
def IsDeterministicRule {n : ℕ} (rule : MarkovRule n) : Prop :=
  ∀ q ev c c', rule.decide q ev c = rule.decide q ev c'

/-- The rule never uses more agents of a type than are available after the event. -/
def IsFeasibleRule {n : ℕ} (rule : MarkovRule n) : Prop :=
  ∀ q ev c i, load (rule.decide q ev c) i ≤ preState q ev i

/-- The probability that the rule moves the state `x` to `y` at the event `ev`. -/
noncomputable def jumpProb {n : ℕ} (D : Instance n) (rule : MarkovRule n) (x : State n)
    (ev : Event n) (y : State n) : ℝ :=
  ((expMeasure 1) {c | postState D x ev (rule.decide x ev c) = y}).toReal

/-- The generator of the post-decision queue-length chain (p.8): arrivals of type `i` at rate `λ_i`,
abandonments of type `i` at rate `x_i` (rate-one patience for each waiting agent), each followed by
the rule's decision. An event that leaves the state unchanged contributes nothing.

**Formalization Note.** It has the form read by the published `holdRate`, `jumpP` and
`PositiveRecurrentCT`. The diagonal is written in closed form, so it has no infinite sum. -/
noncomputable def ruleGen {n : ℕ} (D : Instance n) (rule : MarkovRule n) (x y : State n) : ℝ :=
  if y = x then
    -(∑ i, D.arrivalRate i * (1 - jumpProb D rule x (.arrival i) x) +
      ∑ i, (x i : ℝ) * (1 - jumpProb D rule x (.abandon i) x))
  else
    ∑ i, D.arrivalRate i * jumpProb D rule x (.arrival i) y +
      ∑ i, (x i : ℝ) * jumpProb D rule x (.abandon i) y

/-- `y` is reachable from `x` along transitions of positive rate. -/
def Reaches {n : ℕ} (D : Instance n) (rule : MarkovRule n) (x y : State n) : Prop :=
  Relation.ReflTransGen (fun a b => a ≠ b ∧ 0 < ruleGen D rule a b) x y

/-- The class of states reachable from empty queues (p.9; Lemma B.1, p.27). -/
def reachable {n : ℕ} (D : Instance n) (rule : MarkovRule n) : Set (State n) :=
  {y | Reaches D rule 0 y}

/-- An invariant law of the chain on the class reachable from empty (Lemma B.1, p.27): the published
`IsStationaryCT` (`ν ≥ 0`, `Σ ν = 1`, `νQ = 0`, as absolutely convergent sums), carried by the
reachable class. -/
def IsInvariantLaw {n : ℕ} (D : Instance n) (rule : MarkovRule n) (ν : State n → ℝ) : Prop :=
  IsStationaryCT (ruleGen D rule) ν ∧ ∀ x, ν x ≠ 0 → x ∈ reachable D rule

/-- The expectation `E_ν f` of a nonnegative function of the state, in `ℝ≥0∞`. -/
noncomputable def nuMean {n : ℕ} (ν : State n → ℝ) (f : State n → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' q, ENNReal.ofReal (ν q) * f q

/-- The epochs of the real events, in order (compare the published `epoch`, which also enumerates
virtual departures). -/
noncomputable def realEpoch {n : ℕ} (D : Instance n) (π : MatchingPolicy) (ω : RandomSeeds) :
    ℕ → ℝ≥0∞
  | 0 => sInf (realEventTimes D π ω)
  | q + 1 => sInf {t | t ∈ realEventTimes D π ω ∧ realEpoch D π ω q < t}

/-- **The policy `π` follows the rule** (§2.2, p.8). `π` is an admissible policy, and almost surely,
at the `q`-th real event its type-level matches are the rule's decision on the queue vector just
before the event, the event, and the fresh coin `ω (q, 3)`.

**Formalization Note.** `ω (q, 3)` is a private coordinate of the published `observation`, independent
of the arrivals and of the patience times. Which agent of a type is taken is left to `π` and is
nonanticipating by `admissible`. The rule does not see any unexpired patience time. -/
def Realizes {n : ℕ} (D : Instance n) (rule : MarkovRule n) (π : MatchingPolicy) : Prop :=
  IsPaperPolicy D π ∧ ∀ᵐ ω ∂seedLaw, ∀ (q : ℕ) (ev : Event n), realEpoch D π ω q ≠ ⊤ →
    IsEventAt D π ω (realEpoch D π ω q).toReal ev → ∀ i j, i < j →
      actionCounts D π ω (realEpoch D π ω q).toReal i j =
        rule.decide (queueBefore D π ω (realEpoch D π ω q).toReal) ev (ω (q, 3)) i j

/-- Unit abandonment (Lemma B.1, p.27): "every agent who can wait has independent rate-one exponential
patience; all other agents have zero patience". -/
def IsUnitPatience {n : ℕ} (D : Instance n) : Prop :=
  ∀ i, D.lifetime i = Lifetime.immediate ∨ ∃ h, D.lifetime i = Lifetime.exponential 1 h

/-- `λ_w`: the total arrival rate of the types that can wait (Lemma B.1, p.27). -/
noncomputable def waitRate {n : ℕ} (D : Instance n) : ℝ :=
  ∑ i, if isImmediate (D.lifetime i) then 0 else D.arrivalRate i

/-- `N(q)`: the total population of a state (Lemma B.1, p.27). -/
def population {n : ℕ} (q : State n) : ℕ := ∑ i, q i

/-- The total-variation distance of the source (§1.3, p.6) between the law of `Q(t)` under `π`, on
the seed space, and the law `ν`, in `ℝ≥0∞` so that the supremum has no default value. -/
noncomputable def tvToLaw {n : ℕ} (D : Instance n) (π : MatchingPolicy) (ν : State n → ℝ)
    (t : ℝ) : ℝ≥0∞ :=
  ⨆ A : Set (State n), ENNReal.ofReal
    |(seedLaw {ω | queueLen D π ω t ∈ A}).toReal - (∑' q, Set.indicator A ν q)|

end ImpatientMatching


