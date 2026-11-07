-- Prove2me | Definitions.Def_ImpatientMatching_Value
-- name    : ImpatientMatching_Value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:47:48.245243+00:00
-- url     : https://prove2.me/theorems/d3246a93-7bd1-47d3-bdc6-988095095582
-- title:
--   Admissible policies, the optimal throughput $g^*$, match counts and queue lengths
-- statement:
--   An **admissible policy** is nonanticipating, matches compatible pairs only, and makes its matches only at an arrival or at an abandonment. It may decline an available match, and queues may be unbounded. With $r^\pi(T)=\mathbb E W^\pi(T)/T$ and $g^\pi=\liminf_{T\to\infty}r^\pi(T)$, the optimal value is
--   $$g^*=\sup_\pi g^\pi ,$$
--   the supremum over admissible policies. For a unit-reward instance this is the optimal throughput. The module also defines the expected match count $\mathbb E M^\pi(T)$; the post-decision queue length $Q_i(t)$, counting agents of type $i$ that have arrived, whose patience has not expired, and that are unmatched at $t$; the pre-event queue length $Q_i(t-)$; and the occupied set $P(t)=\{i: Q^s_i(t)>0\}$ of supplier types.
--
--   This is the objective of every value statement in the mission.
--
--   **Formalization Note** The published `optimalReward` also admits zero-reward matches and matches at non-event times, so a local supremum is used. $g^*$ is taken in the extended reals; $g^*$ as a real number is its `toReal`, which is faithful because $0\le g^*\le\Lambda/2$. A zero-patience agent never counts in a queue. The published filtration also shows the virtual departure times of agents already matched; these are independent of the future.
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), §2.1–§2.2, pp.6–8; §4.3, p.13

import Definitions.Def_ImpatientMatching_Input

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DynStochMatching.Reward

namespace ImpatientMatching

/-- The event types of the system (§2.2, p.7: "each arrival or abandonment"). -/
inductive Event (n : ℕ)
  | arrival (i : Fin n)
  | abandon (i : Fin n)

/-- `ev` occurs at time `t` on the path `ω` under the policy `π`: a type-`i` agent arrives at `t`,
or an unmatched agent of a type that can wait reaches the end of its patience at `t`
(Yan–Varma, manuscript (sha256 7b1051b6…), §2.2, p.7).

**Formalization Note.** Published `departureTime` also runs for agents already matched and for
zero-patience agents. Those virtual departures are not events of the source's system, so
`abandon` requires an agent still unmatched at `t` of a type with positive patience. A zero-patience
agent's only event is its arrival. -/
noncomputable def IsEventAt {n : ℕ} (D : Instance n) (π : MatchingPolicy) (ω : RandomSeeds)
    (t : ℝ) : Event n → Prop
  | .arrival i => ∃ k, arrivalTime D.toMarkedPoissonData ω k = t ∧
      arrivalType D.toMarkedPoissonData ω k = some i
  | .abandon i => ∃ k, departureTime D ω k = t ∧
      arrivalType D.toMarkedPoissonData ω k = some i ∧
      D.lifetime i ≠ Lifetime.immediate ∧ unmatchedAt π ω k t

/-- The epochs of the real events of the system on the path `ω` under `π`. -/
def realEventTimes {n : ℕ} (D : Instance n) (π : MatchingPolicy) (ω : RandomSeeds) :
    Set ℝ≥0∞ :=
  {s | ∃ t ev, IsEventAt D π ω t ev ∧ s = ENNReal.ofReal t}

/-- An **admissible policy** of Yan–Varma, manuscript (sha256 7b1051b6…), §2.2, p.7: nonanticipating
(published `admissible`), matching compatible pairs only, and matching only at an arrival or
abandonment. Idling is allowed, and queues may be unbounded.

**Formalization Note.** Published `optimalReward` also allows zero-reward matches and matches at
non-event times, so it is not used. Published `observation` lets a policy see the virtual
departures of agents already matched; those times are independent of the future, so they act as
extra private randomization. -/
def IsPaperPolicy {n : ℕ} (D : Instance n) (π : MatchingPolicy) : Prop :=
  admissible D π ∧ ∀ᵐ ω ∂seedLaw, ∀ e, π e ω ≠ ⊤ →
    pairReward D ω e ≠ 0 ∧ π e ω ∈ realEventTimes D π ω

/-- `g∗ := sup_π g^π` of (1), p.7, for the published long-run average reward `g^π`
(`averageReward`, a liminf over real `T → ∞`), the supremum running over `IsPaperPolicy`. -/
noncomputable def gStar {n : ℕ} (D : Instance n) : EReal :=
  ⨆ π : {π : MatchingPolicy // IsPaperPolicy D π}, averageReward D π.val

/-- `g∗` of an input in a regime, as a real number. It is finite and nonnegative by
`ImpatientMatching.bounds_gStar`, so `toReal` loses nothing. -/
noncomputable def gStarReal (r : Regime) (I : MatchInput) : ℝ :=
  (gStar (toInstance r I)).toReal

/-- `r^π(T) := E W^π(T) / T` of (1), p.7. -/
noncomputable def rate {n : ℕ} (D : Instance n) (π : MatchingPolicy) (T : ℝ) : EReal :=
  ((T⁻¹ : ℝ) : EReal) * expectedReward D π T

/-- `E M^π(T)`: the expected number of pairs matched by time `T` (p.7), in `ℝ≥0∞`. With unit
rewards, it equals the expected reward on `IsPaperPolicy`. -/
noncomputable def EM (π : MatchingPolicy) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' e : ℕ × ℕ, Set.indicator
    {e : ℕ × ℕ | e.1 < e.2 ∧ π e ω ≠ ⊤ ∧ π e ω ≤ ENNReal.ofReal T} (fun _ => (1 : ℝ≥0∞)) e ∂seedLaw

/-- The post-decision queue length `Q_i(t)` (§2.1, p.7): the agents of type `i` that have arrived by
`t`, whose patience has not expired at `t`, and that are unmatched at `t`.

**Formalization Note.** `t < departureTime` makes zero-patience agents never queue: an agent who
is not matched at its arrival instant leaves at once. `Set.ncard` is `0` on an infinite set, which
happens only on a null event, since arrival times tend to infinity almost surely. -/
noncomputable def queueLen {n : ℕ} (D : Instance n) (π : MatchingPolicy) (ω : RandomSeeds)
    (t : ℝ) (i : Fin n) : ℕ :=
  Set.ncard {k | arrivalType D.toMarkedPoissonData ω k = some i ∧
    arrivalTime D.toMarkedPoissonData ω k ≤ t ∧ t < departureTime D ω k ∧ unmatchedAt π ω k t}

/-- The queue length just before `t`, `Q_i(t−)`: agents that arrived before `t`, whose patience has
not expired before `t`, and that have not been matched before `t`. -/
noncomputable def queueBefore {n : ℕ} (D : Instance n) (π : MatchingPolicy) (ω : RandomSeeds)
    (t : ℝ) (i : Fin n) : ℕ :=
  Set.ncard {k | arrivalType D.toMarkedPoissonData ω k = some i ∧
    arrivalTime D.toMarkedPoissonData ω k < t ∧ t ≤ departureTime D ω k ∧
    ∀ e : ℕ × ℕ, e.1 = k ∨ e.2 = k → π e ω = ⊤ ∨ ENNReal.ofReal t ≤ π e ω}

open Classical in
/-- `P(t) := {i ∈ V_H : Q^s_i(t) > 0}` of p.13 on the supplier block `Fin nS`, post-decision. -/
noncomputable def occupied {nS nC : ℕ} (D : Instance (nS + nC)) (π : MatchingPolicy)
    (ω : RandomSeeds) (t : ℝ) : Finset (Fin nS) :=
  Finset.univ.filter fun i => 0 < queueLen D π ω t (Fin.castAdd nC i)

end ImpatientMatching


