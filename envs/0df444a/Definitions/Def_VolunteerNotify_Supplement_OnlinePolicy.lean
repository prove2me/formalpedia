-- Prove2me | Definitions.Def_VolunteerNotify_Supplement_OnlinePolicy
-- name    : VolunteerNotify_Supplement_OnlinePolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:23:42.251443+00:00
-- url     : https://prove2.me/theorems/8394b687-267c-4827-9b15-df73c70d0af5
-- title:
--   §3, Definition 3 — online policies (randomized, non-anticipating) and their $\mathrm{POL}_{\mathcal I}$
-- statement:
--   An **online policy** for an instance $\mathcal I=(\lambda,p,g)$ of the online volunteer notification problem decides, in every period $t$, which subset $N_t\subseteq[V]$ of volunteers to notify. It knows $\lambda$, $p$ and $g$, and it may randomize. Its choice at $t$ may depend only on what has happened so far: the arrivals $A_1,\dots,A_t$ (including the current one), its own earlier choices $N_1,\dots,N_{t-1}$, the volunteers who responded in periods $1,\dots,t-1$, and the sets of active volunteers in periods $1,\dots,t$. Formally it is a rule giving, for every period and every such history, a probability distribution over subsets of $[V]$.
--
--   Under a policy, the process evolves as in §3: a task of type $s$ arrives at $t$ with probability $\lambda_{s,t}$, independently across periods; a volunteer is notified at $t$ if a task arrives and she is in $N_t$; an active notified volunteer responds with probability $p_{v,s}$ and, whether or not she responds, becomes inactive for an independent $Z\sim g$ periods; inactive volunteers ignore notifications and are unaffected; the task is completed if some notified active volunteer responds. $\mathrm{POL}_{\mathcal I}(\pi)$ is the expected number of completed tasks.
--
--   This is the class over which Theorem 2 and Lemmas 5–6 bound the performance of every online policy. It contains the paper's policies, which do not observe states, and the larger class used in the proofs of Claim 4 and of Lemma 6.
--
--   **Formalization Note** The process reuses the published primitives (`Prim`, `primMass`) and dynamics (`nextActive`, `respondents`, `completedCount`) of `VolunteerNotify.Process`, with the notification coordinates replaced by the policy's choices (`withNotif`). The history (`observe`) fills only the periods the policy has seen. Because all randomness is discrete, $\mathrm{POL}$ is a `tsum` over primitives and notified sets of their joint probability times the number of completed tasks; it is defined for every instance and every policy.
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, §3, pp.9–10; Definition 3, p.12; proof of Claim 4, p.38; fn. 24, p.42

import Mathlib
import Definitions.Def_VolunteerNotify_Instance
import Definitions.Def_VolunteerNotify_Process

namespace VolunteerNotify.Supplement

variable {V S T : ℕ}

/-- What an online policy may have seen when it chooses whom to notify at a period `t`
(Manshadi–Rodilitz, arXiv:2002.08474v7, §3, pp.9–10; proof of Claim 4, p.38; fn. 24, p.42): the
arrivals `A_m`, the set of active volunteers at `m`, the volunteers it notified at `m`, and the
volunteers who responded at `m`.

**Formalization Note.** The fields are functions on all periods; `observe` fills only the
periods the policy has seen (`m ≤ t` for arrivals and activity, `m < t` for its own notifications
and the responses) and puts `none` / `∅` elsewhere. The policy also receives `t`, so it knows which
entries are filled. -/
structure History (V S T : ℕ) where
  /-- `arrival m` is the task type arriving at `m`, `none` for no task. -/
  arrival : Fin T → Option (Fin S)
  /-- `active m` is the set of volunteers active at `m`. -/
  active : Fin T → Finset (Fin V)
  /-- `notified m` is the set the policy chose to notify at `m`. -/
  notified : Fin T → Finset (Fin V)
  /-- `responded m` is the set of volunteers who responded at `m`. -/
  responded : Fin T → Finset (Fin V)

/-- The realization of the published primitives `Prim` in which the notification coordinates are
replaced by the policy's choices `N`: `v` is "notified about type `s` at `t`" iff `v ∈ N t`. With
it the published dynamics `nextActive`, `IsActive`, `respondents` and `completedCount` describe the
process under the policy: a volunteer is notified at `t` iff a task arrives and `v ∈ N t`; an
active notified volunteer is inactive for `Z_{v,t}` periods; an inactive one is unaffected
(arXiv:2002.08474v7, p.9). -/
def withNotif (a : Prim V S T → ℕ) (N : Fin T → Finset (Fin V)) : Prim V S T → ℕ
  | .notify v _ t => if v ∈ N t then 1 else 0
  | i => a i

open scoped Classical in
/-- The history observed at period `t` on the primitives `a` when the policy notifies `N`.
It depends only on the arrivals up to `t`, on `N` before `t`, and on the response coins and
inter-activity times of earlier notifications through the responses and activity states they
caused: the policy never sees future arrivals, future response coins or the draws `Z` themselves. -/
noncomputable def observe (a : Prim V S T → ℕ) (N : Fin T → Finset (Fin V)) (t : Fin T) :
    History V S T where
  arrival m := if m ≤ t then arrivalOf a m else none
  active m := if m ≤ t then Finset.univ.filter (fun v => IsActive (withNotif a N) v m) else ∅
  notified m := if m < t then N m else ∅
  responded m := if m < t then respondents (withNotif a N) m else ∅

/-- An **online policy** for the instance `I` (arXiv:2002.08474v7, §3, pp.9–10: upon an arrival
the platform makes an immediate, irrevocable decision which subset of volunteers to notify, knowing
`λ, p, g`): at each period `t` it draws the set `N ⊆ [V]` to notify with probability
`rule t h N`, where `h` is the observed history (`History`, `observe`).

**Formalization Note.** This is a randomized, non-anticipating (behavioural) rule. It may use
the instance, which it depends on, the arrivals up to and including `t`, its own past choices, the
past responses and the activity states of all volunteers up to `t`. The class contains the paper's
policies, which do not observe states (p.10), and the larger class of the proofs of Claim 4 (p.38)
and fn. 24 (p.42). Randomization by an internal seed is covered: a perfect-recall finite-horizon
mixed rule has a behavioural equivalent. -/
structure OnlinePolicy (I : Instance V S T) where
  /-- `rule t h N` is the probability of notifying exactly `N` at `t` after the history `h`. -/
  rule : Fin T → History V S T → Finset (Fin V) → ℝ
  rule_nonneg : ∀ t h N, 0 ≤ rule t h N
  rule_sum_one : ∀ t h, ∑ N, rule t h N = 1

/-- The probability of the primitive realization `a` (arrivals, response coins and inter-activity
times; product of the published laws `primMass`). The notification coordinates have law
`primMass I 0`, a point mass at `0`; `withNotif` overwrites them with the policy's choices. -/
noncomputable def primWeight (I : Instance V S T) (a : Prim V S T → ℕ) : ℝ :=
  ∏ i, primMass I 0 i (a i)

/-- The probability that the policy `π` notifies the sets `N` on the primitives `a`. -/
noncomputable def policyWeight {I : Instance V S T} (π : OnlinePolicy I) (a : Prim V S T → ℕ)
    (N : Fin T → Finset (Fin V)) : ℝ :=
  ∏ t, π.rule t (observe a N t) (N t)

/-- `POL_I` of an online policy `π`, arXiv:2002.08474v7, Definition 3, p.12: the expected number of
completed tasks (a task is completed iff some notified active volunteer responds, p.10), on the
canonical discrete probability space of the primitives `a` and the notified sets `N`, whose joint
law is `primWeight I a * policyWeight π a N`.

**Formalization Note.** The space is countable, so the expectation is a `tsum`. For an instance
the weights are nonnegative, sum to `1`, and `completedCount ≤ T`, so the family is summable and
the `tsum` is the true expectation; it is defined for every instance and every policy, so a
hypothesis "π is `c`-competitive" is never vacuous. -/
noncomputable def polValue (I : Instance V S T) (π : OnlinePolicy I) : ℝ :=
  ∑' z : (Prim V S T → ℕ) × (Fin T → Finset (Fin V)),
    primWeight I z.1 * policyWeight π z.1 z.2 * completedCount (withNotif z.1 z.2)

end VolunteerNotify.Supplement


