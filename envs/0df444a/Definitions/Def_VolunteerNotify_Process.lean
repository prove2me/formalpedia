-- Prove2me | Definitions.Def_VolunteerNotify_Process
-- name    : VolunteerNotify_Process
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:37:38.289216+00:00
-- url     : https://prove2.me/theorems/b8bb19e3-c8e7-4b7f-a5b8-80abd11d28f7
-- title:
--   §3, Algorithm 1, Definitions 3–4 — the online process, $\mathrm{POL}_{\mathcal I}$ and the contribution of a volunteer
-- statement:
--   Fix an instance and notification probabilities $w$. The **online process** lives on a probability space carrying the following primitives, jointly independent:
--
--   1. the arrival $A_t\in\{0,\dots,S\}$, with $P(A_t=s)=\lambda_{s,t}$, where $0$ means no task;
--   2. notification coins $N_{v,s,t}\in\{0,1\}$ with $P(N_{v,s,t}=1)=w_{v,s,t}$;
--   3. response coins $R_{v,s,t}\in\{0,1\}$ with $P(R_{v,s,t}=1)=p_{v,s}$;
--   4. inter-activity times $Z_{v,t}$ with law $g$, the time volunteer $v$ stays away if notified at $t$.
--
--   All volunteers start active. Let $b_v(t)$ be the first period at or after which $v$ is active, so $b_v(1)=1$ and $v$ is active at $t$ iff $b_v(t)\le t$. Volunteer $v$ is notified at $t$ iff a task of some type $s$ arrives and $N_{v,s,t}=1$. If $v$ is active and notified at $t$, then $b_v(t+1)=t+Z_{v,t}$, whether or not she responds; otherwise $b_v(t+1)=b_v(t)$. Let $\mathrm{Resp}(t)$ be the set of active, notified volunteers with $R_{v,A_t,t}=1$. The task at $t$ is completed iff $\mathrm{Resp}(t)\ne\emptyset$, and
--   $$
--   \mathrm{POL}_{\mathcal I}=\mathbb E\Bigl[\sum_{t=1}^T\mathbb 1\{\mathrm{Resp}(t)\neq\emptyset\}\Bigr],\qquad
--   \text{contribution of }v=\mathbb E\Bigl[\sum_{t=1}^T\mathbb 1\{v=\min\mathrm{Resp}(t)\}\Bigr].
--   $$
--   The online phase of Algorithm 1 is the case $w=\tilde x$; it never looks at volunteers' states or responses.
--
--   **Formalization Note** All primitives are $\mathbb N$-valued so that a single `iIndepFun` covers them, and the law of each is a mass function `primMass`. Periods in `nextActive` are 0-based. The counts are bounded by $T$ and measurable, so the expectations are genuine integrals.
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, §3, pp.9–10; Definition 3, p.12; Definition 4, p.13; Algorithm 1, p.17; Appendix A.1, p.34

import Mathlib
import Definitions.Def_VolunteerNotify_Instance

open MeasureTheory ProbabilityTheory

namespace VolunteerNotify

variable {V S T : ℕ}

/-- The index set of the primitive randomness of the online phase, Manshadi–Rodilitz,
arXiv:2002.08474v7, pp.9–10, 13, 17, 34: the arrival `A_t`, the notification coin `N_{v,s,t}`, the
response coin `R_{v,s,t}`, and the inter-activity time `Z_{v,t}` of volunteer `v` if notified at
`t` (p.34). -/
inductive Prim (V S T : ℕ) : Type
  | arrival (t : Fin T)
  | notify (v : Fin V) (s : Fin S) (t : Fin T)
  | respond (v : Fin V) (s : Fin S) (t : Fin T)
  | gap (v : Fin V) (t : Fin T)
  deriving DecidableEq, Fintype

/-- The mass function of a `{0, 1}`-valued coin with success probability `a`. -/
def coinMass (a : ℝ) : ℕ → ℝ
  | 0 => 1 - a
  | 1 => a
  | _ => 0

/-- The law of each primitive, as a mass function on `ℕ`, when volunteer `v` is notified about a
task of type `s` at `t` with probability `w v s t`.

**Formalization Note.** `A_t` takes the value `0` for "no task", with probability `λ_{0,t}`, and
`n + 1` for type `n`, so the paper's types `1, …, S` are its values. -/
def primMass (I : Instance V S T) (w : Decision V S T) : Prim V S T → ℕ → ℝ
  | .arrival t, 0 => I.noTask t
  | .arrival t, n + 1 => if h : n < S then I.lam ⟨n, h⟩ t else 0
  | .notify v s t, n => coinMass (w v s t) n
  | .respond v s _, n => coinMass (I.p v s) n
  | .gap _ _, n => I.g n

/-- The task type arriving at `t` on a realization `a` of the primitives; `none` is "no task". -/
def arrivalOf (a : Prim V S T → ℕ) (t : Fin T) : Option (Fin S) :=
  match a (.arrival t) with
  | 0 => none
  | n + 1 => if h : n < S then some ⟨n, h⟩ else none

/-- Volunteer `v` is notified at `t` on the realization `a`: a task of some type `s` arrives and
the coin `N_{v,s,t}` is `1`. The policy does not look at volunteers' states. -/
def IsNotified (a : Prim V S T → ℕ) (v : Fin V) (t : Fin T) : Prop :=
  ∃ s, arrivalOf a t = some s ∧ a (.notify v s t) = 1

open scoped Classical in
/-- `nextActive a v n` is `b_v`, the first period at or after which `v` is active again, seen at
the start of period `n`, on the realization `a`: `b_v(1) = 1` because all volunteers start active
(arXiv:2002.08474v7, p.9); if `v` is active (`b_v(t) ≤ t`) and notified at `t`, then
`b_v(t + 1) = t + Z_{v,t}`, whether or not `v` responds; otherwise `b_v(t + 1) = b_v(t)`, because
an inactive volunteer is "unaffected by additional notifications" (p.9).

**Formalization Note.** Periods here are 0-based: `n` is paper period `n + 1`, and the differences
of periods are unchanged. -/
noncomputable def nextActive (a : Prim V S T → ℕ) (v : Fin V) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if h : n < T then
      if nextActive a v n ≤ n ∧ IsNotified a v ⟨n, h⟩ then n + a (.gap v ⟨n, h⟩)
      else nextActive a v n
    else nextActive a v n

/-- Volunteer `v` is active at `t` on the realization `a`. -/
def IsActive (a : Prim V S T → ℕ) (v : Fin V) (t : Fin T) : Prop :=
  nextActive a v t ≤ t

open scoped Classical in
/-- `Resp(t)`: the volunteers who are active and notified at `t` and respond to the task, the
coin `R_{v,A_t,t}` being `1`. -/
noncomputable def respondents (a : Prim V S T → ℕ) (t : Fin T) : Finset (Fin V) :=
  Finset.univ.filter fun v =>
    IsActive a v t ∧ ∃ s, arrivalOf a t = some s ∧ a (.notify v s t) = 1 ∧ a (.respond v s t) = 1

open scoped Classical in
/-- The number of completed tasks on the realization `a`: the task at `t` is completed iff at
least one notified volunteer responds (arXiv:2002.08474v7, p.10). -/
noncomputable def completedCount (a : Prim V S T → ℕ) : ℝ :=
  ∑ t, if (respondents a t).Nonempty then 1 else 0

open scoped Classical in
/-- The number of tasks completed by `v` on the realization `a` under the index-based priority
scheme, arXiv:2002.08474v7, Definition 4, p.13: of those who respond, the one with the smallest
index completes the task. The scheme only attributes a completed task (fn. 15). -/
noncomputable def completedBy (a : Prim V S T → ℕ) (v : Fin V) : ℝ :=
  ∑ t, if v ∈ respondents a t ∧ ∀ u < v, u ∉ respondents a t then 1 else 0

/-- The online process of instance `I` under the policy that, when a task of type `s` arrives at
`t`, notifies each volunteer `v` independently with probability `w v s t`, on a probability space
`(Ω, μ)`: measurable primitives, jointly independent as one family, with the laws `primMass`.
Algorithm 1 is the case `w = x̃`.

**Formalization Note.** The primitives are all `ℕ`-valued so that one `iIndepFun` covers them. The
statement over all such spaces specializes to any space on which the paper's model is realized.
`N_{v,s,t}` is drawn for every `s`, but only `s = A_t` is used. -/
structure Process (I : Instance V S T) (w : Decision V S T) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) where
  /-- The primitive random variables. -/
  prim : Prim V S T → Ω → ℕ
  measurable_prim : ∀ i, Measurable (prim i)
  indep : iIndepFun prim μ
  law : ∀ i n, μ.real (prim i ⁻¹' {n}) = primMass I w i n

/-- `POL_I`, arXiv:2002.08474v7, Definition 3, p.12: the expected number of completed tasks. -/
noncomputable def POL {I : Instance V S T} {w : Decision V S T} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (P : Process I w μ) : ℝ :=
  ∫ ω, completedCount (fun i => P.prim i ω) ∂μ

/-- The contribution of `v`, arXiv:2002.08474v7, p.13, Lemma 2, p.17: the expected number of tasks
`v` completes under the index-based priority scheme. -/
noncomputable def contribution {I : Instance V S T} {w : Decision V S T} {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} (P : Process I w μ) (v : Fin V) : ℝ :=
  ∫ ω, completedBy (fun i => P.prim i ω) v ∂μ

end VolunteerNotify


