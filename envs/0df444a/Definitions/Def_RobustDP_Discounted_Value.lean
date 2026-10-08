-- Prove2me | Definitions.Def_RobustDP_Discounted_Value
-- name    : RobustDP_Discounted_Value
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:13.596623+00:00
-- url     : https://prove2.me/theorems/893f5459-50d8-4262-8ebe-6635bea580d0
-- title:
--   Policies, the dynamic and static adversaries, and the robust values V^π_λ, V̂^π_λ and V*_λ of (19)–(20)
-- statement:
--   Fix a discounted ambiguous MDP $(\mathcal S,\mathcal A,\mathcal P,r,\lambda)$.
--
--   1. A **policy** $\pi=(d_0,d_1,\dots)$ assigns to every epoch $n$ and history $h_n$ a probability measure $d_n(h_n)\in\mathcal M(\mathcal A(s_n))$; $\Pi$ is the set of all history dependent randomized policies.
--   2. The **dynamic adversary** (Rectangularity, (2)–(3)) chooses, for every epoch $n$, history $h_n$ and admissible action $a\in\mathcal A(s_n)$, a measure $p_{h_n,a}\in\mathcal P(s_n,a)$; it may choose a different measure every time a state–action pair is met. A choice of these measures is an element of $\mathcal T^\pi=\prod_t\mathcal T^{d_t}$.
--   3. The **static adversary** chooses one $\bar p_{sa}\in\mathcal P(s,a)$ for every pair $(s,a)$ and uses it every time $(s,a)$ is encountered.
--   4. Given $\pi$, an adversary choice and $s_0=s$, the law $\mathbf P$ of the history is $\mathbf P(h_{n+1})=\mathbf P(h_n)\,d_n(h_n)(a_n)\,p_{h_n,a_n}(s_{n+1})$, and the expected discounted reward is
--   $$\mathbf E^{\mathbf P}\Big[\sum_{t=0}^\infty\lambda^t r(s_t,a_t,s_{t+1})\Big]=\sum_{t=0}^\infty\lambda^t\,\mathbf E^{\mathbf P}\big[r(s_t,a_t,s_{t+1})\big].$$
--   5. The robust value of $\pi$ (19), the static value, and the robust value function (20) are
--   $$V^\pi_\lambda(s)=\inf_{\mathbf P\in\mathcal T^\pi}\mathbf E^{\mathbf P}\Big[\sum_{t=0}^\infty\lambda^t r(s_t,d_t(h_t),s_{t+1})\Big],\qquad \hat V^\pi_\lambda(s)=\inf_{\bar p}\mathbf E^{\mathbf P_{\bar p}}\Big[\sum_{t=0}^\infty\lambda^t r(s_t,d_t(h_t),s_{t+1})\Big],\qquad V^*_\lambda(s)=\sup_{\pi\in\Pi}V^\pi_\lambda(s).$$
--   6. A sequence $(d_0,d_1,\dots)$ of deterministic Markov decision rules gives the **deterministic Markov policy** that plays $d_n(s_n)$ at epoch $n$; $\Pi_{MD}$ is the set of these. The **stationary** policy $(d,d,\dots)$ uses one rule $d$ at every epoch; a randomized Markov rule $q$ likewise gives the stationary randomized policy $(q,q,\dots)$.
--
--   These are the objects of (19)–(20) and of Theorems 4–5, Corollary 2 and Lemmas 1–3.
--
--   **Formalization Note** The epoch-$t$ expectation is computed under the law of the history $h_{t+1}$, built epoch by epoch with `PMF.bind`; epochs start at $t=0$, so the first reward is undiscounted. The series over $t$ converges absolutely because its $t$-th term is at most $\lambda^tR$ in absolute value. The infimum over adversaries and the supremum over policies are taken in $\mathbb R$; both families are nonempty and every value lies in $[-R/(1-\lambda),R/(1-\lambda)]$, so neither is a junk value. The adversary's measures for inadmissible actions are unconstrained and never used.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), pp. 8–9, (19)–(20), the dynamic and static models; Rectangularity (2)–(3), p. 4; Π_MD, p. 9, Theorem 4

import Mathlib
import Definitions.Def_RobustDP_Discounted_Model

namespace RobustDP.Discounted

variable {S A : Type*} [Countable S] [Countable A]

/-- The set `Π` of all history dependent randomized policies `π = (d_0, d_1, …)`: at every epoch
`n` and history `h_n` a probability measure `d_n(h_n) ∈ M(A(s_n))`. -/
def Policy (M : Model S A) :=
  {d : (n : ℕ) → History S A n → PMF A //
    ∀ n, ∀ h : History S A n, ∀ a ∈ (d n h).support, a ∈ M.Aset h.cur}

/-- The dynamic adversary, i.e. one element of `T^π = ∏_t T^{d_t}` (Rectangularity, (2)–(3)):
for every epoch `n`, every history `h_n` and every admissible action `a`, a conditional measure
`p_{h_n, a} ∈ P(s_n, a)` for the next state. A different measure may be chosen every time a
state–action pair is encountered. -/
def Adversary (M : Model S A) :=
  {σ : (n : ℕ) → History S A n → A → PMF S //
    ∀ n, ∀ h : History S A n, ∀ a ∈ M.Aset h.cur, σ n h a ∈ M.P h.cur a}

/-- The static adversary (p. 9): one fixed `p_{sa} ∈ P(s, a)` for every state–action pair,
used every time the pair `(s, a)` is encountered. -/
def StaticAdversary (M : Model S A) :=
  {p : S → A → PMF S // ∀ s, ∀ a ∈ M.Aset s, p s a ∈ M.P s a}

/-- The law of the history `h_n` when the process starts in `s₀ = s`, the decision maker uses
the decision rules `d` and the adversary uses the conditional measures `σ`:
`P(h_{n+1}) = P(h_n) · q_{d_n(h_n)}(a_n) · p_{h_n a_n}(s_{n+1})`, the product measure of (3). -/
noncomputable def pathLaw (d : (n : ℕ) → History S A n → PMF A)
    (σ : (n : ℕ) → History S A n → A → PMF S) (s : S) : (n : ℕ) → PMF (History S A n)
  | 0 => PMF.pure (History.init s)
  | n + 1 => (pathLaw d σ s n).bind fun h =>
      (d n h).bind fun a => (σ n h a).map fun s' => h.extend a s'

/-- The reward `r(s_n, a_n, s_{n+1})` earned at epoch `n`, read off a history `h_{n+1}`. -/
def lastReward (M : Model S A) {n : ℕ} (h : History S A (n + 1)) : ℝ :=
  M.r (h.1 (Fin.last n)).1 (h.1 (Fin.last n)).2 h.2

/-- The expected discounted reward `E^P[Σ_{t=0}^∞ λ^t r(s_t, d_t(h_t), s_{t+1})]` from
`s₀ = s` under the decision rules `d` and the adversary's choices `σ`, computed as
`Σ_{t ≥ 0} λ^t E^P[r(s_t, a_t, s_{t+1})]` (the series converges absolutely, its `t`-th term
being at most `λ^t R` in absolute value). -/
noncomputable def discountedReward (M : Model S A) (d : (n : ℕ) → History S A n → PMF A)
    (σ : (n : ℕ) → History S A n → A → PMF S) (s : S) : ℝ :=
  ∑' t : ℕ, M.lam ^ t * RobustDP.FiniteHorizon.expect (pathLaw d σ s (t + 1)) (lastReward M)

/-- The robust value of a policy in the dynamic model, (19):
`V^π_λ(s) = inf_{P ∈ T^π} E^P[Σ_{t=0}^∞ λ^t r(s_t, d_t(h_t), s_{t+1})]`. -/
noncomputable def V (M : Model S A) (π : Policy M) (s : S) : ℝ :=
  ⨅ σ : Adversary M, discountedReward M π.1 σ.1 s

/-- The value of a policy in the static model: `V̂^π_λ(s)`, the infimum over static adversaries
`p̄ = (p̄_{sa})` of the (non-robust) discounted reward of `π` under `p̄`. -/
noncomputable def Vstatic (M : Model S A) (π : Policy M) (s : S) : ℝ :=
  ⨅ p : StaticAdversary M, discountedReward M π.1 (fun _ h a => p.1 h.cur a) s

/-- The robust value function, (20): `V*_λ(s) = sup_{π ∈ Π} V^π_λ(s)`, the supremum over all
history dependent randomized policies. -/
noncomputable def Vstar (M : Model S A) (s : S) : ℝ :=
  ⨆ π : Policy M, V M π s

/-- The deterministic Markov policy `π = (d_0, d_1, …)` of a sequence of deterministic Markov
decision rules: at epoch `n` it plays `d_n(s_n)` with probability one. -/
noncomputable def markovPolicy (M : Model S A) (f : ℕ → DecisionRule M) : Policy M :=
  ⟨fun n h => PMF.pure ((f n).1 h.cur), fun n h a ha => by
    rw [PMF.support_pure, Set.mem_singleton_iff] at ha
    exact ha ▸ (f n).2 h.cur⟩

/-- The stationary deterministic policy `π = (d, d, …)`. -/
noncomputable def stationary (M : Model S A) (d : DecisionRule M) : Policy M :=
  markovPolicy M (fun _ => d)

/-- The stationary randomized Markov policy `π = (q, q, …)`: at every epoch `n` it draws the
action from `q_{s_n}`. -/
def stationaryRand (M : Model S A) (q : RandRule M) : Policy M :=
  ⟨fun _ h => q.1 h.cur, fun _ h a ha => q.2 h.cur a ha⟩

end RobustDP.Discounted


