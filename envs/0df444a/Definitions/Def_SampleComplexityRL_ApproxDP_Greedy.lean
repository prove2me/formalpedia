-- Prove2me | Definitions.Def_SampleComplexityRL_ApproxDP_Greedy
-- name    : SampleComplexityRL_ApproxDP_Greedy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:27.111599+00:00
-- url     : https://prove2.me/theorems/e40b60ac-cb0c-4d6a-be0b-d8afdea5d3c1
-- title:
--   Deterministic policies, the normalized backup operator B and greedy policies (§2.3.1, §3.1–3.2)
-- statement:
--   This module fixes the vocabulary of Chapter 3 of Kakade's thesis on top of the normalized $\gamma$-discounted model (finite state set $S$, finite nonempty action set $A$, transition kernel $P(s'\mid s,a)$, reward $r(s,a)$, discount $\gamma$).
--
--   1. **Deterministic policies.** A deterministic stationary policy $f:S\to A$ is identified with the stochastic policy that puts all mass on $f(s)$: $\pi_f(a\mid s)=1$ if $a=f(s)$ and $0$ otherwise. Values of $f$ are the values of $\pi_f$.
--   2. **One-step lookahead.** For a state vector $J\in\mathbb R^S$,
--   $$
--   (LJ)(s,a)=(1-\gamma)\,r(s,a)+\gamma\,\mathbb E_{s'\sim P(\cdot\mid s,a)}[J(s')]=(1-\gamma)\,r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)\,J(s').
--   $$
--   3. **Backup operator** (§2.3.1):
--   $$
--   [BJ](s)=\max_{a\in A}\big((1-\gamma)\,r(s,a)+\gamma\,\mathbb E_{s'\sim P(\cdot\mid s,a)}[J(s')]\big).
--   $$
--   4. **Greedy policies.** A deterministic policy $f$ is greedy with respect to state-action values $Q\in\mathbb R^{S\times A}$ if $Q(s,a)\le Q(s,f(s))$ for every state $s$ and action $a$, i.e. $f(s)\in\arg\max_a Q(s,a)$, with ties broken arbitrarily.
--
--   The backup operator drives value iteration, and the greedy relation is the policy-improvement step of both approximate value iteration and approximate policy iteration in Chapter 3. The normalized state-action value of a policy, $Q_\pi(s,a)=(1-\gamma)r(s,a)+\gamma\,\mathbb E_{s'}[V_\pi(s')]$, is exactly the lookahead of $V_\pi$.
--
--   **Formalization Note** The factor $1-\gamma$ makes all values lie in $[0,1]$ when rewards lie in $[0,1]$ (Definition 2.2.4 of the thesis). The maximum in $B$ is a `Finset.sup'` over the nonempty finite action set. Greedy policies are described by a relation rather than by a choice of argmax, so every statement about "the greedy policy" holds for every tie-breaking rule.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 22 (Definition 2.1.2, deterministic policies), p. 26 (Section 2.3.1, backup operator B), p. 39 (greedy policy), p. 40 (Section 3.2.1)

import Mathlib
import Definitions.Def_ApproxOptRL_Shared_Model

namespace SampleComplexityRL.ApproxDP

/-- A deterministic stationary policy `f : S → A` as the indicator policy
`π(a|s) = 1` if `a = f s` and `0` otherwise (Kakade 2003, §2.1, p. 22). -/
def detPolicy {S A : Type} [DecidableEq A] (f : S → A) : S → A → ℝ :=
  fun s a => if a = f s then 1 else 0

/-- The normalized one-step lookahead of a state vector `J`:
`(1 - γ) r(s,a) + γ E_{s' ∼ P(·|s,a)}[J(s')]` (Kakade 2003, p. 26 and p. 40). -/
noncomputable def lookahead {S A : Type} [Fintype S]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (J : S → ℝ) (s : S) (a : A) : ℝ :=
  (1 - γ) * r s a + γ * ∑ s', P s a s' * J s'

/-- The backup operator of §2.3.1 (Kakade 2003, p. 26):
`[BJ](s) = max_{a ∈ A} ((1 - γ) r(s,a) + γ E_{s' ∼ P(·|s,a)}[J(s')])`. -/
noncomputable def backup {S A : Type} [Fintype S] [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (J : S → ℝ) (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => lookahead P r γ J s a)

/-- `f` is a greedy (deterministic) policy with respect to the state-action values `Q`:
`f s ∈ argmax_a Q(s,a)` for every state `s`, ties broken arbitrarily (Kakade 2003, p. 39). -/
def IsGreedy {S A : Type} (Q : S → A → ℝ) (f : S → A) : Prop :=
  ∀ s a, Q s a ≤ Q s (f s)

end SampleComplexityRL.ApproxDP


