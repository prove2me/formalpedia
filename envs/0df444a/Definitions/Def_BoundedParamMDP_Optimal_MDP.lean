-- Prove2me | Definitions.Def_BoundedParamMDP_Optimal_MDP
-- name    : BoundedParamMDP_Optimal_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:01:49.13639+00:00
-- url     : https://prove2.me/theorems/439ef5d0-ef2b-40a5-b2c1-05aaf6231eb2
-- title:
--   Exact discounted MDP ⟨Q, A, F, R⟩, policies, the value function $V_{M,\pi}$ and the operators $VI_{M,\pi}$, $VI_{M,\alpha}$
-- statement:
--   This file fixes the exact Markov decision processes of Section 2 of Givan, Leach and Dean.
--
--   1. **Exact MDP.** An exact MDP $M=\langle Q,A,F,R\rangle$ consists of a finite set $Q$ of states, a finite set $A$ of actions, transition probabilities $F_{pq}(\alpha)=\Pr(X_{t+1}=q\mid X_t=p,\,U_t=\alpha)$ with $F_{pq}(\alpha)\ge 0$ and $\sum_{q\in Q}F_{pq}(\alpha)=1$ for every $p\in Q$, $\alpha\in A$, a real reward $R(q)$ for each state, and a discount rate $0\le\gamma<1$.
--   2. **Policies.** A policy is a map $\pi:Q\to A$; the set of all policies is $\Pi$. Together with $M$ it determines the Markov chain with transition matrix $P_\pi(p,q)=F_{pq}(\pi(p))$.
--   3. **Value function.** The value function of $\pi$ in $M$ is the expected discounted cumulative reward
--   $$
--   V_{M,\pi}(p)=\sum_{t=0}^{\infty}\gamma^{t}\,\big(P_\pi^{\,t}R\big)(p)=\sum_{t=0}^{\infty}\gamma^{t}\,\mathbb E\big[R(X_t)\mid X_0=p\big].
--   $$
--   4. **Value-iteration operators** (eq. (7)). For $v:Q\to\mathbb R$,
--   $$
--   VI_{M,\pi}(v)(p)=R(p)+\gamma\sum_{q\in Q}F_{pq}(\pi(p))\,v(q),\qquad VI_{M,\alpha}(v)(p)=R(p)+\gamma\sum_{q\in Q}F_{pq}(\alpha)\,v(q).
--   $$
--   5. **Dominance.** $V_1\le_{\mathrm{dom}}V_2$ means $V_1(q)\le V_2(q)$ for every state $q$; $V_1<_{\mathrm{dom}}V_2$ means $V_1\le_{\mathrm{dom}}V_2$ and $V_1(q)<V_2(q)$ for at least one $q$.
--
--   These are the objects every result of the paper is stated in: the members of a bounded-parameter MDP are exact MDPs of this kind.
--
--   **Formalization Note** `F p α q` is $F_{pq}(\alpha)$ (source state, action, target state). The discount rate is a field of the MDP; the members of a BMDP all carry the BMDP's discount rate. $V_{M,\pi}$ is defined by the convergent series above (the terms are bounded by $\gamma^t\max_q|R(q)|$), not as a solution of the Bellman equation (2); that it solves (2) uniquely is Theorem 3. $\le_{\mathrm{dom}}$ is Lean's pointwise order `≤` on `Q → ℝ`; $<_{\mathrm{dom}}$ is `domLT`. The paper's footnote 1 notes that more general reward functions are possible; the paper, and this file, use state rewards $R(q)$.
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), manuscript of May 22, 2000, pp. 4–6, Section 2, eqs. (1), (2), (7)

import Mathlib

open Matrix

namespace BoundedParamMDP.Optimal

/-- An exact Markov decision process `M = ⟨Q, A, F, R⟩` with discount rate `γ`
(Givan–Leach–Dean 2000, Section 2, pp. 4–5, eqs. (1)–(2)) over a finite state set `Q` and a
finite action set `A`. `F p α q` is the transition probability `F_{pq}(α)` from `p` to `q`
under action `α`; every row `F p α ·` is a probability distribution. `R q` is the real reward
of state `q`, and `0 ≤ γ < 1` is the discount rate. -/
structure MDP (Q A : Type*) [Fintype Q] where
  /-- `F p α q = F_{pq}(α) = Pr(X_{t+1} = q | X_t = p, U_t = α)` -/
  F : Q → A → Q → ℝ
  F_nonneg : ∀ p α q, 0 ≤ F p α q
  F_sum : ∀ p α, ∑ q, F p α q = 1
  /-- the reward `R(q)` of state `q` -/
  R : Q → ℝ
  /-- the discount rate `γ` -/
  γ : ℝ
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1

/-- A (deterministic, stationary) policy `π : Q → A`; the set of all policies is `Π`. -/
abbrev Policy (Q A : Type*) := Q → A

/-- The transition matrix of the Markov chain determined by `M` and the policy `π`:
the entry `(p, q)` is `F_{pq}(π(p))`. -/
def chainMatrix {Q A : Type*} [Fintype Q] (M : MDP Q A) (π : Policy Q A) : Matrix Q Q ℝ :=
  Matrix.of fun p q => M.F p (π p) q

/-- The value function `V_{M,π}` (p. 5): the expected discounted cumulative reward
`V_{M,π}(p) = ∑_{t ≥ 0} γ^t E[R(X_t) | X_0 = p]`, where `X_t` is the Markov chain with
transition matrix `chainMatrix M π`. -/
noncomputable def value {Q A : Type*} [Fintype Q] [DecidableEq Q]
    (M : MDP Q A) (π : Policy Q A) : Q → ℝ :=
  fun p => ∑' t : ℕ, M.γ ^ t * (((chainMatrix M π) ^ t) *ᵥ M.R) p

/-- The policy value-iteration operator `VI_{M,π}` of eq. (7), p. 6:
`VI_{M,π}(v)(p) = R(p) + γ ∑_{q ∈ Q} F_{pq}(π(p)) v(q)`. -/
def VIpol {Q A : Type*} [Fintype Q] (M : MDP Q A) (π : Policy Q A) (v : Q → ℝ) : Q → ℝ :=
  fun p => M.R p + M.γ * ∑ q, M.F p (π p) q * v q

/-- The action value-iteration operator `VI_{M,α}` of eq. (7), p. 6:
`VI_{M,α}(v)(p) = R(p) + γ ∑_{q ∈ Q} F_{pq}(α) v(q)`. -/
def VIact {Q A : Type*} [Fintype Q] (M : MDP Q A) (α : A) (v : Q → ℝ) : Q → ℝ :=
  fun p => M.R p + M.γ * ∑ q, M.F p α q * v q

/-- The strict dominance order `V₁ <_dom V₂` (p. 5): `V₁ ≤_dom V₂` and `V₁(q) < V₂(q)` at
some state `q`. (`V₁ ≤_dom V₂` is the pointwise order `V₁ ≤ V₂` on `Q → ℝ`.) -/
def domLT {Q : Type*} (V₁ V₂ : Q → ℝ) : Prop :=
  V₁ ≤ V₂ ∧ ∃ q, V₁ q < V₂ q

end BoundedParamMDP.Optimal


