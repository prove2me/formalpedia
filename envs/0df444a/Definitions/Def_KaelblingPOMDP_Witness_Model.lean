-- Prove2me | Definitions.Def_KaelblingPOMDP_Witness_Model
-- name    : KaelblingPOMDP_Witness_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:44.876543+00:00
-- url     : https://prove2.me/theorems/7413aa12-4023-477e-bc5f-d0c8c56a57ac
-- title:
--   The POMDP ⟨S, A, T, R, Ω, O⟩ with discount γ, t-step policy trees, their values V_p(s) and V_p(b) = b · α_p, V_t, Pr(o | a, b), SE(b, a, o) and p_new (§2.1, §3.1, §3.3, §4.1, §4.4.2)
-- statement:
--   This file fixes the model of Kaelbling, Littman and Cassandra and the objects built from it.
--
--   A **partially observable Markov decision process** is a tuple $\langle S, A, T, R, \Omega, O\rangle$ together with a discount factor $\gamma$, where $S$, $A$ and $\Omega$ are finite sets of states, actions and observations, $T(s, a, s')$ is the probability of moving to $s'$ when action $a$ is taken in state $s$, $R(s, a)$ is the expected immediate reward, and $O(s', a, o)$ is the probability of observing $o$ after taking action $a$ and landing in state $s'$. The **standing hypotheses** are that every $T(s, a, \cdot)$ and every $O(s', a, \cdot)$ is a probability distribution and that
--   $$0 < \gamma \le 1;$$
--   $\gamma = 1$ is the undiscounted finite-horizon case. Rewards may have any sign.
--
--   A **t-step policy tree** is a single action when $t = 1$; for $t \ge 2$ it consists of a root action $a(p)$ and, for each observation $o$, a $(t-1)$-step subtree $o(p)$. The **value** of a tree is defined by the recursion
--   $$V_p(s) = R(s, a(p)) + \gamma \sum_{s' \in S} T(s, a(p), s') \sum_{o \in \Omega} O(s', a(p), o)\, V_{o(p)}(s'),$$
--   with $V_p(s) = R(s, a(p))$ for a 1-step tree. A **belief state** is a probability vector $b$ on $S$, and the value of $p$ at $b$ is $V_p(b) = \sum_s b(s) V_p(s) = b \cdot \alpha_p$ with $\alpha_p = \langle V_p(s_1), \dots, V_p(s_n)\rangle$. The optimal $t$-step value is $V_t(b) = \max_{p} V_p(b)$ over the finite set of all $t$-step trees.
--
--   The **state estimator** is
--   $$SE(b, a, o)(s') = \frac{O(s', a, o) \sum_{s} T(s, a, s')\, b(s)}{\Pr(o \mid a, b)}, \qquad \Pr(o \mid a, b) = \sum_{s'} O(s', a, o) \sum_s T(s, a, s')\, b(s).$$
--
--   Finally, for a $t$-step tree $p$, an observation $o$ and a $(t-1)$-step tree $p'$, the tree $p_{\mathrm{new}}$ agrees with $p$ in its action and all its subtrees except for observation $o$, for which $o(p_{\mathrm{new}}) = p'$.
--
--   These are the objects in which the witness theorem and its lemmas are stated.
--
--   **Formalization Note** `PolicyTree A Ω n` is the type of $(n+1)$-step trees: an action for $n = 0$ and a pair (root action, subtree function) otherwise; it carries `Fintype` and `Nonempty` instances. `value M p s` is $V_p(s)$, `valueAt M p b` is $V_p(b)$, `optValue M n` is $V_{n+1}$, `obsProb` is $\Pr(o \mid a, b)$, `stateEstimator` is $SE$ and `PolicyTree.replace p o p'` is $p_{\mathrm{new}}$. Belief states are the points of `stdSimplex ℝ S`. When $\Pr(o \mid a, b) = 0$ the state estimator divides by zero and Lean returns the zero vector; statements that need a belief state assume $\Pr(o \mid a, b) \ne 0$.
-- source:
--   Kaelbling, Littman, Cassandra, Planning and acting in partially observable stochastic domains, Artificial Intelligence 101:99–134 (1998), DOI 10.1016/S0004-3702(98)00023-X, pp. 101–102 (§2.1), p. 105 (§3.1), p. 107 (§3.3), pp. 108–110 (§4.1), p. 115 (§4.4.2)

import Mathlib

namespace KaelblingPOMDP.Witness

open Finset

universe u

/-- A partially observable Markov decision process `⟨S, A, T, R, Ω, O⟩` with a discount factor `γ`
(Kaelbling, Littman, Cassandra, *Planning and acting in partially observable stochastic domains*,
Artificial Intelligence 101:99–134 (1998), §2.1 pp. 101–102 and §3.1 p. 105).

* `T s a s'` is the transition probability `T(s, a, s')` of landing in `s'` after action `a` in `s`;
* `R s a` is the expected immediate reward `R(s, a)`;
* `O s' a o` is `O(s', a, o)`, the probability of observing `o` after taking `a` and landing in `s'`
  (argument order: resulting state, action, observation, as on p. 105);
* `γ` is the discount factor.

The standing hypotheses on these data are the separate predicate `POMDP.IsValid`. -/
structure POMDP (S A Ω : Type u) where
  /-- transition function `T(s, a, s')` -/
  T : S → A → S → ℝ
  /-- reward function `R(s, a)` -/
  R : S → A → ℝ
  /-- observation function `O(s', a, o)` -/
  O : S → A → Ω → ℝ
  /-- discount factor `γ` -/
  γ : ℝ

variable {S A Ω : Type u}

/-- The standing hypotheses of the paper's finite-horizon setting: `T(s, a, ·)` and `O(s', a, ·)` are
probability distributions (`T : S × A → Π(S)`, p. 101; `O : S × A → Π(Ω)`, p. 105), and the discount
factor satisfies `0 < γ ≤ 1` (p. 102: "we will also use a discount factor; when it has value one, it
is equivalent to the simple finite-horizon case"). The rewards may have any sign. -/
structure POMDP.IsValid [Fintype S] [Fintype Ω] (M : POMDP S A Ω) : Prop where
  T_nonneg : ∀ s a s', 0 ≤ M.T s a s'
  T_sum : ∀ s a, ∑ s', M.T s a s' = 1
  O_nonneg : ∀ s' a o, 0 ≤ M.O s' a o
  O_sum : ∀ s' a, ∑ o, M.O s' a o = 1
  γ_pos : 0 < M.γ
  γ_le_one : M.γ ≤ 1

/-- Policy trees (§4.1, pp. 108–109), indexed by `n` = depth − 1: `PolicyTree A Ω n` is the type of
**(n + 1)-step policy trees**. A 1-step tree (`n = 0`) is a single action; an (n + 2)-step tree is a
root action together with one (n + 1)-step subtree for every observation. -/
def PolicyTree (A Ω : Type u) : ℕ → Type u
  | 0 => A
  | n + 1 => A × (Ω → PolicyTree A Ω n)

namespace PolicyTree

/-- There are finitely many t-step policy trees ("Let P be the finite set of all t-step policy
trees", p. 110). -/
instance instFintype [Fintype A] [Fintype Ω] [DecidableEq Ω] : ∀ n, Fintype (PolicyTree A Ω n)
  | 0 => (inferInstance : Fintype A)
  | n + 1 =>
    have := instFintype n
    (inferInstance : Fintype (A × (Ω → PolicyTree A Ω n)))

instance instNonempty [Nonempty A] : ∀ n, Nonempty (PolicyTree A Ω n)
  | 0 => (inferInstance : Nonempty A)
  | n + 1 =>
    have := instNonempty n
    (inferInstance : Nonempty (A × (Ω → PolicyTree A Ω n)))

/-- The action `a(p)` at the root of a tree of depth at least 2. -/
def action {n : ℕ} (p : PolicyTree A Ω (n + 1)) : A := p.1

/-- The subtree `o(p)` followed after observation `o` at the top level of a tree of depth at least 2. -/
def subtree {n : ℕ} (p : PolicyTree A Ω (n + 1)) (o : Ω) : PolicyTree A Ω n := p.2 o

/-- The tree `p_new` of §4.4.2, p. 115: it agrees with `p` in its action and in all its subtrees
except for observation `o`, for which `o(p_new) = p'`. -/
def replace [DecidableEq Ω] {n : ℕ} (p : PolicyTree A Ω (n + 1)) (o : Ω) (p' : PolicyTree A Ω n) :
    PolicyTree A Ω (n + 1) :=
  (p.1, Function.update p.2 o p')

end PolicyTree

variable [Fintype S] [Fintype Ω]

/-- The value `V_p(s)` of executing the policy tree `p` from world state `s` (§4.1, p. 109):
`V_p(s) = R(s, a(p))` for a 1-step tree, and
`V_p(s) = R(s, a(p)) + γ Σ_{s'} T(s, a(p), s') Σ_{o} O(s', a(p), o) V_{o(p)}(s')` in general. -/
noncomputable def value (M : POMDP S A Ω) : {n : ℕ} → PolicyTree A Ω n → S → ℝ
  | 0, a, s => M.R s a
  | _ + 1, p, s =>
    M.R s p.1 + M.γ * ∑ s', M.T s p.1 s' * ∑ o, M.O s' p.1 o * value M (p.2 o) s'

/-- The value of a policy tree at a belief state, `V_p(b) = Σ_s b(s) V_p(s) = b · α_p` (p. 110),
where `α_p = ⟨V_p(s_1), …, V_p(s_n)⟩`. Belief states are the points of `stdSimplex ℝ S` (p. 107). -/
noncomputable def valueAt (M : POMDP S A Ω) {n : ℕ} (p : PolicyTree A Ω n) (b : S → ℝ) : ℝ :=
  ∑ s, b s * value M p s

/-- The optimal (n + 1)-step value function `V_{n+1}(b) = max_{p ∈ P} b · α_p`, the maximum over the
finite nonempty set `P` of all (n + 1)-step policy trees (p. 110). -/
noncomputable def optValue [Fintype A] [DecidableEq Ω] [Nonempty A] (M : POMDP S A Ω) (n : ℕ)
    (b : S → ℝ) : ℝ :=
  (Finset.univ : Finset (PolicyTree A Ω n)).sup' Finset.univ_nonempty (fun p => valueAt M p b)

/-- `Pr(o | a, b) = Σ_{s'} O(s', a, o) Σ_s T(s, a, s') b(s)`, the probability of observing `o` after
taking action `a` in belief state `b` — the normalizing factor of the state estimator (§3.3, p. 107). -/
noncomputable def obsProb (M : POMDP S A Ω) (b : S → ℝ) (a : A) (o : Ω) : ℝ :=
  ∑ s', M.O s' a o * ∑ s, M.T s a s' * b s

/-- The state estimator `SE(b, a, o) = b'` of §3.3, p. 107:
`b'(s') = O(s', a, o) Σ_s T(s, a, s') b(s) / Pr(o | a, b)`.
When `Pr(o | a, b) = 0` Lean's convention `x / 0 = 0` makes this the zero vector, which is not a belief
state; every claim that `SE(b, a, o)` is a belief state assumes `Pr(o | a, b) ≠ 0`. -/
noncomputable def stateEstimator (M : POMDP S A Ω) (b : S → ℝ) (a : A) (o : Ω) : S → ℝ :=
  fun s' => M.O s' a o * (∑ s, M.T s a s' * b s) / obsProb M b a o

end KaelblingPOMDP.Witness


