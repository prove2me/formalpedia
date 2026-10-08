-- Prove2me | Definitions.Def_LovejoyPOMDP_Monotone_Model
-- name    : LovejoyPOMDP_Monotone_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:39:18.767989+00:00
-- url     : https://prove2.me/theorems/1c0ef39f-9cb2-44c1-8586-eab221708044
-- title:
--   §2 — the finite POMDP, σ(k; π, a), the Bayes update T(π, a, k), h(π, a, V) of (2), the values V*_t of (3) and the bounded Bellman solution V*
-- statement:
--   A **finite partially observed Markov decision process** (POMDP) in the sense of Lovejoy (1987, §2) consists of a finite state set $S=\{1,\dots,n\}$, a finite observation set $O=\{1,\dots,m\}$, a finite action set $A$, and
--
--   1. rewards $g(i,a)\in\mathbb R$, received when the current state is $i$ and action $a$ is chosen;
--   2. transition matrices $P^a=(p^a_{ij})$, $p^a_{ij}=\Pr\{s_{t+1}=j\mid s_t=i,\,a_t=a\}$, each row $P^a(i)$ lying in $\Pi(S)$;
--   3. observation matrices $R^a=(r^a_{jk})$, $r^a_{jk}=\Pr\{k\mid s_{t+1}=j,\,a_t=a\}$, each row $r^a(j)$ lying in $\Pi(O)$, with the standing assumption $r^a_{jk}>0$ for all $j,k,a$;
--   4. a discount factor $\beta\ge 0$.
--
--   For a belief $\pi\in\Pi(S)$ and an action $a$ define the predicted state distribution $(\pi P^a)_j=\sum_{i}\pi_i p^a_{ij}$, the observation probabilities and the Bayes update
--   $$\sigma(k;\pi,a)=\sum_{i\in S}\sum_{j\in S}\pi_i p^a_{ij} r^a_{jk},\qquad T_j(\pi,a,k)=\frac{\sum_{i\in S}\pi_i p^a_{ij} r^a_{jk}}{\sigma(k;\pi,a)},$$
--   and, for a value function $V$ on $\Pi(S)$, the operator (2)
--   $$h(\pi,a,V)=\sum_{i\in S}\pi_i g(i,a)+\beta\sum_{k\in O}\sigma(k;\pi,a)\,V\big(T(\pi,a,k)\big).$$
--   Write $\sigma(\pi,a)$ for the vector $(\sigma(k;\pi,a))_{k\in O}$.
--
--   **Finite horizon.** Given a horizon $N$ and a salvage value $g_s:S\to\mathbb R$, the optimal values are defined by the recursion (3):
--   $$V^*_{N+1}(\pi)=\sum_{i\in S}\pi_i g_s(i),\qquad V^*_t(\pi)=\max\{h(\pi,a,V^*_{t+1}) : a\in A\},\quad t=1,\dots,N.$$
--
--   **Infinite horizon.** For $0<\beta<1$ the infinite-horizon optimal value $V^*$ is the bounded solution on $\Pi(S)$ of $V(\pi)=\max_{a\in A} h(\pi,a,V)$. Since $\sum_k\sigma(k;\pi,a)=1$ and $T(\pi,a,k)\in\Pi(S)$, the map $V\mapsto\max_a h(\cdot,a,V)$ is a $\beta$-contraction for the sup-metric on bounded functions on $\Pi(S)$, so this solution exists and is unique; it is the uniform limit of the recursion (3) from any bounded start.
--
--   These objects are the language of Lemmas 1.2, 1.3, 2.3 and Propositions 1 and 2.
--
--   **Formalization Note** The standing assumptions (stochastic rows, $r^a_{jk}>0$, $\beta\ge0$) are fields of the structure `POMDP S O A`, so every statement about a POMDP carries them. Value functions are maps `(S → ℝ) → ℝ`; only their values on $\Pi(S)$ matter. The recursion is counted by steps to go: `valueToGo gs 0` is the salvage term, `valueToGo gs (n+1) π = max_a h(π, a, valueToGo gs n)`, and `Vstar gs N t = valueToGo gs (N + 1 - t)` is $V^*_t$ for $1\le t\le N+1$. The maximum over $A$ is `Finset.sup'` over the nonempty finite set of actions. The division in $T$ is by $\sigma(k;\pi,a)>0$ on $\Pi(S)$; off the simplex Lean's $x/0=0$ applies and is never used. `IsBellmanSolution V` says that $V$ is bounded on $\Pi(S)$ and satisfies the Bellman equation on $\Pi(S)$. Its equivalence with the optimum over history-dependent strategies (cited by the paper from Åström, Bertsekas and Blackwell) is not part of the formalization.
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, pp. 737–738, §2 (model, σ, T, πP^a, r^a_jk > 0), eq. (2) h, eq. (3) V*_t, Infinite-Horizon Problem (V*); p. 741 (Σ_i π_i g(i, a) in α(π))

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Orders

namespace LovejoyPOMDP.Monotone

/-! # §2 of Lovejoy (1987): the finite POMDP, the Bayes update and the optimal values

Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*,
Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, §2, pp. 737–738, (2), (3).

**Formalization Note.** States `S = {1, …, n}`, observations `O = {1, …, m}` and actions `A` are
finite types; their orders (needed only by the theorems) are added there as `[LinearOrder _]`.
The standing assumptions of §2 are fields of the structure, so every statement about a
`POMDP` carries them: each row `P^a(i)` lies in `Π(S)`, each row `r^a(j)` lies in `Π(O)`,
`r^a_{jk} > 0` for all `j, k, a` (p. 738), and `β ≥ 0` (p. 737). The observation `k` is generated
by the *next* state `j` and the current action `a`. Value functions are functions
`V : (S → ℝ) → ℝ`; only their values on `Π(S)` matter, because `T(π, a, k) ∈ Π(S)` for
`π ∈ Π(S)`. The division in `T` is honest on `Π(S)`, where `σ(k; π, a) > 0`; off the simplex
Lean's `x / 0 = 0` convention applies and is never used. -/

/-- A discrete-time, finite, partially observed Markov decision process (§2, pp. 737–738):
rewards `g(i, a)`, transition matrices `P^a = (p^a_{ij})`, observation matrices
`R^a = (r^a_{jk})` with `r^a_{jk} = Pr{k | s_{t+1} = j, a_t = a}`, and a discount factor `β`,
together with the standing assumptions `P^a(i) ∈ Π(S)`, `r^a(j) ∈ Π(O)`, `r^a_{jk} > 0`, `β ≥ 0`. -/
structure POMDP (S O A : Type*) [Fintype S] [Fintype O] where
  /-- the reward `g(i, a)` received if `s_t = i` and `a_t = a` -/
  g : S → A → ℝ
  /-- the transition probabilities `p^a_{ij} = P a i j` -/
  P : A → S → S → ℝ
  /-- the observation probabilities `r^a_{jk} = R a j k` -/
  R : A → S → O → ℝ
  /-- the discount factor `β` -/
  β : ℝ
  /-- every row `P^a(i)` of `P^a` lies in `Π(S)` -/
  P_row : ∀ a i, P a i ∈ stdSimplex ℝ S
  /-- every row `r^a(j)` of `R^a` lies in `Π(O)` -/
  R_row : ∀ a j, R a j ∈ stdSimplex ℝ O
  /-- the standing assumption `r^a_{jk} > 0` for all `j, k, a` (p. 738) -/
  R_pos : ∀ a j k, 0 < R a j k
  /-- `β ≥ 0` (p. 737) -/
  β_nonneg : 0 ≤ β

noncomputable section

namespace POMDP

variable {S O A : Type*} [Fintype S] [Fintype O] [Fintype A] (M : POMDP S O A)

/-- `πP^a`, the element of `Π(S)` with `j`-th component `Σ_{i∈S} π_i p^a_{ij}` (p. 738). -/
def predict (π : S → ℝ) (a : A) : S → ℝ :=
  fun j => ∑ i, π i * M.P a i j

/-- `σ(k; π, a) = Σ_{i∈S} Σ_{j∈S} π_i p^a_{ij} r^a_{jk}` (p. 737), the probability of observing
`k` after action `a` from the belief `π`. As a function of `k` this is the vector
`σ(π, a) ∈ Π(O)`. -/
def sigma (π : S → ℝ) (a : A) : O → ℝ :=
  fun k => ∑ i, ∑ j, π i * M.P a i j * M.R a j k

/-- The Bayes update `T(π, a, k)` (p. 737), with `j`-th component
`T_j(π, a, k) = Σ_{i∈S} π_i p^a_{ij} r^a_{jk} / σ(k; π, a)`. -/
def bayes (π : S → ℝ) (a : A) (k : O) : S → ℝ :=
  fun j => (∑ i, π i * M.P a i j * M.R a j k) / M.sigma π a k

/-- The expected one-step reward `Σ_{i∈S} π_i g(i, a)` (the function maximized by the myopic
policy `α(π)`, p. 741). -/
def myopic (π : S → ℝ) (a : A) : ℝ :=
  ∑ i, π i * M.g i a

/-- The operator `h` of (2), p. 738:
`h(π, a, V) = Σ_{i∈S} π_i g(i, a) + β Σ_{k∈O} σ(k; π, a) V(T(π, a, k))`. -/
def hOp (π : S → ℝ) (a : A) (V : (S → ℝ) → ℝ) : ℝ :=
  M.myopic π a + M.β * ∑ k, M.sigma π a k * V (M.bayes π a k)

/-- The finite-horizon recursion (3), p. 738, counted by the number of steps to go:
`valueToGo gs 0 π = Σ_{i∈S} π_i g_s(i)` (the salvage stage) and
`valueToGo gs (n + 1) π = max_{a ∈ A} h(π, a, valueToGo gs n)`. -/
def valueToGo [Nonempty A] (gs : S → ℝ) : ℕ → (S → ℝ) → ℝ
  | 0 => fun π => ∑ i, π i * gs i
  | n + 1 => fun π => Finset.univ.sup' Finset.univ_nonempty (fun a => M.hOp π a (valueToGo gs n))

/-- The optimal value functions `V*_t` of (3), p. 738, for horizon `N < ∞` and salvage `g_s`:
`V*_t = valueToGo gs (N + 1 - t)`, so `V*_{N+1}(π) = Σ_i π_i g_s(i)` and
`V*_t(π) = max{h(π, a, V*_{t+1}) : a ∈ A}` for `t = 1, …, N`. Only `1 ≤ t ≤ N + 1` is meaningful;
every theorem states that range. -/
def Vstar [Nonempty A] (gs : S → ℝ) (N t : ℕ) : (S → ℝ) → ℝ :=
  M.valueToGo gs (N + 1 - t)

/-- `V` is a bounded solution of the Bellman equation on `Π(S)` (the infinite-horizon optimal
value `V*`, p. 738): `V` is bounded on `Π(S)` and `V(π) = max{h(π, a, V) : a ∈ A}` for every
`π ∈ Π(S)`. For `0 < β < 1` the map `V ↦ max_a h(·, a, V)` is a `β`-contraction on the bounded
functions on `Π(S)` with the sup-metric `ρ`, so exactly one such `V` exists on `Π(S)`: the
limit `V*` of the recursion (3) described on p. 738. -/
def IsBellmanSolution [Nonempty A] (V : (S → ℝ) → ℝ) : Prop :=
  (∃ C : ℝ, ∀ π ∈ stdSimplex ℝ S, |V π| ≤ C) ∧
    ∀ π ∈ stdSimplex ℝ S, V π = Finset.univ.sup' Finset.univ_nonempty (fun a => M.hOp π a V)

end POMDP

end

end LovejoyPOMDP.Monotone


