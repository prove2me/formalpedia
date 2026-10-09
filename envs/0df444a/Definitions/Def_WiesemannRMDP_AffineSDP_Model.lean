-- Prove2me | Definitions.Def_WiesemannRMDP_AffineSDP_Model
-- name    : WiesemannRMDP_AffineSDP_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:55.050292+00:00
-- url     : https://prove2.me/theorems/01afd2fe-6a06-4313-9a28-1cd131b2462b
-- title:
--   Robust MDP with an affinely parametrized ambiguity set (§1, §2.1, §3): S, A, r(s,a,s′), λ, p₀, Ξ (3b), p^ξ (3a), P̂ and r̂ (7), v (8)
-- statement:
--   This module fixes the robust Markov decision process of Wiesemann, Kuhn and Rustem for a fixed stationary policy.
--
--   **Data.** Let $\mathcal S$ and $\mathcal A$ be finite sets of states and actions. A transition reward $r(s,a,s')$ is received when action $a$ is chosen in state $s$ and the next state is $s'$; $\lambda$ is the discount factor and $p_0$ the initial state distribution. The uncertain parameter $\xi$ ranges over the set $\Xi\subseteq\mathbb R^q$ of (3b), defined by data $(O_l,o_l,\omega_l)_{l=1}^L$, and the transition probabilities are affine in $\xi$:
--   $$p^\xi(\cdot\mid s,a) := k_{sa} + K_{sa}\,\xi,\qquad k_{sa}\in\mathbb R^S,\ K_{sa}\in\mathbb R^{S\times q}. \tag{3a}$$
--
--   **Standing assumptions.** (1) $O_l\preceq 0$, $\Xi$ is bounded and contains a Slater point; (2) $p^\xi(\cdot\mid s,a)$ lies in the probability simplex $\mathcal M(\mathcal S)$ for every $\xi\in\Xi$ and $(s,a)$; (3) $r(s,a,s')\ge 0$; (4) $\lambda\in(0,1)$; (5) $p_0\in\mathcal M(\mathcal S)$.
--
--   **Induced Markov reward process.** A stationary randomized policy is $\pi=(\pi(\cdot\mid s))_{s\in\mathcal S}\in[\mathcal M(\mathcal A)]^S$; the set of these is $\Pi$. For $\pi\in\Pi$ and $\xi\in\Xi$,
--   $$\widehat P_{ss'}(\pi;\xi) := \sum_{a}\pi(a\mid s)\,p^\xi(s'\mid s,a),\qquad \widehat r_s(\pi;\xi) := \sum_a \pi(a\mid s)\sum_{s'}p^\xi(s'\mid s,a)\,r(s,a,s'), \tag{7}$$
--   and the **reward to-go** is
--   $$v(\pi;\xi) := \sum_{t=0}^\infty\big[\lambda\widehat P(\pi;\xi)\big]^t\,\widehat r(\pi;\xi). \tag{8}$$
--
--   These objects are the vocabulary of the affine approximation (19) and the semidefinite program (20) of Theorem 3.8.
--
--   **Formalization Note.** The standing assumptions are bundled in `Model.Standing`. The reward to-go is defined by the series (8); the paper defines it as the expected discounted reward (5) along sample paths and states that (5) equals (8), citing Puterman. The series is meaningful for $\pi\in\Pi$, $\xi\in\Xi$, which is where it is used. $\widehat P$ and $\widehat r$ are built from the published `InducedTransition` and `InducedReward`, membership of $p^\xi(\cdot\mid s,a)$ in the simplex is the published `IsTransitionKernel`, and $\Pi$ is the published `IsPolicy`. The rewards depend on the next state $s'$.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), pp. 2, 5–6, 14–15: §1 (model, (1)), §2.1 ((3a), (3b)), §3 ((7a), (7b), (8))

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_AffineSDP_ParamSet

namespace WiesemannRMDP.AffineSDP

open FoundationsML.ReinforcementLearning Matrix

/-- The data of a robust MDP with an affinely parametrized ambiguity set (Wiesemann, Kuhn &
Rustem, *Robust Markov Decision Processes*, Optimization Online 2610, revision of February 9,
2012, §1 p. 2 and §2.1 pp. 5–6):

* `r s a s'` is the expected reward `r(s, a, s')` for choosing action `a` in state `s` when the
  next state is `s'` (p. 2);
* `lam` is the discount factor `λ` and `p0` the initial state distribution `p₀` (p. 2);
* `O l`, `o l`, `ω l` (`l = 1, …, L`) describe the parameter set `Ξ ⊆ ℝ^q` of (3b);
* `k s a` and `K s a` describe the affine transition probabilities
  `p^ξ(·|s, a) = k_{sa} + K_{sa} ξ` of (3a).

The standing assumptions on these data are collected in `Model.Standing`. -/
structure Model (St Act : Type*) (q L : ℕ) where
  /-- Transition rewards `r(s, a, s')`. -/
  r : St → Act → St → ℝ
  /-- Discount factor `λ`. -/
  lam : ℝ
  /-- Initial state distribution `p₀`. -/
  p0 : St → ℝ
  /-- Quadratic coefficient matrices `O_l` of (3b). -/
  O : Fin L → Matrix (Fin q) (Fin q) ℝ
  /-- Linear coefficient vectors `o_l` of (3b). -/
  o : Fin L → Fin q → ℝ
  /-- Constant terms `ω_l` of (3b). -/
  ω : Fin L → ℝ
  /-- Offsets `k_{sa} ∈ ℝ^S` of (3a). -/
  k : St → Act → St → ℝ
  /-- Slopes `K_{sa} ∈ ℝ^{S×q}` of (3a). -/
  K : St → Act → Matrix St (Fin q) ℝ

namespace Model

variable {St Act : Type*} {q L : ℕ}

/-- The parameter set `Ξ` of (3b), p. 6, built from the model's `O_l`, `o_l`, `ω_l`. -/
def Xi (M : Model St Act q L) : Set (Fin q → ℝ) :=
  XiSet M.O M.o M.ω

/-- The affine transition probabilities (3a), p. 5: `p^ξ(s'|s, a) := (k_{sa} + K_{sa} ξ)_{s'}`.
It is a probability distribution in `s'` for `ξ ∈ Ξ` under `Model.Standing`. -/
def pXi [Fintype St] (M : Model St Act q L) (ξ : Fin q → ℝ) : St → Act → St → ℝ :=
  fun s a s' => M.k s a s' + (M.K s a *ᵥ ξ) s'

/-- The standing assumptions of §1 (p. 2) and §2.1 (pp. 5–6):

1. the data of (3b) satisfy `XiStanding`: `O_l` symmetric with `O_l ⪯ 0`, `Ξ` bounded, and `Ξ`
   contains a Slater point;
2. `p^ξ(·|s, a)` is a probability distribution on `S` for every `ξ ∈ Ξ` and `(s, a)`
   ("an affine function from Ξ to M(S)");
3. all rewards are non-negative, `r(s, a, s') ∈ ℝ₊`;
4. the discount factor satisfies `λ ∈ (0, 1)`;
5. the initial distribution `p₀` lies in the probability simplex `M(S)`. -/
def Standing [Fintype St] (M : Model St Act q L) : Prop :=
  XiStanding M.O M.o M.ω ∧
  (∀ ξ ∈ M.Xi, IsTransitionKernel (M.pXi ξ)) ∧
  (∀ s a s', 0 ≤ M.r s a s') ∧
  (0 < M.lam ∧ M.lam < 1) ∧
  M.p0 ∈ stdSimplex ℝ St

/-- The expected one-step reward `∑_{s'} p^ξ(s'|s, a) r(s, a, s')` of action `a` in state `s`. -/
def expReward [Fintype St] (M : Model St Act q L) (ξ : Fin q → ℝ) : St → Act → ℝ :=
  fun s a => ∑ s' : St, M.pXi ξ s a s' * M.r s a s'

/-- The MRP transition matrix (7a), p. 14:
`P̂_{ss'}(π; ξ) := ∑_{a∈A} π(a|s) p^ξ(s'|s, a)`, with rows indexed by the current state.
`π s a` is `π(a|s)`. -/
noncomputable def Phat [Fintype St] [Fintype Act] (M : Model St Act q L)
    (π : St → Act → ℝ) (ξ : Fin q → ℝ) : Matrix St St ℝ :=
  Matrix.of fun s s' => InducedTransition π (M.pXi ξ) s s'

/-- The MRP expected state rewards (7b), p. 14:
`r̂_s(π; ξ) := ∑_{a∈A} π(a|s) ∑_{s'∈S} p^ξ(s'|s, a) r(s, a, s')`. -/
noncomputable def rhat [Fintype St] [Fintype Act] (M : Model St Act q L)
    (π : St → Act → ℝ) (ξ : Fin q → ℝ) : St → ℝ :=
  InducedReward π (M.expReward ξ)

/-- The reward to-go function, defined by the series (8), p. 15:
`v(π; ξ) := ∑_{t=0}^∞ [λ P̂(π; ξ)]^t r̂(π; ξ)`.

**Formalization Note.** The paper defines `v_s(π; ξ)` as the expected discounted total reward (5)
from initial state `s` under `p^ξ` and the stationary policy `π`, and states that it equals the
series (8) ("see [20]"). The series is taken as the definition. It converges for `π ∈ Π`,
`ξ ∈ Ξ` (then `P̂(π; ξ)` is row-stochastic and `λ < 1`); only those arguments are meaningful. -/
noncomputable def v [Fintype St] [DecidableEq St] [Fintype Act] (M : Model St Act q L)
    (π : St → Act → ℝ) (ξ : Fin q → ℝ) : St → ℝ :=
  ∑' t : ℕ, ((M.lam • M.Phat π ξ) ^ t) *ᵥ M.rhat π ξ

end Model

end WiesemannRMDP.AffineSDP


