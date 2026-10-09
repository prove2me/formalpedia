-- Prove2me | Definitions.Def_WiesemannRMDP_SRect_Model
-- name    : WiesemannRMDP_SRect_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:03.686369+00:00
-- url     : https://prove2.me/theorems/fd8b7988-5b46-4ccf-8937-fc9697be91e6
-- title:
--   Robust MDP with an affinely parametrized ambiguity set (§1, §2.1, §3, §4): Ξ (3b), p^ξ (3a), s-rectangularity, P̂ and r̂ (7), v (8), the maps φ (11) and ϕ (25), problems (10)/(24)
-- statement:
--   This module fixes the robust Markov decision process of Wiesemann, Kuhn and Rustem and the objects their policy evaluation and improvement theorems speak about.
--
--   **Data.** Let $\mathcal S$ and $\mathcal A$ be finite sets of states and actions. A transition reward $r(s,a,s')\ge 0$ is received when action $a$ is chosen in state $s$ and the next state is $s'$; $\lambda\in(0,1)$ is the discount factor and $p_0\in\mathcal M(\mathcal S)$ the initial distribution, where $\mathcal M(\mathcal X)$ is the probability simplex in $\mathbb R^{\mathcal X}$.
--
--   **Ambiguity set.** The uncertain parameter $\xi$ ranges over
--   $$\Xi := \{\xi\in\mathbb R^q : \xi^\top O_l\,\xi + o_l^\top\xi + \omega_l \ge 0\ \ \forall\, l=1,\dots,L\} \tag{3b}$$
--   with $O_l$ symmetric and $O_l\preceq 0$; $\Xi$ is assumed bounded and to contain a Slater point $\bar\xi$ with $\bar\xi^\top O_l\bar\xi + o_l^\top\bar\xi + \omega_l>0$ for all $l$. The transition probabilities are affine in $\xi$, $p^\xi(\cdot\mid s,a) := k_{sa} + K_{sa}\xi$, and lie in $\mathcal M(\mathcal S)$ for every $\xi\in\Xi$. The ambiguity set is $\mathcal P := \{P\in[\mathcal M(\mathcal S)]^{S\times A} : \exists\,\xi\in\Xi,\ P_{sa}=p^\xi(\cdot\mid s,a)\ \forall (s,a)\}$ (3a). It is **s-rectangular** if $\mathcal P = \times_{s\in\mathcal S}\mathcal P_s$ with $\mathcal P_s := \{(P_{s1},\dots,P_{sA}) : P\in\mathcal P\}$.
--
--   **Policies and the induced Markov reward process.** $\Pi$ is the set of stationary randomized policies $\pi=(\pi(\cdot\mid s))_{s\in\mathcal S}\in[\mathcal M(\mathcal A)]^S$. For $\pi\in\Pi$ and $\xi\in\Xi$,
--   $$\widehat P_{ss'}(\pi;\xi) := \sum_{a}\pi(a\mid s)\,p^\xi(s'\mid s,a),\qquad \widehat r_s(\pi;\xi) := \sum_a \pi(a\mid s)\sum_{s'}p^\xi(s'\mid s,a)\,r(s,a,s'), \tag{7}$$
--   and the **reward to-go** is
--   $$v(\pi;\xi) := \sum_{t=0}^\infty\big[\lambda\widehat P(\pi;\xi)\big]^t\,\widehat r(\pi;\xi). \tag{8}$$
--
--   **Robust Bellman maps.** For $w\in\mathbb R^S$ and $s\in\mathcal S$,
--   $$\phi_s(\pi;w) := \min_{\xi\in\Xi}\Big\{\widehat r_s(\pi;\xi) + \lambda\sum_{s'}\widehat P_{ss'}(\pi;\xi)\,w_{s'}\Big\}, \tag{11}$$
--   $$\varphi_s(w) := \max_{\pi\in\Pi}\phi_s(\pi;w). \tag{25}$$
--   (In Lean, (11) is `phiEval` and (25) is `phiImprove`.)
--
--   **Problems (10) and (24).** A reward to-go function $\vartheta:\Xi\to\mathbb R^S$ is feasible for $\pi$ if $\vartheta(\xi)\le\widehat r(\pi;\xi)+\lambda\widehat P(\pi;\xi)\vartheta(\xi)$ componentwise for all $\xi\in\Xi$, and its objective value is $\inf_{\xi\in\Xi}p_0^\top\vartheta(\xi)$. Problem (10) maximizes this objective over continuous feasible $\vartheta$ for a fixed $\pi$; problem (24) maximizes it over $\pi\in\Pi$ as well.
--
--   These are the shared vocabulary of the mission: Theorem 3.2 solves (10) and Theorem 4.1 solves (24) over s-rectangular ambiguity sets.
--
--   **Formalization Note.** The standing assumptions are bundled in `Model.Standing`. The reward to-go is defined by the series (8); the paper defines it as the expected discounted reward (5) and states that (5) equals (8), citing Puterman. The minimum in (11), the maximum in (25) and the infimum of the objective are infima and suprema over the subtypes $\Xi$ and $\Pi$; they are attained under the standing assumptions, and the objective is used only for $\vartheta$ continuous on $\Xi$. The page prints $\omega$ without index in (3b); $\omega_l$ is used, as in (16b) and (20b). $\widehat P$ and $\widehat r$ are built from the published `InducedTransition` and `InducedReward`, $\Pi$ is the published `IsPolicy`, and membership of $p^\xi(\cdot\mid s,a)$ in the simplex is the published `IsTransitionKernel`.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), pp. 2, 5–6, 8, 14–16, 25–26: §1 (model, (1)), §2.1 ((3a), (3b), s-rectangularity), §2.2 (stationary policies), §3 ((7a), (7b), (8), (10)), §3.1 ((11)), §4 ((24), (25))

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward

namespace WiesemannRMDP.SRect

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

/-- The parameter set (3b), p. 6:
`Ξ := {ξ ∈ ℝ^q : ξᵀ O_l ξ + o_lᵀ ξ + ω_l ≥ 0 ∀ l = 1, …, L}`.

**Formalization Note.** The page prints `ω` without the index `l` in (3b); (16b), (17), (20b),
(20c) print `ω_l`, which is used here. -/
def Xi (M : Model St Act q L) : Set (Fin q → ℝ) :=
  {ξ | ∀ l : Fin L, 0 ≤ ξ ⬝ᵥ (M.O l *ᵥ ξ) + M.o l ⬝ᵥ ξ + M.ω l}

/-- The affine transition probabilities (3a), p. 5: `p^ξ(s'|s, a) := (k_{sa} + K_{sa} ξ)_{s'}`.
Written `M.pXi ξ s a s'`. It is a probability distribution in `s'` for `ξ ∈ Ξ` under
`Model.Standing`. -/
def pXi [Fintype St] (M : Model St Act q L) (ξ : Fin q → ℝ) : St → Act → St → ℝ :=
  fun s a s' => M.k s a s' + (M.K s a *ᵥ ξ) s'

/-- The ambiguity set (3a), p. 5:
`𝒫 := {P ∈ [M(S)]^{S×A} : ∃ ξ ∈ Ξ such that P_{sa} = p^ξ(·|s, a) ∀ (s, a)}`. -/
def ambiguitySet [Fintype St] (M : Model St Act q L) : Set (St → Act → St → ℝ) :=
  {P | IsTransitionKernel P ∧ ∃ ξ ∈ M.Xi, P = M.pXi ξ}

/-- s-rectangularity, p. 6: `𝒫 = ×_{s∈S} 𝒫_s` with `𝒫_s := {(P_{s1}, …, P_{sA}) : P ∈ 𝒫}`.
A kernel `P` lies in the product `×_s 𝒫_s` iff for every state `s` its block
`P_s = (P_{s1}, …, P_{sA})` (in Lean, `P s`) is the block of some member of `𝒫`. -/
def IsSRectangular [Fintype St] (M : Model St Act q L) : Prop :=
  M.ambiguitySet = {P | ∀ s : St, ∃ P' ∈ M.ambiguitySet, P s = P' s}

/-- The standing assumptions of §1 (p. 2) and §2.1 (pp. 5–6):

1. `O_l ⪯ 0` for every `l` (`-O_l` positive semidefinite, which includes `O_l ∈ 𝕊^q`);
2. `Ξ` is bounded;
3. `Ξ` contains a Slater point `ξ̄` with `ξ̄ᵀ O_l ξ̄ + o_lᵀ ξ̄ + ω_l > 0` for all `l`;
4. `p^ξ(·|s, a)` is a probability distribution on `S` for every `ξ ∈ Ξ` and `(s, a)`
   ("an affine function from Ξ to M(S)");
5. all rewards are non-negative, `r(s, a, s') ∈ ℝ₊`;
6. the discount factor satisfies `λ ∈ (0, 1)`;
7. the initial distribution `p₀` lies in the probability simplex `M(S)`. -/
def Standing [Fintype St] (M : Model St Act q L) : Prop :=
  (∀ l : Fin L, (-(M.O l)).PosSemidef) ∧
  Bornology.IsBounded M.Xi ∧
  (∃ ξbar : Fin q → ℝ, ∀ l : Fin L,
      0 < ξbar ⬝ᵥ (M.O l *ᵥ ξbar) + M.o l ⬝ᵥ ξbar + M.ω l) ∧
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

/-- The robust policy evaluation map (11), p. 16:
`φ_s(π; w) := min_{ξ^s∈Ξ} { r̂_s(π; ξ^s) + λ P̂ᵀ_{s·}(π; ξ^s) w }` for every `s ∈ S`,
where `P̂ᵀ_{s·}(π; ξ) w = ∑_{s'} P̂_{ss'}(π; ξ) w_{s'}`.

**Formalization Note.** The minimum is written as the infimum over the subtype `Ξ`. Under
`Model.Standing`, `Ξ` is nonempty and compact and the objective is continuous in `ξ`, so the
infimum is attained and equals the paper's minimum. -/
noncomputable def phiEval [Fintype St] [Fintype Act] (M : Model St Act q L)
    (π : St → Act → ℝ) (w : St → ℝ) : St → ℝ :=
  fun s => ⨅ ξ : M.Xi, (M.rhat π ξ s + M.lam * ∑ s' : St, M.Phat π ξ s s' * w s')

/-- The robust policy improvement map (25), p. 26: `ϕ_s(w) := max_{π∈Π} {φ_s(π; w)}` for every
`s ∈ S`, where `Π` is the set of stationary randomized policies (`IsPolicy`).

**Formalization Note.** The maximum is written as the supremum over the subtype of policies.
`Π` is a nonempty compact set (a product of simplices, for nonempty `A`), and under
`Model.Standing` `φ_s(·; w)` is bounded on it, so the supremum is the paper's maximum. -/
noncomputable def phiImprove [Fintype St] [Fintype Act] (M : Model St Act q L)
    (w : St → ℝ) : St → ℝ :=
  fun s => ⨆ π : {π : St → Act → ℝ // IsPolicy π}, M.phiEval π.1 w s

/-- Feasibility of a reward to-go function `ϑ : Ξ → ℝ^S` for the policy `π` in problems (10)
(p. 15) and (24) (p. 25): `ϑ(ξ) ≤ r̂(π; ξ) + λ P̂(π; ξ) ϑ(ξ)` for all `ξ ∈ Ξ`, componentwise. -/
def Feasible [Fintype St] [Fintype Act] (M : Model St Act q L)
    (π : St → Act → ℝ) (ϑ : (Fin q → ℝ) → St → ℝ) : Prop :=
  ∀ ξ ∈ M.Xi, ϑ ξ ≤ M.rhat π ξ + M.lam • (M.Phat π ξ *ᵥ ϑ ξ)

/-- The objective of problems (10) and (24): `inf_{ξ∈Ξ} {p₀ᵀ ϑ(ξ)}`.

**Formalization Note.** The infimum is over the subtype `Ξ`. It is used only for `ϑ` continuous
on `Ξ` (the class `ϑ : Ξ ↦c ℝ^S` of (10) and (24)); then, `Ξ` being nonempty and compact under
`Model.Standing`, it is a finite, attained minimum. -/
noncomputable def objective [Fintype St] (M : Model St Act q L)
    (ϑ : (Fin q → ℝ) → St → ℝ) : ℝ :=
  ⨅ ξ : M.Xi, M.p0 ⬝ᵥ ϑ ξ

end Model

end WiesemannRMDP.SRect


