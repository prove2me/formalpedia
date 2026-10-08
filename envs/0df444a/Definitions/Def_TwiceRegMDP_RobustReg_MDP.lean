-- Prove2me | Definitions.Def_TwiceRegMDP_RobustReg_MDP
-- name    : TwiceRegMDP_RobustReg_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:12:12.01883+00:00
-- url     : https://prove2.me/theorems/77b59b18-43ac-4821-b744-bfcd7a9e1f97
-- title:
--   Finite discounted MDP: policies, $r^\pi$, $P^\pi$, the evaluation operator $T^\pi_{(P,r)}$, support functions and optimal solutions
-- statement:
--   Let $\mathcal S$ and $\mathcal A$ be finite sets of states and actions, and write $\mathcal X := \mathcal S\times\mathcal A$. This file fixes the basic objects of a finite discounted Markov decision process used throughout the mission.
--
--   1. A **policy** $\pi\in\Delta_{\mathcal A}^{\mathcal S}$ assigns to every state $s$ a probability distribution $\pi_s\in\Delta_{\mathcal A}$ over actions.
--   2. For a reward $r\in\mathbb R^{\mathcal X}$, the **expected reward** under $\pi$ is $r^\pi(s) := \langle \pi_s, r(s,\cdot)\rangle = \sum_{a}\pi_s(a)\,r(s,a)$.
--   3. For an array $P(s'\mid s,a)$ and $v\in\mathbb R^{\mathcal S}$, $(P^\pi v)(s) := \sum_{s'} P^\pi(s'\mid s)\,v(s')$ with $P^\pi(s'\mid s) := \langle \pi_s, P(s'\mid s,\cdot)\rangle$.
--   4. For a discount factor $\gamma$, the **evaluation Bellman operator** is
--   $$T^\pi_{(P,r)}v := r^\pi + \gamma P^\pi v .$$
--   5. The inner product on $\mathbb R^{\mathcal S}$ is $\langle v,\mu\rangle := \sum_s v(s)\mu(s)$.
--   6. The **support function** of a set $C\subseteq\mathbb R^{\iota}$ ($\iota$ finite) is $\sigma_C(y) := \max_{a\in C}\langle a,y\rangle$.
--   7. A vector $v$ is **the optimal solution** of $\max_{w\in\mathbb R^{\mathcal S}}\langle w,\mu_0\rangle$ subject to $w\in F$ when $v\in F$, $\langle w,\mu_0\rangle\le\langle v,\mu_0\rangle$ for every $w\in F$, and $v$ is the only point of $F$ attaining this value.
--
--   These are the objects of Section 2 of the paper; every theorem of the mission is stated in terms of them.
--
--   **Formalization Note.** A transition array is a function `P : S → A → S → ℝ` with `P s a s'` $=P(s'\mid s,a)$; the operators are defined for arbitrary arrays (so that $(P_0+P)^\pi = P_0^\pi + P^\pi$ holds by definition), and the kernel property is a separate hypothesis (the referenced `IsTransitionKernel`). $P^\pi(s'\mid s)$ is the referenced `InducedTransition`. The support function is the real `sSup` of $\{\langle a,y\rangle : a\in C\}$; it equals the maximum when $C$ is nonempty and compact, which every theorem assumes (on an empty or unbounded set the real `sSup` is $0$).
-- source:
--   Derman, Geist and Mannor, Twice regularized MDPs and the equivalence between robustness and regularization, arXiv:2110.06267v1, p. 2 (Notations: inner product, support function) and p. 3, Section 2 (Discounted MDPs and LP formulation: policies, r^π, P^π, T^π_(P,r))

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition

namespace TwiceRegMDP.RobustReg

/-- A (stochastic, stationary) policy `π ∈ Δ_A^S` (Derman–Geist–Mannor, arXiv:2110.06267v1, p. 3):
for every state `s`, `π s` is a probability distribution over the finite action set `A`. -/
def IsPolicy {S A : Type} [Fintype A] (π : S → A → ℝ) : Prop :=
  ∀ s : S, π s ∈ stdSimplex ℝ A

/-- The expected reward under `π`, `r^π(s) := ⟨π_s, r(s, ·)⟩` (p. 3). -/
def rewardPi {S A : Type} [Fintype A] (π : S → A → ℝ) (r : S → A → ℝ) : S → ℝ :=
  fun s => ∑ a, π s a * r s a

/-- The policy transition operator applied to `v`:
`(P^π v)(s) := ∑_{s'} P^π(s'|s) v(s')` with `P^π(s'|s) := ⟨π_s, P(s'|s, ·)⟩` (p. 3), where
`P^π(s'|s)` is the published `InducedTransition π P s s' = ∑_a π s a * P s a s'`.
Here `P s a s'` is `P(s'|s, a)`; `P` is an arbitrary array, not necessarily a kernel. -/
noncomputable def transPi {S A : Type} [Fintype S] [Fintype A] (π : S → A → ℝ)
    (P : S → A → S → ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => ∑ s', FoundationsML.ReinforcementLearning.InducedTransition π P s s' * v s'

/-- The evaluation Bellman operator `T^π_{(P,r)} v := r^π + γ P^π v` (p. 3). -/
noncomputable def evalOp {S A : Type} [Fintype S] [Fintype A] (γ : ℝ) (P : S → A → S → ℝ)
    (r : S → A → ℝ) (π : S → A → ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => rewardPi π r s + γ * transPi π P v s

/-- The inner product `⟨v, μ⟩ := ∑_s v(s) μ(s)` on `ℝ^S` (p. 2). -/
def pairing {S : Type} [Fintype S] (v μ : S → ℝ) : ℝ :=
  ∑ s, v s * μ s

/-- The support function `σ_C(y) := max_{a ∈ C} ⟨a, y⟩` of a set `C ⊆ ℝ^ι` (p. 2), written as the
real `sSup` of `{⟨a, y⟩ : a ∈ C}`. This is the true maximum when `C` is nonempty and compact; every
use in this mission is under that hypothesis (on an empty or unbounded set the real `sSup` is `0`). -/
noncomputable def supportFn {ι : Type} [Fintype ι] (C : Set (ι → ℝ)) (y : ι → ℝ) : ℝ :=
  sSup ((fun a : ι → ℝ => ∑ i, a i * y i) '' C)

/-- `v` is *the* optimal solution of `max_{w ∈ ℝ^S} ⟨w, μ₀⟩ s.t. w ∈ F`: it is feasible, no feasible
point has a larger objective, and it is the only feasible point attaining the optimal objective. -/
def IsOptimalSolution {S : Type} [Fintype S] (μ₀ : S → ℝ) (F : Set (S → ℝ)) (v : S → ℝ) : Prop :=
  v ∈ F ∧ (∀ w ∈ F, pairing w μ₀ ≤ pairing v μ₀) ∧
    (∀ w ∈ F, pairing w μ₀ = pairing v μ₀ → w = v)

end TwiceRegMDP.RobustReg


