-- Prove2me | Definitions.Def_CorruptRobustRL_Supervised_MDP
-- name    : CorruptRobustRL_Supervised_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:49:48.53215+00:00
-- url     : https://prove2.me/theorems/8fcf2f7c-e22b-4bba-be7d-11534b7f2273
-- title:
--   §2, pp. 6–8 — tabular episodic MDP, $Q^\star$/$V^\star$ by backward recursion, mixtures of deterministic Markov policies, trajectory law, values, occupancies, concatenation
-- statement:
--   This file fixes the tabular episodic setting of Lykouris, Simchowitz, Slivkins and Sun.
--
--   **Nominal MDP.** States form a finite set $\mathcal X$ and actions a finite nonempty set $\mathcal A$; episodes have $H$ stages. The nominal MDP consists of an initial distribution $p^\star_0$ on $\mathcal X$, transition probabilities $p^\star(x'\mid x,a)$ that are the same at every stage, and mean rewards $r^\star(x,a)\in[0,1]$. "Nominal" means that $p^\star_0$ and every $p^\star(\cdot\mid x,a)$ are probability vectors and $0\le r^\star\le1$.
--
--   **Optimal values.** With $V^\star_{H+1}\equiv0$, define backward in $h$
--   $$Q^\star_h(x,a)=r^\star(x,a)+\sum_{x'}p^\star(x'\mid x,a)\,V^\star_{h+1}(x'),\qquad V^\star_h(x)=\max_{a}Q^\star_h(x,a),$$
--   let $\pi^\star_h(x)=\{a: Q^\star_h(x,a)=V^\star_h(x)\}$ be the set of optimal actions and $V^\star=\sum_x p^\star_0(x)V^\star_1(x)$.
--
--   **Policies.** A deterministic Markov policy $\sigma$ assigns an action $\sigma_h(x)$ to each stage and state. A randomized Markovian policy $\pi$ is a finite mixture of deterministic Markov policies: atoms $\sigma_i$ with weights $w_i\ge0$, $\sum_i w_i=1$. The concatenation $\sigma\oplus_h\sigma'$ follows $\sigma$ at stages before $h$ and $\sigma'$ from stage $h$ on; for a mixture it is taken atom by atom (Definition 4.3 and footnote 17).
--
--   **Trajectories.** Under a deterministic $\sigma$ the state sequence has law
--   $$P^\sigma(x_1,\dots,x_H)=p^\star_0(x_1)\prod_{t<H}p^\star\big(x_{t+1}\mid x_t,\sigma_t(x_t)\big),$$
--   with $a_t=\sigma_t(x_t)$. The file defines expectations of step-additive functionals $E^\sigma[\sum_h g_h(x_h,a_h)]$, the value $V^\sigma=E^\sigma[\sum_h r^\star(x_h,a_h)]$ and the occupancies $P^\sigma[(x_\tau,a_\tau)=(x,a)]$, and extends all three to mixtures by averaging over atoms with the weights $w_i$.
--
--   These objects are the language of every statement of the mission.
--
--   **Formalization Note** Stages are 0-based in Lean: the paper's stage $h\in[H]$ is Lean's `h - 1`, and the terminal values $V_{H+1}\equiv0$ sit at Lean index `H`. Rewards enter only through their mean $r^\star$, since every quantity of the mission is an expected sum of rewards. $V^\star$ is defined by the recursion of p. 8; that it equals the maximum of $V^\pi$ over policies is the standard fact the paper uses. A mixture is a structure with a finite index type `ι`, weights `w` and atoms `σ`; `IsMixture` states that the weights form a probability vector. The occupancy at a stage $\tau\ge H$ is $0$.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, pp. 6–8, §2 (model, randomized Markovian policies, nominal MDP, $Q^\star$, $V^\star$); p. 14, Definition 4.3 and footnote 17

import Mathlib

namespace CorruptRobustRL.Supervised

open Finset

/-- A probability vector on a finite type: nonnegative entries summing to one. -/
def IsProbVec {α : Type} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- The nominal tabular MDP `M = (p⋆₀, p⋆, D_rew)` of §2 (pp. 6–7), with the reward distribution
represented by its mean `r⋆(x, a) = E[R]`. The transition `p⋆` does not depend on the stage. -/
structure NominalMDP (X A : Type) where
  /-- initial distribution `p⋆₀` -/
  p0 : X → ℝ
  /-- transition probabilities `p⋆(x' | x, a)`, written `pstar x a x'` -/
  pstar : X → A → X → ℝ
  /-- mean reward `r⋆(x, a)` -/
  rstar : X → A → ℝ

variable {X A : Type}

/-- `p⋆₀` and every row `p⋆(· | x, a)` are probability vectors, and `r⋆ ∈ [0, 1]`. -/
def NominalMDP.IsNominal [Fintype X] (M : NominalMDP X A) : Prop :=
  IsProbVec M.p0 ∧ (∀ x a, IsProbVec (M.pstar x a)) ∧ ∀ x a, 0 ≤ M.rstar x a ∧ M.rstar x a ≤ 1

section Optimal

variable [Fintype X] [Fintype A] [Nonempty A]

/-- Optimal values indexed by the number `n` of remaining stages:
`V(0) ≡ 0` and `V(n+1)(x) = max_a (r⋆(x,a) + Σ_{x'} p⋆(x'|x,a) V(n)(x'))`. -/
noncomputable def VstarRem (M : NominalMDP X A) : ℕ → X → ℝ
  | 0, _ => 0
  | n + 1, x => univ.sup' univ_nonempty
      (fun a => M.rstar x a + ∑ x', M.pstar x a x' * VstarRem M n x')

/-- `V⋆_h` (p. 8) at the 0-based stage `h` of an episode of horizon `H`: the paper's stage `h + 1`.
`Vstar M H H ≡ 0` is the paper's `V⋆_{H+1} ≡ 0`. -/
noncomputable def Vstar (M : NominalMDP X A) (H h : ℕ) (x : X) : ℝ :=
  VstarRem M (H - h) x

/-- `Q⋆_h(x, a) = r⋆(x, a) + p⋆(x, a)ᵀ V⋆_{h+1}` (p. 8), 0-based stage `h`. -/
noncomputable def Qstar (M : NominalMDP X A) (H h : ℕ) (x : X) (a : A) : ℝ :=
  M.rstar x a + ∑ x', M.pstar x a x' * Vstar M H (h + 1) x'

/-- The set `π⋆_h(x) = {a : Q⋆_h(x, a) = V⋆_h(x)}` of optimal actions (Definition 4.1). -/
noncomputable def optActions [DecidableEq A] (M : NominalMDP X A) (H h : ℕ) (x : X) : Finset A := by
  classical
  exact univ.filter (fun a => Qstar M H h x a = Vstar M H h x)

/-- `V⋆ = E_{x₁ ∼ p⋆₀}[V⋆_1(x₁)]`. -/
noncomputable def Vstar0 (M : NominalMDP X A) (H : ℕ) : ℝ :=
  ∑ x, M.p0 x * Vstar M H 0 x

end Optimal

/-- A deterministic Markov policy: the action `σ t x` at the 0-based stage `t` in state `x`. -/
abbrev DetPolicy (X A : Type) := ℕ → X → A

/-- A randomized Markovian policy, i.e. a finitely supported distribution over deterministic Markov
policies (§2, p. 7; footnote 17): atoms `σ i` with weights `w i`. -/
structure Mixture (X A : Type) where
  ι : Type
  [instFintype : Fintype ι]
  w : ι → ℝ
  σ : ι → DetPolicy X A

attribute [instance] Mixture.instFintype

/-- The weights of a mixture are nonnegative and sum to one. -/
def Mixture.IsMixture (π : Mixture X A) : Prop :=
  (∀ i, 0 ≤ π.w i) ∧ ∑ i, π.w i = 1

/-- The mixture putting all its mass on one deterministic policy. -/
def DetPolicy.toMixture (σ : DetPolicy X A) : Mixture X A where
  ι := Unit
  w := fun _ => 1
  σ := fun _ => σ

/-- Concatenation `σ ⊕_h σ'` (Definition 4.3): follow `σ` at the 0-based stages `t < h`, then `σ'`.
The paper's `π ⊕_h π'` with stage `h ∈ [H]` is `concat π (h - 1) π'`. -/
def concat (σ : DetPolicy X A) (h : ℕ) (σ' : DetPolicy X A) : DetPolicy X A :=
  fun t x => if t < h then σ t x else σ' t x

/-- Concatenation of a mixture with a deterministic policy, atom by atom (footnote 17): draw an atom
`σ i` with probability `w i` and play `σ i ⊕_h σ'`. -/
def concatMix (π : Mixture X A) (h : ℕ) (σ' : DetPolicy X A) : Mixture X A where
  ι := π.ι
  w := π.w
  σ := fun i => concat (π.σ i) h σ'

section Trajectories

variable [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]

/-- The law of the state sequence `(x₁, …, x_H)` (0-based `s 0, …, s (H-1)`) under a deterministic
Markov policy: `p⋆₀(x₁) Π_{t<H} p⋆(x_{t+1} | x_t, σ_t(x_t))`. -/
noncomputable def trajProb (M : NominalMDP X A) (H : ℕ) (σ : DetPolicy X A) (s : Fin H → X) : ℝ :=
  ∏ t : Fin H,
    if (t : ℕ) = 0 then M.p0 (s t)
    else M.pstar (s ⟨(t : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩)
      (σ ((t : ℕ) - 1) (s ⟨(t : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩)) (s t)

/-- `E^σ[Σ_{h=1}^H g_h(x_h, a_h)]` for a deterministic Markov policy, `a_h = σ_h(x_h)`. -/
noncomputable def expectDet (M : NominalMDP X A) (H : ℕ) (σ : DetPolicy X A)
    (g : ℕ → X → A → ℝ) : ℝ :=
  ∑ s : Fin H → X, trajProb M H σ s * ∑ t : Fin H, g t (s t) (σ t (s t))

/-- `V^σ = E^σ[Σ_h r⋆(x_h, a_h)]`. -/
noncomputable def value (M : NominalMDP X A) (H : ℕ) (σ : DetPolicy X A) : ℝ :=
  expectDet M H σ (fun _ x a => M.rstar x a)

/-- Occupancy `P^σ[(x_τ, a_τ) = (x, a)]` at the 0-based stage `τ` (zero for `τ ≥ H`). -/
noncomputable def occ (M : NominalMDP X A) (H : ℕ) (σ : DetPolicy X A) (τ : ℕ) (x : X) (a : A) : ℝ :=
  if hτ : τ < H then
    ∑ s : Fin H → X, if s ⟨τ, hτ⟩ = x ∧ σ τ x = a then trajProb M H σ s else 0
  else 0

/-- `E^π[Σ_h g_h(x_h, a_h)] = Σ_i w_i E^{σ_i}[⋯]` for a mixture. -/
noncomputable def mixExpect (M : NominalMDP X A) (H : ℕ) (π : Mixture X A)
    (g : ℕ → X → A → ℝ) : ℝ :=
  ∑ i, π.w i * expectDet M H (π.σ i) g

/-- `V^π = Σ_i w_i V^{σ_i}`. -/
noncomputable def mixValue (M : NominalMDP X A) (H : ℕ) (π : Mixture X A) : ℝ :=
  ∑ i, π.w i * value M H (π.σ i)

/-- `P^π[(x_τ, a_τ) = (x, a)] = Σ_i w_i P^{σ_i}[⋯]`. -/
noncomputable def mixOcc (M : NominalMDP X A) (H : ℕ) (π : Mixture X A) (τ : ℕ) (x : X) (a : A) : ℝ :=
  ∑ i, π.w i * occ M H (π.σ i) τ x a

end Trajectories

end CorruptRobustRL.Supervised


