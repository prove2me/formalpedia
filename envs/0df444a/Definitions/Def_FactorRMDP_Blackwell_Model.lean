-- Prove2me | Definitions.Def_FactorRMDP_Blackwell_Model
-- name    : FactorRMDP_Blackwell_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:25:19.151714+00:00
-- url     : https://prove2.me/theorems/58e76aad-7965-4a4c-b58c-9b859c98a4b7
-- title:
--   The factor-matrix robust MDP of §1–§3: rewards, p₀, u, the factor matrix set 𝒲, r-rectangularity, policies, T_π, L(π,W), v^{π,W}_λ, R(π,W,λ), β, z_λ(π), robust solutions, φ and F
-- statement:
--   **The model.** Let $\mathbb S$ and $\mathbb A$ be finite sets of states and actions, with rewards $r_{sa}\ge 0$ and an initial distribution $p_0\in\Delta(\mathbb S)$. The transition kernel has a **factor structure** (2.1)–(2.2): there are fixed coefficients $u^i_{sa}\ge0$ for $i\in[r]$, with $\sum_{i=1}^r u^i_{sa}=1$ for every $(s,a)$, and a **factor matrix** $W=(w_1,\dots,w_r)$ whose columns $w_i\in\Delta(\mathbb S)$ are probability vectors; the kernel is
--   $$
--   P_{sas'}=\sum_{i=1}^r u^i_{sa}\,w_{i,s'} .
--   $$
--   The uncertainty set $\mathcal W$ of factor matrices is nonempty, convex and compact. Its projection on the $i$-th factor is $\mathcal W^i$, and $\mathcal W$ is **$r$-rectangular** (Assumption 2.2) when $\mathcal W=\mathcal W^1\times\dots\times\mathcal W^r$.
--
--   **Policies and values.** A stationary policy $\pi\in\Pi$ assigns to each state a distribution $\pi_s\in\Delta(\mathbb A)$; it is **deterministic** when every $\pi_s$ is a vertex of the simplex. Write $r_\pi=(\sum_a\pi_{sa}r_{sa})_s$, $T_\pi=(\sum_a\pi_{sa}u^i_{sa})_{s,i}\in\mathbb R^{S\times r}$ and $L(\pi,W)=T_\pi W^\top$, the state-to-state transition matrix under $\pi$ and $W$. For a discount $\lambda$ the value function and the expected reward (1.1) are
--   $$
--   v^{\pi,W}_\lambda=\sum_{t=0}^\infty \lambda^t L(\pi,W)^t r_\pi,\qquad R(\pi,W,\lambda)=p_0^\top v^{\pi,W}_\lambda .
--   $$
--   The adversary's value (Section 3) is $\beta=\sum_t\lambda^t (W^\top T_\pi)^t W^\top r_\pi$. The worst-case value of a policy is $z_\lambda(\pi)=\min_{W\in\mathcal W}R(\pi,W,\lambda)$, and a pair $(\pi^*,W^*)$ is an **optimal solution of the robust MDP problem (1.2)** when $\pi^*\in\Pi$ maximizes $z_\lambda$ over $\Pi$ and $W^*\in\mathcal W$ attains $\min_{W\in\mathcal W}R(\pi^*,W,\lambda)$.
--
--   The file also records the operators $\varphi(\pi,\beta)_i=\min_{w_i\in\mathcal W^i}w_i^\top(r_\pi+\lambda T_\pi\beta)$ (Appendix A) and
--   $$
--   F(v)_s=\max_{a\in\mathbb A}\Big\{r_{sa}+\lambda\sum_{i=1}^r u^i_{sa}\min_{w_i\in\mathcal W^i}w_i^\top v\Big\},
--   $$
--   the deterministic form of the operator of (5.1), which the paper states is equivalent to the maximum over $\pi_s\in\Delta$.
--
--   This is the common model of every statement of the mission.
--
--   **Formalization Note** States and actions are arbitrary finite types; factors are indexed by `Fin r`, i.e. the paper's $[r]=\{1,\dots,r\}$ shifted to $\{0,\dots,r-1\}$. A factor matrix is a function `W : Fin r → S → ℝ` whose $i$-th entry is the factor $w_i$. Nonemptiness of $\mathcal W$ is implicit in the paper (a minimum over $\mathcal W$ is taken) and is a field of the structure. The second sentence of Assumption 2.4 (an $\epsilon$-optimization oracle of cost $\mathrm{comp}(\mathcal W^i)$) only feeds operation counts and is not formalized. Value functions are the discounted sums, not fixed points of a Bellman equation, so that no Bellman identity holds by definition. The infima `z` and `minFactor` are real `sInf`s; theorems state minima and maxima with `IsLeast`/`IsGreatest`. The discount $\lambda$ is an argument (`lam`) of every discounted object, because this mission varies it; theorems at a fixed discount assume $0<\lambda<1$.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), pp. 1–10 and 26–27, §1–§3, (1.1), (1.2), (2.1), (2.2), Assumptions 2.2, 2.4, (3.1), (5.1), Appendix A p. 22, Appendix G.1 p. 26

import Mathlib
import Definitions.Def_FactorRMDP_ValueIter_Model

namespace FactorRMDP.Blackwell

open Matrix Filter Topology

/-- §1–§2 (pp. 1–3): finite states `S` (𝕊) and actions `A` (𝔸), `r` factors (`Fin r`, the paper's
[r] shifted to 0-based), rewards r_sa ≥ 0, initial distribution p₀ ∈ Δ(𝕊), coefficients u^i_sa
(`u i s a`), and the factor matrix set 𝒲 of (2.1)–(2.2). A factor matrix is `W : Fin r → S → ℝ`;
`W i` is the factor wᵢ (the i-th column of W ∈ ℝ^{S×r}). 𝒲 is nonempty, convex and compact, and
every factor of every W ∈ 𝒲 is a probability vector on 𝕊. -/
structure Model (S A : Type*) [Fintype S] [Fintype A] (r : ℕ) where
  rew : S → A → ℝ
  p0 : S → ℝ
  u : Fin r → S → A → ℝ
  Wset : Set (Fin r → S → ℝ)
  rew_nonneg : ∀ s a, 0 ≤ rew s a
  p0_mem : p0 ∈ stdSimplex ℝ S
  u_nonneg : ∀ i s a, 0 ≤ u i s a
  u_sum : ∀ s a, ∑ i, u i s a = 1
  W_simplex : ∀ W ∈ Wset, ∀ i, W i ∈ stdSimplex ℝ S
  W_nonempty : Wset.Nonempty
  W_convex : Convex ℝ Wset
  W_compact : IsCompact Wset

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] {r : ℕ}

namespace Model
variable (M : Model S A r)

/-- 𝒲ⁱ: the projection of 𝒲 on the i-th factor. -/
def factorSet (i : Fin r) : Set (S → ℝ) := (fun W => W i) '' M.Wset

/-- Assumption 2.2 (r-rectangularity): 𝒲 = 𝒲¹ × ⋯ × 𝒲^r. -/
def IsRRect : Prop := M.Wset = Set.univ.pi M.factorSet

/-- r_π = (Σ_a π_sa r_sa)_s. -/
def rpi (π : S → A → ℝ) : S → ℝ := fun s => ∑ a, π s a * M.rew s a

/-- T_π = (Σ_a π_sa u^i_sa)_{(s,i)} (p. 6). -/
def T (π : S → A → ℝ) : Matrix S (Fin r) ℝ := fun s i => ∑ a, π s a * M.u i s a

/-- L(π, W) = T_π Wᵀ, the transition matrix on 𝕊 under π and the kernel of W (p. 20, p. 27):
[L]_{ss′} = Σ_a π_sa P_sas′ with P_sas′ = Σᵢ u^i_sa w_{i,s′}. -/
def L (π : S → A → ℝ) (W : Fin r → S → ℝ) : Matrix S S ℝ := M.T π * (FactorRMDP.ValueIter.wmat W)ᵀ

/-- v^{π,W}_λ: the expected discounted reward (1.1) from each initial state, for a stationary π,
Σ_t λ^t L(π,W)^t r_π. -/
noncomputable def value (lam : ℝ) (π : S → A → ℝ) (W : Fin r → S → ℝ) : S → ℝ :=
  ∑' t : ℕ, lam ^ t • ((M.L π W) ^ t *ᵥ M.rpi π)

/-- R(π, W, λ) = p₀ᵀ v^{π,W}_λ, i.e. (1.1) with s₀ ∼ p₀. -/
noncomputable def R (lam : ℝ) (π : S → A → ℝ) (W : Fin r → S → ℝ) : ℝ :=
  M.p0 ⬝ᵥ M.value lam π W

/-- β: the adversary's value function in the adversarial MDP (3.1), from each factor-state i:
Σ_t λ^t (WᵀT_π)^t Wᵀ r_π. -/
noncomputable def advValue (lam : ℝ) (π : S → A → ℝ) (W : Fin r → S → ℝ) : Fin r → ℝ :=
  ∑' t : ℕ, lam ^ t • ((((FactorRMDP.ValueIter.wmat W)ᵀ * M.T π) ^ t) *ᵥ ((FactorRMDP.ValueIter.wmat W)ᵀ *ᵥ M.rpi π))

/-- The values of the policy evaluation problem: the set {R(π, W, λ) | W ∈ 𝒲}. Theorems state
z(π) = min with `IsLeast` of this set. -/
def evalValues (lam : ℝ) (π : S → A → ℝ) : Set ℝ := M.R lam π '' M.Wset

/-- z_λ(π) = min_{W∈𝒲} R(π, W, λ), as a real `sInf` of `evalValues` (nonempty, bounded below by 0
for policies in Π and λ ∈ (0, 1), and attained since 𝒲 is compact). -/
noncomputable def z (lam : ℝ) (π : S → A → ℝ) : ℝ := sInf (M.evalValues lam π)

/-- (π*, W*) is a solution of the robust MDP problem (1.2) over Π (as in (4.1)): π* ∈ Π attains
max_{π∈Π} z_λ(π), and W* ∈ 𝒲 attains min_{W∈𝒲} R(π*, W, λ). -/
def IsRobustSolution (lam : ℝ) (π : S → A → ℝ) (W : Fin r → S → ℝ) : Prop :=
  π ∈ FactorRMDP.ValueIter.Policies S A ∧ W ∈ M.Wset ∧
    IsGreatest (M.z lam '' FactorRMDP.ValueIter.Policies S A) (M.z lam π) ∧ IsLeast (M.evalValues lam π) (M.R lam π W)

/-- min_{wᵢ∈𝒲ⁱ} wᵢᵀ v (a real `sInf`; 𝒲ⁱ is nonempty and compact). -/
noncomputable def minFactor (i : Fin r) (v : S → ℝ) : ℝ :=
  sInf ((fun w => w ⬝ᵥ v) '' M.factorSet i)

/-- φ(π, β)ᵢ = min_{wᵢ∈𝒲ⁱ} wᵢᵀ(r_π + λ T_π β) (Appendix A, p. 22). -/
noncomputable def phi (lam : ℝ) (π : S → A → ℝ) (β : Fin r → ℝ) : Fin r → ℝ :=
  fun i => M.minFactor i (M.rpi π + lam • (M.T π *ᵥ β))

/-- F (p. 10), in the deterministic form the paper states equivalent to (5.1):
F(v)_s = max_{a∈𝔸} { r_sa + λ Σᵢ u^i_sa min_{wᵢ∈𝒲ⁱ} wᵢᵀv }. -/
noncomputable def F [Nonempty A] (lam : ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => Finset.univ.sup' Finset.univ_nonempty
    (fun a => M.rew s a + lam * ∑ i, M.u i s a * M.minFactor i v)

end Model
end FactorRMDP.Blackwell


