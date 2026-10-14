-- Prove2me | Definitions.Def_FactorRMDP_ValueIter_Model
-- name    : FactorRMDP_ValueIter_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T19:32:49.356139+00:00
-- url     : https://prove2.me/theorems/7bd07e52-deb8-470c-8c5c-f139e7e7ba4e
-- title:
--   §1–§5, pp. 1–10 — the factor-matrix robust MDP: rewards, p₀, coefficients u, the factor matrix set 𝒲, r-rectangularity, policies, T_π, v^{π,W}, R(π,W), β, z(π), φ and F
-- statement:
--   A **robust Markov decision process with factor matrix uncertainty** consists of the following data.
--
--   1. A finite set of states $\mathbb S$ and a finite, nonempty set of actions $\mathbb A$.
--   2. Nonnegative rewards $r_{sa} \ge 0$ for $(s,a) \in \mathbb S \times \mathbb A$, and an initial distribution $p_0$ on $\mathbb S$.
--   3. A number $r$ of **factors**, indexed by $[r]$, and fixed coefficients $u^i_{sa} \ge 0$ with $\sum_{i=1}^r u^i_{sa} = 1$ for every $(s,a)$.
--   4. A nonempty, convex, compact set $\mathcal W$ of **factor matrices** $W = (w_1,\dots,w_r) \in \mathbb R^{S\times r}$ whose columns $w_i$ are probability vectors on $\mathbb S$.
--
--   A factor matrix $W$ induces the transition kernel $P_{sas'} = \sum_{i=1}^r u^i_{sa} w_{i,s'}$. Write $\mathcal W^i$ for the set of $i$-th factors $\{w_i : W \in \mathcal W\}$. The set $\mathcal W$ is **r-rectangular** (Assumption 2.2) if $\mathcal W = \mathcal W^1 \times \cdots \times \mathcal W^r$.
--
--   A stationary policy $\pi = (\pi_{sa})$ assigns to every state a distribution $\pi_s$ on $\mathbb A$; the set of such policies is $\Pi$, and $\pi$ is **deterministic** if every $\pi_s$ puts mass $1$ on one action. For $\pi \in \Pi$ let $r_\pi = (\sum_a \pi_{sa} r_{sa})_s$ and $T_\pi = (\sum_a \pi_{sa} u^i_{sa})_{(s,i)} \in \mathbb R^{S\times r}$. The chain on $\mathbb S$ under $\pi$ and $W$ has transition matrix $L(\pi,W) = T_\pi W^\top$. For a discount factor $\lambda$ the decision maker's **value function** and the **expected discounted reward** are
--
--   $$v^{\pi,W} = \sum_{t=0}^\infty \lambda^t L(\pi,W)^t r_\pi, \qquad R(\pi,W) = p_0^\top v^{\pi,W},$$
--
--   and the **adversary's value function** in the adversarial MDP (3.1), with states $[r]$, actions $\mathbb S$ and policy $W$, is
--
--   $$\beta^{\pi,W} = \sum_{t=0}^\infty \lambda^t (W^\top T_\pi)^t W^\top r_\pi \in \mathbb R^r.$$
--
--   The worst-case reward of $\pi$ is $z(\pi) = \min_{W\in\mathcal W} R(\pi,W)$, and $(\pi^*,W^*)$ **solves the robust MDP problem** if $\pi^*$ maximizes $z$ over $\Pi$ and $W^*$ minimizes $R(\pi^*,\cdot)$ over $\mathcal W$. Finally,
--
--   $$\varphi(\pi,\beta)_i = \min_{w_i\in\mathcal W^i} w_i^\top(r_\pi + \lambda T_\pi\beta), \qquad F(v)_s = \max_{a\in\mathbb A}\Big\{ r_{sa} + \lambda \sum_{i=1}^r u^i_{sa} \min_{w_i\in\mathcal W^i} w_i^\top v \Big\},$$
--
--   and Algorithm VI-PI is $v^0 = 0$, $v^{k+1} = F(v^k)$. The quantity $\max_{\pi\in\Pi} R(\pi, W)$ is also named, for the min-max duality.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Factors are indexed by `Fin r`, i.e. $\{0,\dots,r-1\}$ instead of $\{1,\dots,r\}$. A factor matrix is a function `Fin r → S → ℝ`; `wmat W` is the $S\times r$ matrix with columns $w_i$. $\mathcal W^i$ is the projection of $\mathcal W$; r-rectangularity is a predicate `IsRRect`, not built into the structure, because some results hold without it. Nonemptiness of $\mathcal W$ and of $\mathbb A$ is implicit in the paper and explicit here. The discount $\lambda$ is an argument; theorems assume $0<\lambda<1$. $v^{\pi,W}$ and $\beta^{\pi,W}$ are the discounted sums, not solutions of Bellman equations. $z(\pi)$, $\min_{w_i}$ and $\max_\pi R(\pi,W)$ are real infima/suprema of nonempty bounded sets; theorems state attainment with `IsLeast`/`IsGreatest`. $F$ is the deterministic form (max over actions), which the paper states equivalent to its max over $\pi_s \in \Delta$ (p. 10). The ε-oracle of Assumption 2.4 is not formalized.
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), pp. 1–10, §1–§5, (1.1), (1.2), (2.1), (2.2), Assumption 2.2, (3.1), (VI-PI); Appendix A, p. 22 (φ); p. 10 (F)

import Mathlib

namespace FactorRMDP.ValueIter

open Matrix Filter Topology

/-- The robust MDP with factor matrix uncertainty of Goyal and Grand-Clément, *Robust Markov
Decision Process: Beyond Rectangularity*, arXiv:1811.00215v8 (2021), §1–§2, pp. 1–3, (1.1), (2.1),
(2.2): finite states `S` (𝕊) and actions `A` (𝔸), `r` factors indexed by `Fin r` (the paper's
`[r] = {1, …, r}` shifted to `{0, …, r - 1}`), rewards `rew s a = r_sa ≥ 0` (p. 1), an initial
distribution `p0 = p₀ ∈ Δ(𝕊)`, coefficients `u i s a = u^i_sa ≥ 0` with `∑ᵢ u^i_sa = 1`, and the set
`Wset = 𝒲` of factor matrices. A factor matrix is `W : Fin r → S → ℝ`; `W i` is the factor `wᵢ`
(the `i`-th column of `W ∈ ℝ^{S×r}`). By (2.1)–(2.2) every factor is a probability vector on `𝕊`,
and `𝒲` is convex and compact; its nonemptiness is implicit in the paper (a minimum over `𝒲` is
taken) and is a field here. The kernel induced by `W` is `P_sas′ = ∑ᵢ u^i_sa w_{i,s′}`. -/
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

/-- `Π`, the stationary, possibly randomized policies (pp. 1, 6): `π s a = π_sa`, and every row
`π_s` lies in the simplex `Δ` over `𝔸`. -/
def Policies (S A : Type*) [Fintype A] : Set (S → A → ℝ) := {π | ∀ s, π s ∈ stdSimplex ℝ A}

/-- A deterministic policy (p. 7): every row `π_s` is a vertex of `Δ`, i.e. `π_sa = 1` if
`a = d(s)` and `0` otherwise, for a map `d : 𝕊 → 𝔸`. -/
def IsDeterministic (π : S → A → ℝ) : Prop :=
  ∃ d : S → A, ∀ s a, π s a = if a = d s then 1 else 0

/-- The `S × r` matrix of a factor matrix: column `i` is `wᵢ`, so `(wmat W)ᵀ *ᵥ v = Wᵀv = (wᵢᵀv)ᵢ`. -/
def wmat (W : Fin r → S → ℝ) : Matrix S (Fin r) ℝ := fun s i => W i s

namespace Model

variable (M : Model S A r)

/-- `𝒲ⁱ`, the projection of `𝒲` on the `i`-th factor. Under r-rectangularity `𝒲 = 𝒲¹ × ⋯ × 𝒲^r`
these are exactly the factor sets of Assumption 2.2. -/
def factorSet (i : Fin r) : Set (S → ℝ) := (fun W => W i) '' M.Wset

/-- Assumption 2.2 (r-rectangularity), p. 4: `𝒲 = 𝒲¹ × ⋯ × 𝒲^r`. -/
def IsRRect : Prop := M.Wset = Set.univ.pi M.factorSet

/-- `r_π = (∑ₐ π_sa r_sa)_s`; its `s`-th entry is the paper's `r_{π_s,s}`. -/
def rpi (π : S → A → ℝ) : S → ℝ := fun s => ∑ a, π s a * M.rew s a

/-- `T_π = (∑ₐ π_sa u^i_sa)_{(s,i) ∈ 𝕊 × [r]}` (p. 6). -/
def T (π : S → A → ℝ) : Matrix S (Fin r) ℝ := fun s i => ∑ a, π s a * M.u i s a

/-- `L(π, W) = T_π Wᵀ`, the transition matrix on `𝕊` of the Markov chain induced by `π` and the
kernel of `W` (p. 20): `[L]_{ss′} = ∑ₐ π_sa P_sas′` with `P_sas′ = ∑ᵢ u^i_sa w_{i,s′}`. -/
def L (π : S → A → ℝ) (W : Fin r → S → ℝ) : Matrix S S ℝ := M.T π * (wmat W)ᵀ

/-- `v^{π,W}`, the decision maker's value function: the expected discounted reward (1.1) from each
initial state, `∑ₜ λᵗ L(π,W)ᵗ r_π` (the law of `s_t` from `s₀ = s` is row `s` of `L(π,W)ᵗ`). It is a
discounted sum, not the solution of a Bellman equation. -/
noncomputable def value (lam : ℝ) (π : S → A → ℝ) (W : Fin r → S → ℝ) : S → ℝ :=
  ∑' t : ℕ, lam ^ t • ((M.L π W) ^ t *ᵥ M.rpi π)

/-- `R(π, W) = p₀ᵀ v^{π,W}`, the expected discounted reward (1.1) with `s₀ ∼ p₀` (p. 8 writes
`R(π, W)` for `R(π, P)`). -/
noncomputable def R (lam : ℝ) (π : S → A → ℝ) (W : Fin r → S → ℝ) : ℝ :=
  M.p0 ⬝ᵥ M.value lam π W

/-- `β`, the adversary's value function in the adversarial MDP (3.1) with states `[r]`, actions `𝕊`
and policy `W`, from each factor-state `i`: `∑ₜ λᵗ (WᵀT_π)ᵗ Wᵀ r_π`. A discounted sum, not the
solution of the Bellman recursion (3.2). -/
noncomputable def advValue (lam : ℝ) (π : S → A → ℝ) (W : Fin r → S → ℝ) : Fin r → ℝ :=
  ∑' t : ℕ, lam ^ t • ((((wmat W)ᵀ * M.T π) ^ t) *ᵥ ((wmat W)ᵀ *ᵥ M.rpi π))

/-- The values `{R(π, W) | W ∈ 𝒲}` of the policy evaluation problem. -/
def evalValues (lam : ℝ) (π : S → A → ℝ) : Set ℝ := M.R lam π '' M.Wset

/-- `z(π) = min_{W ∈ 𝒲} R(π, W)` (p. 2), as a real infimum. The set is nonempty and bounded below by
`0`; theorems state attainment separately with `IsLeast`. -/
noncomputable def z (lam : ℝ) (π : S → A → ℝ) : ℝ := sInf (M.evalValues lam π)

/-- `(π*, W*)` solves the robust MDP problem (1.2) over `Π` (as in (4.1)): `π* ∈ Π` attains
`max_{π ∈ Π} z(π)` and `W* ∈ 𝒲` attains `min_{W ∈ 𝒲} R(π*, W)`. -/
def IsRobustSolution (lam : ℝ) (π : S → A → ℝ) (W : Fin r → S → ℝ) : Prop :=
  π ∈ Policies S A ∧ W ∈ M.Wset ∧
    IsGreatest (M.z lam '' Policies S A) (M.z lam π) ∧ IsLeast (M.evalValues lam π) (M.R lam π W)

/-- `max_{π ∈ Π} R(π, W)`, the nominal optimal value under the factor matrix `W` (right-hand side of
(4.7)), as a real supremum (nonempty since `𝔸` is nonempty, bounded above by `max r / (1 - λ)`). -/
noncomputable def maxR (lam : ℝ) (W : Fin r → S → ℝ) : ℝ :=
  sSup ((fun π => M.R lam π W) '' Policies S A)

/-- `min_{wᵢ ∈ 𝒲ⁱ} wᵢᵀ v`, as a real infimum (genuine: `𝒲ⁱ` is nonempty and compact). -/
noncomputable def minFactor (i : Fin r) (v : S → ℝ) : ℝ :=
  sInf ((fun w => w ⬝ᵥ v) '' M.factorSet i)

/-- `φ(π, β)ᵢ = min_{wᵢ ∈ 𝒲ⁱ} wᵢᵀ(r_π + λ T_π β)` (Appendix A, p. 22). The iterates of `φ(π, ·)`
from `0` are Algorithm VI-PE (p. 6). -/
noncomputable def phi (lam : ℝ) (π : S → A → ℝ) (β : Fin r → ℝ) : Fin r → ℝ :=
  fun i => M.minFactor i (M.rpi π + lam • (M.T π *ᵥ β))

/-- The operator `F` of §5 (p. 10) on `ℝ^S`, in the deterministic form the paper states equivalent to
its definition: `F(v)_s = max_{a ∈ 𝔸} { r_sa + λ ∑ᵢ u^i_sa min_{wᵢ ∈ 𝒲ⁱ} wᵢᵀ v }`. -/
noncomputable def F [Nonempty A] (lam : ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => Finset.univ.sup' Finset.univ_nonempty
    (fun a => M.rew s a + lam * ∑ i, M.u i s a * M.minFactor i v)

/-- Algorithm VI-PI (p. 9): `v⁰ = 0`, `v^{k+1} = F(v^k)`. -/
noncomputable def viPI [Nonempty A] (lam : ℝ) (k : ℕ) : S → ℝ := (M.F lam)^[k] 0

end Model

end FactorRMDP.ValueIter


