-- Prove2me | Definitions.Def_ReusableAssort_Hybrid_Model
-- name    : ReusableAssort_Hybrid_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:00.482835+00:00
-- url     : https://prove2.me/theorems/85b2fd81-27db-47de-81f0-733116582cec
-- title:
--   §2.1–§2.2 and (1), pp. 8–11 — instance, Assumptions 1–2, the Bayesian expected LP, c_min and ε*
-- statement:
--   This file sets up the model of Bayesian online assortment of reusable resources and its linear-programming benchmark.
--
--   **Instance.** A platform rents $n$ products; product $i$ has an integer initial inventory $c_i \ge 1$. Consumers arrive at times $t = 1, \dots, T$. Consumer $t$ has a type $z_t$ drawn independently from a known distribution $F_t$ on a finite type space $\mathcal Z$. A type $z$ fixes a choice model $\phi^z(S, i)$ (the probability that a consumer of type $z$ rents product $i$ when offered the assortment $S$), rental fees $r^z_i$, and for each product a rental-duration distribution $g^z_i$ on $\{1, \dots, T\}$. Assortments are drawn from a collection $\mathcal S$ of feasible subsets of $[n]$. Write $\bar G^z_i(k) = \Pr[d > k]$ for $d \sim g^z_i$.
--
--   **Assumptions.** The instance satisfies
--   1. *weak substitutability* (Assumption 1): $\phi^z(\emptyset, i) = 0$, and $\phi^z(S \cup \{j\}, i) \le \phi^z(S, i)$ for $S, S \cup \{j\} \in \mathcal S$ and $j \ne i$;
--   2. *downward-closed feasibility* (Assumption 2): $\mathcal S$ is nonempty and closed under taking subsets;
--   3. for $S \in \mathcal S$, $\phi^z(S, \cdot)$ is a sub-probability supported on $S$ (the remaining mass is the probability of renting nothing);
--   4. fees are nonnegative, each $g^z_i$ is a probability distribution on $\{1, \dots, T\}$, and each $F_t$ ($1 \le t \le T$) is a probability distribution on $\mathcal Z$.
--
--   **The benchmark** Expected-LP$[\{F_t\}_{t=1}^T]$ has a variable $y_{S,t,z} \ge 0$ for each $S \in \mathcal S$, time $t$ and type $z$:
--   $$\max_{y \ge 0} \sum_{t=1}^T \sum_{z} \sum_{S \in \mathcal S} \sum_{i=1}^n F_t(z)\, r^{z}_i\, \phi^{z}(S, i)\, y_{S,t,z}$$
--   subject to $\sum_{\tau=1}^t \sum_{z} \sum_{S \in \mathcal S} F_\tau(z)\, \bar G^{z}_i(t-\tau)\, \phi^{z}(S,i)\, y_{S,\tau,z} \le c_i$ for every product $i$ and time $t$, and $\sum_{S \in \mathcal S} y_{S,t,z} \le 1$ for every $t$ and $z$. A solution is *normalized* when $\sum_{S \in \mathcal S} y_{S,t,z} = 1$ for all $t, z$ (possible without loss of generality since $\emptyset \in \mathcal S$). The *contribution* of product $i$ is $\sum_t \sum_z \sum_{S} F_t(z)\, y_{S,t,z}\, \phi^z(S,i)\, r^z_i$; the objective is the sum of the contributions. Finally $c_{\min} = \min_i c_i$ and
--   $$\varepsilon^*(x) = \min_{\gamma \in [0,1]} \; 1 - (1-\gamma)\Big(1 - \exp\Big(-\frac{\gamma^2 x}{2-\gamma}\Big)\Big),$$
--   with $\gamma^*(x)$ denoting any minimizer.
--
--   These objects are shared by every statement of the mission: the online algorithms are compared with the LP value, and their guarantees are expressed through $\varepsilon^*$.
--
--   **Formalization Note** Products are `Fin n` (the paper's product $i$ is index $i-1$); times are the paper's $1, \dots, T$. One finite type space replaces the per-time spaces $\mathcal Z_t$ ($F_t$ may vanish off $\mathcal Z_t$). Durations live in $\{1,\dots,T\}$ (a longer duration never returns within the horizon). The conditions on $\phi$ are imposed for $S \in \mathcal S$ only, and weak substitutability is required when $S \cup \{j\} \in \mathcal S$, because $\phi^z$ is defined on $\mathcal S$. Fees $r \ge 0$ and $c_i \ge 1$ are added (fees are payments; $c_i \in \mathbb Z_+$ and the DP (3) divides by $c_i$). $\varepsilon^*$ is the infimum of a continuous function over the compact interval $[0,1]$, so it is attained; $c_{\min}$ needs $n \ge 1$.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, pp. 8–11, §2.1 (Assumptions 1–2), §2.2 (Expected-LP[{F_t}_{t=1}^T]), §3 eq. (1) and the normalization of p. 11

import Mathlib

namespace ReusableAssort.Hybrid

/-- An instance of Bayesian online assortment of reusable resources (§2.1, pp. 8–9).
Products are `Fin n` (the paper's product `i` is `⟨i - 1, _⟩`), times are `1, …, T`,
types range over one finite type space `Z` (the disjoint union of the paper's `𝒵_t`).
* `c i` — initial inventory `c_i`;
* `feas` — the collection `𝒮` of feasible assortments;
* `phi z S i` — the choice probability `ϕ^z(S, i)`;
* `r z i` — the rental fee `r^z_i`;
* `g z i d` — the p.d.f. `g^z_i(d)` of the rental duration;
* `F t z` — the type distribution `F_t(z)` at time `t`. -/
structure Instance (n T : ℕ) (Z : Type) [Fintype Z] where
  c : Fin n → ℕ
  feas : Finset (Finset (Fin n))
  phi : Z → Finset (Fin n) → Fin n → ℝ
  r : Z → Fin n → ℝ
  g : Z → Fin n → ℕ → ℝ
  F : ℕ → Z → ℝ

variable {n T : ℕ} {Z : Type} [Fintype Z]

/-- The standing assumptions of §2.1: Assumption 1 (weak substitutability, on `𝒮`),
Assumption 2 (downward-closed feasibility, `𝒮` nonempty), `ϕ^z(S, ·)` a sub-probability
supported on `S` for `S ∈ 𝒮`, nonnegative fees, integer inventories `c_i ≥ 1`, rental
durations distributed on `{1, …, T}`, and each `F_t` (`1 ≤ t ≤ T`) a probability
distribution on `Z`. -/
structure Instance.Assumptions (I : Instance n T Z) : Prop where
  phi_empty : ∀ z i, I.phi z ∅ i = 0
  weak_subst : ∀ z, ∀ S ∈ I.feas, ∀ i j, j ≠ i → insert j S ∈ I.feas →
    I.phi z (insert j S) i ≤ I.phi z S i
  feas_nonempty : I.feas.Nonempty
  down_closed : ∀ S ∈ I.feas, ∀ S' ⊆ S, S' ∈ I.feas
  phi_nonneg : ∀ z, ∀ S ∈ I.feas, ∀ i, 0 ≤ I.phi z S i
  phi_support : ∀ z, ∀ S ∈ I.feas, ∀ i, i ∉ S → I.phi z S i = 0
  phi_sum_le : ∀ z, ∀ S ∈ I.feas, ∑ i ∈ S, I.phi z S i ≤ 1
  r_nonneg : ∀ z i, 0 ≤ I.r z i
  one_le_c : ∀ i, 1 ≤ I.c i
  g_nonneg : ∀ z i d, 0 ≤ I.g z i d
  g_zero : ∀ z i, I.g z i 0 = 0
  g_gt : ∀ z i d, T < d → I.g z i d = 0
  g_sum : ∀ z i, ∑ d ∈ Finset.Icc 1 T, I.g z i d = 1
  F_nonneg : ∀ t z, 0 ≤ I.F t z
  F_sum : ∀ t ∈ Finset.Icc 1 T, ∑ z, I.F t z = 1

/-- `Ḡ^z_i(k) = Pr[d > k]` for a rental duration `d ∼ g^z_i`. -/
noncomputable def Gbar (I : Instance n T Z) (z : Z) (i : Fin n) (k : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 T).filter (fun d => k < d), I.g z i d

/-- Objective of Expected-LP[{F_t}] (p. 10); `y t z S` is `y_{S,t,z}`. -/
noncomputable def lpObj (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ∑ z, ∑ S ∈ I.feas, ∑ i,
    I.F t z * I.r z i * I.phi z S i * y t z S

/-- Feasibility for Expected-LP[{F_t}] (p. 10). -/
def LPFeasible (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) : Prop :=
  (∀ t ∈ Finset.Icc 1 T, ∀ z, ∀ S ∈ I.feas, 0 ≤ y t z S) ∧
  (∀ i, ∀ t ∈ Finset.Icc 1 T,
    ∑ τ ∈ Finset.Icc 1 t, ∑ z, ∑ S ∈ I.feas,
      I.F τ z * Gbar I z i (t - τ) * I.phi z S i * y τ z S ≤ I.c i) ∧
  (∀ t ∈ Finset.Icc 1 T, ∀ z, ∑ S ∈ I.feas, y t z S ≤ 1)

/-- An optimal solution of Expected-LP[{F_t}]. -/
def LPOptimal (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) : Prop :=
  LPFeasible I y ∧ ∀ y', LPFeasible I y' → lpObj I y' ≤ lpObj I y

/-- The normalization `∑_{S ∈ 𝒮} y_{S,t,z} = 1` of p. 11. -/
def Normalized (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ z, ∑ S ∈ I.feas, y t z S = 1

/-- The contribution of product `i` to the LP objective. -/
noncomputable def contrib (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) (i : Fin n) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ∑ z, ∑ S ∈ I.feas, I.F t z * y t z S * I.phi z S i * I.r z i

/-- `c_min = min_i c_i`. -/
def cmin [NeZero n] (I : Instance n T Z) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty I.c

/-- The function minimized in (1): `1 - (1 - γ)(1 - exp(-γ² x / (2 - γ)))`. -/
noncomputable def hfun (γ x : ℝ) : ℝ :=
  1 - (1 - γ) * (1 - Real.exp (-(γ ^ 2 * x / (2 - γ))))

/-- `ε*(x) = min_{γ ∈ [0,1]} hfun γ x`, equation (1), p. 11. -/
noncomputable def epsStar (x : ℝ) : ℝ :=
  sInf ((fun γ => hfun γ x) '' Set.Icc 0 1)

/-- `γ` is a minimizer `γ*(x)` of (1). -/
def IsGammaStar (x γ : ℝ) : Prop :=
  γ ∈ Set.Icc (0 : ℝ) 1 ∧ hfun γ x = epsStar x

end ReusableAssort.Hybrid


