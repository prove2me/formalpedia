-- Prove2me | Definitions.Def_BundleShaping_NoOrderSet_Model
-- name    : BundleShaping_NoOrderSet_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:11:32.87752+00:00
-- url     : https://prove2.me/theorems/1323cecb-4588-4530-a5ef-f0e1a99cd04e
-- title:
--   §3–§5.1, eqs. (1), (9), (14), pp. 10–22 — bundle-to-stock assembly, replenishment and market-share DP: demand, costs, H_t, G_t, V_t, no-order-set problem
-- statement:
--   This file sets up the **bundle-to-stock (BTS)** dynamic program of Song and Xue for a firm that assembles $J$ potential bundles from $I$ items and chooses, in each period, which bundles to offer through a vector of market shares.
--
--   **Data.** There are $T\ge 1$ periods $t=1,\dots,T$ and a discount rate $\beta\in(0,1]$. The bill of materials is a nonnegative matrix $A=(\alpha_{ij})$: bundle $j$ uses $\alpha_{ij}$ units of item $i$. In period $t$ the expected volume of potential customers is $\lambda_t>0$, and $\varepsilon_t=(\varepsilon_{jt})_{j}$ is a random vector with law $\mu_t$, whose coordinates have zero mean and finite variance and may be correlated across bundles. $\Omega\subseteq\mathbb R^J_+$ is the set of feasible market-share vectors and $\tau_t:\Omega\to\mathbb R$ is the revenue rate function. Unit costs are $c_{it}$ (procurement), $a_{jt}$ (assembly), $b_{jt}$ (backorder) and $h_{it}$ (holding), and
--
--   $$c^p_{it}=c_{it}-\beta c_{i,t+1},\quad a^p_{jt}=a_{jt}-\beta a_{j,t+1},\quad b^p_{jt}=b_{jt}-a^p_{jt},\quad \tilde c_{jt}=\sum_i c_{it}\alpha_{ij},\quad \tilde h_{jt}=\sum_i h_{it}\alpha_{ij},\quad \tilde c^p_{jt}=\sum_i c^p_{it}\alpha_{ij}.$$
--
--   **Demand (1).** For a market-share vector $q$, the demand for bundle $j$ in period $t$ is $d_{jt}(q,\varepsilon_t)=q_j\lambda_t+q_j\varepsilon_{jt}$.
--
--   **The program (9).** With $x^-=\max(-x,0)$ and $x^+=\max(x,0)$ taken coordinatewise, row-vector costs and $E$ the expectation under $\mu_t$,
--
--   $$\pi_t(q)=\tau_t(q)-a_tq-c_tAq,\qquad H_t(y,z,q)=b^p_tE(z-d_t)^-+h_tAE(z-d_t)^++h_t(y-Az),$$
--
--   $$G^m_t(y,z,q)=\lambda_t\pi_t(q)-c^p_t(y-\lambda_tAq)-H_t(y,z,q),\qquad G_t(y,z,q)=G^m_t(y,z,q)+\beta E\,V_{t+1}(y-Ad_t),$$
--
--   $$V_{T+1}\equiv 0,\qquad V_t(x)=\sup\{G_t(y,z,q): y-Az\ge 0,\ y\ge x,\ q\in\Omega\},\quad t=1,\dots,T.$$
--
--   Here $x$ is the net inventory of items, $y$ the item order-up-to level, $z$ the scheduled net production of bundles and $q$ the market-share vector. A triple is **optimal in (9)** if it is feasible and maximizes $G_t$ over the feasible set.
--
--   **No-order sets.** For $I^+\subseteq\{1,\dots,I\}$ (items that are not ordered) and $I^-$ its complement, the **modified problem** maximizes $G_t$ over $\{y_{I^+}=x_{I^+},\ y\ge Az,\ q\in\Omega\}$, and problem **(14)** maximizes $G_t$ over $\{y_{I^+}=x_{I^+},\ y_{I^-}=[Az]_{I^-},\ y\ge Az,\ q\in\Omega\}$. The **bundling strategy** of $q$ is $\{j: q_j>0\}$.
--
--   **Standing assumptions.** Property-CV (Definition 1, Assumption 1): $\tau_t$ is concave on $\Omega$, and $\Omega$ is compact and convex; $b^p_t\ge 0$ and $c^p_t+h_t\ge 0$ (p. 17). The **coercivity conditions** used for existence of maximizers are: $\tau_t$ continuous on $\Omega$, $\tilde c^p_{jt}<b^p_{jt}$ and $\tilde c^p_{jt}+\tilde h_{jt}>0$, i.e. the fill rate $\xi_{jt}=(b^p_{jt}-\tilde c^p_{jt})/(b^p_{jt}+\tilde h_{jt})$ of §5.2 lies in $(0,1)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Items and bundles are finite types; vectors are functions to $\mathbb R$ ordered coordinatewise, and $Az$ is `A *ᵥ z`. The value function is defined by recursion on the number of remaining periods, so $V_t=0$ for $t>T$; $V_t(x)$ is a real supremum (`sSup`), which is a genuine finite supremum under the standing assumptions. The sign conventions $h_t\ge 0$, $A\ge 0$, $\lambda_t>0$, $0<\beta\le 1$, $\Omega\subseteq\mathbb R^J_+$ and $\Omega\neq\emptyset$ are implicit in the paper and are made explicit in `Standing`. Period-indexed assumptions are imposed for $1\le t\le T$. The set (14) keeps the constraint $y\ge Az$ of the modified problem, which the printed (14) omits (see the text following Lemma 2).
-- source:
--   Song & Xue, Demand Shaping Through Bundling and Product Configuration, SSRN 3168907 (version of Aug. 19, 2020), pp. 10–22: eq. (1) p. 11, Definition 1 p. 12, Assumption 1 p. 15, cost vectors p. 17, program (P)/(9) p. 19, modified problem and (14) p. 22; fill rate ξ p. 25

import Mathlib

namespace BundleShaping.NoOrderSet

open MeasureTheory Matrix

noncomputable section

/-- Data of the bundle-to-stock (BTS) model of Song & Xue, §3–§4 (pp. 10–19).
Items are indexed by `I`, potential bundles by `J`, periods by `t : ℕ` (the paper's
`t ∈ {1, …, T}`; costs `c` and `a` are also read at `T + 1`). -/
structure Params (I J : Type) [Fintype I] [Fintype J] where
  /-- planning horizon `T` -/
  T : ℕ
  /-- discount rate `β` (p. 16) -/
  β : ℝ
  /-- bill of materials `A = (α_ij)` (p. 10) -/
  A : Matrix I J ℝ
  /-- expected volume of potential customers `λ_t` (eq. (1)) -/
  lam : ℕ → ℝ
  /-- law of the random error vector `ε_t = (ε_jt)_j` of period `t` (eq. (1));
  correlation across bundles `j` is allowed -/
  μ : ℕ → Measure (J → ℝ)
  /-- set `Ω` of feasible market-share vectors (Definition 1) -/
  Ω : Set (J → ℝ)
  /-- revenue rate function `τ_t` (p. 12) -/
  τ : ℕ → (J → ℝ) → ℝ
  /-- unit procurement cost `c_it` (p. 17) -/
  c : ℕ → I → ℝ
  /-- unit assembly cost `a_jt` (p. 17) -/
  a : ℕ → J → ℝ
  /-- unit backorder cost `b_jt` (p. 17) -/
  b : ℕ → J → ℝ
  /-- unit holding cost `h_it` (p. 17) -/
  h : ℕ → I → ℝ

variable {I J : Type} [Fintype I] [Fintype J]

namespace Params

variable (P : Params I J)

/-- `cᵖ_it = c_it − β c_{i,t+1}` (p. 17). -/
def cp (t : ℕ) (i : I) : ℝ := P.c t i - P.β * P.c (t + 1) i

/-- `aᵖ_jt = a_jt − β a_{j,t+1}` (p. 17). -/
def ap (t : ℕ) (j : J) : ℝ := P.a t j - P.β * P.a (t + 1) j

/-- `bᵖ_jt = b_jt − aᵖ_jt` (p. 17). -/
def bp (t : ℕ) (j : J) : ℝ := P.b t j - P.ap t j

/-- `c̃_jt = Σ_i c_it α_ij` (p. 17). -/
def ctil (t : ℕ) (j : J) : ℝ := ∑ i, P.c t i * P.A i j

/-- `h̃_jt = Σ_i h_it α_ij` (p. 17). -/
def htil (t : ℕ) (j : J) : ℝ := ∑ i, P.h t i * P.A i j

/-- `c̃ᵖ_jt = Σ_i cᵖ_it α_ij`, the bundle-level procurement savings (`cᵖ_t A`, p. 25). -/
def ctilp (t : ℕ) (j : J) : ℝ := ∑ i, P.cp t i * P.A i j

/-- Demand (1): `d_jt(q, ε_t) = q_j λ_t + q_j ε_jt`. -/
def demand (t : ℕ) (q ε : J → ℝ) : J → ℝ := fun j => q j * P.lam t + q j * ε j

/-- Profit rate `π_t(q) = τ_t(q) − a_t q − c_t A q` (p. 19). -/
def profitRate (t : ℕ) (q : J → ℝ) : ℝ :=
  P.τ t q - ∑ j, P.a t j * q j - ∑ i, P.c t i * (P.A *ᵥ q) i

/-- Expected inventory cost (p. 19):
`H_t(y, z, q) = bᵖ_t E(z − d_t)⁻ + h_t A E(z − d_t)⁺ + h_t (y − Az)`,
with `x⁻ = max(−x, 0)` and `x⁺ = max(x, 0)`. -/
def H (t : ℕ) (y : I → ℝ) (z q : J → ℝ) : ℝ :=
  (∑ j, P.bp t j * ∫ ε, max (P.demand t q ε j - z j) 0 ∂(P.μ t))
  + (∑ i, P.h t i * ∑ j, P.A i j * ∫ ε, max (z j - P.demand t q ε j) 0 ∂(P.μ t))
  + ∑ i, P.h t i * (y - P.A *ᵥ z) i

/-- Expected one-period profit (p. 19):
`Gᵐ_t(y, z, q) = λ_t π_t(q) − cᵖ_t (y − λ_t A q) − H_t(y, z, q)`. -/
def Gm (t : ℕ) (y : I → ℝ) (z q : J → ℝ) : ℝ :=
  P.lam t * P.profitRate t q - ∑ i, P.cp t i * (y - P.lam t • (P.A *ᵥ q)) i - P.H t y z q

/-- Feasible set of (9) at net inventory `x`: `y − Az ≥ 0`, `y ≥ x`, `q ∈ Ω`. -/
def Feas9 (x y : I → ℝ) (z q : J → ℝ) : Prop :=
  P.A *ᵥ z ≤ y ∧ x ≤ y ∧ q ∈ P.Ω

/-- Value recursion indexed by the number `k` of remaining stages:
`Vfrom 0 t = 0` and `Vfrom (k+1) t x = sup { Gᵐ_t(y,z,q) + β E[Vfrom k (t+1) (y − A d_t)] : (9) }`. -/
def Vfrom : ℕ → ℕ → (I → ℝ) → ℝ
  | 0, _, _ => 0
  | k + 1, t, x =>
      sSup {v | ∃ (y : I → ℝ) (z q : J → ℝ), P.Feas9 x y z q ∧
        v = P.Gm t y z q + P.β * ∫ ε, Vfrom k (t + 1) (y - P.A *ᵥ P.demand t q ε) ∂(P.μ t)}

/-- The BTS value function `V_t` of (9): `V_t(x) = max {G_t(y,z,q) : y − Az ≥ 0, y ≥ x, q ∈ Ω}`
for `t ≤ T`, and `V_t = 0` for `t > T` (in particular `V_{T+1} = 0`). -/
def V (t : ℕ) (x : I → ℝ) : ℝ := P.Vfrom (P.T + 1 - t) t x

/-- `G_t(y, z, q) = Gᵐ_t(y, z, q) + β E V_{t+1}(y − A d_t)` (p. 19). -/
def G (t : ℕ) (y : I → ℝ) (z q : J → ℝ) : ℝ :=
  P.Gm t y z q + P.β * ∫ ε, P.V (t + 1) (y - P.A *ᵥ P.demand t q ε) ∂(P.μ t)

/-- `(y, z, q)` is optimal in (9) at period `t` and net inventory `x`. -/
def Opt9 (t : ℕ) (x y : I → ℝ) (z q : J → ℝ) : Prop :=
  P.Feas9 x y z q ∧ ∀ (y' : I → ℝ) (z' q' : J → ℝ), P.Feas9 x y' z' q' → P.G t y' z' q' ≤ P.G t y z q

/-- Feasible set of the modified problem of p. 22 with no-order set `S = I⁺`:
`y_{I⁺} = x_{I⁺}`, `y ≥ Az`, `q ∈ Ω` (the constraint `y_i ≥ x_i`, `i ∈ I⁻`, removed). -/
def FeasMod (S : Finset I) (x y : I → ℝ) (z q : J → ℝ) : Prop :=
  (∀ i ∈ S, y i = x i) ∧ P.A *ᵥ z ≤ y ∧ q ∈ P.Ω

/-- Feasible set of (14) with no-order set `S = I⁺`: `y_{I⁺} = x_{I⁺}`, `y_{I⁻} = [Az]_{I⁻}`,
`q ∈ Ω`, and (kept from the modified problem) `Az ≤ y`. -/
def Feas14 (S : Finset I) (x y : I → ℝ) (z q : J → ℝ) : Prop :=
  (∀ i ∈ S, y i = x i) ∧ (∀ i, i ∉ S → y i = (P.A *ᵥ z) i) ∧ P.A *ᵥ z ≤ y ∧ q ∈ P.Ω

/-- `(y, z, q)` is a maximizer of `G_t` over the feasible set of (14) for `S = I⁺`. -/
def Max14 (t : ℕ) (S : Finset I) (x y : I → ℝ) (z q : J → ℝ) : Prop :=
  P.Feas14 S x y z q ∧
    ∀ (y' : I → ℝ) (z' q' : J → ℝ), P.Feas14 S x y' z' q' → P.G t y' z' q' ≤ P.G t y z q

/-- `(y, z, q)` is a maximizer of `G_t` over the modified problem of p. 22 for `S = I⁺`. -/
def MaxMod (t : ℕ) (S : Finset I) (x y : I → ℝ) (z q : J → ℝ) : Prop :=
  P.FeasMod S x y z q ∧
    ∀ (y' : I → ℝ) (z' q' : J → ℝ), P.FeasMod S x y' z' q' → P.G t y' z' q' ≤ P.G t y z q

/-- Standing assumptions of §3–§4 (pp. 10–17), together with the implicit sign conventions
of the model: `1 ≤ T`, `0 < β ≤ 1`, `A ≥ 0`; for every period `1 ≤ t ≤ T`: `λ_t > 0`,
`ε_t` has a probability law whose coordinates have zero mean and finite variance,
`τ_t` is concave on `Ω` (Property-CV (a), Assumption 1), `bᵖ_t ≥ 0`, `cᵖ_t + h_t ≥ 0`
(p. 17), `h_t ≥ 0`; and `Ω` is a nonempty compact convex subset of `ℝ^J_+`
(Property-CV (b)). -/
def Standing : Prop :=
  1 ≤ P.T ∧ 0 < P.β ∧ P.β ≤ 1 ∧ (∀ i j, 0 ≤ P.A i j) ∧
  P.Ω.Nonempty ∧ IsCompact P.Ω ∧ Convex ℝ P.Ω ∧ (∀ q ∈ P.Ω, 0 ≤ q) ∧
  ∀ t, 1 ≤ t → t ≤ P.T →
    0 < P.lam t ∧ IsProbabilityMeasure (P.μ t) ∧
    (∀ j, Integrable (fun ε : J → ℝ => ε j) (P.μ t)) ∧
    (∀ j, ∫ ε, ε j ∂(P.μ t) = 0) ∧
    (∀ j, MemLp (fun ε : J → ℝ => ε j) 2 (P.μ t)) ∧
    ConcaveOn ℝ P.Ω (P.τ t) ∧
    (∀ j, 0 ≤ P.bp t j) ∧ (∀ i, 0 ≤ P.cp t i + P.h t i) ∧ (∀ i, 0 ≤ P.h t i)

/-- Added for the existence clause of Theorem 2(b) and for Theorem 2(c): for `1 ≤ t ≤ T`,
`τ_t` is continuous on `Ω`, and `c̃ᵖ_jt < bᵖ_jt`, `0 < c̃ᵖ_jt + h̃_jt` (equivalently the
fill rate `ξ_jt = (bᵖ_jt − c̃ᵖ_jt)/(bᵖ_jt + h̃_jt)` of §5.2 lies in `(0, 1)`). -/
def Coercive : Prop :=
  ∀ t, 1 ≤ t → t ≤ P.T →
    ContinuousOn (P.τ t) P.Ω ∧ (∀ j, P.ctilp t j < P.bp t j) ∧ (∀ j, 0 < P.ctilp t j + P.htil t j)

end Params

/-- The bundling strategy `S(q) = {j : q_j > 0}` of a market-share vector (§3.1, p. 10;
Theorem 2(c)). -/
def bundlingStrategy (q : J → ℝ) : Set J := {j | 0 < q j}

end

end BundleShaping.NoOrderSet


