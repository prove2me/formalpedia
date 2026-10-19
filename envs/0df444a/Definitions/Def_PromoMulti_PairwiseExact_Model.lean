-- Prove2me | Definitions.Def_PromoMulti_PairwiseExact_Model
-- name    : PromoMulti_PairwiseExact_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:58.109765+00:00
-- url     : https://prove2.me/theorems/e92eeea9-68cb-49bc-b0c8-0e9de55681f2
-- title:
--   §2–§3, pp. 6–13 — multi-item promotion model: price ladders, demand (1), MPOP, pure promotion vectors, coefficients (5)/(6)/(15), App(κ) objective (4), (Multi-POP) feasible set
-- statement:
--   This file sets up the multi-item promotion optimization model of Cohen, Kalas and Perakis and the class of approximations $\mathrm{App}(\kappa)$.
--
--   **Instance.** There are $N$ items and a selling season of $T$ periods. As assumed in §2.1, inventory suffices to meet demand throughout the season; inventory is therefore not a decision variable. Item $i$ has a price ladder of $K^i+1$ price points $q^{i0}, q^{i1}, \dots, q^{iK^i}$, where level $0$ is the regular price, common to all items: $q^{i0}=q^0$. Item $i$ has unit costs $c^i_t$ and a memory parameter $M^i$. Under Assumption 1 the demand of item $i$ at period $t$ is a function
--   $$d^i_t\big(p^i_t, p^i_{t-1}, \dots, p^i_{t-M^i}, \mathbf p_t\big)$$
--   of its own current and $M^i$ past prices and of the current prices of the items (cross past prices do not enter).
--
--   **Plans and profit.** A plan $\gamma$ chooses a price level $\gamma^i_t \in \{0,\dots,K^i\}$ for every item and period, so $p^i_t = q^{i\gamma^i_t}$. Prices before the first period are $q^0$. The total profit of a plan is
--   $$\mathrm{MPOP}(\gamma)=\sum_{i=1}^N\sum_{t=1}^T (p^i_t-c^i_t)\, d^i_t\big(p^i_t,\dots,p^i_{t-M^i},\mathbf p_t\big),$$
--   and $\mathbf p^0$ is the regular plan, with level $0$ everywhere.
--
--   **Pure promotion vectors and coefficients.** A pattern $\sigma$ assigns a level $\sigma_i$ to each item; its support $S(\sigma)=\{i : \sigma_i\neq 0\}$ is the set of items it promotes. For a period $t$, $\mathbf p^\sigma_t$ is the plan using $\sigma$ at period $t$ and the regular price everywhere else, and $\sigma|_U$ keeps $\sigma$ on $U$ and sets level $0$ off $U$. The coefficient of $\sigma$ at $t$ is the alternating sum
--   $$b^\sigma_t=\sum_{U\subseteq S(\sigma)}(-1)^{|S(\sigma)|-|U|}\,\mathrm{MPOP}\big(\mathbf p^{\sigma|_U}_t\big).$$
--   For one promoted item this is (5), $b^{kj}_t=\mathrm{MPOP}(\mathbf p^{kj}_t)-\mathrm{MPOP}(\mathbf p^0)$; for two it is (6); for three it is (15). The contribution $[b^\sigma_t]_{i,\tau}$ of item $i$ at period $\tau$ is the same alternating sum with $\mathrm{MPOP}$ replaced by the profit of item $i$ at period $\tau$.
--
--   **App(κ).** The App(κ) objective of a plan $\gamma$ is
--   $$\mathrm{MPOP}(\mathbf p^0)+\sum_{t=1}^T\ \sum_{\sigma:\,1\le |S(\sigma)|\le\kappa} b^\sigma_t\,\mathbf 1\{\gamma^i_t=\sigma_i\ \text{for all } i\in S(\sigma)\},$$
--   which is (4) for $\kappa=2$. The feasible set is that of (Multi-POP): at most $L^i$ promotions of item $i$, at most one promotion of item $i$ in any window of $S^i+1$ consecutive periods, at most $L_T$ promotions in total, and at most $C_t$ promoted items in period $t$. An optimal solution of App(κ) is a feasible plan maximizing the App(κ) objective over all feasible plans. Finally, (8) says the cross-item effects are additively separable:
--   $$d^i_t\big(p^i_t,\dots,p^i_{t-M^i},\mathbf p_t\big)=h^i_t\big(p^i_t,\dots,p^i_{t-M^i}\big)+\sum_{j\neq i}H^{ji}_t(p^j_t).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Periods are `Fin T`, 0-based (period $t$ of the paper is index $t-1$); items are `Fin N`; all prices and profits are real. A plan is a function giving one level `Fin (K i + 1)` per item and period, which is the binary encoding $\gamma^{ik}_t$ with $\sum_k\gamma^{ik}_t=1$. The pairwise binaries $\gamma^{k\ell ij}_t$ of the paper are separate variables tied by the consistency constraints (7); for integral plans (7) forces them to equal $\gamma^{ki}_t\gamma^{\ell j}_t$, which is the indicator used in `appObj`. The paper writes App(κ) out only for $\kappa\le 2$ and says "one can similarly formalize" the rest; App(κ) for $\kappa\ge3$ is the inclusion–exclusion extension of (4), with the general coefficient of p. 38. Prices before period 1 are $q^0$ (a convention; the appendix uses $h^i_t(p^i_t,q^0,\dots,q^0)$). The demand receives the whole current price vector; coordinate $i$ duplicates the window's entry $0$, and (8) reads only the coordinates $j\neq i$. The ladder order $q^{iK^i}<\dots<q^{i1}<q^0$ is not imposed (Theorem 1 does not use it). The inter-item business rules 2, 3 and 5 of §2.2 are not in (Multi-POP) and are omitted. `open Classical` supplies decidability of the indicator.
-- source:
--   Cohen, Kalas & Perakis, Promotion Optimization for Multiple Items in Supermarkets, SSRN preprint 3061451, pp. 6–13 (PDF 6–13), §2, §3, Assumption 1, (1)–(7), (Multi-POP); p. 14 (PDF 14), (8); Appendix p. 38 (PDF 38), general coefficient

import Mathlib

open Classical

namespace PromoMulti.PairwiseExact

/-- A multi-item promotion instance (Cohen–Kalas–Perakis, §2, pp. 6–8): `N` items, `T` periods
(period `t` of the paper is index `t.val = t - 1`), price ladders with level `0` the regular
price `q⁰` common to all items, unit costs `cⁱₜ`, memories `Mⁱ`, and demand functions of the form
(1) under Assumption 1: `d i t w p` is the demand of item `i` at period `t` when its own window of
current and past prices is `w` (`w u = pⁱₜ₋ᵤ`, `u = 0, …, Mⁱ`) and the current price vector is `p`. -/
structure Instance (N T : ℕ) where
  /-- `Kⁱ`, the number of promotion prices of item `i`. -/
  K : Fin N → ℕ
  /-- The regular price `q⁰`. -/
  q0 : ℝ
  /-- The price ladder: `q i k = qⁱᵏ`, level `0` being the regular price. -/
  q : (i : Fin N) → Fin (K i + 1) → ℝ
  /-- p. 7: `qⁱ⁰ = q⁰` for every item. -/
  q_zero : ∀ i, q i 0 = q0
  /-- Unit costs `cⁱₜ`. -/
  c : Fin N → Fin T → ℝ
  /-- Memory parameters `Mⁱ`. -/
  M : Fin N → ℕ
  /-- Demand `dⁱₜ(pⁱₜ, …, pⁱₜ₋ₘⁱ, p⁻ⁱₜ)`: own window and current price vector. -/
  d : (i : Fin N) → Fin T → (Fin (M i + 1) → ℝ) → (Fin N → ℝ) → ℝ

variable {N T : ℕ}

/-- A plan: a price level for every item and period (the binaries `γⁱᵏₜ` with `Σₖ γⁱᵏₜ = 1`). -/
abbrev Plan (I : Instance N T) := (i : Fin N) → Fin T → Fin (I.K i + 1)

/-- The price `pⁱₜ = Σₖ qⁱᵏ γⁱᵏₜ` of item `i` at period `t` under plan `γ`. -/
def price (I : Instance N T) (γ : Plan I) (i : Fin N) (t : Fin T) : ℝ := I.q i (γ i t)

/-- The own price window `(pⁱₜ, pⁱₜ₋₁, …, pⁱₜ₋ₘⁱ)` of item `i` at period `t`; prices before the
first period are the regular price `q⁰` (convention). -/
def window (I : Instance N T) (γ : Plan I) (i : Fin N) (t : Fin T) : Fin (I.M i + 1) → ℝ :=
  fun u => if h : u.val ≤ t.val then price I γ i ⟨t.val - u.val, by omega⟩ else I.q0

/-- Profit `(pⁱₜ − cⁱₜ) dⁱₜ(…)` of item `i` at period `t` under plan `γ`. -/
def profit (I : Instance N T) (γ : Plan I) (i : Fin N) (t : Fin T) : ℝ :=
  (price I γ i t - I.c i t) * I.d i t (window I γ i t) (fun j => price I γ j t)

/-- The (Multi-POP) objective: total profit over all items and periods. -/
def MPOP (I : Instance N T) (γ : Plan I) : ℝ := ∑ i, ∑ t, profit I γ i t

/-- The regular plan `p⁰`: regular price for every item at every period. -/
def regular (I : Instance N T) : Plan I := fun _ _ => 0

/-- A single-period pattern: a price level for every item. -/
abbrev Pattern (I : Instance N T) := (i : Fin N) → Fin (I.K i + 1)

/-- The set of items a pattern promotes. -/
def supp {I : Instance N T} (σ : Pattern I) : Finset (Fin N) :=
  Finset.univ.filter (fun i => σ i ≠ 0)

/-- `σ|U`: keep the levels of `σ` on `U`, regular price elsewhere. -/
def restrict {I : Instance N T} (σ : Pattern I) (U : Finset (Fin N)) : Pattern I :=
  fun i => if i ∈ U then σ i else 0

/-- The pure promotion vector `pᵗ_σ`: pattern `σ` at period `t`, regular price everywhere else
(`pᵏʲₜ` of p. 12 for one item, `pᵏℓʲᵘₜ` of p. 13 for two items, …). -/
def pure (I : Instance N T) (t : Fin T) (σ : Pattern I) : Plan I :=
  fun i τ => if τ = t then σ i else 0

/-- The coefficient `b^σ_t = Σ_{U ⊆ S(σ)} (−1)^{|S(σ)| − |U|} MPOP(p_t^{σ|U})`, which is (5) for one
promoted item, (6) for two, (15) for three and the `b¹²···ᴷ` of p. 38 in general. -/
def coef (I : Instance N T) (t : Fin T) (σ : Pattern I) : ℝ :=
  ∑ U ∈ (supp σ).powerset,
    (-1 : ℝ) ^ ((supp σ).card - U.card) * MPOP I (pure I t (restrict σ U))

/-- The contribution of item `i` at period `τ` to the coefficient `b^σ_t` (the `[b^{ijk}]_{i,t}`
of p. 37). -/
def contrib (I : Instance N T) (t : Fin T) (σ : Pattern I) (i : Fin N) (τ : Fin T) : ℝ :=
  ∑ U ∈ (supp σ).powerset,
    (-1 : ℝ) ^ ((supp σ).card - U.card) * profit I (pure I t (restrict σ U)) i τ

/-- Plan `γ` uses pattern `σ` on the items `σ` promotes at period `t`; for an integral plan this
is the value of the product variable `γ^σ_t` forced by the consistency constraints (7). -/
def agrees {I : Instance N T} (γ : Plan I) (t : Fin T) (σ : Pattern I) : Prop :=
  ∀ i ∈ supp σ, γ i t = σ i

/-- The App(κ) objective of a plan: `MPOP(p⁰)` plus, for every period and every pattern promoting
between `1` and `κ` items, its coefficient times the indicator that the plan uses it ((4)). -/
noncomputable def appObj (I : Instance N T) (κ : ℕ) (γ : Plan I) : ℝ :=
  MPOP I (regular I) + ∑ t, ∑ σ ∈ Finset.univ.filter
      (fun σ : Pattern I => 1 ≤ (supp σ).card ∧ (supp σ).card ≤ κ),
    coef I t σ * (if agrees γ t σ then 1 else 0)

/-- The business-rule data of (Multi-POP): `Lⁱ`, `Sⁱ`, `L_T`, `Cₜ`. -/
structure Rules (N T : ℕ) where
  /-- `Lⁱ`: maximal number of promotions of item `i`. -/
  L : Fin N → ℕ
  /-- `Sⁱ`: no-touch period of item `i`. -/
  S : Fin N → ℕ
  /-- `L_T`: maximal total number of promotions. -/
  LT : ℕ
  /-- `Cₜ`: maximal number of promotions in period `t`. -/
  C : Fin T → ℕ

/-- The feasible set of (Multi-POP) (p. 10). -/
def Feasible {I : Instance N T} (R : Rules N T) (γ : Plan I) : Prop :=
  (∀ i, (Finset.univ.filter fun t => γ i t ≠ 0).card ≤ R.L i) ∧
  (∀ i (t : Fin T), (Finset.univ.filter fun τ : Fin T =>
      t ≤ τ ∧ τ.val ≤ t.val + R.S i ∧ γ i τ ≠ 0).card ≤ 1) ∧
  ((Finset.univ.filter fun p : Fin N × Fin T => γ p.1 p.2 ≠ 0).card ≤ R.LT) ∧
  (∀ t, (Finset.univ.filter fun i => γ i t ≠ 0).card ≤ R.C t)

/-- `γ` is an optimal solution of App(κ): feasible and maximizing the App(κ) objective over all
feasible plans. -/
def IsOptimalApp (I : Instance N T) (R : Rules N T) (κ : ℕ) (γ : Plan I) : Prop :=
  Feasible R γ ∧ ∀ γ' : Plan I, Feasible R γ' → appObj I κ γ' ≤ appObj I κ γ

/-- (8): the cross-item effects are additively separable,
`dⁱₜ(own window, pₜ) = hⁱₜ(own window) + Σ_{j ≠ i} Hʲⁱₜ(pʲₜ)`, with `H j i t = Hʲⁱₜ`. -/
def AdditiveCross (I : Instance N T) (h : (i : Fin N) → Fin T → (Fin (I.M i + 1) → ℝ) → ℝ)
    (H : Fin N → Fin N → Fin T → ℝ → ℝ) : Prop :=
  ∀ i t w (p : Fin N → ℝ), I.d i t w p = h i t w + ∑ j ∈ Finset.univ.erase i, H j i t (p j)

end PromoMulti.PairwiseExact


