-- Prove2me | Definitions.Def_GenericBudgets_AlmostEqual_Setting
-- name    : GenericBudgets_AlmostEqual_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:32:43.0235+00:00
-- url     : https://prove2.me/theorems/a747b137-9488-40df-96e0-45e1a7aebfa2
-- title:
--   §2, pp. 6–7; §§4–6, pp. 10–15 — allocations, prices, demand, CE, PO, standard valuations, (anti-)proportionality, truncated share, combination pricing, Condition (1), $T_i$, $R_i$
-- statement:
--   This file sets up the discrete Fisher market of Babaioff, Nisan and Talgam-Cohen with indivisible items and budgets of artificial currency.
--
--   **Market.** There are $m$ indivisible items $M=\{0,\dots,m-1\}$ and $n$ agents. Agent $i$ has a valuation $v_i : 2^M \to \mathbb R$ on bundles and a budget $b_i$. An **allocation** $\mathcal S=(\mathcal S_1,\dots,\mathcal S_n)$ is a partition of *all* items among the agents; it is represented by a map $\sigma$ sending each item to the agent who receives it, so that $\mathcal S_i=\{j : \sigma(j)=i\}$. A **price vector** $p\in\mathbb R^M$ prices a bundle additively, $p(S)=\sum_{j\in S}p_j$.
--
--   **Demand and equilibrium.** A bundle $S$ is **demanded** by an agent with valuation $w$ and budget $\beta$ at prices $p$ if
--   $$p(S)\le \beta \quad\text{and}\quad p(T)>\beta \text{ for every bundle } T \text{ with } w(T)>w(S).$$
--   A **competitive equilibrium (CE)** (Definition 2.1) is a pair $(\mathcal S,p)$ with non-negative prices such that every $\mathcal S_i$ is demanded by agent $i$. Prices are **budget-exhausting** for $\mathcal S$ if $p(\mathcal S_i)=b_i$ for every $i$. An allocation is **Pareto optimal (PO)** (Definition 2.3) if for every other allocation $\mathcal S'\ne\mathcal S$ some agent $i$ has $v_i(\mathcal S_i)>v_i(\mathcal S'_i)$.
--
--   **Standing assumptions on valuations** (§2.1): $w$ is additive ($w(S)=\sum_{j\in S}w(\{j\})$), normalized ($w(M)=1$), non-negative, monotone ($w(S)<w(T)$ whenever $S\subsetneq T$) and strict ($w(S)\ne w(T)$ whenever $S\ne T$).
--
--   **Fairness notions.** An allocation is **budget-proportional** if $v_i(\mathcal S_i)\ge b_i\,v_i(M)$ for every agent, and **anti-proportional** if $v_i(\mathcal S_i)\le b_i\,v_i(M)$ for every agent with strict inequality for at least one. For agent $i$, the **truncated share** (Definition 5.3) is
--   $$b_i^-=\max\{v_i(\mathcal S_i) : \mathcal S \text{ PO},\ v_i(\mathcal S_i)\le b_i\},$$
--   attained at the PO allocation $\hat{\mathcal S}^i$; an allocation gives agent $i$ her truncated share if $v_i(\mathcal S_i)\ge b_i^-$. The **augmented share** (Definition 5.4) $b_i^+=\min\{v_i(\mathcal S_i):\mathcal S\text{ PO},\ v_i(\mathcal S_i)\ge b_i\}$ is attained at $\check{\mathcal S}^i$.
--
--   **Two-agent objects.** For two agents:
--   1. A **combination pricing** (Definition 4.2) is $p_j=\alpha v_1(\{j\})+\beta v_2(\{j\})$ with $\alpha,\beta\ge 0$ and $\max\{\alpha,\beta\}>0$.
--   2. The **marginal value** of $S$ given $T$ is $v(S\mid T)=v(S\cup T)-v(T)$, and **Condition (1)** (p. 10) asks that for $i\ne k$ and all bundles $S\subseteq\mathcal S_i$, $T\subseteq\mathcal S_k$,
--   $$v_i(S\mid \mathcal S_i\setminus S)>v_i(T\mid \mathcal S_i\setminus S)\ \text{and}\ v_k(S\mid \mathcal S_k\setminus T)>v_k(T\mid \mathcal S_k\setminus T)\implies p(S)>p(T).$$
--   3. The **rectangle** $T_i$ (Definition 6.1), for the other agent $k$, is the set of allocations with $v_i(\hat{\mathcal S}^i_i)<v_i(\mathcal S_i)<v_i(\hat{\mathcal S}^k_i)$ and $0<v_k(\mathcal S_k)<v_k(\hat{\mathcal S}^k_k)$.
--   4. The budget pair $(b_i,1-b_i)$ lies in the **exceptional set** $R_i$ (Definition 6.2) if, for two PO allocations $\mathcal S(r),\mathcal S(r+1)$ that are consecutive in agent $i$'s order of PO allocations,
--   $$\frac{b_i}{v_i(\mathcal S(r+1)_i)}=\frac{1-b_i}{1-v_i(\mathcal S(r)_i)}.$$
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** Items are `Fin m`, agents `Fin n`, and an allocation is a map `σ : Fin m → Fin n`, which builds in market clearing. Demand ranges over all bundles. Non-negativity of prices is part of `IsCE`. Strictness is taken as plain injectivity of each valuation on bundles; the paper's single exception for identical items (p. 6) is dropped, so markets with identical items are excluded. The budget-proportional share is written $b_i\,v_i(M)$, which equals the page's $b_i$ under normalization. The truncated share is encoded without the max: `GetsTruncatedShare v b σ i` says $v_i(\mathcal S_i)$ is at least $v_i(\mathcal S'_i)$ for every PO $\mathcal S'$ with $v_i(\mathcal S'_i)\le b_i$; `IsTruncMaximizer`/`IsAugMinimizer` say $\sigma$ is $\hat{\mathcal S}^i$/$\check{\mathcal S}^i$. `InRectT` quantifies over the maximizers $\hat{\mathcal S}^i,\hat{\mathcal S}^k$, which are unique under strictness. `InR` replaces the index $r$ by "two PO allocations with no PO allocation strictly between them in agent $i$'s order" and cross-multiplies the equation; both denominators are positive for consecutive PO allocations, so the forms agree. In the two-agent objects agent 1, 2 of the paper are indices 0, 1.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, pp. 6–7 (§2.1, §2.2, Definitions 2.1, 2.3), p. 10 (Definition 4.2, Condition (1)), p. 12 (anti-proportional), p. 13 (Definitions 5.3, 5.4), p. 15 (Definitions 6.1, 6.2)

import Mathlib

namespace GenericBudgets.AlmostEqual

open Finset

variable {m n : ℕ}

/-- §2.2, p. 6: the bundle of agent `i` under the allocation `σ` (item `j` goes to agent `σ j`). -/
def bundle (σ : Fin m → Fin n) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => σ j = i)

/-- §2.2, p. 6: the price of a bundle, `p(S) = ∑_{j ∈ S} p_j`. -/
def price (p : Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  ∑ j ∈ S, p j

/-- §2.2, p. 6: `S` is demanded at prices `p` with budget `β` by an agent with valuation `w`:
`p(S) ≤ β`, and `p(T) > β` for every bundle `T` with `w(T) > w(S)`. -/
def IsDemanded (w : Finset (Fin m) → ℝ) (β : ℝ) (p : Fin m → ℝ) (S : Finset (Fin m)) : Prop :=
  price p S ≤ β ∧ ∀ T : Finset (Fin m), w S < w T → β < price p T

/-- Def. 2.1, p. 7: `(σ, p)` is a competitive equilibrium: prices are non-negative and every agent's
bundle is demanded. -/
def IsCE (v : Fin n → Finset (Fin m) → ℝ) (b : Fin n → ℝ) (σ : Fin m → Fin n) (p : Fin m → ℝ) :
    Prop :=
  (∀ j, 0 ≤ p j) ∧ ∀ i, IsDemanded (v i) (b i) p (bundle σ i)

/-- Def. 2.3, p. 7: `σ` is Pareto optimal: every other allocation is strictly worse for some agent. -/
def IsPO (v : Fin n → Finset (Fin m) → ℝ) (σ : Fin m → Fin n) : Prop :=
  ∀ σ' : Fin m → Fin n, σ' ≠ σ → ∃ i, v i (bundle σ' i) < v i (bundle σ i)

/-- §2.1, p. 6: the standing assumptions on a valuation: additive, normalized, non-negative,
monotone and strict (strictness without the paper's identical-items exception). -/
structure IsStandardValuation (w : Finset (Fin m) → ℝ) : Prop where
  additive : ∀ S, w S = ∑ j ∈ S, w {j}
  normalized : w Finset.univ = 1
  nonneg : ∀ S, 0 ≤ w S
  monotone : ∀ S T, S ⊂ T → w S < w T
  strict : Function.Injective w

/-- p. 8: every agent gets at least her budget-proportional share `b_i · v_i(M)`. -/
def IsBudgetProportional (v : Fin n → Finset (Fin m) → ℝ) (b : Fin n → ℝ) (σ : Fin m → Fin n) :
    Prop :=
  ∀ i, b i * v i Finset.univ ≤ v i (bundle σ i)

/-- p. 12: every agent gets at most her budget-proportional share, and some agent strictly less. -/
def IsAntiProportional (v : Fin n → Finset (Fin m) → ℝ) (b : Fin n → ℝ) (σ : Fin m → Fin n) :
    Prop :=
  (∀ i, v i (bundle σ i) ≤ b i * v i Finset.univ) ∧ ∃ i, v i (bundle σ i) < b i * v i Finset.univ

/-- Def. 5.3, p. 13: `σ` is the maximizing PO allocation `Ŝ^i` defining agent `i`'s truncated share
`b_i^-`. -/
def IsTruncMaximizer (v : Fin n → Finset (Fin m) → ℝ) (b : Fin n → ℝ) (i : Fin n)
    (σ : Fin m → Fin n) : Prop :=
  IsPO v σ ∧ v i (bundle σ i) ≤ b i ∧
    ∀ σ', IsPO v σ' → v i (bundle σ' i) ≤ b i → v i (bundle σ' i) ≤ v i (bundle σ i)

/-- Def. 5.4, p. 13: `σ` is the minimizing PO allocation `Š^i` defining agent `i`'s augmented share
`b_i^+`. -/
def IsAugMinimizer (v : Fin n → Finset (Fin m) → ℝ) (b : Fin n → ℝ) (i : Fin n)
    (σ : Fin m → Fin n) : Prop :=
  IsPO v σ ∧ b i ≤ v i (bundle σ i) ∧
    ∀ σ', IsPO v σ' → b i ≤ v i (bundle σ' i) → v i (bundle σ i) ≤ v i (bundle σ' i)

/-- Def. 5.3, p. 13: `σ` gives agent `i` her truncated share, `v_i(S_i) ≥ b_i^-`, where `b_i^-` is the
maximum of `v_i(S'_i)` over PO allocations `S'` with `v_i(S'_i) ≤ b_i`. -/
def GetsTruncatedShare (v : Fin n → Finset (Fin m) → ℝ) (b : Fin n → ℝ) (σ : Fin m → Fin n)
    (i : Fin n) : Prop :=
  ∀ σ', IsPO v σ' → v i (bundle σ' i) ≤ b i → v i (bundle σ' i) ≤ v i (bundle σ i)

/-- §2.2, p. 7: prices are budget-exhausting for σ. -/
def IsBudgetExhausting (b : Fin n → ℝ) (σ : Fin m → Fin n) (p : Fin m → ℝ) : Prop :=
  ∀ i, price p (bundle σ i) = b i

/-- Def. 4.2, p. 10: `p` is a combination pricing, `p_j = α v_1({j}) + β v_2({j})` with `α, β ≥ 0` and
`max {α, β} > 0` (agents 1, 2 of the paper are indices 0, 1). -/
def IsCombinationPricing (v : Fin 2 → Finset (Fin m) → ℝ) (p : Fin m → ℝ) : Prop :=
  ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 < max α β ∧ ∀ j, p j = α * v 0 {j} + β * v 1 {j}

/-- §4.1, p. 10: the marginal value `w(S | T) = w(S ∪ T) − w(T)`. -/
def marg (w : Finset (Fin m) → ℝ) (S T : Finset (Fin m)) : ℝ :=
  w (S ∪ T) - w T

/-- Condition (1), p. 10: for `i ≠ k` and bundles `S ⊆ S_i`, `T ⊆ S_k`, if
`v_i(S | S_i \ S) > v_i(T | S_i \ S)` and `v_k(S | S_k \ T) > v_k(T | S_k \ T)` then `p(S) > p(T)`. -/
def Condition1 (v : Fin 2 → Finset (Fin m) → ℝ) (σ : Fin m → Fin 2) (p : Fin m → ℝ) : Prop :=
  ∀ i k : Fin 2, i ≠ k → ∀ S T : Finset (Fin m), S ⊆ bundle σ i → T ⊆ bundle σ k →
    marg (v i) T (bundle σ i \ S) < marg (v i) S (bundle σ i \ S) →
    marg (v k) T (bundle σ k \ T) < marg (v k) S (bundle σ k \ T) →
    price p T < price p S

/-- Def. 6.1, p. 15: σ lies in the rectangle T_i (k is the other agent). -/
def InRectT (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ) (i k : Fin 2) (σ : Fin m → Fin 2) :
    Prop :=
  ∃ σi σk, IsTruncMaximizer v b i σi ∧ IsTruncMaximizer v b k σk ∧
    v i (bundle σi i) < v i (bundle σ i) ∧ v i (bundle σ i) < v i (bundle σk i) ∧
    0 < v k (bundle σ k) ∧ v k (bundle σ k) < v k (bundle σk k)

/-- Def. 6.2, p. 15: the budget pair (b_i, 1 − b_i) lies in R_i. Consecutive PO allocations in agent i's
order, cross-multiplied (both denominators are positive). -/
def InR (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ) (i : Fin 2) : Prop :=
  ∃ σ σ' : Fin m → Fin 2, IsPO v σ ∧ IsPO v σ' ∧ v i (bundle σ i) < v i (bundle σ' i) ∧
    (∀ τ, IsPO v τ → ¬ (v i (bundle σ i) < v i (bundle τ i) ∧ v i (bundle τ i) < v i (bundle σ' i))) ∧
    b i * (1 - v i (bundle σ i)) = (1 - b i) * v i (bundle σ' i)

end GenericBudgets.AlmostEqual


