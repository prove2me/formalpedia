-- Prove2me | Definitions.Def_ProductFraming_Nest_Model
-- name    : ProductFraming_Nest_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:22.439486+00:00
-- url     : https://prove2.me/theorems/19ea834c-7b60-449c-807b-de1e28bedf8a
-- title:
--   Product framing: choice model, Assumptions A1 and A3, page-count law, problems (1) and (2), $U(x)$, $V^{OPT}$
-- statement:
--   There are $n$ products $[n]=\{1,\dots,n\}$; product $i$ has unit revenue $r_i$. Products are organized into $m$ pages, each holding at most $p$ products. A consumer views the first $X\in[m]$ pages, where $X$ is random with law $\lambda(x)=\mathbb P[X=x]$ (so $\lambda(x)\ge 0$ and $\sum_{x\in[m]}\lambda(x)=1$) and tail $\Lambda(x)=\mathbb P[X\ge x]=\sum_{y=x}^{m}\lambda(y)$. We write $\mathbb E[\min(X,x)]=\sum_{y\in[m]}\lambda(y)\min(y,x)$ for real $x$ and $\mathbb E[X]=\sum_{x\in[m]}\lambda(x)\,x$.
--
--   1. **Choice model.** $P(i,S)$ is the probability that a consumer with consideration set $S\subseteq[n]$ buys product $i$. It satisfies $P(i,S)\ge 0$, $P(i,S)=0$ if $i\notin S$, and $\sum_{i\in S}P(i,S)\le 1$ (at most one purchase).
--   2. **Assumption A1.** $P(i,S)\ge P(i,T)$ for all $i\in S$ and $S\subseteq T\subseteq[n]$.
--   3. **Assumption A3 (NBUE).** With $q(x)=\mathbb E[X-x+1\mid X\ge x]=\frac{1}{\Lambda(x)}\sum_{y=x}^{m}\lambda(y)(y-x+1)$, the law is NBUE if $q(x)\le q(1)$ for all $x\in[m]$.
--   4. **Revenue and problem (2).** $R(S)=\sum_{i\in S}r_iP(i,S)$, and
--   $$G(c)=\max_{S\subseteq[n],\ |S|\le c}R(S),\qquad U(x)=G(x\cdot p).$$
--   5. **Problem (1).** A framing places each product on at most one page so that every page holds at most $p$ products. A consumer who views $x$ pages has as consideration set the products on pages $1,\dots,x$. The expected revenue of a framing $f$ is $\sum_{x\in[m]}\lambda(x)R(\text{consideration set at }x)$, and
--   $$V^{OPT}=\max_{f\ \text{feasible}}\ \sum_{x\in[m]}\lambda(x)\,R\big(\{k: k \text{ is on one of the pages } 1,\dots,x\}\big).$$
--
--   These are the objects all statements of the mission are about: Theorem 2 bounds $V^{OPT}$ by $\mathbb E[U(X)]=\sum_x\lambda(x)U(x)$, and A1 and A3 are the hypotheses of the approximation guarantee.
--
--   **Formalization Note** Products are `Fin n`. Pages are the naturals $1,\dots,m$ (1-based, as in the paper). A framing is a map `f : Fin n → ℕ`: product $i$ is on page $f(i)$ if $1\le f(i)\le m$ and is not displayed if $f(i)=0$; this encodes $f\in\{0,1\}^{n\times m}$ with $\sum_x f_{ix}\le1$. $V^{OPT}$ is a `Finset.sup'` over the finite, nonempty set of feasible framings `Fin n → Fin (m+1)` (the empty framing is feasible), and $G(c)$ a `Finset.sup'` over the sets of size at most $c$ (containing $\emptyset$). The law `lam : ℕ → ℝ` is only used on $[1,m]$. When $\Lambda(x)=0$ the quotient $q(x)$ is $0$ (Lean's $a/0=0$), so A3 imposes nothing at such $x$, which is the intended reading (conditioning on a null event). A2 is taken with $\varepsilon=0$, as the paper does (p. 8): $U$ is the exact optimum of (2); polynomial time is not modelled.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, §3, pp. 5–7, (1), (2), (3); §4.1, p. 8, Assumptions A1–A3

import Mathlib

namespace ProductFraming.Nest

open Finset

/-! The product framing model of Gallego, Li, Truong, Wang, *Approximation Algorithms for Product
Framing and Pricing*, Operations Research (2020), authors' accepted manuscript, §3, pp. 5–7, problems
(1)–(3), and §4.1, p. 8, Assumptions A1 and A3.

Products are `Fin n` (the paper's `[n]`). Pages are the naturals `1, …, m`, kept 1-based as on the
page. The number of pages `X ∈ [m]` a consumer views has law `λ(x) = P[X = x]`, given by
`lam : ℕ → ℝ`; only its values on `[1, m]` are used. -/

/-- A general choice model (§3, pp. 5–6): `P i S` is the purchase probability `P(i, S)` of product `i`
when the consideration set is `S`. Probabilities are nonnegative, `P(i, S) = 0` if `i ∉ S`, and the
consumer purchases at most one product, so `∑_{i ∈ S} P(i, S) ≤ 1`. -/
structure IsChoiceModel {n : ℕ} (P : Fin n → Finset (Fin n) → ℝ) : Prop where
  nonneg : ∀ i S, 0 ≤ P i S
  eq_zero_of_not_mem : ∀ i S, i ∉ S → P i S = 0
  sum_le_one : ∀ S, ∑ i ∈ S, P i S ≤ 1

/-- Assumption A1 (p. 8): `P(i, S) ≥ P(i, T)` for all `i ∈ S` and `S ⊆ T ⊆ [n]`. -/
def SatisfiesA1 {n : ℕ} (P : Fin n → Finset (Fin n) → ℝ) : Prop :=
  ∀ S T : Finset (Fin n), ∀ i, S ⊆ T → i ∈ S → P i T ≤ P i S

/-- `lam` is the law `λ(x) = P[X = x]` of the number of pages `X ∈ [m]` a consumer views (§3, p. 6). -/
def IsPageLaw (m : ℕ) (lam : ℕ → ℝ) : Prop :=
  (∀ x ∈ Icc 1 m, 0 ≤ lam x) ∧ ∑ x ∈ Icc 1 m, lam x = 1

/-- The tail `Λ(x) = P[X ≥ x] = ∑_{y = x}^{m} λ(y)` (§3, p. 6). -/
def tail (m : ℕ) (lam : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ y ∈ Icc x m, lam y

/-- `E[min(X, x)] = ∑_{y ∈ [m]} λ(y) min(y, x)`, for a real `x`. -/
noncomputable def Emin (m : ℕ) (lam : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ y ∈ Icc 1 m, lam y * min (y : ℝ) x

/-- The mean `E[X] = ∑_{x ∈ [m]} λ(x) x`. -/
def mean (m : ℕ) (lam : ℕ → ℝ) : ℝ :=
  ∑ x ∈ Icc 1 m, lam x * (x : ℝ)

/-- `q(x) = E[X − x + 1 | X ≥ x] = (∑_{y=x}^{m} λ(y)(y − x + 1)) / Λ(x)` (p. 8). When `Λ(x) = 0` the
quotient is `0` (Lean's `a / 0 = 0`). -/
noncomputable def q (m : ℕ) (lam : ℕ → ℝ) (x : ℕ) : ℝ :=
  (∑ y ∈ Icc x m, lam y * ((y : ℝ) - x + 1)) / tail m lam x

/-- Assumption A3 (p. 8), in the paper's equivalent form: `X` is NBUE iff `q(x) ≤ q(1)` for all
`x ∈ [m]`. -/
def IsNBUE (m : ℕ) (lam : ℕ → ℝ) : Prop :=
  ∀ x ∈ Icc 1 m, q m lam x ≤ q m lam 1

/-- `R(S) = ∑_{i ∈ S} r_i P(i, S)`, the expected revenue when `S` is the consideration set (p. 9). -/
def R {n : ℕ} (r : Fin n → ℝ) (P : Fin n → Finset (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, r i * P i S

/-- Problem (2) (p. 7): `G(c) = max_{S ⊆ [n], |S| ≤ c} ∑_{i ∈ S} r_i P(i, S)`. The family is finite
and contains `∅`. -/
noncomputable def G {n : ℕ} (r : Fin n → ℝ) (P : Fin n → Finset (Fin n) → ℝ) (c : ℕ) : ℝ :=
  (univ.filter (fun S : Finset (Fin n) => S.card ≤ c)).sup' ⟨∅, by simp⟩ (R r P)

/-- `U(x) ≡ G(x · p)` (p. 7), the optimal expected revenue from consumers who see `x` pages. -/
noncomputable def U {n : ℕ} (p : ℕ) (r : Fin n → ℝ) (P : Fin n → Finset (Fin n) → ℝ) (x : ℕ) : ℝ :=
  G r P (x * p)

/-- A framing `f : Fin n → ℕ`: product `i` is displayed on page `f i` if `1 ≤ f i ≤ m`, and is not
displayed if `f i = 0`. It is feasible for (1) if every page holds at most `p` products. -/
def IsFeasibleFraming {n : ℕ} (m p : ℕ) (f : Fin n → ℕ) : Prop :=
  (∀ i, f i ≤ m) ∧ ∀ x ∈ Icc 1 m, (univ.filter (fun i => f i = x)).card ≤ p

/-- The consideration set `{k ∈ [n] : ∑_{l=1}^{x} f_{kl} = 1}` of a consumer who views `x` pages. -/
def consideration {n : ℕ} (f : Fin n → ℕ) (x : ℕ) : Finset (Fin n) :=
  univ.filter (fun k => 1 ≤ f k ∧ f k ≤ x)

/-- The objective of (1): `∑_{x ∈ [m]} λ(x) ∑_{i ∈ [n]} r_i P(i, consideration set at x)`. -/
def V {n : ℕ} (m : ℕ) (r : Fin n → ℝ) (P : Fin n → Finset (Fin n) → ℝ) (lam : ℕ → ℝ)
    (f : Fin n → ℕ) : ℝ :=
  ∑ x ∈ Icc 1 m, lam x * R r P (consideration f x)

open Classical in
/-- The feasible framings of (1), as maps `Fin n → Fin (m + 1)` (page `0` = not displayed). -/
noncomputable def feasibleFramings (n m p : ℕ) : Finset (Fin n → Fin (m + 1)) :=
  univ.filter (fun f => IsFeasibleFraming m p (fun i => (f i : ℕ)))

/-- The empty framing (nothing displayed) is feasible. -/
theorem zero_mem_feasibleFramings (n m p : ℕ) :
    (fun _ => 0) ∈ feasibleFramings n m p := by
  classical
  simp only [feasibleFramings, IsFeasibleFraming, mem_filter, mem_univ, true_and]
  refine ⟨fun _ => by simp, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (mem_Icc.mp hx).1
  have : (univ.filter (fun i : Fin n => (((0 : Fin (m + 1)) : ℕ)) = x)) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro i _
    simp only [Fin.val_zero]
    omega
  rw [this]
  simp

/-- `V^OPT` of problem (1) (p. 6): the maximum of the objective over the feasible framings. -/
noncomputable def Vopt (n m p : ℕ) (r : Fin n → ℝ) (P : Fin n → Finset (Fin n) → ℝ)
    (lam : ℕ → ℝ) : ℝ :=
  (feasibleFramings n m p).sup' ⟨_, zero_mem_feasibleFramings n m p⟩
    (fun f => V m r P lam (fun i => (f i : ℕ)))

end ProductFraming.Nest


