-- Prove2me | Definitions.Def_BalancedPrices_Extension_Model
-- name    : BalancedPrices_Extension_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T15:08:19.126112+00:00
-- url     : https://prove2.me/theorems/0298bd64-0d15-464b-9832-fb8a478ccae3
-- title:
--   §2–3, pp. 547–549 — outcome profiles, x_S, x_[i−1], downward closure, exchange compatibility, welfare, v(OPT(v, S)), pricing rules and (α, β)-balancedness
-- statement:
--   The deterministic model of §2 and Definition 3.1.
--
--   There are $n$ agents. Agent $i$ has an outcome space $X_i$ containing a null outcome $\varnothing$; an outcome profile is $\mathbf x=(x_1,\dots,x_n)\in X=X_1\times\dots\times X_n$.
--
--   1. For $S\subseteq N$, $\mathbf x_S$ gives $x_i$ to the agents $i\in S$ and $\varnothing$ to the others; $\mathbf x_{[i-1]}$ is $\mathbf x$ with the outcomes of agents $i,\dots,n$ set to $\varnothing$.
--   2. A set $\mathcal F\subseteq X$ of feasible outcomes is **downward-closed** if $\mathbf x\in\mathcal F$ implies $\mathbf x_S\in\mathcal F$ for all $S\subseteq N$.
--   3. A set $\mathcal H\subseteq X$ is **exchange compatible** with $\mathbf x$ if $(y_i,\mathbf x_{-i})\in\mathcal F$ for all $\mathbf y\in\mathcal H$ and all $i$; a family $(\mathcal F_{\mathbf x})_{\mathbf x\in X}$ is exchange compatible if $\mathcal F_{\mathbf x}$ is exchange compatible with $\mathbf x$ for every $\mathbf x\in X$.
--   4. For valuations $v_i:X_i\to\mathbb R$, the **welfare** is $\mathbf v(\mathbf x)=\sum_i v_i(x_i)$, and $\mathbf v(\mathrm{OPT}(\mathbf v,S))=\sup_{\mathbf x\in S}\mathbf v(\mathbf x)$.
--   5. A **pricing rule** assigns to agent $i$, outcome $x_i$ and partial allocation $\mathbf y$ a price $p_i(x_i\mid\mathbf y)\in[0,\infty]$, with $p_i(x_i\mid\mathbf y)=\infty$ whenever $\mathbf y\in\mathcal F$ and $(x_i,\mathbf y_{-i})\notin\mathcal F$.
--   6. (**Definition 3.1**) Let $\alpha>0$, $\beta\ge0$. A pricing rule $p^{\mathbf v}$ is **$(\alpha,\beta)$-balanced** for the valuation profile $\mathbf v$ with respect to the outcome $\mathrm{ALG}(\mathbf v)$, the family $(\mathcal F_{\mathbf x})$ and the index order if for all $\mathbf x\in\mathcal F$
--   $$\text{(a)}\ \sum_{i\in N}p^{\mathbf v}_i(x_i\mid\mathbf x_{[i-1]})\ge\frac1\alpha\bigl(\mathbf v(\mathrm{ALG}(\mathbf v))-\mathbf v(\mathrm{OPT}(\mathbf v,\mathcal F_{\mathbf x}))\bigr),\qquad\text{(b)}\ \sum_{i\in N}p^{\mathbf v}_i(x'_i\mid\mathbf x_{[i-1]})\le\beta\cdot\mathbf v(\mathrm{OPT}(\mathbf v,\mathcal F_{\mathbf x}))\ \ \forall\mathbf x'\in\mathcal F_{\mathbf x}.$$
--
--   These are the objects in which every statement of the mission is phrased; balancedness is the full-information condition that Theorem 3.2 extends to the Bayesian setting.
--
--   **Formalization Note** Agents are `Fin n`, 0-based, so `pre nul x i` keeps the agents `j < i`. Prices are `ℝ≥0∞`-valued with `⊤` for $\infty$; the right side of (a) is passed through `ENNReal.ofReal`, so a negative right side becomes $0$ (prices are nonnegative, so this is the paper's meaning), and no price sum is ever converted to a real number. The requirement "$\infty$ off $\mathcal F$" is imposed at feasible partial allocations $\mathbf y\in\mathcal F$, the paper's domain of $p_i(\cdot\mid\mathbf y)$ (p. 547). $\mathbf v(\mathrm{OPT}(\mathbf v,S))$ is a real supremum, $0$ for $S=\varnothing$; it is meaningful because the theorems assume valuations in $[0,1]$. Definition 3.1 uses ALG only through $\mathbf v(\mathrm{ALG}(\mathbf v))$, so `Balanced` takes the outcome $\mathrm{ALG}(\mathbf v)$ itself as its argument `a`.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), pp. 547–549, §2, §3, Definition 3.1

import Mathlib

namespace BalancedPrices.Extension

open scoped ENNReal

/-- An outcome profile: one outcome `x i : X i` for every agent `i : Fin n`. -/
abbrev Outcome {n : ℕ} (X : Fin n → Type*) := ∀ i, X i

/-- A valuation profile, as functions: `v i (x i)` is agent `i`'s value for outcome `x i`. -/
abbrev Valuation {n : ℕ} (X : Fin n → Type*) := ∀ i, X i → ℝ

/-- A pricing rule: `p i xi y` is the price `p_i(x_i | y)` of outcome `xi` offered to agent `i`
given the partial allocation `y`; `⊤` is the price `∞`. -/
abbrev PriceRule {n : ℕ} (X : Fin n → Type*) := ∀ i, X i → Outcome X → ℝ≥0∞

/-- `x_S`: agents in `S` keep `x i`, every other agent receives the null outcome `nul i`. -/
def restrictTo {n : ℕ} {X : Fin n → Type*} (nul x : Outcome X)
    (S : Finset (Fin n)) : Outcome X :=
  fun i => if i ∈ S then x i else nul i

/-- `x_[i−1]`: the outcomes of agents `i, …, n` set to the null outcome. Agents are 0-based, so
this keeps exactly the agents `j < i`. -/
def pre {n : ℕ} {X : Fin n → Type*} (nul x : Outcome X) (i : Fin n) : Outcome X :=
  restrictTo nul x (Finset.univ.filter fun j => j < i)

/-- `F` is downward-closed: `x ∈ F` implies `x_S ∈ F` for every `S ⊆ N`. -/
def DownClosed {n : ℕ} {X : Fin n → Type*} (nul : Outcome X) (F : Set (Outcome X)) : Prop :=
  ∀ x ∈ F, ∀ S : Finset (Fin n), restrictTo nul x S ∈ F

/-- `H` is exchange compatible with `x`: `(y_i, x_{−i}) ∈ F` for all `y ∈ H` and all `i`. -/
def ExchCompat {n : ℕ} {X : Fin n → Type*} (F : Set (Outcome X))
    (x : Outcome X) (H : Set (Outcome X)) : Prop :=
  ∀ y ∈ H, ∀ i, Function.update x i (y i) ∈ F

/-- A family `(F_x)_{x ∈ X}` is exchange compatible if `F_x` is exchange compatible with `x`
for **every** outcome profile `x` (not only the feasible ones). -/
def ExchFamily {n : ℕ} {X : Fin n → Type*} (F : Set (Outcome X))
    (Fam : Outcome X → Set (Outcome X)) : Prop :=
  ∀ x, ExchCompat F x (Fam x)

/-- A pricing rule assigns price `∞` to every outcome `xi` that cannot be added to the
feasible partial allocation `y`, i.e. with `(x_i, y_{−i}) ∉ F`. -/
def IsPricingRule {n : ℕ} {X : Fin n → Type*} (F : Set (Outcome X)) (p : PriceRule X) : Prop :=
  ∀ i xi y, y ∈ F → Function.update y i xi ∉ F → p i xi y = ⊤

/-- The welfare `v(x) = ∑_i v_i(x_i)`. -/
def welfare {n : ℕ} {X : Fin n → Type*} (v : Valuation X) (x : Outcome X) : ℝ :=
  ∑ i, v i (x i)

/-- `v(OPT(v, S))`, the optimal welfare over `S`, as a real supremum (`0` for `S = ∅`). -/
noncomputable def optVal {n : ℕ} {X : Fin n → Type*}
    (v : Valuation X) (S : Set (Outcome X)) : ℝ :=
  sSup (welfare v '' S)

/-- Definition 3.1: the pricing rule `p` is `(α, β)`-balanced for the valuation profile `v`
with respect to the outcome `a = ALG(v)`, the family `Fam` and the index order of `Fin n`. -/
def Balanced {n : ℕ} {X : Fin n → Type*} (nul : Outcome X) (α β : ℝ) (F : Set (Outcome X))
    (Fam : Outcome X → Set (Outcome X)) (v : Valuation X) (a : Outcome X)
    (p : PriceRule X) : Prop :=
  ∀ x ∈ F,
    ENNReal.ofReal ((1 / α) * (welfare v a - optVal v (Fam x))) ≤
        ∑ i, p i (x i) (pre nul x i) ∧
      ∀ x' ∈ Fam x, (∑ i, p i (x' i) (pre nul x i)) ≤ ENNReal.ofReal (β * optVal v (Fam x))

end BalancedPrices.Extension


