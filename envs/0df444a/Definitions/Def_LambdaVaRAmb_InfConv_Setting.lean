-- Prove2me | Definitions.Def_LambdaVaRAmb_InfConv_Setting
-- name    : LambdaVaRAmb_InfConv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:19.39326+00:00
-- url     : https://prove2.me/theorems/8b5da4f5-a0d1-4c5d-b81e-e7284a17e483
-- title:
--   pp. 5–16 — the domain 𝒳, continuous capacities, ℋ_D and ℋ*, allocations and □, downsets and induced risk measures (4), 𝒜̃ₓ, Πₙ(Ω), 𝒜^{𝚲,𝐰}ₓ, the tail allocation
-- statement:
--   This file fixes the vocabulary of the inf-convolution and comonotonic risk-sharing results of Liu and Schied, *Lambda Value-at-Risk under ambiguity and risk sharing*. It builds on the companion file of capacities and Lambda Value-at-Risk: a **capacity** $w:\mathcal F\to[0,1]$ is an increasing set function with $w(\emptyset)=0$ and $w(\Omega)=1$; $\mathcal H$ is the set of functions $\Lambda:\mathbb R\to(0,1)$, $\mathcal H_I$ its increasing members; and $\Lambda\mathrm{VaR}^w(X)=\inf\{x\in\mathbb R: w(X>x)\le\Lambda(x)\}\in[-\infty,\infty]$ with $\inf\emptyset=\infty$.
--
--   **Random variables.** $(\Omega,\mathcal F)$ is a measurable space; a random variable is an $\mathcal F$-measurable map $X:\Omega\to\mathbb R$. The paper works on a set $\mathcal X$ of random variables containing all bounded ones, "with good enough properties, such as $\mathcal X_0$ or $\mathcal X_1$" (bounded, resp. all, random variables). Here $\mathcal X$ is any set of real functions such that
--
--   1. every member is measurable;
--   2. every bounded measurable function belongs to it;
--   3. $(X-c)\mathbb 1_A+d\in\mathcal X$ for $X\in\mathcal X$, $A\in\mathcal F$, $c,d\in\mathbb R$;
--   4. $f(X)\in\mathcal X$ for $X\in\mathcal X$ and every increasing $1$-Lipschitz $f$ with $f(0)=0$.
--
--   **Continuous capacities.** A capacity $w$ is *continuous* if $w(A_n)\to0$ whenever $A_n\downarrow\emptyset$.
--
--   **More Lambda functions.** $\mathcal H_D$ is the set of decreasing members of $\mathcal H$; $\mathcal H^*_I$ and $\mathcal H^*_D$ are the increasing and decreasing functions $\Lambda:\mathbb R\to(0,1]$. "Increasing" and "decreasing" are meant in the weak sense.
--
--   **Inf-convolution.** For $n$ agents, $\mathbb A_n(X)=\{(X_1,\dots,X_n)\in\mathcal X^n:\sum_i X_i=X\}$ is the set of allocations of $X$, and for $\rho_1,\dots,\rho_n:\mathcal X\to[-\infty,\infty]$
--   $$
--   \mathop{\square}_{i=1}^n\rho_i(X)=\inf\Big\{\sum_{i=1}^n\rho_i(X_i):(X_1,\dots,X_n)\in\mathbb A_n(X)\Big\}.
--   $$
--   An allocation is *optimal* if it attains this infimum.
--
--   **Downsets and induced risk measures.** $\mathcal A\subseteq\mathcal F$ is a *downset* if $\emptyset\in\mathcal A$ and every event contained in a member of $\mathcal A$ belongs to $\mathcal A$. A family $\{\mathcal A_x\}_{x\in\mathbb R}$ of downsets is increasing (decreasing) if $\mathcal A_x\subseteq\mathcal A_y$ ($\supseteq$) for $x\le y$, and a decreasing family is left-continuous if $\bigcap_{y<x}\mathcal A_y=\mathcal A_x$ for every $x$. The family induces the risk measure
--   $$
--   \rho(X)=\inf\{x\in\mathbb R:\{X>x\}\in\mathcal A_x\}. \tag{4}
--   $$
--
--   **Families built from $n$ agents.** For families $\{\mathcal A^{(i)}_x\}$, $i\in[n]$,
--   $$
--   \widetilde{\mathcal A}_x=\bigcup_{y_1+\dots+y_n=x}\Big\{\bigcup_{i=1}^nA_i:A_i\in\mathcal A^{(i)}_{y_i}\Big\},
--   $$
--   and for $\boldsymbol\Lambda=(\Lambda_1,\dots,\Lambda_n)$, $\mathbf w=(w_1,\dots,w_n)$,
--   $$
--   \mathcal A^{\boldsymbol\Lambda,\mathbf w}_x=\Big\{\bigcup_{i=1}^nA_i: A_i\in\mathcal F,\ w_i(A_i)\le\Lambda_i(y_i),\ \textstyle\sum_iy_i=x\Big\}.
--   $$
--   $\Pi_n(\Omega)$ is the set of measurable partitions $(A_1,\dots,A_n)$ of $\Omega$ (parts may be empty). Given $x^*\in\mathbb R$, $(y^*_i)$ and $(A^*_i)$, the *tail allocation* is $X_i=(X-x^*)\mathbb 1_{A^*_i}+y^*_i$.
--
--   These objects are the vocabulary of Theorem 1, Theorem 3, Proposition 8 and Theorem 4 of the paper.
--
--   **Formalization Note** Capacities, $\mathcal H$, $\mathcal H_I$ and $\Lambda\mathrm{VaR}$ are imported from the companion file (`LambdaVaRAmb.Robust`). Capacities are real-valued functions on all subsets of $\Omega$ whose axioms are imposed on measurable sets only; values on non-measurable sets are never read, since every event used is of the form $\{X>x\}$ with $X$ measurable or a member of a downset (downsets consist of measurable sets, and closure is under measurable subsets). Induced risk measures and the inf-convolution take values in `EReal`, so $\inf\emptyset=+\infty$ and an unbounded set has infimum $-\infty$, as in the paper; in a sum of `EReal` values Lean sets $+\infty+(-\infty)=-\infty$, and the statements that use $\square$ assume what the paper assumes to exclude that mix (values in $[-\infty,\infty)$). Sums $\sum_iX_i=X$ are pointwise, agents are indexed by `Fin n`, and statements assume $n\ge1$. Clauses 1–4 on $\mathcal X$ are the disclosed reading of "good enough properties": $\mathcal X_0$ and $\mathcal X_1$ both satisfy them. Left-continuity is a separate predicate; the statements pair it with "decreasing", as the paper does.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, pp. 5–7 (§2: 𝒳, capacities, ℋ, (1), 𝔸_n, □), pp. 9–10 (§3: downsets, (4), ℋ*_I, ℋ*_D), pp. 15–16 (§5.1: 𝒜̃_x, Π_n(Ω), 𝒜^{𝚲,𝐰}_x, (8), (10))

import Mathlib
import Definitions.Def_LambdaVaRAmb_Robust_Setting

namespace LambdaVaRAmb.InfConv

variable {Ω : Type*} [MeasurableSpace Ω]

/-- p. 5: a domain 𝒳 of random variables "with good enough properties, such as 𝒳₀ or 𝒳₁". -/
structure IsRVDomain (dom : Set (Ω → ℝ)) : Prop where
  measurable : ∀ X ∈ dom, Measurable X
  bounded_mem : ∀ X : Ω → ℝ, Measurable X → (∃ C : ℝ, ∀ ω, |X ω| ≤ C) → X ∈ dom
  split_mem : ∀ X ∈ dom, ∀ A : Set Ω, MeasurableSet A → ∀ c d : ℝ,
    (fun ω => (X ω - c) * A.indicator 1 ω + d) ∈ dom
  comp_mem : ∀ X ∈ dom, ∀ f : ℝ → ℝ, Monotone f → LipschitzWith 1 f → f 0 = 0 →
    (fun ω => f (X ω)) ∈ dom

/-- p. 6: a continuous capacity: `w(Aₙ) → 0` whenever `Aₙ ↓ ∅`. -/
def IsContinuousCapacity (w : Set Ω → ℝ) : Prop :=
  LambdaVaRAmb.Robust.IsCapacity w ∧ ∀ A : ℕ → Set Ω, (∀ n, MeasurableSet (A n)) → Antitone A → (⋂ n, A n) = ∅ →
    Filter.Tendsto (fun n => w (A n)) Filter.atTop (nhds 0)

/-- p. 6: `ℋ_D`, the decreasing functions in `ℋ`. -/
def InHD (Λ : ℝ → ℝ) : Prop := LambdaVaRAmb.Robust.InH Λ ∧ Antitone Λ

/-- p. 10: `ℋ*_I`, the increasing functions `Λ : ℝ → (0, 1]`. -/
def InHStarI (Λ : ℝ → ℝ) : Prop := (∀ x, 0 < Λ x ∧ Λ x ≤ 1) ∧ Monotone Λ

/-- p. 10: `ℋ*_D`, the decreasing functions `Λ : ℝ → (0, 1]`. -/
def InHStarD (Λ : ℝ → ℝ) : Prop := (∀ x, 0 < Λ x ∧ Λ x ≤ 1) ∧ Antitone Λ

/-- p. 7: `𝔸ₙ(X)`, the allocations `(X₁, …, Xₙ) ∈ 𝒳ⁿ` with `Σᵢ Xᵢ = X`. -/
def Allocations (dom : Set (Ω → ℝ)) (n : ℕ) (X : Ω → ℝ) : Set (Fin n → Ω → ℝ) :=
  {Xs | (∀ i, Xs i ∈ dom) ∧ ∀ ω, ∑ i, Xs i ω = X ω}

/-- p. 7: the inf-convolution `□ᵢ ρᵢ(X) = inf {Σᵢ ρᵢ(Xᵢ) : (X₁, …, Xₙ) ∈ 𝔸ₙ(X)}`. -/
noncomputable def infConv (dom : Set (Ω → ℝ)) {n : ℕ} (ρ : Fin n → (Ω → ℝ) → EReal)
    (X : Ω → ℝ) : EReal :=
  ⨅ Xs ∈ Allocations dom n X, ∑ i, ρ i (Xs i)

/-- p. 7: `(X₁, …, Xₙ) ∈ 𝔸ₙ(X)` is an optimal allocation if `Σᵢ ρᵢ(Xᵢ) = □ᵢ ρᵢ(X)`. -/
def IsOptimalAllocation (dom : Set (Ω → ℝ)) {n : ℕ} (ρ : Fin n → (Ω → ℝ) → EReal)
    (X : Ω → ℝ) (Xs : Fin n → Ω → ℝ) : Prop :=
  Xs ∈ Allocations dom n X ∧ ∑ i, ρ i (Xs i) = infConv dom ρ X

/-- p. 9: `𝒜 ⊆ ℱ` is a downset if `∅ ∈ 𝒜` and `A ∈ 𝒜` whenever `B ∈ 𝒜` and `A ⊆ B` (A ∈ ℱ). -/
def IsDownset (𝒜 : Set (Set Ω)) : Prop :=
  (∀ A ∈ 𝒜, MeasurableSet A) ∧ ∅ ∈ 𝒜 ∧ ∀ A B, MeasurableSet A → B ∈ 𝒜 → A ⊆ B → A ∈ 𝒜

/-- (4), p. 9: the risk measure induced by a family of downsets, `ρ(X) = inf {x | {X > x} ∈ 𝒜ₓ}`. -/
noncomputable def inducedRM (𝒜 : ℝ → Set (Set Ω)) (X : Ω → ℝ) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | {ω | x < X ω} ∈ 𝒜 x})

/-- p. 9: a decreasing family is left-continuous if `⋂_{y<x} 𝒜_y = 𝒜_x` for all `x`. -/
def IsLeftContFamily (𝒜 : ℝ → Set (Set Ω)) : Prop := ∀ x, (⋂ y ∈ Set.Iio x, 𝒜 y) = 𝒜 x

/-- p. 15: `𝒜̃ₓ = ⋃_{y₁+⋯+yₙ=x} ⊕ᵢ 𝒜⁽ⁱ⁾_{yᵢ}`, with `⊕ᵢ 𝒜⁽ⁱ⁾_{yᵢ} = {∪ᵢ Aᵢ : Aᵢ ∈ 𝒜⁽ⁱ⁾_{yᵢ}}`. -/
def convFamily {n : ℕ} (𝒜 : Fin n → ℝ → Set (Set Ω)) (x : ℝ) : Set (Set Ω) :=
  {E | ∃ y : Fin n → ℝ, ∑ i, y i = x ∧ ∃ A : Fin n → Set Ω, (∀ i, A i ∈ 𝒜 i (y i)) ∧ E = ⋃ i, A i}

/-- p. 15: `Πₙ(Ω)`, measurable partitions of `Ω` (some parts may be empty). -/
def IsMeasPartition {n : ℕ} (A : Fin n → Set Ω) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧ (⋃ i, A i) = Set.univ ∧ Pairwise (fun i j => Disjoint (A i) (A j))

/-- p. 16: `𝒜^{Λ,w}ₓ = {∪ᵢ Aᵢ : wᵢ(Aᵢ) ≤ Λᵢ(yᵢ), i ∈ [n], where Σᵢ yᵢ = x}`. -/
def capFamily {n : ℕ} (Λ : Fin n → ℝ → ℝ) (w : Fin n → Set Ω → ℝ) (x : ℝ) : Set (Set Ω) :=
  {E | ∃ y : Fin n → ℝ, ∑ i, y i = x ∧ ∃ A : Fin n → Set Ω,
    (∀ i, MeasurableSet (A i) ∧ w i (A i) ≤ Λ i (y i)) ∧ E = ⋃ i, A i}

/-- (8)/(10), pp. 15–16: the allocation `Xᵢ = (X − x*) 1_{A*ᵢ} + y*ᵢ`. -/
noncomputable def tailAllocation {n : ℕ} (X : Ω → ℝ) (xstar : ℝ) (y : Fin n → ℝ)
    (A : Fin n → Set Ω) : Fin n → Ω → ℝ :=
  fun i ω => (X ω - xstar) * (A i).indicator 1 ω + y i

end LambdaVaRAmb.InfConv


