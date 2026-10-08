-- Prove2me | Definitions.Def_MangasarianFJ_GenFJ_Setting
-- name    : MangasarianFJ_GenFJ_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:25:50.651482+00:00
-- url     : https://prove2.me/theorems/f1dc72b4-8fac-42c2-a86e-e2ad1d5d0dd5
-- title:
--   §1–§3, pp. 38–43 — feasible set S (2.19), solution of (1.1), active set M̄ (2.13), D (2.14), Fritz John conditions (2.9)–(2.12), Kuhn–Tucker conditions (3.1)–(3.3)
-- statement:
--   These definitions set up the nonlinear program of Mangasarian and Fromovitz,
--
--   $$
--   \text{minimize } \theta(x) \quad\text{subject to}\quad g_i(x)\le 0,\ i\in M=\{1,\dots,m\},\qquad h_j(x)=0,\ j\in K=\{1,\dots,k\}, \tag{1.1}
--   $$
--
--   where $\theta, g_i, h_j : E^n \to \mathbb R$ are real functions on $n$-dimensional Euclidean space $E^n$. For a point $\bar x\in E^n$:
--
--   1. **Feasible set** (2.19): $S=\{x\in E^n : g_i(x)\le 0,\ i\in M,\ h_j(x)=0,\ j\in K\}$.
--   2. **Solution of (1.1)**: $\bar x\in S$ and $\theta(\bar x)\le\theta(x)$ for every $x\in S$, i.e. $\theta(\bar x)$ is the minimum of $\theta$ on $S$.
--   3. **Active set** (2.13): $\bar M=\{i\in M : g_i(\bar x)=0\}$.
--   4. **The set $D$** (2.14): $D=\{x\in E^n : g_i(x)<0,\ i\in M\setminus\bar M\}$, the points at which every constraint inactive at $\bar x$ is strictly satisfied.
--   5. **Generalized Fritz John conditions** (2.9)–(2.12) hold at $\bar x$ if there are $\bar u=(\bar u_0,\bar u_1,\dots,\bar u_m)\in E^{m+1}$ and $\bar v=(\bar v_1,\dots,\bar v_k)\in E^k$ with
--   $$
--   \bar u_0\nabla\theta(\bar x)+\sum_{i=1}^m\bar u_i\nabla g_i(\bar x)+\sum_{j=1}^k\bar v_j\nabla h_j(\bar x)=0,\qquad \sum_{i=1}^m\bar u_i g_i(\bar x)=0,\qquad \bar u\ge 0,\qquad (\bar u,\bar v)\ne 0 .
--   $$
--   6. **Kuhn–Tucker conditions** (3.1)–(3.3) hold at $\bar x$ if there are $\bar u\in E^m$, $\bar v\in E^k$ with
--   $$
--   \nabla\theta(\bar x)+\sum_{i=1}^m\bar u_i\nabla g_i(\bar x)+\sum_{j=1}^k\bar v_j\nabla h_j(\bar x)=0,\qquad \sum_{i=1}^m\bar u_i g_i(\bar x)=0,\qquad \bar u_i\ge 0,\ i\in M .
--   $$
--
--   The Fritz John conditions differ from the Kuhn–Tucker conditions only in the multiplier $\bar u_0\ge 0$ of $\nabla\theta$, which may vanish; the nontriviality condition $(\bar u,\bar v)\ne 0$ ranges over all of $\bar u_0,\dots,\bar u_m,\bar v_1,\dots,\bar v_k$ ("some but not all components can vanish", footnote 1, p. 40).
--
--   **Formalization Note** $E^n$ is `EuclideanSpace ℝ (Fin n)` and $\nabla f(\bar x)$ is Mathlib's `gradient f xbar`. The page indices $i=1,\dots,m$ and $j=1,\dots,k$ become `Fin m` and `Fin k` (0-based: page index $i$ is Lean index $i-1$). The multiplier vector $\bar u\in E^{m+1}$ is split into `u0 : ℝ` (for $\theta$) and `u : Fin m → ℝ`; $\bar u\ge0$ is $0\le\bar u_0$ and $0\le \bar u_i$ for all $i$; $(\bar u,\bar v)\ne0$ is "$\bar u_0\ne0$, or some $\bar u_i\ne0$, or some $\bar v_j\ne0$". "Solution of (1.1)" is a global minimizer over $S$, as on p. 42. The functions are not required to be differentiable in these definitions; the theorems add the paper's standing $C^1$ assumption.
-- source:
--   Mangasarian and Fromovitz, The Fritz John necessary optimality conditions in the presence of equality and inequality constraints, J. Math. Anal. Appl. 17 (1967), pp. 38–43, (1.1), (2.9)–(2.14), (2.19), (3.1)–(3.3)

import Mathlib

namespace MangasarianFJ.GenFJ

/-- The feasible set `S` of problem (1.1), display (2.19):
`S = {x ∈ Eⁿ | gᵢ(x) ≤ 0, i ∈ M; hⱼ(x) = 0, j ∈ K}`.
Page indices `i = 1, …, m` and `j = 1, …, k` are `Fin m` and `Fin k` (0-based). -/
def feasibleSet {n m k : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (h : Fin k → EuclideanSpace ℝ (Fin n) → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, g i x ≤ 0) ∧ ∀ j, h j x = 0}

/-- `x̄` is a solution of (1.1): `x̄` is feasible and `θ(x̄)` is the minimum of `θ` on `S`
(a global minimizer over the feasible set, p. 42). -/
def IsSolution {n m k : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (h : Fin k → EuclideanSpace ℝ (Fin n) → ℝ)
    (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  xbar ∈ feasibleSet g h ∧ ∀ x ∈ feasibleSet g h, θ xbar ≤ θ x

/-- The active index set `M̄ = {i ∈ M | gᵢ(x̄) = 0}`, displays (2.13) and (3.4). -/
def activeSet {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (xbar : EuclideanSpace ℝ (Fin n)) : Set (Fin m) :=
  {i | g i xbar = 0}

/-- The set `D = {x ∈ Eⁿ | gᵢ(x) < 0, i ∈ M − M̄}`, display (2.14). -/
def region {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (xbar : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, i ∉ activeSet g xbar → g i x < 0}

/-- The generalized Fritz John conditions (2.9)–(2.12) at `x̄`: there are
`ū = (ū₀, ū₁, …, ū_m) ∈ E^{m+1}` (here `u0` and `u`) and `v̄ ∈ E^k` (here `v`) with
(2.9) `ū₀∇θ(x̄) + Σ ūᵢ∇gᵢ(x̄) + Σ v̄ⱼ∇hⱼ(x̄) = 0`, (2.10) `Σ ūᵢ gᵢ(x̄) = 0`,
(2.11) `ū ≥ 0` (all of `ū₀, ū₁, …, ū_m`), and (2.12) `(ū, v̄) ≠ 0`. -/
def FritzJohnConditions {n m k : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (h : Fin k → EuclideanSpace ℝ (Fin n) → ℝ)
    (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ (u0 : ℝ) (u : Fin m → ℝ) (v : Fin k → ℝ),
    u0 • gradient θ xbar + ∑ i, u i • gradient (g i) xbar
        + ∑ j, v j • gradient (h j) xbar = 0 ∧
    ∑ i, u i * g i xbar = 0 ∧
    0 ≤ u0 ∧ (∀ i, 0 ≤ u i) ∧
    (u0 ≠ 0 ∨ (∃ i, u i ≠ 0) ∨ ∃ j, v j ≠ 0)

/-- The Kuhn–Tucker conditions (3.1)–(3.3) at `x̄`: there are `ū ∈ E^m` and `v̄ ∈ E^k` with
(3.1) `∇θ(x̄) + Σ ūᵢ∇gᵢ(x̄) + Σ v̄ⱼ∇hⱼ(x̄) = 0`, (3.2) `Σ ūᵢ gᵢ(x̄) = 0`, (3.3) `ūᵢ ≥ 0`. -/
def KuhnTuckerConditions {n m k : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (h : Fin k → EuclideanSpace ℝ (Fin n) → ℝ)
    (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ (u : Fin m → ℝ) (v : Fin k → ℝ),
    gradient θ xbar + ∑ i, u i • gradient (g i) xbar + ∑ j, v j • gradient (h j) xbar = 0 ∧
    ∑ i, u i * g i xbar = 0 ∧
    ∀ i, 0 ≤ u i

end MangasarianFJ.GenFJ


