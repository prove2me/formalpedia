-- Prove2me | Definitions.Def_MassartDKW_Tight_EmpiricalProcess
-- name    : MassartDKW_Tight_EmpiricalProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:39:59.850376+00:00
-- url     : https://prove2.me/theorems/9bbeb384-99b2-4d10-b4d1-62d7565d06ee
-- title:
--   §1, p. 1269 — empirical distribution function F̂ₙ and the Kolmogorov–Smirnov statistics Dₙ⁺, Dₙ⁻, Dₙ
-- statement:
--   Let $x_1,\dots,x_n$ be real random variables on a probability space $(\Omega,\mathcal F,P)$, and let $\mu$ be a probability measure on $\mathbb R$ with distribution function $F(x)=\mu(]-\infty,x])$.
--
--   1. The **empirical distribution function** of the sample is
--   $$\hat F_n(x)=\frac1n\sum_{i=1}^n \mathbb 1_{(x_i\le x)},\qquad x\in\mathbb R .$$
--   2. With the centred and normalised empirical process $Z_n=\sqrt n(\hat F_n-F)$, the **Kolmogorov–Smirnov statistics** are
--   $$D_n^+=\sup_{x\in\mathbb R}Z_n(x),\qquad D_n^-=\sup_{x\in\mathbb R}\bigl(-Z_n(x)\bigr),\qquad D_n=\sup_{x\in\mathbb R}|Z_n(x)| .$$
--
--   These are the goodness-of-fit statistics whose tail probabilities the Dvoretzky–Kiefer–Wolfowitz inequality controls; every probabilistic statement of the mission is about $D_n^-$ or $D_n$.
--
--   **Formalization Note** The sample is a family `X : Fin n → Ω → ℝ` (indices $0,\dots,n-1$), and $F$ is Mathlib's `cdf μ`. Each supremum is a real supremum of a function with values in $[-1,1]$ (both $\hat F_n$ and $F$ take values in $[0,1]$), so it is bounded and nonempty and no junk value arises. The factor $\sqrt n$ is outside the supremum, as in $Z_n=\sqrt n(\hat F_n-F)$. At $n=0$ the division by $n$ returns $0$; every theorem of the mission assumes $n\ge1$.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1269, §1 (definition of F̂_n, Z_n, D_n^+, D_n^-, D_n)

import Mathlib

namespace MassartDKW.Tight

open MeasureTheory ProbabilityTheory

/-- The empirical distribution function `F̂_n(x) = (1/n) Σ_{i=1}^n 𝟙(x_i ≤ x)` of the sample
`X 0 ω, …, X (n-1) ω` (Massart 1990, §1, p. 1269). -/
noncomputable def ecdf {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ω : Ω) (x : ℝ) : ℝ :=
  ((Finset.univ.filter (fun i => X i ω ≤ x)).card : ℝ) / n

/-- The one-sided Kolmogorov–Smirnov statistic `D_n⁺ = sup_{x ∈ ℝ} √n (F̂_n(x) − F(x))`,
where `F` is the distribution function `cdf μ` of the common law `μ`. -/
noncomputable def Dplus {Ω : Type*} {n : ℕ} (μ : Measure ℝ) (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  Real.sqrt n * ⨆ x : ℝ, (ecdf X ω x - cdf μ x)

/-- The one-sided Kolmogorov–Smirnov statistic `D_n⁻ = sup_{x ∈ ℝ} √n (F(x) − F̂_n(x))`. -/
noncomputable def Dminus {Ω : Type*} {n : ℕ} (μ : Measure ℝ) (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  Real.sqrt n * ⨆ x : ℝ, (cdf μ x - ecdf X ω x)

/-- The two-sided Kolmogorov–Smirnov statistic `D_n = sup_{x ∈ ℝ} √n |F̂_n(x) − F(x)|`. -/
noncomputable def Dtwo {Ω : Type*} {n : ℕ} (μ : Measure ℝ) (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  Real.sqrt n * ⨆ x : ℝ, |ecdf X ω x - cdf μ x|

end MassartDKW.Tight


