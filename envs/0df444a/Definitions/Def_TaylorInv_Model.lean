-- Prove2me | Definitions.Def_TaylorInv_Model
-- name    : TaylorInv_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:30:24.124333+00:00
-- url     : https://prove2.me/theorems/4abe683d-a2f1-49d9-a3f9-92d3ae963f8b
-- title:
--   One-warehouse, multi-retailer system with demand features: data and Assumptions 1–3
-- statement:
--   A warehouse supplies $J$ retailers. Retailer $j$ has holding cost $h'_j$, lost-sales cost $b_j$ and $P$ demand features $x_{j1},\dots,x_{jP}$; the warehouse has holding cost $h_0$. Under the linear demand model (Assumption 1) retailer $j$'s demand is
--   $$
--   D_j=\gamma_j+\sum_{p=1}^P\beta_{jp}x_{jp}+\epsilon_j ,
--   $$
--   where the noise $\epsilon_j$ has a density $f_j$ supported on an interval $[lo_j,hi_j]$.
--
--   The **standing assumptions** with bounds $\bar D,\bar\epsilon,\bar B,\bar M,\bar\sigma$ and a probability measure $\mu$ on the features are:
--
--   1. the cost order $0\le h_0\le h'_j$ for all $j$ and $h'_i\le b_j$ for all $i,j$, i.e. $0\le h_0\le\underline h\le h'_j\le\bar h\le b_j$;
--   2. (Assumption 1) $\beta_j\neq0$, $|\beta_{jp}|\le\bar B$, and the noise has mean zero;
--   3. (Assumption 2) $f_j$ is a measurable probability density that vanishes off $[lo_j,hi_j]$, satisfies $\ell_j\le f_j\le u_j$ on $[lo_j,hi_j]$ with $0<\ell_j\le u_j$, and is Lipschitz there; $-\bar\epsilon\le lo_j$, $hi_j\le\bar\epsilon$; and for almost every feature outcome the demand lies in $[0,\bar D]$ for every noise value in the support;
--   4. (Assumption 3) the $JP$ features are mutually independent random variables with $|x_{jp}|\le\bar M$ almost surely and $\mathrm{Var}(x_{jp})\le\bar\sigma^2$.
--
--   These objects are the model of every statement in the mission.
--
--   **Formalization Note** The structure `Model J P Ω` holds data only; `Model.Assumptions` collects every hypothesis. Retailers are `Fin J`, features `Fin P`. The noise enters only through its density: with $\epsilon_j$ independent of $x_j$, the paper's conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ are integrals against $f_j$, so the noise independence of Assumption 1 needs no separate hypothesis. The paper's "domain" of the density is the interval $[lo_j,hi_j]$.
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, §3, pp.7–8; Assumptions 1–3, pp.14–15

import Mathlib

open MeasureTheory ProbabilityTheory

namespace TaylorInv

/-- The data of a one-warehouse, `J`-retailer system with `P` demand features per retailer
(Huang, Shang, Yang & Zhou, *Taylor Approximation of Inventory Policies for One-Warehouse,
Multi-Retailer Systems with Demand Feature Information*, SSRN 3993516 (Jan 29 2023), §3, pp.7–8,
and Assumptions 1–3, pp.14–15).

Retailer `j` faces the demand `D_j = γ_j + ∑_p β_jp x_jp + ϵ_j` (Assumption 1). The fields are the
warehouse holding cost `h₀`, the retailer holding costs `h′_j` (`h'`), the lost-sales costs `b_j`,
the intercepts `γ_j`, the coefficients `β_jp`, the density `f_j` of the noise `ϵ_j` with the
endpoints `lo_j ≤ hi_j` of its support and the density bounds `ℓ_j, u_j` of Assumption 2, and the
features `x_jp` as functions `X j p` on a sample space `Ω`.

**Formalization Note** The retailers are `Fin J` (the paper's `j = 1, …, J`), the features of a
retailer are `Fin P`. The features are random variables on `Ω`; the probability measure is a separate
argument of the predicates that use it. The noise enters only through its density: the paper's
conditional expectations `𝔼_{ϵ_j}[· | x_j]` with `ϵ_j` independent of `x_j` are integrals against
`f_j`. No proposition is bundled here; every assumption is in `Model.Assumptions`. -/
structure Model (J P : ℕ) (Ω : Type*) where
  /-- Warehouse holding cost rate `h₀`. -/
  h₀ : ℝ
  /-- Retailer holding cost `h′_j`. -/
  h' : Fin J → ℝ
  /-- Retailer lost-sales cost `b_j`. -/
  b : Fin J → ℝ
  /-- Demand intercept `γ_j`. -/
  γ : Fin J → ℝ
  /-- Demand coefficients `β_jp`. -/
  β : Fin J → Fin P → ℝ
  /-- Density `f_j` of the noise `ϵ_j` (Lebesgue density on `ℝ`). -/
  f : Fin J → ℝ → ℝ
  /-- Lower end `lo_j` of the support of `ϵ_j`. -/
  lo : Fin J → ℝ
  /-- Upper end `hi_j` of the support of `ϵ_j`. -/
  hi : Fin J → ℝ
  /-- Lower density bound `ℓ_j` (Assumption 2). -/
  ℓ : Fin J → ℝ
  /-- Upper density bound `u_j` (Assumption 2). -/
  u : Fin J → ℝ
  /-- Feature `x_jp` as a function of the outcome `ω`. -/
  X : Fin J → Fin P → Ω → ℝ

/-- The standing assumptions of Theorem 1 (Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023)):
the cost order of §3, p.8, `0 ≤ h₀ ≤ h̲ ≤ h′_j ≤ h̄ ≤ b_j ≤ b̄ < ∞`, and Assumptions 1–3, pp.14–15,
with the bounds `D̄` (demand), `ϵ̄` (noise), `B̄` (coefficients), `M̄` (features) and `σ̄²`
(feature variances), under the probability measure `μ` of the features.

**Formalization Note** `h₀ ≤ h̲ ≤ h′_j ≤ h̄ ≤ b_j` with `h̲ = min_j h′_j`, `h̄ = max_j h′_j` is written
as `h₀ ≤ h′_j` for all `j` and `h′_i ≤ b_j` for all `i, j`; `b̄ < ∞` is automatic for real numbers.
The noise "domain" of Assumption 2 is the interval `[lo_j, hi_j]`: the density vanishes outside it
and lies in `[ℓ_j, u_j]` on it (this makes `F_j(·|x_j)` absolutely continuous and strictly increasing
on the support), and it is Lipschitz there. `∫ f_j = 1` forces `f_j` to be integrable. "Demand in
`[0, D̄]`" is required for every noise value in the support, for almost every feature outcome.
The independence of the noise from the features and across retailers is encoded by integrating
against `f_j` (see `Model`). Assumption 3's independence is mutual independence of all `J·P`
features. -/
structure Model.Assumptions {J P : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model J P Ω)
    (Dbar ϵbar Bbar Mbar σbar : ℝ) (μ : Measure Ω) : Prop where
  /-- `0 ≤ h₀` (p.8). -/
  h₀_nonneg : 0 ≤ M.h₀
  /-- `h₀ ≤ h̲ ≤ h′_j` (p.8). -/
  h₀_le_h' : ∀ j, M.h₀ ≤ M.h' j
  /-- `h̄ = max_i h′_i ≤ b_j` (p.8). -/
  h'_le_b : ∀ i j, M.h' i ≤ M.b j
  /-- Assumption 1: `β_j` is a non-zero vector. -/
  β_ne_zero : ∀ j, M.β j ≠ 0
  /-- Assumption 1: `‖β_j‖_∞ ≤ B̄`. -/
  β_le : ∀ j p, |M.β j p| ≤ Bbar
  /-- Assumption 1: the noise has mean zero. -/
  noise_mean_zero : ∀ j, ∫ e, e * M.f j e = 0
  /-- Assumption 2: the density is measurable. -/
  f_measurable : ∀ j, Measurable (M.f j)
  /-- Assumption 2: the density integrates to one. -/
  f_integral : ∀ j, ∫ e, M.f j e = 1
  /-- Assumption 2: the density vanishes off its domain `[lo_j, hi_j]`. -/
  f_zero_off : ∀ j e, e ∉ Set.Icc (M.lo j) (M.hi j) → M.f j e = 0
  /-- Assumption 2: `0 < ℓ_j ≤ u_j`. -/
  ℓ_pos : ∀ j, 0 < M.ℓ j
  ℓ_le_u : ∀ j, M.ℓ j ≤ M.u j
  /-- Assumption 2: `f_j ∈ [ℓ_j, u_j]` on its domain. -/
  f_mem : ∀ j, ∀ e ∈ Set.Icc (M.lo j) (M.hi j), M.ℓ j ≤ M.f j e ∧ M.f j e ≤ M.u j
  /-- Assumption 2: `f_j` is Lipschitz continuous on its domain. -/
  f_lipschitz : ∀ j, ∃ K, LipschitzOnWith K (M.f j) (Set.Icc (M.lo j) (M.hi j))
  /-- Assumption 2: the noise is bounded in `[-ϵ̄, ϵ̄]`. -/
  support_le : ∀ j, -ϵbar ≤ M.lo j ∧ M.hi j ≤ ϵbar
  /-- Assumption 2: the demand is bounded in `[0, D̄]`. -/
  demand_mem : ∀ᵐ ω ∂μ, ∀ j, ∀ e ∈ Set.Icc (M.lo j) (M.hi j),
    0 ≤ M.γ j + ∑ p, M.β j p * M.X j p ω + e ∧ M.γ j + ∑ p, M.β j p * M.X j p ω + e ≤ Dbar
  /-- Assumption 3: the features are random variables. -/
  X_measurable : ∀ j p, Measurable (M.X j p)
  /-- Assumption 3: the features `x_jp` are (mutually) independent. -/
  X_indep : iIndepFun (fun q : Fin J × Fin P => M.X q.1 q.2) μ
  /-- Assumption 3: `|x_jp| ≤ M̄`. -/
  X_bound : ∀ j p, ∀ᵐ ω ∂μ, |M.X j p ω| ≤ Mbar
  /-- Assumption 3: `Var(x_jp) ≤ σ̄²`. -/
  X_variance : ∀ j p, variance (M.X j p) μ ≤ σbar ^ 2

end TaylorInv


