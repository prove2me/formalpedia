-- Prove2me | Definitions.Def_BastaniBayati_LassoBandit_Model
-- name    : BastaniBayati_LassoBandit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T08:59:54.425634+00:00
-- url     : https://prove2.me/theorems/5c1e9bb1-2612-4c00-85b5-9f7ac42fa460
-- title:
--   The covariate bandit model and Assumptions 1–4
-- statement:
--   The model of Bastani and Bayati (§2.1–2.2). There are $K$ arms with unknown parameters $\beta_1,\dots,\beta_K\in\mathbb R^d$. At each time $t=1,2,\dots$ a covariate vector $X_t$ is observed, and pulling arm $i$ yields the reward $X_t^\top\beta_i+\varepsilon_{i,t}$.
--
--   **Probabilistic model** (`IsCovariateNoiseModel`). On a probability space: the covariates $X_1,X_2,\dots$ are i.i.d. with law $\mathcal P_X$, and every realization lies in a deterministic measurable set $\mathcal X\subseteq\mathbb R^d$; the noises $\varepsilon_{i,t}$ are independent, each $\sigma$-subgaussian (Definition 1: $\mathbb E[e^{s\varepsilon}]\le e^{\sigma^2s^2/2}$ for all $s\in\mathbb R$), not necessarily identically distributed; the noise family is independent of the covariate sequence.
--
--   With $X\sim\mathcal P_X$:
--
--   1. **Assumption 1** (Parameter Set): there are $x_{\max}>0$, $b>0$ with $\|x\|_\infty\le x_{\max}$ for all $x\in\mathcal X$ and $\|\beta_i\|_1\le b$ for all $i$.
--   2. **Assumption 2** (Margin Condition): there is $C_0>0$ with $\Pr[0<|X^\top(\beta_i-\beta_j)|\le\kappa]\le C_0\kappa$ for all arms $i\ne j$ and all $\kappa>0$.
--   3. **Assumption 3** (Arm Optimality): the arms split into disjoint sets $\mathcal K_{opt}\cup\mathcal K_{sub}=[K]$, and there are $h>0$, $p_*>0$ such that (a) $x^\top\beta_i<\max_{j\ne i}x^\top\beta_j-h$ for every $i\in\mathcal K_{sub}$ and $x\in\mathcal X$, and (b) every $i\in\mathcal K_{opt}$ has $\Pr[X\in U_i]\ge p_*$, where
--   $$U_i=\{x\in\mathcal X : x^\top\beta_i>\max_{j\ne i}x^\top\beta_j+h\}.$$
--   4. **Assumption 4** (Compatibility Condition): there is $\phi_0>0$ with $\Sigma_i\in\mathcal C(\mathrm{supp}(\beta_i),\phi_0)$ for each $i\in\mathcal K_{opt}$, where $\Sigma_i=\mathbb E[XX^\top\mid X\in U_i]$.
--
--   These are the standing hypotheses of Propositions 2–3 and Theorem 1.
--
--   **Formalization Note** Times are natural numbers and only $t\ge 1$ is constrained. $\|x\|$ on `Fin d → ℝ` is Mathlib's sup norm. $\Sigma_i$ is the uncentred conditional second-moment matrix $\mathbb E[XX^\top\mathbf 1\{X\in U_i\}]/\Pr[X\in U_i]$ (the paper's endnote 1). $\max_{j\ne i}$ is a supremum over the $K-1\ge 1$ other arms. Measurability of $\mathcal X$ and of the random variables is stated explicitly.
-- source:
--   Bastani & Bayati, Online Decision Making with High-Dimensional Covariates, Operations Research 68(1):276–294 (2020), doi:10.1287/opre.2019.1902, p. 280 (§2.1, Definition 1, Remark 3), pp. 281–282 (Assumptions 1–4), p. 293 (endnote 1)

import Mathlib
import Definitions.Def_BastaniBayati_LassoBandit_Basic

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace BastaniBayati.LassoBandit

/-- `max_{j ≠ i} xᵀβ_j`, the best reward at covariate `x` among the arms other than `i`
(Bastani–Bayati, Assumption 3). Arms are `Fin K`; for `K ≥ 2` the index set is finite and
nonempty, so the supremum is a maximum. -/
noncomputable def maxOther {d K : ℕ} (β : Fin K → Fin d → ℝ) (x : Fin d → ℝ) (i : Fin K) : ℝ :=
  ⨆ j : {j : Fin K // j ≠ i}, x ⬝ᵥ β j

/-- The region `Uᵢ ≡ {x ∈ 𝒳 | xᵀβᵢ > max_{j≠i} xᵀβⱼ + h}` of Assumption 3(b), p. 281. -/
def optRegion {d K : ℕ} (𝒳 : Set (Fin d → ℝ)) (β : Fin K → Fin d → ℝ) (h : ℝ) (i : Fin K) :
    Set (Fin d → ℝ) :=
  {x | x ∈ 𝒳 ∧ maxOther β x i + h < x ⬝ᵥ β i}

/-- The conditional second-moment matrix `E[XXᵀ | X ∈ U] = E[XXᵀ 1{X ∈ U}] / Pr[X ∈ U]` for
`X ∼ 𝒫_X` (Assumption 4, p. 282; by endnote 1 the paper's "covariance matrix" is the uncentred
matrix `E[XXᵀ]`). -/
noncomputable def condSecondMoment {d : ℕ} (PX : Measure (Fin d → ℝ)) (U : Set (Fin d → ℝ)) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun a b => (∫ x in U, x a * x b ∂PX) / (PX U).toReal

/-- The probabilistic model of §2.1 (p. 280) and Remark 3, on a probability space `(Ω, P)`.
Times are `t = 1, 2, …` (the values at `t = 0` are never used).
* the covariates `X₁, X₂, …` are i.i.d. with law `𝒫_X`, and every realization lies in the
  deterministic (measurable) set `𝒳 ⊆ ℝᵈ`;
* the noises `ε_{i,t}` (`i ∈ [K]`, `t ≥ 1`) are independent, each `σ`-subgaussian in the sense of
  Definition 1 (`E[e^{sε}] ≤ e^{σ²s²/2}` for all `s`), not necessarily identically distributed;
* the noise family is independent of the covariate sequence. -/
structure IsCovariateNoiseModel {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ} (P : Measure Ω)
    (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ)
    (ε : Fin K → ℕ → Ω → ℝ) (σ : ℝ≥0) : Prop where
  measurableSet_domain : MeasurableSet 𝒳
  measurable_X : ∀ t, 1 ≤ t → Measurable (X t)
  measurable_ε : ∀ i t, 1 ≤ t → Measurable (ε i t)
  mem_domain : ∀ t, 1 ≤ t → ∀ ω, X t ω ∈ 𝒳
  law_X : ∀ t, 1 ≤ t → P.map (X t) = PX
  iIndep_X : iIndepFun (fun t : ℕ => X (t + 1)) P
  iIndep_ε : iIndepFun (fun p : Fin K × ℕ => ε p.1 (p.2 + 1)) P
  indep_X_ε : IndepFun (fun ω (t : ℕ) => X (t + 1) ω) (fun ω (p : Fin K × ℕ) => ε p.1 (p.2 + 1) ω) P
  subgaussian : ∀ i t, 1 ≤ t → HasSubgaussianMGF (ε i t) (σ ^ 2) P

/-- **Assumption 1** (Parameter Set), p. 281: positive constants `x_max`, `b` with `‖x‖_∞ ≤ x_max`
for all `x ∈ 𝒳` and `‖βᵢ‖₁ ≤ b` for all arms. (`‖x‖` on `Fin d → ℝ` is Mathlib's sup norm
`maxⱼ |xⱼ|`.) -/
def ParameterSet {d K : ℕ} (𝒳 : Set (Fin d → ℝ)) (β : Fin K → Fin d → ℝ) (xmax b : ℝ) : Prop :=
  0 < xmax ∧ 0 < b ∧ (∀ x ∈ 𝒳, ‖x‖ ≤ xmax) ∧ ∀ i, l1Norm (β i) ≤ b

/-- **Assumption 2** (Margin Condition), p. 281: a constant `C₀ > 0` with
`Pr[0 < |Xᵀ(βᵢ − βⱼ)| ≤ κ] ≤ C₀ κ` for all arms `i ≠ j` and all `κ > 0`, where `X ∼ 𝒫_X`. -/
def MarginCondition {d K : ℕ} (PX : Measure (Fin d → ℝ)) (β : Fin K → Fin d → ℝ) (C0 : ℝ) :
    Prop :=
  0 < C0 ∧ ∀ i j : Fin K, i ≠ j → ∀ κ : ℝ, 0 < κ →
    PX {x | 0 < |x ⬝ᵥ (β i - β j)| ∧ |x ⬝ᵥ (β i - β j)| ≤ κ} ≤ ENNReal.ofReal (C0 * κ)

/-- **Assumption 3** (Arm Optimality), p. 281: `𝒦_opt`, `𝒦_sub` are disjoint and cover `[K]`, and
for some `h > 0` and `p_* > 0`: (a) every `i ∈ 𝒦_sub` has `xᵀβᵢ < max_{j≠i} xᵀβⱼ − h` for every
`x ∈ 𝒳`; (b) every `i ∈ 𝒦_opt` has `Pr[X ∈ Uᵢ] ≥ p_*`. -/
def ArmOptimality {d K : ℕ} (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ))
    (β : Fin K → Fin d → ℝ) (Kopt Ksub : Finset (Fin K)) (h pstar : ℝ) : Prop :=
  0 < h ∧ 0 < pstar ∧ Disjoint Kopt Ksub ∧ Kopt ∪ Ksub = Finset.univ ∧
    (∀ i ∈ Ksub, ∀ x ∈ 𝒳, x ⬝ᵥ β i < maxOther β x i - h) ∧
    ∀ i ∈ Kopt, ENNReal.ofReal pstar ≤ PX (optRegion 𝒳 β h i)

/-- **Assumption 4** (Compatibility Condition), p. 282: a constant `φ₀ > 0` such that for each
`i ∈ 𝒦_opt`, `Σᵢ ≡ E[XXᵀ | X ∈ Uᵢ] ∈ 𝒞(supp(βᵢ), φ₀)`. -/
def CompatibilityAssumption {d K : ℕ} (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ))
    (β : Fin K → Fin d → ℝ) (Kopt : Finset (Fin K)) (h φ0 : ℝ) : Prop :=
  0 < φ0 ∧ ∀ i ∈ Kopt,
    condSecondMoment PX (optRegion 𝒳 β h i) ∈ compatSet (supp (β i)) φ0

end BastaniBayati.LassoBandit


