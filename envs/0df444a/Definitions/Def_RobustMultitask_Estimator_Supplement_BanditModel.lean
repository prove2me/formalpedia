-- Prove2me | Definitions.Def_RobustMultitask_Estimator_Supplement_BanditModel
-- name    : RobustMultitask_Estimator_Supplement_BanditModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:58:47.414135+00:00
-- url     : https://prove2.me/theorems/6b38adb6-2988-4495-9ef6-d0418a874d1f
-- title:
--   §5.1–5.2, pp. 22–24 — multitask linear contextual bandit, Assumptions 6–10, instance regret
-- statement:
--   The model of §5. There are $N$ bandit instances, $K$ arms and contexts in $\mathbb R^d$; time runs over $t=1,2,\dots$.
--
--   1. **Model.** At time $t$ an arrival occurs at instance $Z_t$, with $\mathbb P(Z_t=j)=p_j>0$. Given $Z_t=j$, the context $X_t$ has law $P^j_X$, and the noise $\varepsilon_t$ is mean-zero $\sigma_j$-subgaussian and independent of $X_t$. The triples $(Z_t,X_t,\varepsilon_t)$ are i.i.d. over $t$. Pulling arm $k$ yields $Y_t=X_t^\top\beta^{Z_t}_k+\varepsilon_t$, and $\beta^j_k=\beta^\dagger_k+\delta^j_k$ with $\|\delta^j_k\|_0\le s$.
--   2. **Assumption 6.** $\|X\|_\infty\le x_{\max}$ for $P^j_X$-almost every context and $\|\beta^j_k\|_1\le b$.
--   3. **Assumption 7.** The arms of instance $j$ split into $\mathcal K^j_{\mathrm{opt}}$ and its complement $\mathcal K^j_{\mathrm{sub}}$; for $k\in\mathcal K^j_{\mathrm{sub}}$, almost every context has some $k'\ne k$ with $X^\top\beta^j_k<X^\top\beta^j_{k'}-h$; for $k\in\mathcal K^j_{\mathrm{opt}}$, $\mathbb P(X\in U^j_k\mid Z=j)\ge p_*$, where $U^j_k=\{x: x^\top\beta^j_k>x^\top\beta^j_{k'}+h\ \forall k'\ne k\}$.
--   4. **Assumption 8.** For $k\in\mathcal K^j_{\mathrm{opt}}$, $\Sigma^j_k=\mathbb E[XX^\top\mid X\in U^j_k,Z=j]$ has $\lambda_{\min}(\Sigma^j_k)\ge\psi$.
--   5. **Assumption 9.** $\mathbb P(|X^\top(\beta^j_k-\beta^j_{k'})|\le\kappa\mid Z=j)\le L\kappa$ for all arms $k\ne k'$ and $\kappa>0$.
--   6. **Assumption 10.** $\mathcal W_k=\{j: k\in\mathcal K^j_{\mathrm{opt}}\}$ has $|\mathcal W_k|=0$ or $|\mathcal W_k|\ge\rho N$.
--   7. **Instance regret.** For a policy playing $\pi_t$,
--   $$R^j=\sum_{t=1}^{H}p_j r^j_t=\sum_{t=1}^{H}\mathbb E\Bigl[\mathbf 1\{Z_t=j\}\bigl(\max_{k}X_t^\top\beta^j_k-X_t^\top\beta^j_{\pi_t}\bigr)\Bigr].$$
--
--   These are the standing assumptions of Theorems 3 and 4 and Propositions 11–14.
--
--   **Formalization Note** Conditional statements given $Z_t=j$ use the conditional measure $\mathbb P[\,\cdot\mid Z_t=j]$. "For any $X\in\mathcal X^j$" is read $P^j_X$-almost surely. Assumption 8 is required for optimal arms only: for a suboptimal arm $U^j_k$ is $P^j_X$-null by Assumption 7, so its conditional covariance is undefined; the source prints "for any arm". Assumption 9 quantifies over distinct arms, as the prose before it says. Maxima over $k'\ne k$ are written as quantifiers, so a single arm needs no special case.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, pp. 22–24, §5.1 (model, regret) and §5.2 (Assumptions 6–10)

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation

namespace RobustMultitask.Estimator.Supplement

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

/-- The multitask linear contextual bandit model of §5.1 (pp. 22–23), on a probability space
`(Ω, P)`. Time steps are `t = 1, 2, …` (index `0` is unused).

* `N` instances (`Fin N`), `K` arms (`Fin K`), contexts in `ℝᵈ`.
* Arrivals: `Z t` is the instance receiving the arrival at time `t`, `P(Z_t = j) = p_j > 0`.
* Contexts: given `Z_t = j`, the context `X_t` has law `P_X^j` (`PX j`).
* Rewards: pulling arm `k` at time `t` with `Z_t = j` yields `X_tᵀβʲ_k + ε_t`; the noise `ε_t` is,
  given `Z_t = j`, `σ_j`-subgaussian with mean zero (Mathlib's `HasSubgaussianMGF` with variance
  proxy `σ_j²` under the conditional measure `P[·|Z_t = j]`) and independent of `X_t`.
* The triples `(Z_t, X_t, ε_t)` are independent and identically distributed over `t`.
* Sparse heterogeneity: `βʲ_k = β†_k + δʲ_k` with `‖δʲ_k‖₀ ≤ s` for all `k, j`. -/
structure IsBanditModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N K d : ℕ}
    (p : Fin N → ℝ) (PX : Fin N → Measure (Fin d → ℝ))
    (β : Fin N → Fin K → Fin d → ℝ) (βdag : Fin K → Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
    (Z : ℕ → Ω → Fin N) (Xc : ℕ → Ω → Fin d → ℝ) (ε : ℕ → Ω → ℝ) : Prop where
  meas_Z : ∀ t, Measurable (Z t)
  meas_X : ∀ t, Measurable (Xc t)
  meas_ε : ∀ t, Measurable (ε t)
  pos_p : ∀ j, 0 < p j
  arrival : ∀ t j, P (Z t ⁻¹' {j}) = ENNReal.ofReal (p j)
  context : ∀ t j, (P[|Z t ⁻¹' {j}]).map (Xc t) = PX j
  pos_σ : ∀ j, 0 < σ j
  noise_subgaussian : ∀ t j, HasSubgaussianMGF (ε t) (σ j ^ 2) (P[|Z t ⁻¹' {j}])
  noise_indep_context : ∀ t j, IndepFun (Xc t) (ε t) (P[|Z t ⁻¹' {j}])
  indep_time : iIndepFun (fun t ω => (Z t ω, Xc t ω, ε t ω)) P
  ident_time : ∀ t, IdentDistrib (fun ω => (Z t ω, Xc t ω, ε t ω))
    (fun ω => (Z 0 ω, Xc 0 ω, ε 0 ω)) P P
  sparse : ∀ j k, l0 (β j k - βdag k) ≤ s

/-- The optimality region `Uʲ_k = {x | xᵀβʲ_k > max_{k′≠k} xᵀβʲ_{k′} + h}` of Assumption 7
(p. 23), written with a universal quantifier over `k′ ≠ k` (so that with a single arm it is the
whole space, the value of a maximum over the empty set being `−∞`). -/
def optRegion {N K d : ℕ} (β : Fin N → Fin K → Fin d → ℝ) (h : ℝ) (j : Fin N) (k : Fin K) :
    Set (Fin d → ℝ) :=
  {x | ∀ k', k' ≠ k → x ⬝ᵥ β j k' + h < x ⬝ᵥ β j k}

/-- `W_k = {j ∈ [N] | k ∈ 𝒦ʲ_opt}` (Assumption 10, p. 24). -/
noncomputable def optInstances {N K : ℕ} (Kopt : Fin N → Finset (Fin K)) (k : Fin K) :
    Finset (Fin N) :=
  Finset.univ.filter (fun j => k ∈ Kopt j)

/-- **Assumptions 6–10** (pp. 23–24) for the bandit model with context laws `PX`, arm
parameters `β`, the optimal-arm sets `𝒦ʲ_opt = Kopt j` (the suboptimal arms `𝒦ʲ_sub` are the
complement), and constants `x_max, b, h, p*, ψ, L, ρ`.

* (6) Boundedness: `x_max > 0`, `b > 0`, `‖X‖_∞ ≤ x_max` for `P_X^j`-almost every context and
  `‖βʲ_k‖₁ ≤ b`.
* (7) Arm optimality: `h > 0`, `p* > 0`; every suboptimal arm `k` has some `k′ ≠ k` with
  `Xᵀβʲ_k < Xᵀβʲ_{k′} − h` for `P_X^j`-almost every context; every optimal arm has
  `P(X ∈ Uʲ_k | Z = j) ≥ p*`.
* (8) Positive definiteness: `ψ > 0` and, for every optimal arm `k ∈ 𝒦ʲ_opt`,
  `Σʲ_k = E[XXᵀ | X ∈ Uʲ_k, Z = j]` has `λ_min(Σʲ_k) ≥ ψ`, in Rayleigh form
  `ψ ‖v‖₂² P_X^j(Uʲ_k) ≤ ∫_{Uʲ_k} (vᵀx)² dP_X^j`. (The source prints "for any arm"; for a
  suboptimal arm `Uʲ_k` is null by (7), so the conditional covariance is undefined there.)
* (9) Margin: `L > 0` and `P(|Xᵀ(βʲ_k − βʲ_{k′})| ≤ κ | Z = j) ≤ Lκ` for all distinct arms
  `k ≠ k′` and `κ > 0`.
* (10) Optimality density: `ρ > 0` and `|W_k| = 0` or `|W_k| ≥ ρN` for every arm `k`. -/
structure BanditAssumptions {N K d : ℕ} (PX : Fin N → Measure (Fin d → ℝ))
    (β : Fin N → Fin K → Fin d → ℝ) (Kopt : Fin N → Finset (Fin K))
    (xmax b h pstar ψ L ρ : ℝ) : Prop where
  pos_xmax : 0 < xmax
  pos_b : 0 < b
  bdd_context : ∀ j, ∀ᵐ x ∂(PX j), linf x ≤ xmax
  bdd_param : ∀ j k, l1 (β j k) ≤ b
  pos_h : 0 < h
  pos_pstar : 0 < pstar
  suboptimal : ∀ j k, k ∉ Kopt j →
    ∀ᵐ x ∂(PX j), ∃ k', k' ≠ k ∧ x ⬝ᵥ β j k < x ⬝ᵥ β j k' - h
  optimal : ∀ j k, k ∈ Kopt j → ENNReal.ofReal pstar ≤ PX j (optRegion β h j k)
  pos_ψ : 0 < ψ
  posdef : ∀ j k, k ∈ Kopt j → ∀ v : Fin d → ℝ,
    ψ * (v ⬝ᵥ v) * (PX j (optRegion β h j k)).toReal
      ≤ ∫ x in optRegion β h j k, (x ⬝ᵥ v) ^ 2 ∂(PX j)
  pos_L : 0 < L
  margin : ∀ j k k', k ≠ k' → ∀ κ : ℝ, 0 < κ →
    PX j {x | |x ⬝ᵥ (β j k - β j k')| ≤ κ} ≤ ENNReal.ofReal (L * κ)
  pos_ρ : 0 < ρ
  density : ∀ k, (optInstances Kopt k).card = 0 ∨ ρ * N ≤ ((optInstances Kopt k).card : ℝ)

/-- The instance-specific cumulative expected regret `Rʲ = ∑_{t=1}^{H} p_j rʲ_t` (p. 23) of a
policy whose arm at time `t` is `π t`, where
`rʲ_t = E[max_{k′} X_tᵀβʲ_{k′} − X_tᵀβʲ_{π_t} | Z_t = j]`. Since `p_j = P(Z_t = j)`,
`p_j rʲ_t = E[1{Z_t = j} (max_{k′} X_tᵀβʲ_{k′} − X_tᵀβʲ_{π_t})]`, which is the summand. -/
noncomputable def taskRegret {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N K d : ℕ}
    (β : Fin N → Fin K → Fin d → ℝ) (Z : ℕ → Ω → Fin N) (Xc : ℕ → Ω → Fin d → ℝ)
    (π : Ω → ℕ → Fin K) (j : Fin N) (H : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 H,
    ∫ ω, (if Z t ω = j then (⨆ k, Xc t ω ⬝ᵥ β j k) - Xc t ω ⬝ᵥ β j (π ω t) else 0) ∂P

end RobustMultitask.Estimator.Supplement


