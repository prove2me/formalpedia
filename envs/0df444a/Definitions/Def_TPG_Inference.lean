-- Prove2me | Definitions.Def_TPG_Inference
-- name    : TPG_Inference
-- status  : Definition
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:02:43.625103+00:00
-- url     : https://prove2.me/theorems/616a3cfa-4d7d-4301-862b-5e7d56f7dc3f
-- title:
--   §6 — summands $B_t$, Newey–West HAC estimator, Assumptions 2–3, modes of convergence, mixing $\sigma$-algebras
-- statement:
--   Objects of §6 (central limit theorem and variance estimation) and of Appendix A.4 of the source. Time is $t=0,\dots,T-1$ (the source's $t+1$); the data are generated under the experimental policy $\pi_{1/2}$ unless stated otherwise.
--
--   1. **Reward-time summands** (`ipw`, `Bt`, `Bbar`): with $w_t^{\mathrm{IPW}}=2(2Z_t-1)$,
--
--   $$B_t=\sum_{i=\max(0,t-k)}^{t}w_i^{\mathrm{IPW}}\,Y_t,\qquad \bar B=\frac1T\sum_{t<T}B_t ,$$
--
--   so that $\bar B=\widehat\tau_k$.
--
--   2. **HAC estimator** (`GammaHat`, `nwWeight`, `hacEst`): for a bandwidth $L$,
--
--   $$\widehat\Gamma_\ell=\frac1T\sum_{t+\ell<T}(B_t-\bar B)(B_{t+\ell}-\bar B),\qquad w_\ell^{\mathrm{NW}}=1-\frac{\ell}{L+1},\qquad \widehat\Omega_T=\widehat\Gamma_0+2\sum_{\ell=1}^{L}w_\ell^{\mathrm{NW}}\,\widehat\Gamma_\ell .$$
--
--   3. **Ideal HAC estimator** (`Env.meanB`, `Env.GammaIdeal`, `Env.hacIdeal`): the same construction with $B_t-\bar B$ replaced by $V_t=B_t-\mu_t$, $\mu_t=\mathbb E[B_t]$, giving $\widetilde\Gamma_\ell$ and $\widetilde\Omega_T$.
--
--   4. **Assumption 2, asymptotic variance** (`Env.normVar`, `Env.AsymptoticVariance k v`): $\frac1T\operatorname{Var}\bigl(\sum_{t<T}B_t\bigr)\to v$ as $T\to\infty$, and $v>0$. The number $v$ is the source's $\sigma_k^2$.
--
--   5. **Assumption 3, Cesàro-$L^2$ mean stability** (`Env.cesaroDevSq`, `Env.MeanStability k`): with $\bar\mu_T=\frac1T\sum_{t<T}\mu_t$,
--
--   $$\Delta_T^2=\frac1T\sum_{t<T}(\mu_t-\bar\mu_T)^2=o\bigl(T^{-2/3}\bigr)\quad\text{as }T\to\infty .$$
--
--   6. **Bandwidth conditions** (`IsBandwidth L`): $L_T<T$ for all $T\ge1$, $L_T\to\infty$, and $L_T=O(T^{1/3})$.
--
--   7. **Modes of convergence as $T\to\infty$** for statistics $W_T$ of the horizon-$T$ trajectory. Convergence in distribution to $\mathcal N(0,v)$ (`Env.TendstoNormal`): $\mathbb E[f(W_T)]\to\int f\,d\mathcal N(0,v)$ for every bounded continuous $f:\mathbb R\to\mathbb R$. Convergence in probability to a constant $c$ (`Env.TendstoInProb`): $\mathbb P(|W_T-c|\ge\varepsilon)\to0$ for every $\varepsilon>0$.
--
--   8. **$\sigma$-algebras for strong mixing** (`sigmaWindow`, `GammaTerm`, `sigmaGamma`): $\mathcal F_a^b=\sigma\bigl((X_t,Z_t,Y_t):a\le t\le b\bigr)$, the local summand $\Gamma_t=2(2Z_t-1)\sum_{u=t}^{\min(t+k,\,T-1)}Y_u$, and $\sigma(\Gamma_t:a\le t\le b)$.
--
--   These objects are used in Theorem 2, Lemmas 2–5 and Corollary 1.
--
--   **Formalization Note** For each $T$ the statistics are random variables on the horizon-$T$ trajectory space with its own law; the laws for different $T$ are consistent with one another, and both modes of convergence in item 7 involve only the law of $W_T$ for each $T$. In Assumption 2 the limit is a parameter $v$ of the predicate. The normal law is taken with variance $\max(v,0)$.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. §6, p. 17: definitions of w^IPW, B_t, B̄, Assumption 2, Assumption 3, Theorem 2 (Γ̂_ℓ, w^NW_ℓ, L_T, Ω̂_T); Appendix A.4, pp. 28–29: Lemma 2 (F_a^b), Corollary 1 (Γ_t); Appendix F.2, p. 42: Lemma 4 (ideal HAC estimator).

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG

variable {S : Type} [Fintype S]

/-- Inverse-propensity weight `w^IPW = 2 (2 Z - 1)` under balanced randomization. -/
noncomputable def ipw (z : Bool) : ℝ :=
  2 * (2 * (if z then (1 : ℝ) else 0) - 1)

/-- Reward-time summand `B_t = ∑_{max(0, t - k) ≤ i ≤ t} w_i^IPW Y_t`. -/
noncomputable def Bt {T : ℕ} (k : ℕ) (t : Fin T) (ω : Traj S T) : ℝ :=
  ∑ i : Fin T, if (i : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (i : ℕ) + k then ipw (Z i ω) * Y t ω else 0

/-- Sample mean `B̄ = (1/T) ∑_{t < T} B_t`. -/
noncomputable def Bbar (T k : ℕ) (ω : Traj S T) : ℝ :=
  (1 / (T : ℝ)) * ∑ t : Fin T, Bt k t ω

/-- Lag-`ℓ` sample autocovariance centered at the sample mean,
`Γ̂_ℓ = (1/T) ∑_{t + ℓ < T} (B_t - B̄)(B_{t+ℓ} - B̄)`. -/
noncomputable def GammaHat (T k ℓ : ℕ) (ω : Traj S T) : ℝ :=
  (1 / (T : ℝ)) * ∑ t : Fin T, ∑ t' : Fin T,
    if (t : ℕ) + ℓ = (t' : ℕ) then (Bt k t ω - Bbar T k ω) * (Bt k t' ω - Bbar T k ω) else 0

/-- Newey–West (Bartlett) weight `w_ℓ^NW = 1 - ℓ / (L + 1)`. -/
noncomputable def nwWeight (L ℓ : ℕ) : ℝ :=
  1 - (ℓ : ℝ) / ((L : ℝ) + 1)

/-- Nonstationary HAC variance estimator with bandwidth `L`,
`Ω̂_T = Γ̂_0 + 2 ∑_{ℓ=1}^{L} w_ℓ^NW Γ̂_ℓ`. -/
noncomputable def hacEst (T k L : ℕ) (ω : Traj S T) : ℝ :=
  GammaHat T k 0 ω + 2 * ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * GammaHat T k ℓ ω

/-- Time-specific mean `μ_t = E[B_t]` under the experimental policy `π_{1/2}`. -/
noncomputable def Env.meanB [MeasurableSpace S] (E : Env S) (T k : ℕ) (t : Fin T) : ℝ :=
  ∫ ω, Bt k t ω ∂(E.expLaw T (1 / 2))

/-- Lag-`ℓ` sample autocovariance centered at the time-specific means,
`Γ̃_ℓ = (1/T) ∑_{t + ℓ < T} (B_t - μ_t)(B_{t+ℓ} - μ_{t+ℓ})`. -/
noncomputable def Env.GammaIdeal [MeasurableSpace S] (E : Env S) (T k ℓ : ℕ)
    (ω : Traj S T) : ℝ :=
  (1 / (T : ℝ)) * ∑ t : Fin T, ∑ t' : Fin T,
    if (t : ℕ) + ℓ = (t' : ℕ) then
      (Bt k t ω - E.meanB T k t) * (Bt k t' ω - E.meanB T k t') else 0

/-- Ideal HAC estimator `Ω̃_T = Γ̃_0 + 2 ∑_{ℓ=1}^{L} w_ℓ^NW Γ̃_ℓ`. -/
noncomputable def Env.hacIdeal [MeasurableSpace S] (E : Env S) (T k L : ℕ)
    (ω : Traj S T) : ℝ :=
  E.GammaIdeal T k 0 ω + 2 * ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * E.GammaIdeal T k ℓ ω

/-- Normalized variance `(1/T) Var(∑_{t < T} B_t)` under `π_{1/2}`. -/
noncomputable def Env.normVar [MeasurableSpace S] (E : Env S) (T k : ℕ) : ℝ :=
  (1 / (T : ℝ)) * variance (fun ω : Traj S T => ∑ t : Fin T, Bt k t ω) (E.expLaw T (1 / 2))

/-- Cesàro-`L²` deviation of the means,
`Δ_T² = (1/T) ∑_{t < T} (μ_t - μ̄_T)²` with `μ̄_T = (1/T) ∑_{t < T} μ_t`. -/
noncomputable def Env.cesaroDevSq [MeasurableSpace S] (E : Env S) (T k : ℕ) : ℝ :=
  (1 / (T : ℝ)) * ∑ t : Fin T,
    (E.meanB T k t - (1 / (T : ℝ)) * ∑ s : Fin T, E.meanB T k s) ^ 2

/-- The sigma-algebra `F_a^b = σ((X_t, Z_t, Y_t) : a ≤ t ≤ b)` on trajectories. -/
@[instance_reducible]
def sigmaWindow [MeasurableSpace S] (T a b : ℕ) : MeasurableSpace (Traj S T) :=
  ⨆ t : Fin T, ⨆ _ : a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b,
    MeasurableSpace.comap (fun ω : Traj S T => ω t) inferInstance

/-- Local summand `Γ_t = 2 (2 Z_t - 1) ∑_{t ≤ u ≤ t + k, u < T} Y_u`. -/
noncomputable def GammaTerm {T : ℕ} (k : ℕ) (t : Fin T) (ω : Traj S T) : ℝ :=
  ipw (Z t ω) * ∑ u : Fin T, if (t : ℕ) ≤ (u : ℕ) ∧ (u : ℕ) ≤ (t : ℕ) + k then Y u ω else 0

/-- The sigma-algebra `σ(Γ_t : a ≤ t ≤ b)` on trajectories. -/
@[instance_reducible]
noncomputable def sigmaGamma (S : Type) (T k a b : ℕ) : MeasurableSpace (Traj S T) :=
  ⨆ t : Fin T, ⨆ _ : a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b,
    MeasurableSpace.comap (fun ω : Traj S T => GammaTerm k t ω) inferInstance

/-- Assumption 2 (asymptotic variance) with limit `v`: the normalized variances
`(1/T) Var(∑_{t < T} B_t)` converge to `v` as `T → ∞`, and `0 < v`. -/
def Env.AsymptoticVariance [MeasurableSpace S] (E : Env S) (k : ℕ) (v : ℝ) : Prop :=
  0 < v ∧ Filter.Tendsto (fun T : ℕ => E.normVar T k) Filter.atTop (nhds v)

/-- Assumption 3 (Cesàro-`L²` mean stability): `Δ_T² = o(T^{-2/3})` as `T → ∞`. -/
def Env.MeanStability [MeasurableSpace S] (E : Env S) (k : ℕ) : Prop :=
  Asymptotics.IsLittleO Filter.atTop
    (fun T : ℕ => E.cesaroDevSq T k) (fun T : ℕ => (T : ℝ) ^ (-(2 / 3) : ℝ))

/-- Bandwidth conditions on the deterministic integer sequence `L_T`:
`0 ≤ L_T < T` for every `T ≥ 1`, `L_T → ∞`, and `L_T = O(T^{1/3})`. -/
def IsBandwidth (L : ℕ → ℕ) : Prop :=
  (∀ T : ℕ, 0 < T → L T < T)
    ∧ Filter.Tendsto L Filter.atTop Filter.atTop
    ∧ Asymptotics.IsBigO Filter.atTop
        (fun T : ℕ => (L T : ℝ)) (fun T : ℕ => (T : ℝ) ^ ((1 : ℝ) / 3))

/-- Convergence in distribution, as the horizon `T → ∞`, of the statistics `W T` computed on a
trajectory of length `T` generated under `π_{1/2}`, to the centered normal law with variance `v`:
`E[f(W_T)] → ∫ f dN(0, v)` for every bounded continuous `f : ℝ → ℝ`. -/
def Env.TendstoNormal [MeasurableSpace S] (E : Env S) (W : (T : ℕ) → Traj S T → ℝ)
    (v : ℝ) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℝ,
    Filter.Tendsto (fun T : ℕ => ∫ ω, f (W T ω) ∂(E.expLaw T (1 / 2))) Filter.atTop
      (nhds (∫ x, f x ∂(gaussianReal 0 (Real.toNNReal v))))

/-- Convergence in probability, as the horizon `T → ∞`, of the statistics `W T` computed on a
trajectory of length `T` generated under `π_{1/2}`, to the constant `c`:
`P(|W_T - c| ≥ ε) → 0` for every `ε > 0`. -/
def Env.TendstoInProb [MeasurableSpace S] (E : Env S) (W : (T : ℕ) → Traj S T → ℝ)
    (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Filter.Tendsto (fun T : ℕ => (E.expLaw T (1 / 2)) {ω | ε ≤ |W T ω - c|}) Filter.atTop
      (nhds 0)

end TPG


