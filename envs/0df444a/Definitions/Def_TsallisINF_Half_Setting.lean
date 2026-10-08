-- Prove2me | Definitions.Def_TsallisINF_Half_Setting
-- name    : TsallisINF_Half_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:07.899424+00:00
-- url     : https://prove2.me/theorems/0657c94f-aebd-49d9-b228-97e3166ae89c
-- title:
--   §2–§3, pp. 5–10, 18 — the randomized adaptive adversary, the law of a run, pseudo-regret, the ½-Tsallis regularizer, (IW)/(RV) estimators, Tsallis-INF, Φ_t, stability, penalty and (4)
-- statement:
--   This file fixes the model of Zimmert and Seldin's analysis of Tsallis-INF (Section 2, Section 3 and Algorithm 1), shared by every mission of the paper.
--
--   1. **Protocol and adversary.** There are $K\ge 1$ arms and rounds $t=1,2,\dots$. The adversary's internal randomization is a seed $\omega\sim\mu$, where $\mu$ is a probability measure on a measurable space $\Omega$. For each seed the adversary is a deterministic adaptive adversary: the loss $\ell_{t,i}\in[0,1]$ of arm $i$ at round $t$ may depend on $\omega$ and on the learner's past actions $I_1,\dots,I_{t-1}$. An action sequence is a map $h$ with $h(t)=I_t$.
--
--   2. **Law of a run.** The learner's weights are $w_{t,i}=w_{t,i}(\omega,h)$. For a horizon $T$ and a quantity $F(\omega,h)$ of the run,
--   $$
--   \mathbb E_T[F]=\int_\Omega\sum_{a\in\{1,\ldots,K\}^T}\Big(\prod_{t=1}^T w_{t,a_t}(\omega,a)\Big)F(\omega,a)\,d\mu(\omega),
--   $$
--   that is, $\omega\sim\mu$ and then $I_t\sim w_t$ successively.
--
--   3. **Pseudo-regret and best arm.** $\overline{Reg}_T=\mathbb E_T\big[\sum_{t=1}^T\ell_{t,I_t}\big]-\min_i\mathbb E_T\big[\sum_{t=1}^T\ell_{t,i}\big]$, and $i^*_T$ is a best arm in expectation in hindsight if it attains the minimum.
--
--   4. **Regularizer.** The ½-Tsallis regularizer with symmetric regularization ($\xi_i=1$) and learning rate $\eta_t$ is
--   $$
--   \Psi_t(w)=-\frac{4}{\eta_t}\sum_{i}\Big(\sqrt{w_i}-\frac{w_i}{2}\Big),
--   $$
--   the case $\alpha=\tfrac12$ of $\Psi(w)/\eta_t$ with $\Psi(w)=-\sum_i\frac{w_i^\alpha-\alpha w_i}{\alpha(1-\alpha)}$. The (RV) learning rate of Theorem 1 is $\eta_t=4\sqrt{1/t}$.
--
--   5. **Estimators.** (IW): $\hat\ell_{t,i}=\mathbb 1(I_t=i)\,\ell_{t,i}/w_{t,i}$. (RV): $\hat\ell_{t,i}=\mathbb 1(I_t=i)(\ell_{t,i}-\mathbb B_t(i))/w_{t,i}+\mathbb B_t(i)$ with $\mathbb B_t(i)=\tfrac12\mathbb 1(w_{t,i}\ge\eta_t^2)$. Cumulative estimates are $\hat L_{t-1}=\sum_{s=1}^{t-1}\hat\ell_s$, so $\hat L_0=0$. An estimator is **unbiased** if $\mathbb E_{I_t\sim w_t}[\hat\ell_t]=\ell_t$ for every seed and past; the definition also asks for measurability in $\omega$ and integrability, so that the expectations are those of the paper.
--
--   6. **Tsallis-INF (Algorithm 1).** At every round $t\ge1$, $w_t\in\Delta^{K-1}$ maximizes $\langle w,-\hat L_{t-1}\rangle-\Psi_t(w)$ over the probability simplex.
--
--   7. **Potential, stability and penalty.** $\Phi_t(Y)=(\Psi_t+\mathcal I_{\Delta^{K-1}})^*(Y)=\max_{w\in\Delta^{K-1}}\langle w,Y\rangle-\Psi_t(w)$. The decomposition (6) of p. 18 has the per-round stability $\mathbb E\big[\ell_{t,I_t}+\Phi_t(-\hat L_t)-\Phi_t(-\hat L_{t-1})\big]$ and the penalty $\mathbb E\big[\sum_{t=1}^T\Phi_t(-\hat L_{t-1})-\Phi_t(-\hat L_t)-\ell_{t,i^*_T}\big]$.
--
--   8. **Self-bounding property (4).** For a gap vector $\Delta$ with zero entry $i^*$ and a constant $C$,
--   $$
--   \overline{Reg}_T\ \ge\ \mathbb E\Big[\sum_{t=1}^T\sum_{i\ne i^*}w_{t,i}\Delta_i\Big]-C,
--   $$
--   and $\Delta_{\min}=\min_{\Delta_i>0}\Delta_i$.
--
--   These definitions give every theorem of the three missions the same loss model, run law and algorithm.
--
--   **Formalization Note** Arms are `Fin K`, so the paper's arm $1$ has index $0$. Action sequences are maps $\mathbb N\to$ `Fin K` with entry $0$ unused; a finite path of length $T$ is extended by a filler arm outside rounds $1,\dots,T$. The weights are given by an argmax predicate on a function $W$, never by a choice function; the objective is strictly concave, so the predicate determines $W$. $\Phi_t$ is a real supremum over the simplex, which is nonempty for $K\ge1$ and on which the objective is continuous, hence bounded. A per-round quantity of round $t$ is taken with horizon $t$. $\Delta_{\min}$ is the infimum of $\Delta_i$ over $i\ne i^*$, which is the paper's $\min_{\Delta_i>0}\Delta_i$ when $i^*$ is the unique zero of $\Delta$; theorems that use it assume $K\ge2$ and the unique zero. The pseudo-regret is defined here rather than taken from the published protocol, whose forecaster depends on past actions only, while Tsallis-INF also depends on the observed losses.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, pp. 5–8, §2, §3, Algorithm 1, (IW), (RV), §3.2; p. 9, Theorem 1 (learning rate); p. 10, (4) and Δ_min; p. 18, (6); p. 20, Lemma 12 (unbiased loss estimators)

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol

open MeasureTheory

namespace TsallisINF.Half

/-- Extend a finite list of actions to the paper's rounds, numbered from one. -/
def extend {K : ℕ} (i₀ : Fin K) (T : ℕ) (a : Fin T → Fin K) (s : ℕ) : Fin K :=
  if hs : 1 ≤ s ∧ s ≤ T then a ⟨s - 1, by omega⟩ else i₀

/-- Expectation over an adversary seed and all action paths of length `T`. -/
noncomputable def expect {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (i₀ : Fin K) (T : ℕ) (F : Ω → (ℕ → Fin K) → ℝ) : ℝ :=
  ∫ ω, ∑ a : Fin T → Fin K,
    (∏ t ∈ Finset.Icc 1 T, W t ω (extend i₀ T a) (extend i₀ T a t)) *
      F ω (extend i₀ T a) ∂μ

/-- Expected loss of the learner minus the least expected loss of a fixed arm. -/
noncomputable def pseudoRegret {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K) (T : ℕ) : ℝ :=
  expect μ W i₀ T (fun ω h => ∑ t ∈ Finset.Icc 1 T, (adv ω).val t h (h t)) -
    ⨅ i : Fin K, expect μ W i₀ T
      (fun ω h => ∑ t ∈ Finset.Icc 1 T, (adv ω).val t h i)

/-- A fixed arm minimizing the expected cumulative loss at horizon `T`. -/
def IsBestInHindsight {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K)
    (T : ℕ) (istar : Fin K) : Prop :=
  ∀ j : Fin K,
    expect μ W i₀ T (fun ω h => ∑ t ∈ Finset.Icc 1 T, (adv ω).val t h istar) ≤
      expect μ W i₀ T (fun ω h => ∑ t ∈ Finset.Icc 1 T, (adv ω).val t h j)

/-- The symmetric one-half Tsallis regularizer at learning rate `η`. -/
noncomputable def psiHalf {K : ℕ} (η : ℝ) (w : Fin K → ℝ) : ℝ :=
  -4 * η⁻¹ * ∑ i, (Real.sqrt (w i) - w i / 2)

/-- Importance-weighted estimate of the loss of arm `i`. -/
noncomputable def estIW {K : ℕ} {Ω : Type*}
    (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (t : ℕ) (ω : Ω) (h : ℕ → Fin K) (i : Fin K) : ℝ :=
  if h t = i then (adv ω).val t h i / W t ω h i else 0

/-- Reduced-variance estimate with baseline one half above the threshold `η_t²`. -/
noncomputable def estRV {K : ℕ} {Ω : Type*} (η : ℕ → ℝ)
    (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (t : ℕ) (ω : Ω) (h : ℕ → Fin K) (i : Fin K) : ℝ :=
  let B : ℝ := if η t ^ 2 ≤ W t ω h i then 1 / 2 else 0
  (if h t = i then ((adv ω).val t h i - B) / W t ω h i else 0) + B

/-- Estimated losses accumulated before round `t`. -/
def Lhat {K : ℕ} {Ω : Type*}
    (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (t : ℕ) (ω : Ω) (h : ℕ → Fin K) (i : Fin K) : ℝ :=
  ∑ s ∈ Finset.Ico 1 t, est s ω h i

/-- Algorithm 1: at each round, weights maximize the regularized estimated reward. -/
def IsTsallisINF {K : ℕ} {Ω : Type*} (η : ℕ → ℝ)
    (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) : Prop :=
  ∀ t, 1 ≤ t → ∀ ω h,
    W t ω h ∈ stdSimplex ℝ (Fin K) ∧
      ∀ v ∈ stdSimplex ℝ (Fin K),
        (∑ i, v i * (-Lhat est t ω h i)) - psiHalf (η t) v ≤
          (∑ i, W t ω h i * (-Lhat est t ω h i)) - psiHalf (η t) (W t ω h)

/-- Convex conjugate of the regularizer restricted to the probability simplex. -/
noncomputable def Phi {K : ℕ} (η : ℕ → ℝ) (t : ℕ) (Y : Fin K → ℝ) : ℝ :=
  ⨆ w : stdSimplex ℝ (Fin K), (∑ i, (w : Fin K → ℝ) i * Y i) - psiHalf (η t) w

/-- The self-bounding constraint (4) at a fixed horizon. -/
noncomputable def SelfBounding {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (i₀ : Fin K) (T : ℕ) (Δ : Fin K → ℝ) (istar : Fin K) (C : ℝ) : Prop :=
  expect μ W i₀ T
    (fun ω h => ∑ t ∈ Finset.Icc 1 T,
      ∑ i ∈ Finset.univ.erase istar, W t ω h i * Δ i) - C ≤
    pseudoRegret μ adv W i₀ T

/-- Minimum gap among arms other than the distinguished zero-gap arm. -/
noncomputable def deltaMin {K : ℕ} (Δ : Fin K → ℝ) (istar : Fin K) : ℝ :=
  ⨅ i : {i : Fin K // i ≠ istar}, Δ i

/-- The RV learning rate of Theorem 1. -/
noncomputable def etaRV (t : ℕ) : ℝ := 4 * Real.sqrt (1 / (t : ℝ))

/-- The stability summand in the decomposition (6), with horizon `t`. -/
noncomputable def stability {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K)
    (η : ℕ → ℝ) (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (t : ℕ) : ℝ :=
  expect μ W i₀ t (fun ω h =>
    (adv ω).val t h (h t) +
      Phi η t (fun i => -Lhat est (t + 1) ω h i) -
      Phi η t (fun i => -Lhat est t ω h i))

/-- The penalty term in the decomposition (6). -/
noncomputable def penalty {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K)
    (η : ℕ → ℝ) (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ)
    (T : ℕ) (istar : Fin K) : ℝ :=
  expect μ W i₀ T (fun ω h =>
    ∑ t ∈ Finset.Icc 1 T,
      (Phi η t (fun i => -Lhat est t ω h i) -
        Phi η t (fun i => -Lhat est (t + 1) ω h i) -
        (adv ω).val t h istar))

/-- A measurable, integrable estimator that is unbiased after fixing the seed and history. -/
def IsUnbiased {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (adv : Ω → RegretBandits.Adversarial.Adversary K)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K)
    (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) : Prop :=
  (∀ t, 1 ≤ t → ∀ h i, Measurable (fun ω => est t ω h i)) ∧
  (∀ t, 1 ≤ t → ∀ i : Fin K,
    Integrable (fun ω => ∑ a : Fin t → Fin K,
      (∏ s ∈ Finset.Icc 1 t, W s ω (extend i₀ t a) (extend i₀ t a s)) *
        |est t ω (extend i₀ t a) i|) μ) ∧
  ∀ t, 1 ≤ t → ∀ ω h i,
    (∑ j : Fin K, W t ω h j * est t ω (Function.update h t j) i) =
      (adv ω).val t h i

end TsallisINF.Half


