-- Prove2me | Definitions.Def_RandomHorizonPG_Asymp_Estimator
-- name    : RandomHorizonPG_Asymp_Estimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:57.049918+00:00
-- url     : https://prove2.me/theorems/2fe8aa23-1f86-4abc-8be8-a53841e9359e
-- title:
--   Algorithms 1 and 3, (3.7)–(3.8), (3.11), pp. 8–11, App. A.3 p. 27 — law of the RPG stochastic gradient ∇̂J(θ) and runs of Algorithm 3
-- statement:
--   This file encodes the **random-horizon policy gradient (RPG)** algorithm of the paper as an explicit probability law and an explicit notion of a run.
--
--   **The estimator.** At parameter $\theta$, Algorithm 3 draws a horizon $T\sim\mathrm{Geom}(1-\gamma)$, $P(T=t)=(1-\gamma)\gamma^t$, and simulates the trajectory $(s_0,a_0,\dots,s_T,a_T)$ with $a_0\sim\pi_\theta(\cdot\mid s_0)$, $s_{t+1}\sim P(\cdot\mid s_t,a_t)$, $a_{t+1}\sim\pi_\theta(\cdot\mid s_{t+1})$. From the last pair $(s_T,a_T)$, Algorithm 1 (EstQ) draws an independent horizon $T'\sim\mathrm{Geom}(1-\gamma^{1/2})$, $P(T'=t)=(1-\gamma^{1/2})\gamma^{t/2}$, rolls out $(s_0,a_0)=(s_T,a_T), s_1,a_1,\dots,s_{T'},a_{T'}$ under the same dynamics and returns
--   $$
--   \hat Q_{\pi_\theta}(s_T,a_T)=\sum_{t=0}^{T'}\gamma^{t/2}R(s_t,a_t). \qquad (3.7)
--   $$
--   The stochastic policy gradient is
--   $$
--   \hat\nabla J(\theta)=\frac1{1-\gamma}\,\hat Q_{\pi_\theta}(s_T,a_T)\,\nabla\log\pi_\theta(a_T\mid s_T). \qquad (3.8)
--   $$
--   The measure $\mathrm{rpgLaw}(\theta)$ on $\mathbb R^d$ is the law of $\hat\nabla J(\theta)$: the sum over all outcomes $(T,T',\text{trajectory},\text{rollout})$ of the outcome's probability times the point mass at the resulting vector.
--
--   **Runs.** Given stepsizes $\alpha_k$ and an initial parameter $\theta_0$, a run of Algorithm 3 on a probability space $(\Omega,\mathcal F,P)$ with a filtration $(\mathcal F_k)$ consists of random parameters $\theta_k$ and stochastic gradients $g_k$ such that
--   1. $\theta_0$ is the input and $\theta_{k+1}=\theta_k+\alpha_k g_k$ on every sample path (3.11);
--   2. $\theta_k$ is $\mathcal F_k$-measurable and $g_k$ is $\mathcal F_{k+1}$-measurable;
--   3. given $\mathcal F_k$, $g_k$ is a fresh draw from $\mathrm{rpgLaw}(\theta_k)$:
--   $$
--   P\big(F\cap\{g_k\in B\}\big)=\int_F \mathrm{rpgLaw}(\theta_k)(B)\,dP\qquad\text{for all }F\in\mathcal F_k\text{ and Borel }B.
--   $$
--
--   These definitions are what makes the convergence results statements about the paper's algorithm rather than about a generic stochastic gradient method.
--
--   **Formalization Note** Trajectories of length $n+1$ are maps $\{0,\dots,n\}\to\mathcal S\times\mathcal A$; their probabilities are written out as products of transition and policy probabilities. $\gamma^{t/2}$ is $(\sqrt\gamma)^t$. The conditional-law condition is stated with set integrals rather than Mathlib's `condExp`. The filtration plays the role of the paper's $\mathcal F_k$ (p. 27), which contains $\theta_0,\dots,\theta_k$ and the samples drawn up to step $k$; the index shift ($g_k$ is the paper's sample with horizon $T_{k+1}$) follows (3.11).
-- source:
--   arXiv:1906.08383v3, Algorithm 1, p. 8; (3.7), (3.8), p. 9; (3.11), p. 10; Algorithm 3, p. 11; App. A.3, p. 27 (filtration F_k)

import Mathlib
import Definitions.Def_RandomHorizonPG_Asymp_Setting

namespace RandomHorizonPG.Asymp

open MeasureTheory

/-- arXiv:1906.08383v3, Algorithm 3, p. 11: the probability of the trajectory
`h = ((s₀,a₀), …, (s_n,a_n))` drawn by Algorithm 3 at parameter `θ`: start at `s₀`,
`a₀ ∼ π_θ(·|s₀)`, `s_{t+1} ∼ P(·|s_t,a_t)`, `a_{t+1} ∼ π_θ(·|s_{t+1})`. -/
noncomputable def startWeight {S A : Type*} [DecidableEq S] {d : ℕ} (P : S → A → S → ℝ)
    (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ) (s₀ : S) (θ : EuclideanSpace ℝ (Fin d))
    {n : ℕ} (h : Fin (n + 1) → S × A) : ℝ :=
  (if (h 0).1 = s₀ then 1 else 0) * π θ s₀ (h 0).2 *
    ∏ t : Fin n, (P (h t.castSucc).1 (h t.castSucc).2 (h t.succ).1 * π θ (h t.succ).1 (h t.succ).2)

/-- arXiv:1906.08383v3, Algorithm 1 (EstQ), p. 8: the probability of the rollout
`h' = ((s₀,a₀), …, (s_n,a_n))` started at the given pair `x = (s, a)` (`s₀ ← s`, `a₀ ← a`, not
resampled), then `s_{t+1} ∼ P(·|s_t,a_t)`, `a_{t+1} ∼ π_θ(·|s_{t+1})`. -/
noncomputable def rolloutWeight {S A : Type*} [DecidableEq S] [DecidableEq A] {d : ℕ}
    (P : S → A → S → ℝ) (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (x : S × A) {n : ℕ} (h' : Fin (n + 1) → S × A) : ℝ :=
  (if h' 0 = x then 1 else 0) *
    ∏ t : Fin n, (P (h' t.castSucc).1 (h' t.castSucc).2 (h' t.succ).1 * π θ (h' t.succ).1 (h' t.succ).2)

/-- arXiv:1906.08383v3, (3.7), p. 9: the EstQ output on a rollout of horizon `T' = n`,
`Q̂ = Σ_{t=0}^{T'} γ^{t/2} R(s_t,a_t)` (the last pair included). -/
noncomputable def qHat {S A : Type*} (R : S → A → ℝ) (γ : ℝ) {n : ℕ}
    (h' : Fin (n + 1) → S × A) : ℝ :=
  ∑ t : Fin (n + 1), Real.sqrt γ ^ (t : ℕ) * R (h' t).1 (h' t).2

/-- The sample space of one RPG step: the horizon `T`, the EstQ horizon `T'`, the trajectory
`(s₀,a₀,…,s_T,a_T)` of Algorithm 3 and the EstQ rollout `(s₀,a₀,…,s_{T'},a_{T'})`. -/
abbrev RPGSample (S A : Type*) : Type _ :=
  Σ T : ℕ, Σ T' : ℕ, (Fin (T + 1) → S × A) × (Fin (T' + 1) → S × A)

/-- arXiv:1906.08383v3, (3.8), p. 9 with Algorithms 1 and 3, pp. 8, 11: the law of the stochastic
policy gradient `∇̂J(θ) = (1/(1−γ)) Q̂_{π_θ}(s_T,a_T) ∇ log π_θ(a_T|s_T)`, where
`T ∼ Geom(1−γ)` (`P(T = t) = (1−γ)γ^t`), `(s_T,a_T)` is the last pair of Algorithm 3's trajectory,
`T' ∼ Geom(1−γ^{1/2})` (`P(T' = t) = (1−γ^{1/2})γ^{t/2}`) independent of `T`, and `Q̂` is EstQ's
output (3.7) on a rollout started at `(s_T,a_T)`. It is the mixture over all outcomes of the
point masses at the resulting vector, weighted by the outcome's probability. -/
noncomputable def rpgLaw {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    {d : ℕ} (P : S → A → S → ℝ) (R : S → A → ℝ) (γ : ℝ)
    (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ) (s₀ : S) (θ : EuclideanSpace ℝ (Fin d)) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  Measure.sum fun i : RPGSample S A =>
    ENNReal.ofReal
        ((1 - γ) * γ ^ i.1 * startWeight P π s₀ θ i.2.2.1 *
          ((1 - Real.sqrt γ) * Real.sqrt γ ^ i.2.1 *
            rolloutWeight P π θ (i.2.2.1 (Fin.last i.1)) i.2.2.2)) •
      Measure.dirac
        ((1 / (1 - γ) * qHat R γ i.2.2.2) •
          score π θ (i.2.2.1 (Fin.last i.1)).1 (i.2.2.1 (Fin.last i.1)).2)

/-- arXiv:1906.08383v3, Algorithm 3, p. 11, (3.11), p. 10, and the filtration of App. A.3, p. 27:
`θ` is a run of the random-horizon policy gradient from `θ₀` with stepsizes `α` on the
probability space `(Ω, μ)` with filtration `ℱ`, and `g k` is the stochastic gradient `∇̂J(θ_k)`
drawn at step `k`:
`θ₀` is the input; `θ_{k+1} = θ_k + α_k g_k` on every sample path; `θ_k` is `ℱ_k`-measurable and
`g_k` is `ℱ_{k+1}`-measurable; and, given `ℱ_k`, `g_k` is a fresh draw of the law `rpgLaw` at
`θ_k`: `μ(F ∩ {g_k ∈ B}) = ∫_F rpgLaw(θ_k)(B) dμ` for every `F ∈ ℱ_k` and Borel `B`. -/
def IsRPGRun {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] {d : ℕ}
    (P : S → A → S → ℝ) (R : S → A → ℝ) (γ : ℝ) (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (s₀ : S) (α : ℕ → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d)) {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : Measure Ω) (ℱ : Filtration ℕ m) (θ g : ℕ → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ ω, θ 0 ω = θ₀) ∧
  (∀ k ω, θ (k + 1) ω = θ k ω + α k • g k ω) ∧
  (∀ k, Measurable[ℱ k] (θ k)) ∧
  (∀ k, Measurable[ℱ (k + 1)] (g k)) ∧
  (∀ k (F : Set Ω), MeasurableSet[ℱ k] F → ∀ B : Set (EuclideanSpace ℝ (Fin d)),
    MeasurableSet B → μ (F ∩ g k ⁻¹' B) = ∫⁻ ω in F, rpgLaw P R γ π s₀ (θ k ω) B ∂μ)

end RandomHorizonPG.Asymp


