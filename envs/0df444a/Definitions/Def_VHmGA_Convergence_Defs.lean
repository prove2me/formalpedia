-- Prove2me | Definitions.Def_VHmGA_Convergence_Defs
-- name    : VHmGA_Convergence_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:39:02.230417+00:00
-- url     : https://prove2.me/theorems/54a058b4-9d90-4104-9f3a-ea995424560f
-- title:
--   The noise level $\sigma^2_{\mathrm{total}}$ of (19) and verified SGD runs: update (18), conditional unbiasedness, bound (19) (§8.1)
-- statement:
--   This file fixes the stochastic model of the convergence analysis in §8 of Dora–Hluchý.
--
--   **Noise level (eq. (19)).** For reals $\sigma,\sigma_{\mathrm{DP}},\sigma_a,\alpha$,
--   $$
--   \sigma^2_{\mathrm{total}}=\sigma^2+\sigma^2_{\mathrm{DP}}+\frac{\alpha}{1-\alpha}\,\sigma_a^2 ,
--   $$
--   where $\sigma^2$ is the variance of the honest workers' mini-batch gradients, $\sigma^2_{\mathrm{DP}}$ the variance of the differential-privacy noise, $\sigma_a^2$ the residual variance of adversarial updates that pass verification, and $\alpha$ the fraction of corrupted workers.
--
--   **Verified SGD run.** Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $g:\mathbb R^d\to\mathbb R^d$ a gradient map, $(\eta_t)$ a step-size sequence, $w_1\in\mathbb R^d$ a fixed starting point, $(w_t)$ and $(\tilde g_t)$ random vectors in $\mathbb R^d$, $(\mathcal G_t)$ $\sigma$-algebras on $\Omega$ and $s\in\mathbb R$. The data form a verified SGD run with noise bound $s$ if, for every $t\ge1$:
--
--   1. $\eta_t>0$;
--   2. $w_1$ is the constant $w_1$, and $w_{t+1}=w_t-\eta_t\tilde g_t$ pointwise (the update (18));
--   3. $\mathcal G_t\subseteq\mathcal F$ and $w_t$ is $\mathcal G_t$-measurable;
--   4. $\tilde g_t$ is integrable and $\mathbb E[\tilde g_t\mid\mathcal G_t]=g(w_t)$ almost surely (conditional unbiasedness);
--   5. $\|\tilde g_t-g(w_t)\|^2$ is integrable and $\mathbb E[\|\tilde g_t-g(w_t)\|^2\mid\mathcal G_t]\le s$ almost surely (the bound (19) with $s=\sigma^2_{\mathrm{total}}$).
--
--   The vector $\tilde g_t$ stands for the verified, differentially private, aggregated gradient of the VHmGA protocol; the protocol itself (commitments, privacy noise, filtering of Byzantine workers) enters only through the bound $s$. Indexing is 1-based as in the paper.
--
--   Every theorem of the mission is stated for such runs. Clause 4 is not among the paper's stated hypotheses on $\tilde g_t$ (the paper calls only the honest workers' gradients unbiased); it is the minimal correction without which the convergence statements are false (see the goal theorem).
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. The conditioning $\sigma$-algebras are parameters, not fixed to $\sigma(w_t)$: any $\mathcal G_t$ making $w_t$ measurable is allowed. They are not required to increase in $t$, since the paper does not use a filtration. Conditional expectations are Mathlib's `condExp`, which is $0$ for non-integrable functions; the integrability clauses in 4 and 5 rule this out. Index $0$ carries no hypothesis.
-- source:
--   Jean Rosemond Dora, Ladislav Hluchý, STOC 2027 submission #955 (October 2026), §8.1 and eqs. (18)–(19), p. 6

import Mathlib

set_option autoImplicit false
open MeasureTheory

namespace VHmGA.Convergence

/-- The total noise level of eq. (19) (Dora–Hluchý, STOC 2027 submission #955, §8.1, p. 6):
`σ²_total = σ² + σ²_DP + α/(1−α)·σ²_a`, with `σ²` the honest sampling variance, `σ²_DP` the
privacy-noise variance, `σ²_a` the adversarial residual variance and `α` the corrupted fraction. -/
noncomputable def sigmaTotalSq (σ σDP σa α : ℝ) : ℝ :=
  σ ^ 2 + σDP ^ 2 + α / (1 - α) * σa ^ 2

/-- A verified SGD run (§8.1 and eqs. (18)–(19), p. 6), indices 1-based as in the paper; index `0`
carries no hypothesis. On a probability space `(Ω, m0, μ)`, with gradient map `g`, step sequence
`η`, deterministic start `w1`, iterates `w`, aggregated gradients `gt`, conditioning σ-algebras `m`
and noise bound `s`, for every `t ≥ 1`:
* `η t > 0`; `w 1 = w1`; `w (t+1) = w t − η t • gt t` pointwise (18);
* `m t ≤ m0` and `w t` is `m t`-measurable (conditioning on `m t` accounts for `w t`);
* `gt t` is integrable and conditionally unbiased: `E[gt t | m t] = g (w t)` a.s.;
* `‖gt t − g (w t)‖²` is integrable and `E[‖gt t − g (w t)‖² | m t] ≤ s` a.s. (19). -/
structure IsVerifiedSGDRun {d : ℕ} {Ω : Type*} [m0 : MeasurableSpace Ω] (μ : Measure Ω)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (η : ℕ → ℝ)
    (w1 : EuclideanSpace ℝ (Fin d)) (w gt : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (m : ℕ → MeasurableSpace Ω) (s : ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  step_pos : ∀ t, 1 ≤ t → 0 < η t
  init : w 1 = fun _ => w1
  update : ∀ t, 1 ≤ t → ∀ ω, w (t + 1) ω = w t ω - η t • gt t ω
  le_ambient : ∀ t, 1 ≤ t → m t ≤ m0
  stronglyMeasurable_iter : ∀ t, 1 ≤ t → StronglyMeasurable[m t] (w t)
  integrable_agg : ∀ t, 1 ≤ t → Integrable (gt t) μ
  unbiased : ∀ t, 1 ≤ t → μ[gt t | m t] =ᵐ[μ] fun ω => g (w t ω)
  integrable_err : ∀ t, 1 ≤ t → Integrable (fun ω => ‖gt t ω - g (w t ω)‖ ^ 2) μ
  err_bound : ∀ t, 1 ≤ t →
    μ[fun ω => ‖gt t ω - g (w t ω)‖ ^ 2 | m t] ≤ᵐ[μ] fun _ => s

end VHmGA.Convergence


