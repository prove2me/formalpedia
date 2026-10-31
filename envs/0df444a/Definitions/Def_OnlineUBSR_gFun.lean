-- Prove2me | Definitions.Def_OnlineUBSR_gFun
-- name    : OnlineUBSR_gFun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:12.954996+00:00
-- url     : https://prove2.me/theorems/d9b3b64d-6cdd-4ba3-ae1a-0b3dc49b748d
-- title:
--   The root function $g(t)=\mathbb E[\ell(-X-t)]-\lambda$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $X$ a random variable (a financial position), $\ell:\mathbb R\to\mathbb R$ a loss function and $\lambda\in\mathbb R$ a risk level. The function $g:\mathbb R\to\mathbb R$ is
--
--   $$
--   g(t)=\mathbb E\big[\ell(-X-t)\big]-\lambda .
--   $$
--
--   Shortfall risk $SR_\lambda(X)$ is the root of $g$ (under Assumption 1), so estimating it is a stochastic root-finding problem; $g$ cannot be evaluated directly, only through samples of $X$.
--
--   **Formalization Note** The expectation is the Bochner integral, which equals the true expectation whenever $\omega\mapsto\ell(-X(\omega)-t)$ is integrable; in every theorem of the mission $X$ is bounded a.s. and $\ell$ is convex, hence continuous, so this holds. $\lambda$ is written `lam`.
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, Online Estimation and Optimization of Utility-Based Shortfall Risk, arXiv:2111.08805v3, §3, eq. (3), p.4

import Mathlib

open MeasureTheory

namespace OnlineUBSR

/-- **The root function `g` of shortfall risk.**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, §3, (3), p.4:
"g(t) := E[ℓ(−X − t)] − λ."

`gFun μ ℓ lam X t = ∫ ℓ(−X(ω) − t) dμ(ω) − lam`, where `μ` is the probability measure of the
underlying space, `ℓ` the loss, `lam` the risk level `λ` and `X` the position.

**Formalization Note.** The expectation is the Bochner integral. It is the true expectation
whenever `ω ↦ ℓ(−X(ω) − t)` is integrable; this holds in every theorem of the mission, where
`X` is measurable and essentially bounded and `ℓ` is convex (hence continuous) on `ℝ`. `λ` is
written `lam` because `λ` is a Lean keyword. -/
noncomputable def gFun {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ℓ : ℝ → ℝ) (lam : ℝ)
    (X : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, ℓ (-X ω - t) ∂μ - lam

end OnlineUBSR


