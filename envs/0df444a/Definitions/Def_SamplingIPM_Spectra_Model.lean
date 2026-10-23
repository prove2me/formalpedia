-- Prove2me | Definitions.Def_SamplingIPM_Spectra_Model
-- name    : SamplingIPM_Spectra_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:39.563989+00:00
-- url     : https://prove2.me/theorems/634af5ce-23ea-47b3-89f6-bd908b41f7b5
-- title:
--   §2.1, §3.1 — local norm ‖v‖_θ of the Boltzmann covariance, the geometric sequence θ_k and the step count m
-- statement:
--   Let $K\subseteq\mathbb R^n$ be a convex body with the Euclidean inner product $\langle\cdot,\cdot\rangle$. For $\theta\in\mathbb R^n$ let $\Sigma(\theta)$ be the covariance of the Boltzmann distribution over $K$ with parameter $\theta$, i.e. of the law with density proportional to $e^{\langle\theta,x\rangle}$ on $K$. By display (3) of the paper, $\Sigma(\theta)$ is also the Hessian $H(\theta)$ of the log partition function $f(\theta)=\ln\int_K e^{\langle\theta,x\rangle}\,dx$.
--
--   This file introduces three objects used in §3.1.
--
--   1. The **local norm** of $v\in\mathbb R^n$ at $\theta$,
--   $$\|v\|_\theta=\sqrt{\langle v,\Sigma(\theta)v\rangle}.$$
--   2. For a complexity parameter $\vartheta$ and a starting point $\theta$, the **geometric sequence**
--   $$\theta_k=\Big(1-\frac{1}{2\sqrt\vartheta+1}\Big)^k\theta,\qquad k=0,1,2,\dots,$$
--   which is the closed form of the paper's recursion $\theta_0=\theta$, $\theta_k=(1-\frac{1}{2\sqrt\vartheta+1})\theta_{k-1}$.
--   3. For a radius $R$, the **step count**
--   $$m=\left\lceil\frac{\log_2\big(\frac{1}{4R\|\theta\|}\big)}{\log_2\big(1-\frac{1}{2\sqrt\vartheta+1}\big)}\right\rceil .$$
--
--   The local norm is the quantity whose lower bounds give Theorem 3.1; the sequence $\theta_k$ and the count $m$ are the paper's device for moving from a large parameter $\theta$ back into the ball $\|\theta\|\le 1/(4R)$.
--
--   **Formalization Note** $\Sigma(\theta)$ is the published bilinear form `covForm K θ` of the Boltzmann law `expFamily K θ`. The ceiling is the natural-number ceiling `⌈·⌉₊`; the ratio inside it is positive whenever $4R\|\theta\|>1$ and $\vartheta>0$, the only regime in which $m$ is used. At $\vartheta\le 0$ or $4R\|\theta\|\le 1$ the value of $m$ is a Lean default and carries no meaning.
-- source:
--   Badenbroek & de Klerk, Complexity Analysis of a Sampling-Based Interior Point Method for Convex Optimization, arXiv:1811.07677v1, pp. 2, 3, 12, §2.1 (local norm, display (3)), proof of Theorem 3.1 (θ_k and m)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_ExpFamily

open scoped RealInnerProductSpace
open EntropicBarrier.Universal

namespace SamplingIPM.Spectra

/-- The local norm `‖v‖_θ = √⟨v, Σ(θ) v⟩` (§2.1, p. 2), where `Σ(θ) = H(θ)` is the covariance of the
Boltzmann distribution over `K` with parameter `θ` (display (3), p. 3). -/
noncomputable def localNorm {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (covForm K θ v v)

/-- The geometric sequence `θ_k = (1 - 1/(2√ϑ+1))^k θ` of the proof of Theorem 3.1 (p. 12):
`θ_0 = θ` and `θ_k = (1 - 1/(2√ϑ+1)) θ_{k-1}`, unrolled to closed form. -/
noncomputable def thetaSeq {n : ℕ} (ϑ : ℝ) (θ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  (1 - 1 / (2 * Real.sqrt ϑ + 1)) ^ k • θ

/-- The step count `m = ⌈log₂(1/(4R‖θ‖)) / log₂(1 - 1/(2√ϑ+1))⌉` of the proof of Theorem 3.1
(p. 12). -/
noncomputable def mSteps {n : ℕ} (R ϑ : ℝ) (θ : EuclideanSpace ℝ (Fin n)) : ℕ :=
  ⌈Real.logb 2 (1 / (4 * R * ‖θ‖)) / Real.logb 2 (1 - 1 / (2 * Real.sqrt ϑ + 1))⌉₊

end SamplingIPM.Spectra


