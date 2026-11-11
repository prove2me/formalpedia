-- Prove2me | Definitions.Def_PreservePast_Task
-- name    : PreservePast_Task
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:39:39.94307+00:00
-- url     : https://prove2.me/theorems/7083c683-a1df-4fc3-9129-5e14d000ea40
-- title:
--   Old regression task, its covariance $C$, gradient $G$ and loss increment $f(H)$
-- statement:
--   Fix a public checkpoint $W_0\in\mathbb R^{m\times n}$. An **old task** is a probability distribution of an input–output pair $(X,Y)\in\mathbb R^n\times\mathbb R^m$ satisfying the energy bounds
--   $$
--   \mathbb E\|X\|^2\le 2,\qquad \mathbb E\|W_0X-Y\|^2\le 1 .
--   $$
--   Its **covariance** and **gradient** are
--   $$
--   C=\mathbb E[XX^\top]\in\mathbb R^{n\times n},\qquad G=\mathbb E[(W_0X-Y)X^\top]\in\mathbb R^{m\times n},
--   $$
--   and the **loss increment** of an update $H\in\mathbb R^{m\times n}$, which changes the checkpoint to $W_0+H$, is
--   $$
--   f(H)=\langle G,H\rangle+\tfrac12\operatorname{tr}(HCH^\top),\qquad \langle A,B\rangle=\sum_{j,i}A_{ji}B_{ji}.
--   $$
--   This is the exact increase of the squared loss $\tfrac12\mathbb E\|(W_0+H)X-Y\|^2$ of the task. A history is a tuple of $K$ tasks.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ` with its Borel σ-algebra; squared Euclidean norms are sums of squares. The two energy bounds are lower Lebesgue integrals, so they also state that both second moments are finite; $C$ and $G$ are then Bochner integrals of integrable functions (no junk value). The trace inner product is the published `WainwrightHDS.NucNorm.traceInner`.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §3.1, p.6 (PDF p.8), (11)–(12)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_traceInner

open MeasureTheory Matrix

namespace PreservePast

/-- **An old regression task** for the public checkpoint `W₀ ∈ ℝ^{m×n}`.
P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §3.1, p.6 (PDF p.8), (11): "Each of the K old tasks is a
distribution of (X, Y) satisfying 𝔼‖X‖² ≤ 2, 𝔼‖W₀X − Y‖² ≤ 1."

A task is a Borel probability law of the input–output pair `(X, Y) ∈ ℝⁿ × ℝᵐ` with input energy
`𝔼‖X‖² ≤ 2` and residual energy `𝔼‖W₀X − Y‖² ≤ 1` (Euclidean norms).

**Formalization Note.** `ℝⁿ` is `Fin n → ℝ` with its Borel (product) σ-algebra and squared
Euclidean norms are written as sums of squares. The two energy bounds are lower Lebesgue integrals
in `ℝ≥0∞`, so they also assert finiteness of both second moments; this makes the covariance and
gradient below genuine Bochner integrals of integrable functions. -/
structure Task {m n : ℕ} (W₀ : Matrix (Fin m) (Fin n) ℝ) where
  /-- The law of `(X, Y)`. -/
  law : Measure ((Fin n → ℝ) × (Fin m → ℝ))
  /-- It is a probability law. -/
  isProb : IsProbabilityMeasure law
  /-- `𝔼‖X‖² ≤ 2`. -/
  energy_input : ∫⁻ z, ENNReal.ofReal (∑ i, z.1 i ^ 2) ∂law ≤ 2
  /-- `𝔼‖W₀X − Y‖² ≤ 1`. -/
  energy_residual : ∫⁻ z, ENNReal.ofReal (∑ j, (W₀ *ᵥ z.1 - z.2) j ^ 2) ∂law ≤ 1

/-- The covariance `C = 𝔼[XXᵀ]` of a task (§3.1, p.6). -/
noncomputable def Task.cov {m n : ℕ} {W₀ : Matrix (Fin m) (Fin n) ℝ} (T : Task W₀) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => ∫ z, z.1 i * z.1 k ∂T.law

/-- The gradient `G = 𝔼[(W₀X − Y)Xᵀ]` of a task (§3.1, p.6). -/
noncomputable def Task.grad {m n : ℕ} {W₀ : Matrix (Fin m) (Fin n) ℝ} (T : Task W₀) :
    Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun j i => ∫ z, (W₀ *ᵥ z.1 - z.2) j * z.1 i ∂T.law

/-- The **loss increment** `f(H) = ⟨G, H⟩ + ½ tr(H C Hᵀ)` of the update `H` (which changes the
checkpoint to `W₀ + H`) on the task, (12), p.6. `⟨A, B⟩ = Σ_{j,i} A_{ji} B_{ji}` is the trace
inner product. -/
noncomputable def Task.lossInc {m n : ℕ} {W₀ : Matrix (Fin m) (Fin n) ℝ} (T : Task W₀)
    (H : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  WainwrightHDS.NucNorm.traceInner T.grad H + (1 / 2) * Matrix.trace (H * T.cov * H.transpose)

end PreservePast


