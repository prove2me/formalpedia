-- Prove2me | Definitions.Def_LCAntiConc_IsIsotropic
-- name    : LCAntiConc_IsIsotropic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:01.748691+00:00
-- url     : https://prove2.me/theorems/46d97826-2748-4256-b96d-47cf245205e1
-- title:
--   Isotropic random vector
-- statement:
--   A random vector $X\in\mathbb R^d$ is **isotropic** if it has mean zero and covariance $I_d$:
--
--   $$\mathbb E X_i=0,\qquad \mathbb E X_iX_j=\mathbf 1\{i=j\}\qquad(1\le i,j\le d).$$
--
--   **Formalization Note** Stated for the law $\mu$ of $X$, a probability measure on `EuclideanSpace ℝ (Fin d)`; the second moments are required to be integrable, which the covariance presupposes.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), §3 Notation, p.15 (PDF p.17)

import Mathlib

namespace LCAntiConc

open MeasureTheory

/-- A random vector `X ∈ ℝ^d` (law `μ`) is isotropic: it has mean zero and covariance `I_d`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), §3 Notation, p.15 (PDF p.17).

**Formalization Note** The law is a probability measure; the second moments are integrable
(covariance `I_d` presupposes them); `𝔼 Xᵢ = 0` and `𝔼 XᵢXⱼ = 1{i = j}`. -/
def IsIsotropic {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ i j, Integrable (fun x : EuclideanSpace ℝ (Fin d) => x i * x j) μ) ∧
    (∀ i, ∫ x, x i ∂μ = 0) ∧ ∀ i j, ∫ x, x i * x j ∂μ = if i = j then 1 else 0

end LCAntiConc


