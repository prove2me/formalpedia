-- Prove2me | Definitions.Def_RBMSensitivity_Data
-- name    : RBMSensitivity_Data
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:16.200747+00:00
-- url     : https://prove2.me/theorems/63d591d2-9e3c-4ce1-a612-fc12807562e3
-- title:
--   The parametrized reflection data $\{(d_i(\cdot),n_i)\}$, $a(\cdot)$, $b(\cdot)$
-- statement:
--   Let $U\subset\mathbb R$ be an open parameter set. For each $i\in\mathcal I$ fix a continuously differentiable $d_i:U\to\mathbb R^J$ with $\langle d_i(\alpha),n_i\rangle=1$ for all $\alpha\in U$; $d_i(\alpha)$ is the constant direction of reflection along $F_i$. Fix continuously differentiable functions
--   $$a:U\to\mathbb M^{J\times J},\qquad b:U\to\mathbb R^J,$$
--   where $\mathbb M^{J\times J}$ is the set of positive definite symmetric matrices; $a(\alpha)$ and $b(\alpha)$ are the covariance and the drift.
--
--   All three coefficients vary with one real parameter, and the mission studies the sensitivity to that parameter.
--
--   **Formalization Note** The functions are total on $\mathbb R$ and constrained on $U$ only. $a$ is continuously differentiable entrywise.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §2.1, p.5

import Mathlib
import Definitions.Def_RBMSensitivity_SimpleCone
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The data of §2.1: arXiv:1907.00472v2, p.5.

An open parameter set `U ⊂ ℝ`, C¹ directions of reflection `d_i : U → ℝ^J` with `⟨d_i(α), n_i⟩ = 1`,
a C¹ covariance `a : U → M^{J×J}` with values in the positive definite symmetric matrices, and a C¹
drift `b : U → ℝ^J`.

**Formalization Note.** Functions are total on `ℝ`, and the conditions are imposed on `U` only.
`ContDiffOn` on the open set `U` is the paper's continuous differentiability. Matrices carry no global
norm, so `a` is C¹ entrywise, which is the same condition. The square root `σ` is not data: see
`Data.sigma`. -/
structure Data (J : ℕ) extends SimpleCone J where
  /-- The open parameter set. -/
  U : Set ℝ
  U_open : IsOpen U
  /-- The directions of reflection `d_i(α)`. -/
  d : Fin J → ℝ → E J
  d_contDiff : ∀ i, ContDiffOn ℝ 1 (d i) U
  d_normal : ∀ i, ∀ α ∈ U, ⟪d i α, n i⟫ = 1
  /-- The covariance `a(α)`. -/
  a : ℝ → Matrix (Fin J) (Fin J) ℝ
  a_contDiff : ∀ i j, ContDiffOn ℝ 1 (fun α => a α i j) U
  a_posDef : ∀ α ∈ U, (a α).PosDef
  /-- The drift `b(α)`. -/
  b : ℝ → E J
  b_contDiff : ContDiffOn ℝ 1 b U

end RBMSensitivity


