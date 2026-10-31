-- Prove2me | Definitions.Def_ShapleyNV_dualObj
-- name    : ShapleyNV_dualObj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:04.865555+00:00
-- url     : https://prove2.me/theorems/aabad24e-8de2-4716-9c83-5ead1a50a587
-- title:
--   Dual objective $\lambda\rho + \mathbb E_{\widehat{\mathbb P}}[\sup_\xi\{\ell(\xi)-\lambda c(\xi,\hat\xi)\}]$
-- statement:
--   For a multiplier $\lambda$, the dual objective of the worst-case problem with ground cost $c$, nominal $\widehat{\mathbb P}$, radius $\rho$ and loss $\ell$ is
--
--   $$
--   \lambda\rho + \mathbb E_{\hat\xi \sim \widehat{\mathbb P}}\Big[ \sup_{\xi} \big\{ \ell(\xi) - \lambda\, c(\xi, \hat\xi) \big\} \Big] \in [0, \infty].
--   $$
--
--   **Formalization Note** Both terms are taken in $[0, \infty]$ (nonnegative parts). When $\ell \ge 0$, $\lambda, \rho \ge 0$ and $c(\hat\xi, \hat\xi) = 0$, as everywhere in this mission, the inner supremum is at least $\ell(\hat\xi) \ge 0$ (choose $\xi = \hat\xi$), so nothing is truncated.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Lemma EC.1, objective of v_D^f, p.ec1 (PDF 22); objectives of (D) and (D̂), p.7

import Mathlib

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Dual objective of a Wasserstein worst case** at a multiplier `λ`:
`λρ + E_{ξ̂ ∼ P̂}[ sup_ξ { ℓ(ξ) − λ c(ξ, ξ̂) } ]`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Lemma EC.1, the objective of `v_D^f`, p.ec1 (PDF 22); the objectives of (D) and (D̂), p.7.

**Formalization Note.** Values are in `ℝ≥0∞`. The inner supremum ranges over all `ξ`. Whenever
`ℓ ≥ 0` and `c(ξ̂, ξ̂) = 0` (the case in this mission), the inner supremum is at least
`ℓ(ξ̂) ≥ 0` (take `ξ = ξ̂`), so truncating at 0 with `ENNReal.ofReal` changes nothing; for
`λ ≥ 0`, `ρ ≥ 0` neither does `ENNReal.ofReal (λρ)`. -/
noncomputable def dualObj {α : Type*} [MeasurableSpace α] (c : α → α → ℝ) (Phat : Measure α) (ρ : ℝ)
    (ℓ : α → ℝ) (lam : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (lam * ρ) + ∫⁻ ξh, (⨆ ξ, ENNReal.ofReal (ℓ ξ - lam * c ξ ξh)) ∂Phat

end ShapleyNV


