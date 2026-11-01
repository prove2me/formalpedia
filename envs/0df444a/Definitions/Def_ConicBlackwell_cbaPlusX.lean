-- Prove2me | Definitions.Def_ConicBlackwell_cbaPlusX
-- name    : ConicBlackwell_cbaPlusX
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:44:54.45885+00:00
-- url     : https://prove2.me/theorems/e7efa322-1e64-4ce7-b87c-24f442ebf56a
-- title:
--   Decision $x_t$ of a CBA$^+$ run
-- statement:
--   The decision $x_t\in\mathbb R^n$ played by CBA$^+$ (Algorithm 1) in round $t\ge1$: $x_1$ is the initial decision and $x_{t+1}=\mathrm{CHOOSEDECISION}_{\mathrm{CBA}^+}(u_t)$ for $t\ge1$.
--
--   **Formalization Note** $x_t$ is the first component of `cbaPlusState` at $t-1$; the value at the unused index $t=0$ is $x_1$ (natural-number subtraction).
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), Algorithm 1, p.6

import Mathlib
import Definitions.Def_ConicBlackwell_cbaPlusState
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **The decision `x_t` of a CBA+ run** (Algorithm 1, p.6): `x₁` is the initial decision and
`x_{t+1} = CHOOSEDECISION_{CBA+}(u_t)` for `t ≥ 1`.
Grand-Clément & Kroer, *Solving Optimization Problems with Blackwell Approachability*, arXiv:2202.12277v1, Algorithm 1, p.6.

Formalization Note: rounds are numbered from `1`; `x_t` is the first component of
`cbaPlusState … (t - 1)`.  The value at `t = 0` (natural subtraction gives `x₁` again) is never
used. -/
noncomputable def cbaPlusX {n : ℕ} (X : Set (E n)) (x₀ x₁ : E n) (ω : ℕ → ℝ)
    (f : ℕ → E n) (t : ℕ) : E n :=
  (cbaPlusState X x₀ x₁ ω f (t - 1)).1

end ConicBlackwell


