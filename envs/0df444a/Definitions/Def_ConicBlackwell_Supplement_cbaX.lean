-- Prove2me | Definitions.Def_ConicBlackwell_Supplement_cbaX
-- name    : ConicBlackwell_Supplement_cbaX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:46:33.419028+00:00
-- url     : https://prove2.me/theorems/5e67fb5d-d470-58eb-b20a-d5bd31dd3c5f
-- title:
--   Decision $x_t$ of a CBA run
-- statement:
--   The decision $x_t\in\mathbb R^n$ played by CBA in round $t\ge1$: $x_1$ is the initial decision and $x_{t+1}=\mathrm{CHOOSEDECISION}_{\mathrm{CBA}^+}(\pi_{\mathcal C}(u_t))$ for $t\ge1$.
--
--   **Formalization Note** $x_t$ is the first component of `cbaState` at $t-1$; the value at the unused index $t=0$ is $x_1$ (natural-number subtraction).
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), §3.1, p.6

import Mathlib
import Definitions.Def_ConicBlackwell_Supplement_cbaState
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell.Supplement

/-- **The decision `x_t` of a CBA run** (§3.1, p.6): `x₁` is the initial decision and
`x_{t+1} = CHOOSEDECISION_{CBA}(u_t) = CHOOSEDECISION_{CBA+}(π_C(u_t))` for `t ≥ 1`.
Grand-Clément & Kroer, *Solving Optimization Problems with Blackwell Approachability*,
arXiv:2202.12277v1, §3.1, p.6.

Formalization Note: rounds are numbered from `1`; `x_t` is the first component of
`cbaState … (t - 1)`.  The value at `t = 0` (natural subtraction gives `x₁` again) is never
used. -/
noncomputable def cbaX {n : ℕ} (X : Set (E n)) (x₀ x₁ : E n) (ω : ℕ → ℝ)
    (f : ℕ → E n) (t : ℕ) : E n :=
  (cbaState X x₀ x₁ ω f (t - 1)).1

end ConicBlackwell.Supplement


