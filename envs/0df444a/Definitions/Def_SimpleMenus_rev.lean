-- Prove2me | Definitions.Def_SimpleMenus_rev
-- name    : SimpleMenus_rev
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:47.182205+00:00
-- url     : https://prove2.me/theorems/b7952e60-7ffd-4e66-b0f6-c8a470e2abd1
-- title:
--   Expected revenue $\mathrm{Rev}(\pi,F)$
-- statement:
--   For the $n$-level mechanism $\pi$ with price levels $v$ and probabilities $x$, and a valuation distribution $F$ on $[0,\bar v]$, the expected revenue is
--
--   $$\mathrm{Rev}(\pi,F)=\int_0^{\bar v} t(w)\,dF(w),$$
--
--   where $t$ is the expected payment. It is the numerator of the competitive ratio.
--
--   **Formalization Note** $F$ is a measure on $\mathbb R$; for the laws used it is a probability measure carried by $[0,\bar v]$, and $t$ is a bounded Borel step function, so the integral is the true one.
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, §2, p.9

import Mathlib
import Definitions.Def_SimpleMenus_pay

open MeasureTheory Set

namespace SimpleMenus

/-- The seller's expected revenue `Rev(π, F) = ∫_0^v̄ t(w) dF(w)` of the `n`-level mechanism with
price levels `v` and probabilities `x` against the valuation law `F` (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, §2, p.9).

Formalization Note: `F` is a measure on `ℝ`; for the laws of the ambiguity set it is a
probability measure carried by `[0, v̄]`, so the integral over `ℝ` is the integral over `[0, v̄]`.
`pay v x` is a bounded Borel step function, hence integrable against every finite measure, so
the Bochner integral never takes its junk value on the laws used. -/
noncomputable def rev {n : ℕ} (v x : Fin n → ℝ) (F : Measure ℝ) : ℝ :=
  ∫ w, pay v x w ∂F

end SimpleMenus


