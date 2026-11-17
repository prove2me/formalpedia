-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_infProphet
-- name    : EffHorizonProphet_Supplement_infProphet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:57:39.858202+00:00
-- url     : https://prove2.me/theorems/e340751a-f6ca-41f9-9bdd-0846f76d5118
-- title:
--   Infinite-horizon prophet benchmark $\mathbb E_D[\sup_i X_i]$
-- statement:
--   The **infinite-horizon prophet benchmark** is
--   $$\mathbb E_D\Big[\sup_{i\ge1}X_i\Big],\qquad X_i=\tilde\gamma^{i-1}Y_i.$$
--   For an admissible $D$ and $0<\tilde\gamma<1$ it is positive and at most $\mathbb E_D[Y]/(1-\tilde\gamma)$.
--
--   **Formalization Note** The supremum and the expectation are taken in $[0,\infty]$ (a lower Lebesgue integral), so no junk value can occur.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 7, p.11

import Mathlib
import Definitions.Def_EffHorizonProphet_Supplement_infSampleLaw
import Definitions.Def_EffHorizonProphet_Supplement_infReward

open MeasureTheory
open scoped ENNReal

namespace EffHorizonProphet.Supplement

/-- The **infinite-horizon prophet benchmark** `E_D[sup_{i ≥ 1} X_i]` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 7, p.11).

**Formalization Note** The supremum and the expectation are taken in `ℝ≥0∞` (a lower Lebesgue
integral of `⨆ i, ofReal (X_i)`), so an unbounded supremum is never replaced by a junk value. For an
admissible `D` the rewards are almost surely nonnegative and the value is finite, at most
`E_D[Y]/(1 − γ̃)` (p.11). -/
noncomputable def infProphet (γ : ℝ) (D : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ⨆ i, ENNReal.ofReal (infReward γ i ω) ∂infSampleLaw D

end EffHorizonProphet.Supplement


