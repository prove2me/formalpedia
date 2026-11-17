-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_infStopReward
-- name    : EffHorizonProphet_Supplement_infStopReward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:58:29.162037+00:00
-- url     : https://prove2.me/theorems/2425a25f-22a3-43d4-901e-9f9a018a12be
-- title:
--   Expected reward $\mathbb E_D[X_\tau]$ of an infinite-horizon stopping rule
-- statement:
--   For an infinite-horizon stopping rule $\tau$, the **expected reward** is $\mathbb E_D[X_\tau]$ with $X_\infty:=0$.
--
--   **Formalization Note** The stopped reward is $\sum_i \mathbf 1\{\tau=i\}X_i$, computed in $[0,\infty]$ and integrated as a lower Lebesgue integral.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 7, p.11

import Mathlib
import Definitions.Def_EffHorizonProphet_Supplement_infSampleLaw
import Definitions.Def_EffHorizonProphet_Supplement_infReward

open MeasureTheory
open scoped ENNReal

namespace EffHorizonProphet.Supplement

open scoped Classical in
/-- The **expected reward `E_D[X_τ]` of an infinite-horizon stopping rule** `τ` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 7,
p.11), with `X_∞ := 0`.

**Formalization Note** The stopped reward is `∑' i, 1{τ = i} · ofReal (X_i)` (at most one nonzero
term; `0` on `{τ = ⊤}`), and the expectation is a lower Lebesgue integral in `ℝ≥0∞`. For an
admissible law the rewards are almost surely nonnegative, so `ofReal` loses nothing. -/
noncomputable def infStopReward (γ : ℝ) (D : Measure ℝ)
    (τ : (ℕ → ℝ × unitInterval) → ℕ∞) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' i : ℕ, (if τ ω = (i : ℕ∞) then ENNReal.ofReal (infReward γ i ω) else 0)
    ∂infSampleLaw D

end EffHorizonProphet.Supplement


