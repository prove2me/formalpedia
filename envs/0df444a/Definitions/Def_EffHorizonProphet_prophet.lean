-- Prove2me | Definitions.Def_EffHorizonProphet_prophet
-- name    : EffHorizonProphet_prophet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:42:56.016468+00:00
-- url     : https://prove2.me/theorems/ad55a66a-50aa-479e-a00d-e1c714bdcc2a
-- title:
--   The prophet benchmark $\mathbb E_D[\max_i X_i]$
-- statement:
--   The **prophet benchmark** is the expected maximum of the observed rewards, $\mathbb E_D[\max_{i\in[n]}X_i]$. For an empty horizon the value is $0$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 3, p.4

import Mathlib
import Definitions.Def_EffHorizonProphet_reward
import Definitions.Def_EffHorizonProphet_sampleLaw

open MeasureTheory

namespace EffHorizonProphet

/-- The **prophet benchmark** `E_D[max_{i ∈ [n]} X_i]` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 3, p.4).

**Formalization Note** `⨆` over the finite type `Fin n` is the maximum; for `n = 0` it is `0`. -/
noncomputable def prophet {S : ℕ} (γ : ℝ) (L : Fin S → ℕ) (D : Measure ℝ) : ℝ :=
  ∫ ω, ⨆ i, reward γ L i ω ∂sampleLaw D L

end EffHorizonProphet


