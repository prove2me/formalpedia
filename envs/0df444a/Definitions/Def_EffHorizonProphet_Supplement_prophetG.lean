-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_prophetG
-- name    : EffHorizonProphet_Supplement_prophetG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:02:55.280372+00:00
-- url     : https://prove2.me/theorems/649231b4-2c14-42f0-830c-9bdd74b474be
-- title:
--   Prophet benchmark of the general model
-- statement:
--   The **prophet benchmark** of the general model is $\mathbb E_D[\max_{i\in[n]}X_i]$ with $X_i=\Gamma_{s-1}Y_i$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), A.6–A.8, pp.35–40

import Mathlib
import Definitions.Def_EffHorizonProphet_sampleLaw
import Definitions.Def_EffHorizonProphet_Supplement_rewardG

open MeasureTheory

namespace EffHorizonProphet.Supplement

/-- The **prophet benchmark of the general model** `E_D[max_{i ∈ [n]} X_i]` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), A.6–A.8,
pp.35–40).

**Formalization Note** `⨆` over the finite type `Fin n` is the maximum (`0` for `n = 0`). -/
noncomputable def prophetG {S : ℕ} (g : ℕ → ℝ) (L : Fin S → ℕ) (D : Measure ℝ) : ℝ :=
  ∫ ω, ⨆ i, rewardG g L i ω ∂sampleLaw D L

end EffHorizonProphet.Supplement


