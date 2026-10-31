-- Prove2me | Definitions.Def_PushInfoShare_profitGap
-- name    : PushInfoShare_profitGap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:33.159653+00:00
-- url     : https://prove2.me/theorems/3d603461-5c56-4192-9a1f-ce7acce5cb0d
-- title:
--   Profit difference between two sharing cases
-- statement:
--   For a family of profiles, the difference $\Pi_i^{\delta}(\phi)-\Pi_i^{\delta'}(\phi)$, as a function of $\phi$. The three gaps of Proposition 5 are $\Pi_i^{P_i}-\Pi_i^N$, $\Pi_i^F-\Pi_i^{P_{3-i}}$ and $\Pi_i^F-\Pi_i^N$.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), §5.1, p.17

import Mathlib
import Definitions.Def_PushInfoShare_profit

open MeasureTheory

namespace PushInfoShare

/-- The profit difference `Πᵢ^δ − Πᵢ^δ'` of manufacturer `i` between the sharing cases `δ` and `δ'`
of the family `str`, as a function of `φ`; Jain, SSRN:3388957 (PDF of 2021-04-25), §5.1, p.17. -/
noncomputable def profitGap {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Fin 2 → Ω → ℝ)
    (str : ℝ → (Fin 2 → Bool) → Profile) (δ δ' : Fin 2 → Bool) (i : Fin 2) (φ : ℝ) : ℝ :=
  profit μ Y (str φ δ) i - profit μ Y (str φ δ') i

end PushInfoShare


