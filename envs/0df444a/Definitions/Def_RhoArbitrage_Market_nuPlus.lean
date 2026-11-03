-- Prove2me | Definitions.Def_RhoArbitrage_Market_nuPlus
-- name    : RhoArbitrage_Market_nuPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:39.793963+00:00
-- url     : https://prove2.me/theorems/53fc9669-8647-4913-9fc8-3709c1f183df
-- title:
--   The quantities $\nu^+$, $\nu_{\min}$ and $\rho_{\min}$
-- statement:
--   From the map $\nu\mapsto\rho_\nu$ define
--
--   $$
--   \nu^+:=\inf\{\nu\ge0:\rho_\nu>0\}\in[0,\infty],
--   $$
--
--   $$
--   \nu_{\min}:=\inf\{\nu\ge0:\rho_{\nu'}>\rho_\nu\text{ for all }\nu'>\nu\},\qquad \rho_{\min}:=\inf\{\rho_\nu:\nu\ge0\}.
--   $$
--
--   The number $\nu^+$ is the level of expected excess return beyond which risk stays positive, and $(\rho_{\min},\nu_{\min})$ describes the minimum-risk point of the optimal boundary.
--
--   **Formalization Note** $\nu^+$ and $\nu_{\min}$ take values in $[0,\infty]$ (`ℝ≥0∞`), so $\inf\emptyset=\infty$. $\rho_{\min}$ takes values in `EReal`.
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, p.8

import Mathlib
import Definitions.Def_RhoArbitrage_Market_rhoNu

open MeasureTheory
open scoped ENNReal

namespace RhoArbitrage

namespace Market

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`ν⁺`.** Herdegen–Khan, arXiv:2202.07610v3, p.8: `ν⁺ := inf{ν ≥ 0 : ρ_ν > 0} ∈ [0, ∞]`.

**Formalization Note.** The value lies in `ℝ≥0∞`, the image of the set under `ENNReal.ofReal`, so
`inf ∅ = ∞`. -/
noncomputable def nuPlus (P : Measure Ω) (M : Market Ω) (ρ : (Ω → ℝ) → EReal) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' {ν : ℝ | 0 ≤ ν ∧ 0 < M.rhoNu P ρ ν})

/-- **`ν_min`.** Herdegen–Khan, arXiv:2202.07610v3, p.8:
`ν_min := inf{ν ≥ 0 : ρ_{ν'} > ρ_ν for all ν' > ν} ∈ [0, ν⁺]`.

**Formalization Note.** The value lies in `ℝ≥0∞`, so `inf ∅ = ∞`. -/
noncomputable def nuMin (P : Measure Ω) (M : Market Ω) (ρ : (Ω → ℝ) → EReal) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' {ν : ℝ | 0 ≤ ν ∧ ∀ ν' : ℝ, ν < ν' → M.rhoNu P ρ ν < M.rhoNu P ρ ν'})

/-- **`ρ_min`.** Herdegen–Khan, arXiv:2202.07610v3, p.8: `ρ_min := inf{ρ_ν : ν ≥ 0} ∈ [-∞, 0]`. -/
noncomputable def rhoMin (P : Measure Ω) (M : Market Ω) (ρ : (Ω → ℝ) → EReal) : EReal :=
  sInf (M.rhoNu P ρ '' Set.Ici 0)

end Market

end RhoArbitrage


