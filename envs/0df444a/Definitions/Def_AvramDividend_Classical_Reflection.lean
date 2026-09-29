-- Prove2me | Definitions.Def_AvramDividend_Classical_Reflection
-- name    : AvramDividend_Classical_Reflection
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-29T00:35:53.733653+00:00
-- url     : https://prove2.me/theorems/25037c46-ad24-4a01-a3e4-424307edd773
-- title:
--   Running supremum/infimum, reflection at the supremum, ruin time tau-hat and reflected dividend value
-- statement:
--   Section 3.3 (p. 7) of Avram, Palmowski and Pistorius introduces the running infimum and supremum of the spectrally negative Levy process X, written I_t = inf_{0<=s<=t} (X_s and 0) and S_t = sup_{0<=s<=t} (X_s or 0) with the conventions c or 0 = max(c,0) and c and 0 = min(c,0), and the processes Y+ = S - X and Y- = X - I reflected at the past supremum and past infimum. This module states those four objects together with the ruin time tau-hat = inf{t >= 0 : Y+_t < 0} and the value E[integral_0^{tau-hat} e^{-qt} dS_t] of eq. (3.12)-(3.13), written with the same paymentTimes and dividendMeasure idiom as dividendValue. It is purely definitional: the fluctuation identities of section 3.3, namely eq. (3.12), eq. (3.13) and the two-sided exit formula eq. (3.6), are separate theorems.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, section 3.3, p. 7, and eq. (3.12)-(3.13) on p. 8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

/-!
Reflection at the running supremum and infimum of a spectrally negative Lévy process, and the
reflected dividend value, of Avram, Palmowski, Pistorius, arXiv:math/0702893v1, §3.3 (p. 7).

`Definitions.Def_AvramDividend_Classical_DividendStrategy` provides the risk process
`U^π_t = x + X_t - D_t` and the ruin time `σ^π = inf{t ≥ 0 : U^π_t < 0}` for a *dividend*
strategy `D`. Proposition 1 (p. 7) is proved for the process `Y⁺ = S - X` reflected at its own
past supremum, whose ruin time `τ̂` is a different stopping time from any `σ^π`. This module
supplies exactly that vocabulary:

* `maxZero` / `minZero`: the paper's `c ∨ 0 = max{c, 0}` and `c ∧ 0 = min{c, 0}` (p. 7);
* `runningSup` / `runningInf`: the paper's `S_t = sup_{0 ≤ s ≤ t} (X_s ∨ 0)` and
  `I_t = inf_{0 ≤ s ≤ t} (X_s ∧ 0)`;
* `reflectedSup` / `reflectedInf`: the paper's `Y⁺ = S - X` and `Y⁻ = X - I`;
* `reflectedRuinTime`: the paper's `τ̂ = inf{t ≥ 0 : Y⁺_t < 0}`;
* `reflectedDividendValue`: the paper's `E[∫_0^{τ̂} e^{-qt} dS_t]`, built from the same
  `paymentTimes` / `dividendMeasure` idiom as `dividendValue` so the two are read alike.

These are definitional only. No fluctuation-theoretic property is asserted here; the identities
of §3.3 — eq. (3.12), eq. (3.13), and the two-sided exit formula (3.6) — are separate theorems.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- `c ∨ 0 = max{c, 0}`, the paper's `max` convention on p. 7. -/
def maxZero (c : ℝ) : ℝ := max c 0

/-- `c ∧ 0 = min{c, 0}`, the paper's `min` convention on p. 7. -/
def minZero (c : ℝ) : ℝ := min c 0

/-- The running supremum `S_t = sup_{0 ≤ s ≤ t} (X_s ∨ 0)` of `X` (p. 7, §3.3). The path is
truncated at `0` from above exactly as in the paper; since `X_0 = 0` this gives `S_0 = 0`. -/
noncomputable def runningSup (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ⨆ s : Icc (0 : ℝ≥0) t, maxZero (X.X s ω)

/-- The running infimum `I_t = inf_{0 ≤ s ≤ t} (X_s ∧ 0)` of `X` (p. 7, §3.3). -/
noncomputable def runningInf (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ⨅ s : Icc (0 : ℝ≥0) t, minZero (X.X s ω)

/-- `X` reflected at its past supremum, `Y⁺ = S - X` (p. 7, §3.3). This is the process whose
ruin time is the paper's `τ̂`. It is *not* of the form `x + X_t - D_t` for a dividend strategy
`D`, so `ruinTime` does not apply to it. -/
noncomputable def reflectedSup (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ω : Ω) : ℝ :=
  runningSup X t ω - X.X t ω

/-- `X` reflected at its past infimum, `Y⁻ = X - I` (p. 7, §3.3). -/
noncomputable def reflectedInf (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ω : Ω) : ℝ :=
  X.X t ω - runningInf X t ω

/-- The ruin time of the process reflected at its supremum,
`τ̂ = inf{t ≥ 0 : Y⁺_t < 0}`, in `[0, ∞]` (`inf ∅ = ∞`). This is the `τ̂^a` of
eq. (3.12) and eq. (3.13), started from `Y⁺_0 = a - x`. -/
noncomputable def reflectedRuinTime (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : reflectedSup X t ω < 0), (t : ℝ≥0∞)

/-- The value carried by the running supremum until the ruin time of the reflected process,
`E[∫_0^{τ̂} e^{-qt} dS_t]`, in `[0, ∞]` (p. 8, eq. (3.12) and (3.13)). Built with the same
`paymentTimes` / `dividendMeasure` idiom as `dividendValue`, so the two values are read alike. -/
noncomputable def reflectedDividendValue (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) :
    ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ t in paymentTimes (reflectedRuinTime X ω),
    ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure (runningSup X) ω) ∂P

end AvramDividend.Classical


