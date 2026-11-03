-- Prove2me | Definitions.Def_QuantumNoise_powerGain
-- name    : QuantumNoise_powerGain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:27:02.367208+00:00
-- url     : https://prove2.me/theorems/40804308-10ad-47aa-8b44-106b247cac17
-- title:
--   Detector power gain $G_P[\omega]$ (5.52)
-- statement:
--   The **power gain** of a detector with no reverse gain is
--   $$
--   G_P[\omega]=\frac{|\chi_{IF}[\omega]|^2}{4\,\operatorname{Im}\chi_{FF}[\omega]\cdot\operatorname{Im}\chi_{II}[\omega]} ,
--   $$
--   the maximal ratio of the power delivered to a load oscillator at the output to the power drawn from the signal oscillator at the input (5.47)–(5.52).
--
--   **Formalization Note** The ratio is a power gain only when $\operatorname{Im}\chi_{FF}[\omega]\cdot\operatorname{Im}\chi_{II}[\omega]>0$ (both back-action dampings positive); statements using it assume this. Lean's $x/0=0$ applies otherwise.
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. V.E.3, Eq. (5.52), p.35

import Mathlib
import Definitions.Def_QuantumNoise_Detector
import Definitions.Def_QuantumNoise_chi

namespace QuantumNoise

/-- The **detector power gain** (no reverse gain)
`G_P[ω] = |χIF[ω]|² / (4 Im χFF[ω] · Im χII[ω])`.

Clerk et al., arXiv:0810.4729v2, Sec. V.E.3, Eq. (5.52), last line, p.35 (printed p.35,
PDF p.35), with `χII` the Kubo gain (5.49) and `χFF` the corresponding input-port gain.

**Formalization Note** The quantity is a power gain only when `Im χFF[ω] · Im χII[ω] > 0` (both
ports passive); statements using it assume this. Lean's `x / 0 = 0` gives `0` otherwise. -/
noncomputable def powerGain {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
    (P : StationaryDynamics 𝒜) (D : Detector P) (ħ : ℝ) (ω : ℝ) : ℝ :=
  ‖chi P ħ D.I D.F ω‖ ^ 2 / (4 * (chi P ħ D.F D.F ω).im * (chi P ħ D.I D.I ω).im)

end QuantumNoise


