-- Prove2me | Definitions.Def_QuantumNoise_IdealNoise
-- name    : QuantumNoise_IdealNoise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:44.887685+00:00
-- url     : https://prove2.me/theorems/09177edf-d4aa-4e6c-affc-0568b5747bb9
-- title:
--   Ideal (quantum-limited) noise condition (4.17)
-- statement:
--   A detector with no reverse gain has **ideal noise** at frequency $\omega$ if the quantum noise inequality holds with equality there:
--   $$
--   \bar S_{II}[\omega]\bar S_{FF}[\omega]-\big|\bar S_{IF}[\omega]\big|^2=\Big|\frac{\hbar\chi_{IF}[\omega]}{2}\Big|^2\Big(1+\Delta\Big[\frac{\bar S_{IF}[\omega]}{\hbar\chi_{IF}[\omega]/2}\Big]\Big).
--   $$
--   Such a "quantum-ideal" detector has the minimal amount of noise at $\omega$ allowed by (4.11); it is condition 1 for reaching the quantum limit on the added noise (p.38).
--
--   **Formalization Note** $\bar S_{II}$, $\bar S_{FF}$ enter through their real parts. When $\chi_{IF}[\omega]=0$ Lean's $x/0=0$ makes the right side $0$; statements that use this condition assume $\chi_{IF}[\omega]\neq0$.
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. IV.A.3, Eq. (4.17), p.23

import Mathlib
import Definitions.Def_QuantumNoise_Detector
import Definitions.Def_QuantumNoise_Sbar
import Definitions.Def_QuantumNoise_chi
import Definitions.Def_QuantumNoise_Delta

namespace QuantumNoise

/-- The **ideal ("quantum-limited") noise condition** of a detector with no reverse gain at
frequency `ω`:
`S̄II[ω] S̄FF[ω] − |S̄IF[ω]|² = |ħ χIF[ω]/2|² (1 + Δ[S̄IF[ω] / (ħ χIF[ω]/2)])`,
i.e. the quantum noise inequality (4.11) holds with equality.

Clerk et al., arXiv:0810.4729v2, Sec. IV.A.3, Eq. (4.17), p.23 (printed p.23, PDF p.23).

**Formalization Note** `S̄II`, `S̄FF` are real and enter through `.re`. Lean's `x / 0 = 0` makes
the right side `0` when `χIF[ω] = 0`; every statement using this condition assumes
`χIF[ω] ≠ 0`. -/
def IdealNoise {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
    (P : StationaryDynamics 𝒜) (D : Detector P) (ħ : ℝ) (ω : ℝ) : Prop :=
  (Sbar P D.I D.I ω).re * (Sbar P D.F D.F ω).re - ‖Sbar P D.I D.F ω‖ ^ 2 =
    ‖(ħ : ℂ) * chi P ħ D.I D.F ω / 2‖ ^ 2 *
      (1 + Delta (Sbar P D.I D.F ω / ((ħ : ℂ) * chi P ħ D.I D.F ω / 2)))

end QuantumNoise


