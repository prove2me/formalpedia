-- Prove2me | Definitions.Def_QuantumNoise_chiTilde
-- name    : QuantumNoise_chiTilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:39.12053+00:00
-- url     : https://prove2.me/theorems/7f7a0af7-95f1-4960-a143-80ad7fe4e33e
-- title:
--   Gain asymmetry $\tilde\chi_{IF}[\omega]=\chi_{IF}[\omega]-\chi_{FI}[\omega]^\ast$
-- statement:
--   The asymmetry between the gain and the reverse gain of a detector is
--   $$
--   \tilde\chi_{IF}[\omega]\equiv\chi_{IF}[\omega]-\big(\chi_{FI}[\omega]\big)^\ast .
--   $$
--   It is defined here for any pair $a,b$ as $\tilde\chi_{ab}=\chi_{ab}-\chi_{ba}^\ast$. It vanishes for a detector with the Onsager symmetry $\chi_{IF}=\chi_{FI}^\ast$, and it sets the size of the quantum term of the noise inequality (4.11).
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. IV.A.3, Eq. (4.10), p.22

import Mathlib
import Definitions.Def_QuantumNoise_chi

namespace QuantumNoise

/-- The **gain asymmetry** `χ̃_{ab}[ω] = χ_{ab}[ω] − (χ_{ba}[ω])*`; for `a = Î`, `b = F̂` it is
`χ̃IF[ω] ≡ χIF[ω] − (χFI[ω])*`, the asymmetry between gain and reverse gain.

Clerk et al., arXiv:0810.4729v2, Sec. IV.A.3, Eq. (4.10), p.22 (printed p.22, PDF p.22). -/
noncomputable def chiTilde {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
    (P : StationaryDynamics 𝒜) (ħ : ℝ) (a b : 𝒜) (ω : ℝ) : ℂ :=
  chi P ħ a b ω - starRingEnd ℂ (chi P ħ b a ω)

end QuantumNoise


