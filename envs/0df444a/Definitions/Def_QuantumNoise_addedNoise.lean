-- Prove2me | Definitions.Def_QuantumNoise_addedNoise
-- name    : QuantumNoise_addedNoise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:27:10.582336+00:00
-- url     : https://prove2.me/theorems/7f495935-c088-493c-85b5-bec66aa1bb8b
-- title:
--   Added position noise $\bar S_{xx,\rm add}[\omega]$ (5.61)
-- statement:
--   For a detector, a coupling strength $A\in\mathbb R$, an oscillator susceptibility $\chi=\chi_{xx}[\omega]\in\mathbb C$ and a sign $\sigma\in\{+1,-1\}$, the **added position noise** at frequency $\omega$ is
--   $$
--   \bar S_{xx,\rm add}[\omega]=\frac{\bar S_{II}}{|\chi_{IF}|^2A^2}+A^2|\chi|^2\bar S_{FF}+\sigma\,\frac{2\operatorname{Re}\big[\chi_{IF}^\ast\,\chi^\ast\,\bar S_{IF}\big]}{|\chi_{IF}|^2},
--   $$
--   with all spectra and gains at $\omega$. The first term is the measurement imprecision noise, the second the back-action contribution, the third their correlation. The printed formula is $\sigma=+1$.
--
--   **Formalization Note** The paper reaches (5.61) from classical Langevin equations, neglecting non-Gaussian corrections; here (5.61) is the definition. $\chi$ is any complex number. The sign $\sigma$ of the cross term is a parameter because the paper's conventions disagree: with (5.45) and $\hat H_{\rm int}=+A\hat x\hat F$ the cross term carries a minus sign, while (5.59) uses the opposite sign of $\chi_{xx}$. $A\neq0$ and $\chi_{IF}\neq0$ are assumed wherever it is used.
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. V.E.5, Eq. (5.61), p.37

import Mathlib
import Definitions.Def_QuantumNoise_Detector
import Definitions.Def_QuantumNoise_Sbar
import Definitions.Def_QuantumNoise_chi

namespace QuantumNoise

/-- The **added position noise** of a linear position detector at frequency `ω`, coupling
strength `A`, oscillator susceptibility `χ = χxx[ω]` and cross-term sign `σ`:
`S̄xx,add[ω] = S̄II / (|χIF|² A²) + A² |χ|² S̄FF + σ · 2 Re[χIF* χ* S̄IF] / |χIF|²`,
all spectra and gains evaluated at `ω`.

Clerk et al., arXiv:0810.4729v2, Sec. V.E.5, Eq. (5.61), p.37 (printed p.37, PDF p.37); the
printed formula is `σ = +1`.

**Formalization Note** (5.61) is taken as the definition of the added noise; the paper reaches
it from the classical Langevin equations (5.41), (5.45)–(5.46), neglecting non-Gaussian
corrections (p.34), and that derivation is not formalized. `χ` is an arbitrary complex number
(the paper's `χxx[ω] = −(1/M)/((ω² − Ω²) + iωΩ/Q[ω])`, (5.45), is one value). The sign `σ = ±1`
of the cross term is a parameter: with (5.45) and `Ĥint = +A x̂ F̂` the cross term of (5.46),
(5.61) carries a minus sign, while the printed plus sign matches the opposite sign convention
for `χxx` used in (5.59); statements quantify over both. `S̄II`, `S̄FF` are real (`.re`).
Lean's `x / 0 = 0` applies when `A = 0` or `χIF = 0`; statements exclude both. -/
noncomputable def addedNoise {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
    (P : StationaryDynamics 𝒜) (D : Detector P) (ħ : ℝ) (ω σ A : ℝ) (χ : ℂ) : ℝ :=
  (Sbar P D.I D.I ω).re / (‖chi P ħ D.I D.F ω‖ ^ 2 * A ^ 2) +
    A ^ 2 * ‖χ‖ ^ 2 * (Sbar P D.F D.F ω).re +
    σ * (2 * (starRingEnd ℂ (chi P ħ D.I D.F ω) * starRingEnd ℂ χ * Sbar P D.I D.F ω).re) /
      ‖chi P ħ D.I D.F ω‖ ^ 2

end QuantumNoise


