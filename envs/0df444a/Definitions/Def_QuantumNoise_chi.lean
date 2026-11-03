-- Prove2me | Definitions.Def_QuantumNoise_chi
-- name    : QuantumNoise_chi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:52.61743+00:00
-- url     : https://prove2.me/theorems/53f491b9-4081-43b4-bc02-115001f48cf6
-- title:
--   Kubo linear-response gain $\chi_{ab}[\omega]$
-- statement:
--   For observables $a,b$ of a stationary quantum system and $\hbar>0$, the **linear-response gain** (susceptibility) is the Fourier transform of the Kubo response function,
--   $$
--   \chi_{ab}(t)=-\frac{i}{\hbar}\,\theta(t)\,\big\langle[a(t),b(0)]\big\rangle_0,\qquad
--   \chi_{ab}[\omega]=\int_{0}^{\infty}dt\,e^{i\omega t}\Big(-\frac{i}{\hbar}\Big)\big\langle[a(t),b(0)]\big\rangle_0 .
--   $$
--   $\chi_{IF}$ is the gain of the detector (4.3), $\chi_{FI}$ the reverse gain (4.6), and $\chi_{II}$, $\chi_{FF}$ the output and input susceptibilities (5.49), (5.52).
--
--   **Formalization Note** The Heaviside factor is the restriction of the integral to $t\in(0,\infty)$; the value $\theta(0)$ does not matter. Fourier convention $e^{+i\omega t}$ (Table I). $\hbar$ is a real parameter, positive in every statement.
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. IV.A.2, Eqs. (4.3), (4.6), pp.21–22, and Sec. V.E.3, Eq. (5.49), p.35

import Mathlib
import Definitions.Def_QuantumNoise_StationaryDynamics

namespace QuantumNoise

/-- The **Kubo linear-response gain** (susceptibility)
`χ_{ab}[ω] = ∫ dt e^{iωt} χ_{ab}(t)`, with `χ_{ab}(t) = −(i/ħ) θ(t) ⟨[a(t), b(0)]⟩₀`.

Clerk et al., arXiv:0810.4729v2, Sec. IV.A.2, Eq. (4.3) (`χIF`, the gain), Eq. (4.6) (`χFI`, the
reverse gain), p.21–22, and Eq. (5.49) (`χII`), p.35 (printed = PDF pages).

**Formalization Note** The Heaviside factor `θ(t)` is the restriction of the integral to
`t ∈ (0, ∞)` (`Set.Ioi 0`); the value of `θ(0)` is irrelevant, `{0}` being a null set. Fourier
convention `e^{+iωt}` (Table I). `ħ` is a real parameter (`ħ > 0` in every statement). -/
noncomputable def chi {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
    (P : StationaryDynamics 𝒜) (ħ : ℝ) (a b : 𝒜) (ω : ℝ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) *
    ((-Complex.I / (ħ : ℂ)) * P.ρ₀ (P.τ t a * b - b * P.τ t a))

end QuantumNoise


