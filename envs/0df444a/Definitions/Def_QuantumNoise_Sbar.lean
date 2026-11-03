-- Prove2me | Definitions.Def_QuantumNoise_Sbar
-- name    : QuantumNoise_Sbar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:53.393803+00:00
-- url     : https://prove2.me/theorems/82d697c6-1b05-4eee-b6f7-1d7e505b6508
-- title:
--   Symmetrized noise spectral density $\bar S_{ab}[\omega]$
-- statement:
--   For observables $a,b$ of a stationary quantum system, the **symmetrized quantum noise spectral density** is
--   $$
--   \bar S_{ab}[\omega]=\frac12\int_{-\infty}^{\infty}dt\,e^{i\omega t}\,\big\langle\{a(t),b(0)\}\big\rangle_0,\qquad \{x,y\}=xy+yx .
--   $$
--   For a detector, $\bar S_{II}$ is the intrinsic output noise, $\bar S_{FF}$ the back-action noise and $\bar S_{IF}$ their cross-correlation (4.4a)–(4.4c). The symmetrized part plays the role of classical noise.
--
--   **Formalization Note** Fourier convention $e^{+i\omega t}$ (Table I). For a self-adjoint $a=b$ the value is real, and statements use its real part. The relation $\bar S_{IF}[\omega]=\tfrac12(S_{IF}[\omega]+S_{IF}[-\omega]^\ast)$ is a theorem of the mission (4.8a), not the definition.
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. IV.A.2, Eqs. (4.4a)–(4.4c), p.22

import Mathlib
import Definitions.Def_QuantumNoise_StationaryDynamics

namespace QuantumNoise

/-- The **symmetrized quantum noise spectral density**
`S̄_{ab}[ω] = ½ ∫_{−∞}^{∞} dt e^{iωt} ⟨{a(t), b(0)}⟩₀`, with `{x, y} = xy + yx`.

Clerk et al., arXiv:0810.4729v2, Sec. IV.A.2, Eqs. (4.4a)–(4.4c), p.22 (printed p.22, PDF p.22):
`S̄FF`, `S̄II`, `S̄IF`.

**Formalization Note** Fourier convention `e^{+iωt}` (Table I). For self-adjoint `a = b`
(`S̄II`, `S̄FF`) the value is real (the integrand is real and even in `t`); statements use its
real part `.re`, which loses nothing. The relation (4.8a) to `S_{ab}` is a theorem (milestone),
not this definition. -/
noncomputable def Sbar {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
    (P : StationaryDynamics 𝒜) (a b : 𝒜) (ω : ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∫ t : ℝ, Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) *
    P.ρ₀ (P.τ t a * b + b * P.τ t a)

end QuantumNoise


