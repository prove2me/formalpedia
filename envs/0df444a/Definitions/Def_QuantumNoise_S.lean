-- Prove2me | Definitions.Def_QuantumNoise_S
-- name    : QuantumNoise_S
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:03.121208+00:00
-- url     : https://prove2.me/theorems/3afe9697-cfb1-40d0-8c2b-144e0ee21131
-- title:
--   Unsymmetrized noise spectral density $S_{ab}[\omega]$
-- statement:
--   For observables $a,b$ of a stationary quantum system, the **unsymmetrized quantum noise spectral density** is
--   $$
--   S_{ab}[\omega]=\int_{-\infty}^{\infty}dt\,e^{i\omega t}\,\langle a(t)\,b(0)\rangle_0 ,\qquad \omega\in\mathbb R .
--   $$
--   The paper defines it for $a=\hat I$, $b=\hat F$ in (4.7); it need not be symmetric in frequency.
--
--   **Formalization Note** The Fourier convention is the paper's, $f[\omega]=\int dt\,e^{+i\omega t}f(t)$ (Table I), not Mathlib's. The integral is Lean's Bochner integral, which equals the paper's integral when the correlator is integrable, as it is for the operators of a `Detector`.
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. IV.A.2, Eq. (4.7), p.22

import Mathlib
import Definitions.Def_QuantumNoise_StationaryDynamics

namespace QuantumNoise

/-- The **unsymmetrized quantum noise spectral density**
`S_{ab}[ω] = ∫_{−∞}^{∞} dt e^{iωt} ⟨a(t) b(0)⟩₀`.

Clerk et al., arXiv:0810.4729v2, Sec. IV.A.2, Eq. (4.7), p.22 (printed p.22, PDF p.22), stated
there for `a = Î`, `b = F̂`.

**Formalization Note** The Fourier convention is the paper's, `f[ω] = ∫ dt e^{+iωt} f(t)`
(Table I, pp.4–5), not Mathlib's `𝓕` (which uses `e^{−2πiξt}`). The integral is Lean's Bochner
integral; it is the paper's integral when the correlator is integrable, as it is for the
operators of a `Detector`. -/
noncomputable def S {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
    (P : StationaryDynamics 𝒜) (a b : 𝒜) (ω : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) * P.ρ₀ (P.τ t a * b)

end QuantumNoise


