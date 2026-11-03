-- Prove2me | Definitions.Def_QuantumNoise_cosPairing
-- name    : QuantumNoise_cosPairing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:47.122858+00:00
-- url     : https://prove2.me/theorems/c5fbeaa1-0113-4144-b812-053e7145244c
-- title:
--   Second moments of the finite-time cosine transforms (4.14)
-- statement:
--   For observables $a,b$, a frequency $\omega$, phases $\delta_a,\delta_b$ and a time $T$, put
--   $$
--   \mathcal C_{ab}(\omega,\delta_a,\delta_b;T)=\frac{2}{T}\int_{-T/2}^{T/2}dt\int_{-T/2}^{T/2}ds\,\cos(\omega t+\delta_a)\cos(\omega s+\delta_b)\,\langle a(t)\,b(s)\rangle_0 .
--   $$
--   With $\hat A=\sqrt{2/T}\int_{-T/2}^{T/2}dt\cos(\omega t+\delta)\hat I(t)$ and $\hat B=\sqrt{2/T}\int_{-T/2}^{T/2}dt\cos(\omega t)\hat F(t)$ (4.14), this is $\langle\hat A\hat A\rangle=\mathcal C_{II}(\omega,\delta,\delta;T)$, $\langle\hat B\hat B\rangle=\mathcal C_{FF}(\omega,0,0;T)$, $\langle\hat A\hat B\rangle=\mathcal C_{IF}(\omega,\delta,0;T)$ and $\langle\hat B\hat A\rangle=\mathcal C_{FI}(\omega,0,\delta;T)$, obtained by expanding the products and using the linearity of the state.
--
--   **Formalization Note** The operator-valued integrals $\hat A$, $\hat B$ are not elements of an abstract $\ast$-algebra; only their second moments enter (4.15), and those are these iterated integrals of correlators.
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. IV.A.3, Eqs. (4.14a)–(4.14b), p.23

import Mathlib
import Definitions.Def_QuantumNoise_StationaryDynamics

namespace QuantumNoise

/-- The expectation `⟨Â B̂⟩₀` of the product of two finite-time cosine transforms
`Â = √(2/T) ∫_{−T/2}^{T/2} dt cos(ωt + δa) a(t)`, `B̂ = √(2/T) ∫_{−T/2}^{T/2} ds cos(ωs + δb) b(s)`,
expanded by linearity of the state:
`(2/T) ∫_{−T/2}^{T/2} dt ∫_{−T/2}^{T/2} ds cos(ωt + δa) cos(ωs + δb) ⟨a(t) b(s)⟩₀`.

Clerk et al., arXiv:0810.4729v2, Sec. IV.A.3, Eqs. (4.14a)–(4.14b), p.23 (printed p.23, PDF
p.23), with `a = Î`, `δa = δ` and `b = F̂`, `δb = 0`. Then `(ΔA)² = ⟨ÂÂ⟩`, `(ΔB)² = ⟨B̂B̂⟩`,
`⟨{Â, B̂}⟩ = ⟨ÂB̂⟩ + ⟨B̂Â⟩` and `⟨[Â, B̂]⟩ = ⟨ÂB̂⟩ − ⟨B̂Â⟩` are values of this function.

**Formalization Note** The operator-valued integrals `Â`, `B̂` are not elements of an abstract
∗-algebra; only their second moments enter (4.15), and those are these double integrals of
correlators (iterated interval integrals). -/
noncomputable def cosPairing {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
    (P : StationaryDynamics 𝒜) (a b : 𝒜) (ω δa δb T : ℝ) : ℂ :=
  ((2 / T : ℝ) : ℂ) * ∫ t in (-T / 2)..(T / 2), ∫ s in (-T / 2)..(T / 2),
    ((Real.cos (ω * t + δa) * Real.cos (ω * s + δb) : ℝ) : ℂ) * P.ρ₀ (P.τ t a * P.τ s b)

end QuantumNoise


