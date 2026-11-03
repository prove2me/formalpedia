-- Prove2me | Definitions.Def_QuantumNoise_Detector
-- name    : QuantumNoise_Detector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:53.399973+00:00
-- url     : https://prove2.me/theorems/9d8a347c-3673-4a58-b507-659d235ebbc2
-- title:
--   Generic linear-response detector (input $\hat F$, output $\hat I$)
-- statement:
--   Let $(\mathcal A,\tau,\rho_0)$ be a stationary quantum system. A **generic linear-response detector** on it is a pair of observables $\hat I,\hat F\in\mathcal A$ (the output and the input operator) such that
--
--   1. $\hat I^\ast=\hat I$ and $\hat F^\ast=\hat F$;
--   2. they are centred: $\langle\hat I\rangle_0=\langle\hat F\rangle_0=0$;
--   3. for $a,b\in\{\hat I,\hat F\}$ the correlator $t\mapsto\langle a(t)\,b\rangle_0$ is continuous and Lebesgue integrable on $\mathbb R$.
--
--   $\hat F$ couples to the signal through $\hat H_{\rm int}=A\hat x\hat F$ and $\hat I$ is read out (Fig. 7). Centring is the paper's "redefining these operators so that their average value is zero at zero coupling".
--
--   **Formalization Note** Condition 3 is not stated in the paper. Every spectral density and gain of the paper is a Fourier integral of one of these correlators, and it is a number at every frequency exactly when the correlator is integrable; continuity makes the finite-time double integrals of (4.14)–(4.15) well defined. The correlators $\langle b\,a(t)\rangle_0$ are the complex conjugates of these, so they are continuous and integrable too.
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. IV.A.2, pp.21–22 (input and output operators; centring before (4.4))

import Mathlib
import Definitions.Def_QuantumNoise_StationaryDynamics

namespace QuantumNoise

/-- A **generic linear-response detector** on a stationary quantum system `P`: an input operator
`F` (coupling to the signal) and an output operator `I` (read out), both self-adjoint and
centred, `⟨F⟩₀ = ⟨I⟩₀ = 0`, whose four correlators `t ↦ ⟨a(t) b⟩₀` (`a, b ∈ {I, F}`) are
continuous and integrable on `ℝ`.

Clerk et al., arXiv:0810.4729v2, Sec. IV.A.2, p.21 (printed p.21, PDF p.21): "The detector has
both an input port, characterized by an operator F̂, and an output port, characterized by an
operator Î"; p.22: "Redefining these operators so that their average value is zero at zero
coupling (i.e. F̂ → F̂ − ⟨F̂⟩₀, Î → Î − ⟨Î⟩₀)".

**Formalization Note** The paper's spectral densities (4.4), (4.7) and Kubo gains (4.3), (4.6) are
Fourier integrals of these correlators; the paper never states a regularity condition. They are
assumed continuous and Lebesgue integrable, so that every spectral density is an honest integral
at every frequency (a non-integrable correlator would make Lean's Bochner integral `0`). The
correlators `⟨b a(t)⟩₀` are then also continuous and integrable, being complex conjugates of
these. -/
structure Detector {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
    (P : StationaryDynamics 𝒜) where
  /-- The output operator `Î`. -/
  I : 𝒜
  /-- The input operator `F̂`. -/
  F : 𝒜
  star_I : star I = I
  star_F : star F = F
  ρ₀_I : P.ρ₀ I = 0
  ρ₀_F : P.ρ₀ F = 0
  continuous_corr : ∀ a ∈ ({I, F} : Set 𝒜), ∀ b ∈ ({I, F} : Set 𝒜),
    Continuous fun t : ℝ => P.ρ₀ (P.τ t a * b)
  integrable_corr : ∀ a ∈ ({I, F} : Set 𝒜), ∀ b ∈ ({I, F} : Set 𝒜),
    MeasureTheory.Integrable fun t : ℝ => P.ρ₀ (P.τ t a * b)

end QuantumNoise


