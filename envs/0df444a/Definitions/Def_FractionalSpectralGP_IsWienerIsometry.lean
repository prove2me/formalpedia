-- Prove2me | Definitions.Def_FractionalSpectralGP_IsWienerIsometry
-- name    : FractionalSpectralGP_IsWienerIsometry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:03.457269+00:00
-- url     : https://prove2.me/theorems/7608beab-185b-4f5a-a551-aa3fe2e6a549
-- title:
--   The isometry $f\mapsto\widetilde f$ of (4.2)
-- statement:
--   For the white noise measure $P$, a linear map $\iota:L^2(\mathbb R,dx)\to L^2(P)$ is the **isometry $f\mapsto\widetilde f$** if it is a linear isometry and
--
--   $$
--   \iota(s)(\omega)=\widetilde s(\omega)=\langle\omega,s\rangle\qquad P\text{-a.e., for every real Schwartz function }s .
--   $$
--
--   By (4.1) the map $s\mapsto\widetilde s$ is isometric for the $L^2(\mathbb R,dx)$ norm, and it extends to $L^2(\mathbb R,dx)$; the theorem `eq_4_2_isometry` states that exactly one such $\iota$ exists.
--
--   **Formalization Note** Complex scalars are used throughout ($L^2(\mathbb R;\mathbb C)\to L^2(P;\mathbb C)$); on real functions this is the paper's real isometry.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, (4.2), p.10

import Mathlib
import Definitions.Def_FractionalSpectralGP_Omega

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- `ι` is the isometry `f ↦ f̃` of (4.2) (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.10): `s̃(ω) = ⟨ω, s⟩` for real
Schwartz `s`, extended to all of `L²(ℝ, dx)`.

**Formalization Note.** `ι` is a complex-linear isometry `L²(ℝ; ℂ) → L²(P; ℂ)` agreeing `P`-a.e.
with `ω ↦ ⟨ω, s⟩` on every real Schwartz function `s`. The milestone `eq_4_2_isometry` states that
for white noise `P` exactly one such `ι` exists, so taking `ι` as a parameter loses nothing. -/
def IsWienerIsometry (P : Measure Omega) (ι : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 P) : Prop :=
  ∀ s : 𝓢(ℝ, ℝ), ι ((s.memLp 2).ofReal.toLp _) =ᵐ[P] fun ω => ((ω s : ℝ) : ℂ)

end FractionalSpectralGP


