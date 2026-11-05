-- Prove2me | Definitions.Def_FractionalSpectralGP_IsWhiteNoise
-- name    : FractionalSpectralGP_IsWhiteNoise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:59.243817+00:00
-- url     : https://prove2.me/theorems/b4eb84d3-7adf-41a1-851f-7e8c99f33345
-- title:
--   White noise measure $P$ on $\mathcal S'$ (4.1)
-- statement:
--   A measure $P$ on $\Omega=\mathcal S'$ is the **white noise measure** if it is a probability measure and
--
--   $$
--   \int_{\mathcal S'}e^{-i\langle s',s\rangle}\,dP(s')=K(s)=e^{-\|s\|^2/2}\qquad\text{for every }s\in\mathcal S,
--   $$
--
--   where $\|s\|^2=\int_{\mathbb R}s(x)^2\,dx$.
--
--   **Formalization Note** The paper obtains $P$ from the Bochner–Minlos theorem, which is not available in Mathlib. Statements take $P$ as a parameter satisfying (4.1); a characteristic functional determines the measure, so nothing is lost.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, (4.1), p.10

import Mathlib
import Definitions.Def_FractionalSpectralGP_Omega

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- `P` is the white noise measure on `Ω = 𝒮'` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, (4.1), p.10): a probability
measure with characteristic functional
`∫_{𝒮'} e^{−i⟨s', s⟩} dP(s') = K(s) = e^{−‖s‖²/2}`, `s ∈ 𝒮`, where `‖s‖` is the `L²(ℝ)` norm.

**Formalization Note.** The paper obtains `P` from the Bochner–Minlos theorem, which is not in
Mathlib; statements take `P` as a parameter satisfying (4.1), which determines it uniquely. -/
def IsWhiteNoise (P : Measure Omega) : Prop :=
  IsProbabilityMeasure P ∧ ∀ s : 𝓢(ℝ, ℝ),
    ∫ ω, Complex.exp (-(Complex.I * (ω s))) ∂P = Real.exp (-(∫ x, s x ^ 2) / 2)

end FractionalSpectralGP


