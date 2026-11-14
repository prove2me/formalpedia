-- Prove2me | Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
-- name    : Kyprianou_Ch01_LevyTripletExponent
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T00:14:38.907681+00:00
-- url     : https://prove2.me/theorems/8770a291-9670-44f3-b135-fc2eb5239d31
-- title:
--   Lévy–Khintchine triplet characteristic exponent in LeanLevy positive sign convention
-- statement:
--   Defines the genuine Lévy–Khintchine exponent of the existing ProbabilityTheory.LevyKhintchineTriple using drift i b ξ, negative Gaussian variance −σ²ξ²/2 and the compensated jump integral of the source measure, following Kyprianou Theorem 1.3 with the sign reversed relative to the printed Ψ. Repairs the earlier draft's invalid assumption that LevyKhintchineTriple has an existing exponent field. No claimed theorem proof.
-- source:
--   Kyprianou (2006), Chapter 1, Theorem 1.3, pp. 3–4, Lévy–Khintchine representation.

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch01

/-- The signed characteristic exponent for a Lévy–Khintchine triple
    in the convention E[exp(iξX_t)] = exp(t * exponent ξ). -/
noncomputable def levyTripleExponent
    (T : ProbabilityTheory.LevyKhintchineTriple) (ξ : ℝ) : ℂ :=
  Complex.I * ((T.drift * ξ : ℝ) : ℂ) -
    (((T.gaussianVariance : ℝ) * ξ ^ 2 / 2 : ℝ) : ℂ) +
      ∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂T.levyMeasure

end Kyprianou.Ch01


