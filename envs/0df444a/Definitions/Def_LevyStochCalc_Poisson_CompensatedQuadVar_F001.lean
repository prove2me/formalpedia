-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedQuadVar_F001
-- name    : LevyStochCalc_Poisson_CompensatedQuadVar_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:44:31.334985+00:00
-- url     : https://prove2.me/theorems/0d2e6871-dacb-45f8-a9fb-c24b2ea92033
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedQuadVar
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedQuadVar. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedQuadVar_F000
import Definitions.Def_SourceProof_2d5131caf39fa038b7f885d9
import Definitions.Def_SourceProof_8d94a00748b094f98df80cc1
import Definitions.Def_SourceProof_f2a2eeccf86b41fdc8b6fb29

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic-variation martingale of the compensated integral

For an adapted mark-step integrand `G`, the compensated square
`t ↦ (∫_0^t ∫_E G dÑ)² − ∫_0^t ∫_E G(u, e)² ν(de) du` is a martingale on the natural
filtration: the increment isometries of `MarkStep` give the set-level identity required by
`LevyStochCalc.Martingale.martingale_sq_sub_of_setIntegral`. The compensated square of the
`L²` integral process is then the `L¹`-limit of the stage compensated squares.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid} (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g)
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ : IsPoissonFiltration N ℱ)

include hℱ in
/-- The compensated square `(∫_0^t ∫_E G dÑ)² − ∫_0^t ∫_E G² dν du` of an adapted mark-step
integrand is a martingale on the natural filtration. -/
theorem martingale_sq_sub_compensator (hG : G.Adapted ℱ) :
    Martingale (fun t ω => (G.integral N t ω) ^ 2 - G.compensator t ω)
      ℱ P :=
  _root_.Prove2MeSourceProof.h_8d94a00748b094f98df80cc1 (G.martingale_integral N hℱ hG)
    (fun t => G.memLp_integral N t) (fun t => (_root_.Prove2MeSourceProof.h_f2a2eeccf86b41fdc8b6fb29 G) hG t)
    (fun t => G.integrable_compensator t)
    (fun _ _ hst _ hB => (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_2d5131caf39fa038b7f885d9 p2mMethodArg0 G) N hℱ hG hst hB)
end MarkStep

end LevyStochCalc.Poisson.Compensated


