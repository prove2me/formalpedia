-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatioLemmas
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatioLemmas
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:27:26.86709+00:00
-- url     : https://prove2.me/theorems/70bded01-0bc4-429d-997f-71572cae0aa4
-- title:
--   POrbit Degree Ratio Lemmas
-- statement:
--   Definitions and structural lemmas for POrbit Degree Ratio Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatioLemmas.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegreeRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
def chartHomogQ (c : (k : ι) → Fin (n k + 1)) (f : MvPolynomial (Coord n) ℚ)
    [Fintype ι] : MvPolynomial (Coord n) ℚ :=
  ∑ m ∈ f.support, C (coeff m f) * ∏ p : Coord n, (X p ^ m p * X ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p))
variable [Fintype ι]
variable [DecidableEq ι]
end
end GroundTheory.Heights₂.Heights


