-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T09:05:40.788313+00:00
-- url     : https://prove2.me/theorems/d281eaca-5180-5780-9aaf-a5b587bcd924
-- title:
--   POrbit Chart Mult Lemmas
-- statement:
--   Definitions and structural lemmas for POrbit Chart Mult Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartQuot
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
namespace OrbitChartMult
variable {ι : Type} {n : ι → ℕ}
def chartCone (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) (D : Type*)
    [CommRing D] [Algebra (chartRing x c) D] : MvPolynomial (Coord n) ℤ →+* MvPolynomial ι D :=
  eval₂Hom (Int.castRingHom _) fun p ↦ C (algebraMap (chartRing x c) D (chartEval x c (X p))) * X p.1
def chartIncl (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    chartRing x c →+* AlgebraicClosure ℚ :=
  (ratioField x).val.toRingHom.comp (chartRing x c).val.toRingHom
variable (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
variable [Fintype ι] [DecidableEq ι]
end OrbitChartMult
end
end GroundTheory.Heights₂.Heights


