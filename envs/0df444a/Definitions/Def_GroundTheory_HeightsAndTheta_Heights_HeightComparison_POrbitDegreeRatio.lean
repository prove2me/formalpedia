-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatio
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatio
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:37:40.465826+00:00
-- url     : https://prove2.me/theorems/fd44c5f6-72cd-42e6-8d35-5882728dd2fc
-- title:
--   POrbit Degree Ratio
-- statement:
--   Definitions and structural lemmas for POrbit Degree Ratio, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatio.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatioLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_samplePoint_blockNonzero_cdc1bb3eff09

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
def ratioVec (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    Coord n → ratioField x :=
  fun p ↦ ⟨x p.1 p.2 / x p.1 (c p.1), div_mem_ratioField x _ _ _⟩
example : BlockNonzero samplePoint := samplePoint_blockNonzero
end
end GroundTheory.Heights₂.Heights


