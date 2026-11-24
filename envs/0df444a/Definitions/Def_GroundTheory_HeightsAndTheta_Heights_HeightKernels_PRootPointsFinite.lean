-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointsFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointsFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:50.881339+00:00
-- url     : https://prove2.me/theorems/60580a7c-d02e-41ed-a8fc-a3e7da9e7724
-- title:
--   PRoot Points Finite
-- statement:
--   Definitions and structural lemmas for PRoot Points Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointsFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
namespace RootPointsFiniteAlt
variable {K : Type*} {ι : K → Type*}
def homog (q : Polynomial ℤ) (p a : Σ k, ι k) : MRing ι :=
  ∑ i ∈ Finset.range (q.natDegree + 1), C (q.coeff i) * X p ^ i * X a ^ (q.natDegree - i)
end RootPointsFiniteAlt
end
end GroundTheory.Heights₂.Heights


