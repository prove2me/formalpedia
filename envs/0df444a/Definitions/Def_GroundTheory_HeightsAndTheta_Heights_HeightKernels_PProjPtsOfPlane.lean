-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOfPlane
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOfPlane
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:36.751412+00:00
-- url     : https://prove2.me/theorems/b471018e-c780-43d4-800b-70884d5544e3
-- title:
--   PProj Pts Of Plane
-- statement:
--   Definitions and structural lemmas for PProj Pts Of Plane, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOfPlane.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
namespace ProjectivePointsOfPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ}
def formPoly (p : Σ _ : Unit, ProjIdx K i) : MvPolynomial (Fin i) K :=
  C (integralBasis K p.2.1) * X p.2.2
end ProjectivePointsOfPlane
end
end GroundTheory.Heights₂.Heights


