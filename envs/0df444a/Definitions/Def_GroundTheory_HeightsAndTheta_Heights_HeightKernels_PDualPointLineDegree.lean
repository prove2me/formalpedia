-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPointLineDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPointLineDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:46.290344+00:00
-- url     : https://prove2.me/theorems/e913d664-9864-478a-a70d-fa552b2ee4a6
-- title:
--   PDual Point Line Degree
-- statement:
--   Definitions and structural lemmas for PDual Point Line Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPointLineDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial Matrix NumberField
open scoped ComplexOrder
noncomputable section
namespace DualPointLineDegreeAlt
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} {K' : Type} [Field K'] [NumberField K'] [Algebra K K']
end DualPointLineDegreeAlt
end
end GroundTheory.Heights₂.Heights


