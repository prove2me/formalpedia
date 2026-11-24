-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:24.641491+00:00
-- url     : https://prove2.me/theorems/92aae5b0-1c9f-4dbe-9157-4d1a1cd815d0
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/Statements.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
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
def KernelsCut.Statement : Prop :=
  SymplecticReduction.Statement ∧ SiegelCoordinates.Statement ∧ FirstCoordinateBound.Statement ∧
    GaussianSum.Statement ∧ ThetaBound.Statement ∧ WeakMatrixArithmetic.Statement ∧
    OrthogonalLines.Statement ∧ LineOfLargeDegree.Statement ∧ ShortVectors.Statement ∧
    RestTerm.Statement ∧ RestTermSharp.Statement ∧ AlternantRowRule.Statement ∧
    AlternantPush.Statement ∧ FrobeniusRectangleBound.Statement
end GroundTheory.Heights₂.Heights


