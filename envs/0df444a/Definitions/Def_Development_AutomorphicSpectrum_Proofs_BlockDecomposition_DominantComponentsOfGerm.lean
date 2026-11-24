-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DominantComponentsOfGerm
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DominantComponentsOfGerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:44.720675+00:00
-- url     : https://prove2.me/theorems/5e6ab8ba-9380-4c1c-a380-68d4256acd7a
-- title:
--   Dominant Components Of Germ
-- statement:
--   Definitions and structural lemmas for Dominant Components Of Germ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DominantComponentsOfGerm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOpenProjectionDominantComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
namespace GlobalTheory.CompanionTheory.ComplexSets
variable {σ : Type} [Fintype σ]
end GlobalTheory.CompanionTheory.ComplexSets


