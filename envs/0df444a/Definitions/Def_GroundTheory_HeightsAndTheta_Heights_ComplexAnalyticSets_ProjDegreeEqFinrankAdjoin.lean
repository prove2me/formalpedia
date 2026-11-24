-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ProjDegreeEqFinrankAdjoin
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ProjDegreeEqFinrankAdjoin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:42.198255+00:00
-- url     : https://prove2.me/theorems/23776b16-8c3a-4db5-aab8-1c95ead42762
-- title:
--   Proj Degree Eq Finrank Adjoin
-- statement:
--   Definitions and structural lemmas for Proj Degree Eq Finrank Adjoin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/ProjDegreeEqFinrankAdjoin.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_IsClosedComplexSubmanifoldIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial
noncomputable section
namespace Objects
variable {n d : ℕ}
section Degree
variable (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]
end Degree
end Objects
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


