-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:25.079907+00:00
-- url     : https://prove2.me/theorems/01d02230-c6ca-4826-bbc7-1af6e0c95e51
-- title:
--   Inhabitants
-- statement:
--   Definitions and structural lemmas for Inhabitants, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Inhabitants.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
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
namespace RestTerms
open MvPolynomial
noncomputable section
open MvPolynomial
abbrev flagTwoFirstRoot : RootRing 1 (1+1) := X ((0:Fin 1), (0 : Fin (1+1)))
abbrev flagTwoSecondRoot : RootRing 1 (1+1) := X ((0:Fin 1), (1 : Fin (1+1)))
end
end RestTerms
end GroundTheory.Heights₂.Heights


