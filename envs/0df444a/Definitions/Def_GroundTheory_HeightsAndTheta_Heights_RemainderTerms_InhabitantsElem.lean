-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsElem
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsElem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:31.226454+00:00
-- url     : https://prove2.me/theorems/1be614f9-73f7-4cb6-916e-9e2ef60d854a
-- title:
--   Inhabitants Elem
-- statement:
--   Definitions and structural lemmas for Inhabitants Elem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsElem.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
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
def inhQ : ℕ → Fin 1 → RootRing 1 (1 + 1) :=
  fun k _ => if k = 1 then C (2⁻¹) * (flagTwoSecondRoot - flagTwoFirstRoot) else if k = 2 then C (2⁻¹) else 0
end
end RestTerms
end GroundTheory.Heights₂.Heights


