-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormRemainder
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormRemainder
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:15.900113+00:00
-- url     : https://prove2.me/theorems/2e02d3c0-4560-412b-a36e-8a221e3ab808
-- title:
--   PPrimitive Form Remainder
-- statement:
--   Definitions and structural lemmas for PPrimitive Form Remainder, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormRemainder.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormRemainder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSeparateWeierstrassDivision
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
open Topology Filter Polynomial
def PrimitiveFormRemainder.analyticSubring (d : ℕ) (y₀ : Fin d → ℂ) : Subring ((Fin d → ℂ) → ℂ) where
  carrier := {g | AnalyticAt ℂ g y₀}
  mul_mem' ha hb := ha.mul hb
  one_mem' := analyticAt_const
  add_mem' ha hb := ha.add hb
  zero_mem' := analyticAt_const
  neg_mem' ha := ha.neg
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


