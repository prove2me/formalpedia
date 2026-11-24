-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormMinimalFactorPoints
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormMinimalFactorPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:46.382805+00:00
-- url     : https://prove2.me/theorems/8ee8936f-a8c9-4b2e-99fd-d6e6de56bd20
-- title:
--   PPrimitive Form Minimal Factor Points
-- statement:
--   Definitions and structural lemmas for PPrimitive Form Minimal Factor Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormMinimalFactorPoints.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormMinimalFactorPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermMinimalPolynomialDivides
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreCentredEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormRemainder
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
namespace PrimitiveFormMinimalFactorPoints
open Topology Filter Polynomial
def anSub {d : ℕ} (y₀ : Fin d → ℂ) : Subring ((Fin d → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f y₀}
  mul_mem' ha hb := AnalyticAt.mul ha hb
  one_mem' := analyticAt_const
  add_mem' ha hb := AnalyticAt.add ha hb
  zero_mem' := analyticAt_const
  neg_mem' ha := AnalyticAt.neg ha
end PrimitiveFormMinimalFactorPoints
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


