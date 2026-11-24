-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermCentredIntegralEquation
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermCentredIntegralEquation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:40.055236+00:00
-- url     : https://prove2.me/theorems/e0a0fe47-33c8-4df6-a588-6129036ad8bf
-- title:
--   PGerm Centred Integral Equation
-- statement:
--   Definitions and structural lemmas for PGerm Centred Integral Equation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermCentredIntegralEquation.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
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
noncomputable section
namespace CentredIntegralEquation
open PrimeGermPrimitivePresentation
variable {σ : Type} [Fintype σ]
def germEval (w : σ → ℂ) : holGerms w →+* ℂ := Germ.valueRingHom.comp (holGerms w).subtype
def constGerm (w : σ → ℂ) : ℂ →+* holGerms w where
  toFun c := toGerm w ⟨fun _ => c, analyticAt_const⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
end CentredIntegralEquation
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


