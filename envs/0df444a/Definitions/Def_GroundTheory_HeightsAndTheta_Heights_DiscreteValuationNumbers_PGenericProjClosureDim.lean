-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:56.935104+00:00
-- url     : https://prove2.me/theorems/85d6408c-53cb-45be-9847-aafd7fd878a7
-- title:
--   PGeneric Proj Closure Dim
-- statement:
--   Definitions and structural lemmas for PGeneric Proj Closure Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDvrConeDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairBundleTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GenericProjClosureDim
variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L] {K : Type*} [DecidableEq K]
  {ι : K → Type*}
def tWeight (K : Type*) [DecidableEq K] : K → K → ℕ := fun k => Pi.single k 1
end GenericProjClosureDim
end
end GroundTheory.Heights₂.Heights.NumbersDVR


