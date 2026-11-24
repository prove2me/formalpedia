-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:13.491939+00:00
-- url     : https://prove2.me/theorems/c6d30c97-4c5e-455f-9ba7-1489f34afbaa
-- title:
--   PMulti Homog Prime Criterion
-- statement:
--   Definitions and structural lemmas for PMulti Homog Prime Criterion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultiHomogPrimeCriterion.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
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
open MvPolynomial
noncomputable section
universe u
namespace MultiHomogPrimeCriterion
variable {K : Type} [Fintype K] [DecidableEq K]
def lexDeg : (K → ℕ) →+ Lex (Fin (Fintype.card K) → ℕ) where
  toFun b := toLex fun j => b ((Fintype.equivFin K).symm j)
  map_zero' := rfl
  map_add' _ _ := rfl
variable {ι : K → Type} {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end MultiHomogPrimeCriterion
end
end GroundTheory.Heights₂.Heights.NumbersDVR


