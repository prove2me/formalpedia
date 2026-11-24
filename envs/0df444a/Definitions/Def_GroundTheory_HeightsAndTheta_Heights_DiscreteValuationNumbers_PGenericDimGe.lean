-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericDimGe
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericDimGe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:46.958905+00:00
-- url     : https://prove2.me/theorems/5a52c732-6913-4cd9-9b53-80588215db13
-- title:
--   PGeneric Dim Ge
-- statement:
--   Definitions and structural lemmas for PGeneric Dim Ge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericDimGe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericDimGe
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
namespace GenericDimGe
section Noetherian
variable {R : Type*} [CommRing R]
end Noetherian
attribute [local instance] MvPolynomial.algebraMvPolynomial
end GenericDimGe
end
end GroundTheory.Heights₂.Heights.NumbersDVR


