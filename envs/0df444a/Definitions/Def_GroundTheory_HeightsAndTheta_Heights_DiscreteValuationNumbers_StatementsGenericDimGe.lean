-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericDimGe
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericDimGe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:04.734487+00:00
-- url     : https://prove2.me/theorems/7a9cb7dd-035e-4ae0-9072-bb60456cc296
-- title:
--   Statements Generic Dim Ge
-- statement:
--   Definitions and structural lemmas for Statements Generic Dim Ge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsGenericDimGe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
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
def GenericDimGe.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    P.IsPrime → P.comap (C : O →+* MRing ι O) = ⊥ →
    ringKrullDim (MRing ι O ⧸ P) ≤ ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) + 1
end
end GroundTheory.Heights₂.Heights.NumbersDVR


