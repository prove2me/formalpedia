-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:16.055208+00:00
-- url     : https://prove2.me/theorems/f5454c64-3878-4634-b2e5-f5db17a04d0f
-- title:
--   St CMLength Parameters
-- statement:
--   Definitions and structural lemmas for St CMLength Parameters, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCMLengthParameters.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects
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
open IsLocalRing
universe u
noncomputable section
def CMLengthParameters.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (P : Ideal B) [P.IsPrime] (d : ℕ) (x : Fin d → B),
    minimalPrimes B = {P} → ringKrullDim (B ⧸ P) = (d : ℕ) →
    Ideal.span (Set.range x) ⊔ P = maximalIdeal B →
      Module.length B (B ⧸ Ideal.span (Set.range x)) =
        Module.length (Localization.AtPrime P) (Localization.AtPrime P)
end
end GroundTheory.Heights₂.Heights


