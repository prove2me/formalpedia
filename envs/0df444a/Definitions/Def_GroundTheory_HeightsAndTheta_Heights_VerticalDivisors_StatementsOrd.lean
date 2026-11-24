-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsOrd
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsOrd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:29.786624+00:00
-- url     : https://prove2.me/theorems/f4c4b14f-227f-4040-a896-119f70cab112
-- title:
--   Statements Ord
-- statement:
--   Definitions and structural lemmas for Statements Ord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/StatementsOrd.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
noncomputable section
def FiniteOrd.Statement : Prop :=
  ∀ (R B : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] (b : B), Function.Injective (fun x : B => b * x) →
      ∀ 𝔫 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔫.asIdeal) (algebraMap B (Localization.AtPrime 𝔫.asIdeal) b) ≠ ⊤
end
end GroundTheory.Heights₂.Heights.Vertical


