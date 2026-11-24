-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjDimSpread
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjDimSpread
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:08.004301+00:00
-- url     : https://prove2.me/theorems/60ceb4f2-5e4e-45f4-8e2b-f3dfb211bbc2
-- title:
--   St Proj Dim Spread
-- statement:
--   Definitions and structural lemmas for St Proj Dim Spread, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StProjDimSpread.lean

import Mathlib
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
open CategoryTheory
def ProjDimSpread.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I P : Ideal R) [P.IsPrime] (ℓ : ℕ),
    HasProjectiveDimensionLE (ModuleCat.of (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))) ℓ →
    ∃ g : R, g ∉ P ∧ ∀ (Q : Ideal R) [Q.IsPrime], g ∉ Q →
      HasProjectiveDimensionLE (ModuleCat.of (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q)))) ℓ
end GroundTheory.Heights₂.Heights


