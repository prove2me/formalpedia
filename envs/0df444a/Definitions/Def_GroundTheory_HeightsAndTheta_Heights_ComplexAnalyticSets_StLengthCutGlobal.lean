-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutGlobal
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutGlobal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:52.528256+00:00
-- url     : https://prove2.me/theorems/9b7a0272-eb89-47c6-9c2d-718c5b0c9546
-- title:
--   St Length Cut Global
-- statement:
--   Definitions and structural lemmas for St Length Cut Global, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLengthCutGlobal.lean

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
universe u v
def LengthCutGlobal.Statement : Prop :=
  ∀ (C : Type u) [CommRing C] [IsNoetherianRing C] (P : Ideal C) [P.IsPrime] (y : C)
    (M : Type v) [AddCommGroup M] [Module C M] [Module.Finite C M],
    IsNilpotent P → IsPrincipalIdealRing (C ⧸ P) → y ∉ P → (P ⊔ Ideal.span {y}).IsMaximal →
      (∀ s ∉ P, ∀ m : M, s • m = 0 → m = 0) →
      Module.length C (M ⧸ (Ideal.span {y} • ⊤ : Submodule C M)) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)
end GroundTheory.Heights₂.Heights


