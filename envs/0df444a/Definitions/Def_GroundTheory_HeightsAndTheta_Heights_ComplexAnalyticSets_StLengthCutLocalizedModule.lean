-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutLocalizedModule
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutLocalizedModule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:33.393363+00:00
-- url     : https://prove2.me/theorems/92a2b31e-d0e1-440d-9439-0ad39f904e3f
-- title:
--   St Length Cut Localized Module
-- statement:
--   Definitions and structural lemmas for St Length Cut Localized Module, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLengthCutLocalizedModule.lean

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
def LengthCutLocalizedModule.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (P : Ideal B) [P.IsPrime] (y : B) (Q₀ : Ideal B) [Q₀.IsPrime]
    (M : Type v) [AddCommGroup M] [Module B M] [Module.Finite B M],
    IsNilpotent P → y ∉ P → Q₀ = P ⊔ Ideal.span {y} → (∀ s ∉ P, ∀ m : M, s • m = 0 → m = 0) →
      Module.length (Localization.AtPrime Q₀)
          (LocalizedModule Q₀.primeCompl (M ⧸ (Ideal.span {y} • ⊤ : Submodule B M))) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)
end GroundTheory.Heights₂.Heights


