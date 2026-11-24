-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
-- name    : Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:21.333627+00:00
-- url     : https://prove2.me/theorems/10c9df2c-3ccb-4ae1-82d9-803ba64625f8
-- title:
--   Cyclic Norm Principle
-- statement:
--   Definitions and structural lemmas for Cyclic Norm Principle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/CyclicNormPrinciple.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace HeckeCharacterZeroLocus
open NumberField IsDedekindDomain
def CyclicNormPrinciple : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsGalois F E → IsCyclic (E ≃ₐ[F] E) → ∀ x : F, x ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 F), ∃ y : TensorProduct F (v.adicCompletion F) E,
        Algebra.norm (v.adicCompletion F) y = algebraMap F (v.adicCompletion F) x) →
    (∀ σ : F →+* ℝ, (¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = σ) → 0 < σ x) →
    ∃ y : E, Algebra.norm F y = x
end HeckeCharacterZeroLocus


