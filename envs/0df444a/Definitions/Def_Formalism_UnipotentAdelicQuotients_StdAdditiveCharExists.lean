-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
-- name    : Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:13.169556+00:00
-- url     : https://prove2.me/theorems/0478af3d-1dbe-42c2-b9f2-a9569daa8849
-- title:
--   Std Additive Char Exists
-- statement:
--   Definitions and structural lemmas for Std Additive Char Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/StdAdditiveCharExists.lean

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
open NumberField
def StdAdditiveCharExists : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F →
    ∃ ψ : AddChar (AdeleRing (𝓞 F) F) ℂ, Continuous ψ ∧ (∀ x, ‖ψ x‖ = 1) ∧
      (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) ∧ (∃ x, ψ x ≠ 1) ∧
      ∀ x : InfiniteAdeleRing F, ψ (x, 0) =
        Complex.exp (-(2 * Real.pi * Complex.I *
          ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ)))
end HeckeCharacterZeroLocus


