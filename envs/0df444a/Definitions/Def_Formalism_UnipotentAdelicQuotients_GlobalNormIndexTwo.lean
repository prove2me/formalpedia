-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_GlobalNormIndexTwo
-- name    : Formalism_UnipotentAdelicQuotients_GlobalNormIndexTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:16.042044+00:00
-- url     : https://prove2.me/theorems/1e79ad9d-8984-4fa2-bc00-9e11f15c00f2
-- title:
--   Global Norm Index Two
-- statement:
--   Definitions and structural lemmas for Global Norm Index Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/GlobalNormIndexTwo.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace Formalism.D.Classical
def GlobalNormIndexTwo : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 →
    ∃! η : (AdeleRing (𝓞 F) F)ˣ →* Circle,
      Continuous η ∧
      (∀ a : Fˣ, η (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) = 1) ∧
      (∀ x : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ,
        η (Units.map (Algebra.norm (AdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F ⊗[F] E →* AdeleRing (𝓞 F) F) x) = 1) ∧
      η ≠ 1
end Formalism.D.Classical
end


