-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelSetsSL2Adelic
-- name    : Formalism_UnipotentAdelicQuotients_SiegelSetsSL2Adelic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:24.470197+00:00
-- url     : https://prove2.me/theorems/ee4a1534-e244-4c73-9352-212d36316053
-- title:
--   Siegel Sets SL2 Adelic
-- statement:
--   Definitions and structural lemmas for Siegel Sets SL2 Adelic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/SiegelSetsSL2Adelic.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace Formalism.D
def adeleOfParts (F : Type) [Field F] [NumberField F] (x : InfiniteAdeleRing F)
    (y : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F := (x, y)
def siegelSetsSL2Adelic : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    ∃ (Ω K : Set (Matrix.SpecialLinearGroup (Fin 2) (AdeleRing (𝓞 F) F))) (t₀ : ℝ),
      IsCompact Ω ∧ (∀ p ∈ Ω, (p : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0) ∧ IsCompact K ∧ 0 < t₀ ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) (AdeleRing (𝓞 F) F),
        ∃ γ ∈ (Matrix.SpecialLinearGroup.map (algebraMap F (AdeleRing (𝓞 F) F))).range,
        ∃ p ∈ Ω, ∃ t : ℝ, t₀ ≤ t ∧
        ∃ a a' : InfiniteAdeleRing F,
          (∀ w, a w * a' w = 1 ∧ InfinitePlace.Completion.extensionEmbedding w (a w) = (t : ℂ)) ∧
          ∃ k ∈ K, ((γ * g : Matrix.SpecialLinearGroup (Fin 2) (AdeleRing (𝓞 F) F)) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
            (p : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) *
              !![adeleOfParts F a 1, 0; 0, adeleOfParts F a' 1] *
              (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
end Formalism.D
end


