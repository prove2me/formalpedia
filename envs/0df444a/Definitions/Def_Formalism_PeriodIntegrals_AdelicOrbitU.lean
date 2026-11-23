-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
-- name    : Formalism_PeriodIntegrals_AdelicOrbitU
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:17.289969+00:00
-- url     : https://prove2.me/theorems/4116e4b2-7339-4b67-ac10-70c5375bf043
-- title:
--   Adelic Orbit U
-- statement:
--   Definitions and structural lemmas for Adelic Orbit U, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/AdelicOrbitU.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
section Vol
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
def AdelicOrbit : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (β : F),
    IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
    ∀ y : Fin 1 → Fin (M + 1) → AF F ⊗[F] E, qR (AF F) σ J (y 0) = algebraMap F (AF F) β →
      ∃ g : HA (AF F) σ J, g • ratTup (AF F) x = y
end Vol
def AdelicOrbitQuad : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Module.finrank F E = 2 → (∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range) → AdelicOrbit F E σ
end PI.AdelicOrbitU


