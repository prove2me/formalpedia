-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensSAChar
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensSAChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:57.432621+00:00
-- url     : https://prove2.me/theorems/15f7afd0-79af-46c4-abca-e277352b8233
-- title:
--   Loc Dens SAChar
-- statement:
--   Definitions and structural lemmas for Loc Dens SAChar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensSAChar.lean

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
open NumberField
namespace PI.VolStabS
def ChInf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ χ : AddChar (InfiniteAdeleRing F) ℂ, Continuous χ →
    (∀ a ∈ Λ, χ (algebraMap F (InfiniteAdeleRing F) a) = 1) → ∀ x, χ x = 1
def ChLift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : AddChar (InfiniteAdeleRing F) ℂ), Continuous χ →
    ∃ ℓ : InfiniteAdeleRing F →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = Complex.exp (ℓ x)
def AddIntF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ g : F →+ ℂ, (∀ a ∈ Λ, ∃ n : ℤ, g a = n) → ∀ a, g a = 0
end PI.VolStabS


