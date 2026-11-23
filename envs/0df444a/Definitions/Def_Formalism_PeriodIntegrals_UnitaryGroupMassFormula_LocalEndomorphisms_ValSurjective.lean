-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:01:50.013138+00:00
-- url     : https://prove2.me/theorems/d681e5b6-12e3-499a-a8dd-8eef681a8ca9
-- title:
--   Val Surjective
-- statement:
--   Definitions and structural lemmas for Val Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/ValSurjective.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocalEnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
namespace PI.LocalEndW
def HenselRoot : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ℓ : ℕ) (u : v.adicCompletion F),
    Valued.v (ℓ : v.adicCompletion F) = 1 → Valued.v (u - 1) < 1 → ∃ z : v.adicCompletion F, z ^ ℓ = u
def IntPreserved : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (τ : v.adicCompletion F →+* v.adicCompletion F) (x : v.adicCompletion F),
    Valued.v x ≤ 1 → Valued.v (τ x) ≤ 1
def ValPreserved : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (τ : v.adicCompletion F →+* v.adicCompletion F) (x : v.adicCompletion F),
    Valued.v (τ x) = Valued.v x
def IntOfHensel : Prop := HenselRoot → IntPreserved
def ValOfInt : Prop := IntPreserved → ValPreserved
def ValContinuous : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (τ : v.adicCompletion F →+* v.adicCompletion F),
    (∀ x, Valued.v (τ x) = Valued.v x) → Continuous τ
def ValSurjective : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (τ : v.adicCompletion F →+* v.adicCompletion F),
    (∀ x, Valued.v (τ x) = Valued.v x) → Function.Surjective τ
end PI.LocalEndW


