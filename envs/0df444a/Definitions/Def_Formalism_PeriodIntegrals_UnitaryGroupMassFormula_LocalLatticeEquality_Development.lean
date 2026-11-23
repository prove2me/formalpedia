-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:16:44.390268+00:00
-- url     : https://prove2.me/theorems/3c427d81-2d5f-4db0-964d-a244a7bcf35b
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeEquality/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
namespace PI.LocLatEq.W
def UnitP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p) (d : 𝓞 F),
    d ∉ p.asIdeal → ∃ u ∈ A.O, u * A.ιE ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) = 1
def AvoidP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 E)),
    (∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal →
      ¬ I ≤ P.asIdeal) →
    ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) d ∈ I
def CoreP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p)
    (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Λ.FG → ∀ y : Fin n → E, bc A y ∈ latL A Λ →
    ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) d • y ∈ Λ
end PI.LocLatEq.W


