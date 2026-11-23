-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:51.172048+00:00
-- url     : https://prove2.me/theorems/42fe89c8-97e0-4025-8b43-4dabc968e380
-- title:
--   Weak Approx F
-- statement:
--   Definitions and structural lemmas for Weak Approx F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/WeakApproxF.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApproxFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace PI.UnitaryApproxFinWork
abbrev Sv {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : Subring (E ⊗[F] v.adicCompletion F) :=
  PI.UnitaryApproxDefs.tensInt (F := F) (v.adicCompletion F) (PI.UnitaryApproxDefs.intOE E) (v.adicCompletionIntegers F).toSubring
abbrev dv {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) : E ⊗[F] v.adicCompletion F :=
  PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (d : F))
abbrev Cong {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) (x : E ⊗[F] v.adicCompletion F) : Prop :=
  ∃ s ∈ Sv E v, x = dv E v d * s
def WeakApproxF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F)))
    (c : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) (D : 𝓞 F), D ≠ 0 →
    ∃ a : F, ∀ v ∈ T, ∃ t ∈ v.adicCompletionIntegers F,
      c v - algebraMap F (v.adicCompletion F) a = algebraMap F (v.adicCompletion F) (D : F) * t
def ApproxE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (x : (v : HeightOneSpectrum (𝓞 F)) → E ⊗[F] v.adicCompletion F) (D : 𝓞 F), D ≠ 0 →
    ∃ e : E, ∀ v ∈ T, Cong E v D (x v - PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) e)
def BddR : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F),
    ∃ c : 𝓞 F, c ≠ 0 ∧ dv E v c * x ∈ Sv E v
def UnitS : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (π : 𝓞 F), π ∈ v.asIdeal → ∀ s ∈ Sv E v,
    ∃ u ∈ Sv E v, (1 + dv E v π * s) * u = 1
def EigAvoid : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → (∃ θ, σ θ ≠ θ) →
    ∀ (T : Finset (HeightOneSpectrum (𝓞 F)))
      (g : (v : HeightOneSpectrum (𝓞 F)) → Matrix n n (E ⊗[F] v.adicCompletion F)),
    ∃ μ : E, σ μ * μ = 1 ∧ ∀ v ∈ T, IsUnit (1 + PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ • g v).det
def CayleyFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ e, σ (σ e) = e) → PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J → IsUnit J.det →
    ∀ (T : Finset (HeightOneSpectrum (𝓞 F)))
      (g : (v : HeightOneSpectrum (𝓞 F)) → GL n (E ⊗[F] v.adicCompletion F)),
      (∀ v ∈ T, g v ∈ PI.UnitaryApproxDefs.UPts σ J (v.adicCompletion F)) →
      (∀ v ∈ T, IsUnit (1 + (g v : Matrix n n (E ⊗[F] v.adicCompletion F))).det) →
      ∀ D : 𝓞 F, D ≠ 0 →
    ∃ γ ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J, ∀ v ∈ T, ∀ i j,
      Cong E v D ((g v : Matrix n n (E ⊗[F] v.adicCompletion F)) i j -
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) ((γ : Matrix n n E) i j))
end PI.UnitaryApproxFinWork
end


