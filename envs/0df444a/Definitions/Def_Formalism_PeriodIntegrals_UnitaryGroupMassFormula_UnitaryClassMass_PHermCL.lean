-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermCL
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermCL
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T15:59:18.463153+00:00
-- url     : https://prove2.me/theorems/b33f496f-728a-410b-8a52-72721f47e9df
-- title:
--   PHerm CL
-- statement:
--   Definitions and structural lemmas for PHerm CL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PHermCL.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermSk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
def TensLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∃ δ : 𝓞 F, δ ≠ 0 ∧ ∀ (t : HeightOneSpectrum (𝓞 F)) (e : E) (c : 𝓞 F),
      (∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (t.adicCompletion F) (PI.UnitaryApproxDefs.intOE E) (t.adicCompletionIntegers F).toSubring,
        PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) e =
          PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) (algebraMap F E (c : F)) * s) →
      ∃ r ∈ Sw F E t, ∃ y : 𝓞 E, (r : E) * (algebraMap F E (δ : F) * e) = algebraMap F E (c : F) * (y : E)
def LatClose : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ e, σ (σ e) = e) → PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J → IsUnit J.det → Submodule.IsLattice E L0 →
    ∀ g : GL (Fin M) E, g ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ D' : 𝓞 F, D ∣ D' → ∀ γ : GL (Fin M) E, γ ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
      ∀ S : Submonoid (𝓞 E), (∀ r ∈ S, σ (r : E) = r) →
      (∀ i j, ∃ r ∈ S, ∃ y : 𝓞 E,
        (r : E) * ((g : Matrix (Fin M) (Fin M) E) i j - (γ : Matrix (Fin M) (Fin M) E) i j) =
          algebraMap F E (D' : F) * (y : E)) →
      locS S (gmap (linOf b γ) L0) = locS S (gmap (linOf b g) L0)
end PI.UnitaryGroupMassFormula.UJClassMass
end


