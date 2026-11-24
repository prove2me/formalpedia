-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjF
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjF
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:31:19.745802+00:00
-- url     : https://prove2.me/theorems/98d80fdd-ee78-46db-88e0-46ac39537f03
-- title:
--   PSurj F
-- statement:
--   Definitions and structural lemmas for PSurj F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjF.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSSkeleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
def Floc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {V : Type}
    [AddCommGroup V] [Module (𝓞 E) V] (v : HeightOneSpectrum (𝓞 F)) (X : Submodule (𝓞 E) V) : Set V :=
  {x | ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) s • x ∈ X}
def PatchF : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    Submodule.IsLattice E L0 →
    (∀ y : Fin M → E, PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) y ∈ latHat F E (crdOf b L0) → y ∈ crdOf b L0) →
    ∀ (γ : UJ (σ : E →+* E) J) (T : Finset (HeightOneSpectrum (𝓞 F))),
      ∃ g : HA (AF F) σ J, latSet σ J b L0 g =
        {x | (∀ v ∈ T, x ∈ Floc v (gmap (linOf b (γ : GL (Fin M) E)) L0)) ∧ (∀ v ∉ T, x ∈ Floc v L0)}
def SemiApprox : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    ∀ N ∈ genus h L0, ∀ T : Finset (HeightOneSpectrum (𝓞 F)),
      ∃ γ : UJ (σ : E →+* E) (gramOf h b), ∀ v ∈ T,
        Floc v (gmap (linOf b (γ : GL (Fin M) E)) L0) = Floc v N
section Cheap
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {V : Type}
  [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
end Cheap
end PI.UnitaryGroupMassFormula.UJClassMass
end


