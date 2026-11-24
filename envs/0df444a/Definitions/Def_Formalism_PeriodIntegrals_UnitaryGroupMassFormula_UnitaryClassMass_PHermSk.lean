-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermSk
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermSk
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T15:37:02.383832+00:00
-- url     : https://prove2.me/theorems/e41d676f-6cc2-478b-935c-a96eb07b89eb
-- title:
--   PHerm Sk
-- statement:
--   Definitions and structural lemmas for PHerm Sk, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PHermSk.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnitaryApproxFin
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
def Sw (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (t : HeightOneSpectrum (𝓞 F)) : Submonoid (𝓞 E) :=
  t.asIdeal.primeCompl.map (algebraMap (𝓞 F) (𝓞 E))
def LocSw : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E), (∀ a, σ a = star a) → (∀ e, σ e = e → ∃ c : F, algebraMap F E c = e) →
    ∀ (V : Type) [AddCommGroup V] [Module (𝓞 E) V] (p : Ideal (𝓞 E)), p.IsMaximal →
    ∀ t : HeightOneSpectrum (𝓞 F), t.asIdeal = p.comap (algebraMap (𝓞 F) (𝓞 E)) →
    ∀ X : Submodule (𝓞 E) V, loc (K := E) p X = locS (Sw F E t) X
def CloseLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ e, σ (σ e) = e) → PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J → IsUnit J.det → Submodule.IsLattice E L0 →
    ∀ g : GL (Fin M) E, g ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ D' : 𝓞 F, D ∣ D' → ∀ γ : GL (Fin M) E, γ ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
      ∀ t : HeightOneSpectrum (𝓞 F),
      (∀ i j, ∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (t.adicCompletion F) (PI.UnitaryApproxDefs.intOE E)
          (t.adicCompletionIntegers F).toSubring,
        PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) ((g : Matrix (Fin M) (Fin M) E) i j) -
            PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) ((γ : Matrix (Fin M) (Fin M) E) i j) =
          PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) (algebraMap F E (D' : F)) * s) →
      locS (Sw F E t) (gmap (linOf b γ) L0) = locS (Sw F E t) (gmap (linOf b g) L0)
def WPlace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : Ideal (𝓞 E)), p.IsMaximal → p.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥
def BcU : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin M) E),
    g ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
    Units.map ((PI.UnitaryApproxDefs.inclE (F := F) (E := E) R).mapMatrix :
      Matrix (Fin M) (Fin M) E →+* Matrix (Fin M) (Fin M) (E ⊗[F] R)).toMonoidHom g ∈ PI.UnitaryApproxDefs.UPts σ J R
def GramOK : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [StarRing E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ a, σ a = star a) → ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V),
    h.IsSymm → h.Nondegenerate → PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) (gramOf h b) ∧ IsUnit (gramOf h b).det
abbrev Fix {E : Type} [Field E] (s : E →+* E) : Subfield E := RingHom.eqLocusField s (RingHom.id E)
def sigFix {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) :
    E →ₐ[Fix (σ : E →+* E)] E :=
  { (σ : E →+* E) with commutes' := fun r => r.2 }
end PI.UnitaryGroupMassFormula.UJClassMass
end


