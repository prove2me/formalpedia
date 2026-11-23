-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UJClassMass
-- name    : Formalism_PeriodIntegrals_UJClassMass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:33.228615+00:00
-- url     : https://prove2.me/theorems/2a883598-d528-46ff-b2bb-900f77c340e7
-- title:
--   UJClass Mass
-- statement:
--   Definitions and structural lemmas for UJClass Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UJClassMass.lean

import Definitions.Def_Formalism_PeriodIntegrals_UJClassFin
import Definitions.Def_Formalism_HermitianLattices_StatementMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
open scoped TensorProduct
open PI.UJClassFin
namespace PI.UJClassMass
def gramOf {E V : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) {M : ℕ} (b : Module.Basis (Fin M) E V) : Matrix (Fin M) (Fin M) E :=
  fun i j => h (b i) (b j)
def crdOf {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) : Set (Fin M → E) :=
  {x | ∑ i, x i • b i ∈ L0}
def stab {G : Type*} [Group G] (Γ K : Subgroup G) (g : G) : Set Γ := {γ | g⁻¹ * ((γ : G) * g) ∈ K}
def UJClassMass : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ (n : ℕ) (g : Fin n → HA (AF F) σ (gramOf h b)),
      (∀ x, ∃ i, ∃ γ : GamG σ (gramOf h b), ∃ k : SFin σ (gramOf h b) (crdOf b L0),
        x = (γ : HA (AF F) σ (gramOf h b)) * g i * k) →
      (∀ i j (γ γ' : GamG σ (gramOf h b)) (k k' : SFin σ (gramOf h b) (crdOf b L0)),
        (γ : HA (AF F) σ (gramOf h b)) * g i * k = (γ' : HA (AF F) σ (gramOf h b)) * g j * k' → i = j) →
      ∑ i, ((Nat.card (stab (GamG σ (gramOf h b)) (SFin σ (gramOf h b) (crdOf b L0)) (g i)) : ℝ))⁻¹ =
        Formalism.HermitianLatticesTheory.mass h L0
end PI.UJClassMass


