-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:14:14.238423+00:00
-- url     : https://prove2.me/theorems/9f94d76e-111f-45fc-b3e5-42c158bef457
-- title:
--   PSurj S
-- statement:
--   Definitions and structural lemmas for PSurj S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjS.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjF
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
def HermApprox : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    ∀ N ∈ genus h L0, ∀ P : Finset (Ideal (𝓞 E)), (∀ p ∈ P, p.IsMaximal) →
      ∃ γ : UJ (σ : E →+* E) (gramOf h b), ∀ p ∈ P,
        loc (K := E) p (gmap (linOf b (γ : GL (Fin M) E)) L0) = loc (K := E) p N
section Over
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable [StarRing E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
end Over
end PI.UnitaryGroupMassFormula.UJClassMass
end


