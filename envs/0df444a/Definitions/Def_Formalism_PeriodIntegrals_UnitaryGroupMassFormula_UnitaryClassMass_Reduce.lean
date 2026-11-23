-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Reduce
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Reduce
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:48.023568+00:00
-- url     : https://prove2.me/theorems/ddcd2c7b-3ad1-41cc-9a1a-66e42389de7a
-- title:
--   Reduce
-- statement:
--   Definitions and structural lemmas for Reduce, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/Reduce.lean

import Definitions.Def_Formalism_PeriodIntegrals_UJClassMass
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
section Abstract
variable {G : Type*} [Group G] (Γ Kf : Subgroup G)
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) (L0 : Submodule (𝓞 K) V)
structure IsDict (Λ : G → Submodule (𝓞 K) V) (ι : Γ → V ≃ₗ[K] V) : Prop where
  mem : ∀ g, Λ g ∈ genus h L0
  isIsom : ∀ γ, ι γ ∈ isom h
  equiv : ∀ g (γ : Γ) (k : Kf), Λ ((γ : G) * g * k) = gmap (ι γ) (Λ g)
  inj : ∀ g g' (u : V ≃ₗ[K] V), u ∈ isom h → gmap u (Λ g') = Λ g →
    ∃ (γ : Γ) (k : Kf), g = (γ : G) * g' * k
  surj : ∀ N ∈ genus h L0, ∃ g, Λ g = N
  card : ∀ g, Nat.card (PI.UJClassMass.stab Γ Kf g) = Nat.card (autL h (Λ g))
variable {Γ Kf h L0}
end Abstract
end PI.UnitaryGroupMassFormula.UJClassMass
end


