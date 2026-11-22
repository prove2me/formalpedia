-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SesquilinearRowSplitting_CoordStep
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SesquilinearRowSplitting_CoordStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:25.034938+00:00
-- url     : https://prove2.me/theorems/53d42243-e556-4c4f-bba9-7e524c313e50
-- title:
--   Coord Step
-- statement:
--   Definitions and structural lemmas for Coord Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SesquilinearRowSplitting/CoordStep.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace PI.SRW
def RepStep : Prop :=
  ∀ (E V : Type) [Field E] [NumberField E] [StarRing E] [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E), h.Nondegenerate →
    ∀ (Λ : Submodule (𝓞 E) V), Submodule.IsLattice E Λ →
    ∀ ℓ : Λ →ₗ[𝓞 E] E, ∃ w : V, ∀ x : Λ, h w x = ℓ x
def CoordStep : Prop :=
  ∀ (E V : Type) [Field E] [AddCommGroup V] [Module E V] (n : ℕ) (g : Fin n → V),
    LinearIndependent E g → ∃ c : Fin n → (V →ₗ[E] E), ∀ i j, c i (g j) = if i = j then 1 else 0
def RetrStep : Prop :=
  ∀ (E V : Type) [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (Λ N : Submodule (𝓞 E) V), N ≤ Λ → Λ.FG →
    (∀ (o : 𝓞 E) (x : V), o ≠ 0 → x ∈ Λ → o • x ∈ N → x ∈ N) →
    ∃ ρ : Λ →ₗ[𝓞 E] V, (∀ x : Λ, ρ x ∈ N) ∧ ∀ x : Λ, (x : V) ∈ N → ρ x = x
end PI.SRW


