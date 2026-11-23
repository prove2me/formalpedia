-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_MassRankOne
-- name    : Formalism_PeriodIntegrals_MassRankOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:53.757366+00:00
-- url     : https://prove2.me/theorems/49ce9d2f-32ec-41eb-88de-9b6432588f1b
-- title:
--   Mass Rank One
-- statement:
--   Definitions and structural lemmas for Mass Rank One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/MassRankOne.lean

import Mathlib
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
namespace PI.MassRankOne
open NumberField Module
def IsPosDef {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ τ : K →+* ℂ, ∀ x : V, x ≠ 0 → 0 < (τ (h x x)).re
def MassRankOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
      [IsScalarTower (𝓞 K) K V']
      (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K)
      (M : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) V'),
      h.IsSymm → IsPosDef h → Module.finrank K V = 1 → Submodule.IsLattice K M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
      h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h' L' 1 →
        Formalism.HermitianLatticesTheory.mass h M = Formalism.HermitianLatticesTheory.mass h' L'
end PI.MassRankOne


