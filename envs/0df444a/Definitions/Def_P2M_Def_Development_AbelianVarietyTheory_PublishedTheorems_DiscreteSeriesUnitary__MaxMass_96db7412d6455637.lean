-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:38.578095+00:00
-- url     : https://prove2.me/theorems/b9326c5a-d1c1-427b-b6d6-caf70dfc4b30
-- title:
--   Max Mass
-- statement:
--   Definitions and structural lemmas for Max Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/DiscreteSeriesUnitary₂/MaxMass.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace GlobalTheory.Mass
def MaxMass : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ n : ℕ, 1 ≤ n → ∃ c : ℝ,
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → PD h → Module.finrank K V = n →
      ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → Formalism.HermitianLatticesTheory.mass h M = c * lamMax h M
end GlobalTheory.Mass


