-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:11.747885+00:00
-- url     : https://prove2.me/theorems/74188531-5a66-43da-85e8-ce70b8172b31
-- title:
--   St Segre Partition
-- statement:
--   Definitions and structural lemmas for St Segre Partition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StSegrePartition.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StokesObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (segre PBlk)
def SegrePartition.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)],
    (∀ k, Nonempty (ι k)) →
      ∃ δ : ℝ, 0 < δ ∧ ∃ ρ : ((k : K) → ι k) → ((Σ k, ι k) → ℂ) → ℝ,
        (∀ i, IsDegZeroSmooth (ρ i)) ∧ (∀ z, ∑ i, ρ i z = 1) ∧
          ∀ i z, ‖segre z i‖ < δ * ‖segre z‖ → ρ i z = 0
end GroundTheory.Heights₂.Heights


