-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:12:03.393497+00:00
-- url     : https://prove2.me/theorems/0c14473a-03af-4390-aa57-795d28ee3ece
-- title:
--   PSegre Partition
-- statement:
--   Definitions and structural lemmas for PSegre Partition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
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
open ReciprocityTheory.ChartRestriction.G.Geo (segre)
namespace SegrePartition
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def segreSq (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) : ℝ := ‖segre z i‖ ^ 2
def segreSqSum (z : (Σ k, ι k) → ℂ) : ℝ := ∑ i, segreSq z i
def numIdx (ι : K → Type*) [∀ k, Fintype (ι k)] : ℝ := Fintype.card ((k : K) → ι k)
def bump (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) : ℝ :=
  Real.smoothTransition (2 * numIdx ι * (segreSq z i / segreSqSum z) - 1)
open Classical in

def rho (i : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if 0 < segreSqSum z then bump z i / ∑ j, bump z j else 1 / numIdx ι
end SegrePartition
end GroundTheory.Heights₂.Heights


