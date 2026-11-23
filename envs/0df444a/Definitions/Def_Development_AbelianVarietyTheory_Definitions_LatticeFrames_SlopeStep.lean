-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_SlopeStep
-- name    : Development_AbelianVarietyTheory_Definitions_LatticeFrames_SlopeStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:12.292673+00:00
-- url     : https://prove2.me/theorems/e2ab017f-0d5d-4c63-9b52-2ec9b0df1601
-- title:
--   Slope Step
-- statement:
--   Definitions and structural lemmas for Slope Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/LatticeFrames/SlopeStep.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Core
open NumberField Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def Target (M : HLat K) : Prop := 0 < M.rank → M.muMaxDual ≤ 0
def IntoDual (N M : HLat K) (Φ : N.V →ₗ[K] Module.Dual K M.V) : Prop :=
  N.L.map (Φ.restrictScalars (𝓞 K)) ≤ M.dualL
def htPhi (N M : HLat K) (Φ : N.V →ₗ[K] Module.Dual K M.V) : ℝ :=
  Formalism.HN.htMap N.b N.X M.dualB M.dualX Φ
def HeightLe (N M : HLat K) (Φ : N.V →ₗ[K] Module.Dual K M.V) (h : ℝ) : Prop :=
  Φ ≠ 0 → htPhi N M Φ ≤ h
def RankHalf (N M : HLat K) (Φ : N.V →ₗ[K] Module.Dual K M.V) : Prop :=
  Module.finrank K N.V < 2 * Module.finrank K (LinearMap.range Φ)
def SlopeLe (N : HLat K) (h : ℝ) : Prop := 2 * N.mu - N.muMax ≤ h
def SlopeStep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (N M : HLat K)
    (Φ : N.V →ₗ[K] Module.Dual K M.V) (h : ℝ), N.Good → M.Good →
    Target M → IntoDual N M Φ → HeightLe N M Φ h → RankHalf N M Φ → SlopeLe N h
end GlobalTheory.Core
end


