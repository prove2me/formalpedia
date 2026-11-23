-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_SlopeStepG
-- name    : Development_AbelianVarietyTheory_Definitions_LatticeFrames_SlopeStepG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:49.345436+00:00
-- url     : https://prove2.me/theorems/9d7cb179-d44b-4557-b38f-cdf68f23f7f1
-- title:
--   Slope Step G
-- statement:
--   Definitions and structural lemmas for Slope Step G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/LatticeFrames/SlopeStepG.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_SlopeStep
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
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def MuMaxLe (B : HLat K) (c : ℝ) : Prop := 0 < B.rank → B.muMax ≤ c
def Into (N B : HLat K) (Ψ : N.V →ₗ[K] B.V) : Prop := ∀ x ∈ N.L, Ψ x ∈ B.L
def HtLe (N B : HLat K) (Ψ : N.V →ₗ[K] B.V) (h : ℝ) : Prop :=
  Ψ ≠ 0 → Formalism.HN.htMap N.b N.X B.b B.X Ψ ≤ h
def RkHalf (N B : HLat K) (Ψ : N.V →ₗ[K] B.V) : Prop :=
  Module.finrank K N.V < 2 * Module.finrank K (LinearMap.range Ψ)
def InPow {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K)) (n : ℤ)
    (A : Submodule (𝓞 K) V) (x : V) : Prop :=
  ∀ a : K, (a = 0 ∨ -n ≤ vAdd w a) → ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • (a • x) ∈ A
def SlopeStepG : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (N B : HLat K)
    (Ψ : N.V →ₗ[K] B.V) (h c : ℝ), N.Good → B.Good →
    MuMaxLe B c → Into N B Ψ → HtLe N B Ψ h → RkHalf N B Ψ → SlopeLe N (h + c)
end GlobalTheory.Core
end


