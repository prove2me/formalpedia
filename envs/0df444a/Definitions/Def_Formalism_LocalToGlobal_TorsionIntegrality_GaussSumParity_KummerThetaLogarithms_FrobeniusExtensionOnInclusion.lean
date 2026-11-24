-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:02.336931+00:00
-- url     : https://prove2.me/theorems/e37af2a1-6762-4148-a400-5d0ab78e395a
-- title:
--   Frobenius Extension On Inclusion
-- statement:
--   Definitions and structural lemmas for Frobenius Extension On Inclusion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusExtensionOnInclusion.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
namespace KF
section Norms
variable (l : ℕ) [hl : Fact l.Prime]
variable {l}
end Norms
end KF
open KF
namespace KF
section Extend
variable (l : ℕ) [hl : Fact l.Prime]
lemma ringA_le_ringB : ringA l ≤ ringB l := Subring.le_topologicalClosure _
def incAB : ringA l →+* ringB l := Subring.inclusion (ringA_le_ringB l)
lemma incAB_unif : IsUniformInducing (incAB l) := by
  have h1 : IsUniformInducing ((↑) : ringB l → ℂ_[l]) := isUniformEmbedding_subtype_val.isUniformInducing
  rw [← h1.of_comp_iff]
  exact isUniformEmbedding_subtype_val.isUniformInducing
lemma incAB_dense : DenseRange (incAB l) := by
  unfold DenseRange
  rw [Subtype.dense_iff]
  intro x hx
  have hsub : (ringA l : Set ℂ_[l]) ⊆ Subtype.val '' Set.range (incAB l) :=
    fun y hy => ⟨incAB l ⟨y, hy⟩, ⟨_, rfl⟩, rfl⟩
  exact closure_mono hsub hx
variable {l}
variable (σ0 : ringA l →+* ringA l) (hiso : ∀ x : ringA l, ‖(σ0 x : ℂ_[l])‖ = ‖(x : ℂ_[l])‖)
def sigF : ringA l →+* ℂ_[l] := (ringA l).subtype.comp σ0
include hiso in
lemma sigF_unif : UniformContinuous (sigF σ0) := by
  apply Isometry.uniformContinuous
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  exact hiso x
def sig1 : ringB l →+* ℂ_[l] :=
  IsDenseInducing.extendRingHom (incAB_unif l) (incAB_dense l) (sigF_unif σ0 hiso)
def jBK (hB : ∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1) : ringB l →+* MaximalUnramifiedExtension l :=
  (ringB l).subtype.codRestrict (MaximalUnramifiedExtension l) (fun x => by
    rw [Subring.subtype_apply]
    exact ((hB x).1 x.2).1)
end Extend
end KF
end Formalism.L2.Th1.D


