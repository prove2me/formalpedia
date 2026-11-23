-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
-- name    : GroundTheory_AutomorphicForms_GKModules_Garding
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:26.674214+00:00
-- url     : https://prove2.me/theorems/0c10298c-d0e6-4c7d-81ff-3079135db370
-- title:
--   Garding
-- statement:
--   Definitions and structural lemmas for Garding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/Garding.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open MeasureTheory NormedSpace Set Filter Topology Metric
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
noncomputable def BanachRep.integrated {K : Type*} [Group K] [TopologicalSpace K] [MeasurableSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep K E) (μ : Measure K)
    (f : K → ℂ) (v : E) : E :=
  ∫ g, f g • π g v ∂μ
namespace IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
def IsTestFunction (f : G → ℂ) : Prop :=
  (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) ∧ HasCompactSupport f
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (π : BanachRep G E)
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ]
end IsExpLieAlgebra
end GroundTheory.Automorphic


