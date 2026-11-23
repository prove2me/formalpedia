-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:28.346639+00:00
-- url     : https://prove2.me/theorems/66712149-9713-4932-8dc3-20cd58db6d0e
-- title:
--   Haar Exp B
-- statement:
--   Definitions and structural lemmas for Haar Exp B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/HaarExpB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.DS.HExp
open Filter Topology Metric NormedSpace Asymptotics
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
theorem hasStrictFDerivAt_exp_zero_alt : HasStrictFDerivAt (exp : 𝔸 → 𝔸)
    ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 :=
  hasStrictFDerivAt_exp_zero (𝕂 := ℝ)
variable (𝔸) in

def logA : 𝔸 → 𝔸 := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).localInverse _ _ _
def F1 (p : 𝔸 × 𝔸) : 𝔸 := logA 𝔸 (exp (-p.1) * exp (p.1 + p.2))
def F2 (p : 𝔸 × 𝔸) : 𝔸 := logA 𝔸 (exp p.1 * exp p.2)
end ReciprocityTheory.ChartRestriction.DS.HExp
noncomputable section
namespace ReciprocityTheory.ChartRestriction.DS.HExp
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
structure Chart (V : Submodule ℝ 𝔸) (G : Type*) [Group G] [TopologicalSpace G] where
  mat : G →* 𝔸
  emb : IsEmbedding mat
  H1 : ∀ X : V, ∃ g, mat g = exp (X : 𝔸)
  H2 : ∀ᶠ Z in 𝓝 (0 : 𝔸), (∃ g, mat g = exp Z) → Z ∈ V
namespace Chart
variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)
def expG (X : V) : G := (C.H1 X).choose
def img (s : Set V) : Set G := {g | ∃ X ∈ s, C.mat g = exp ((X : V) : 𝔸)}
variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace G] [BorelSpace G]
def nu (ρ : ℝ) (μ : Measure G) : Measure V :=
  (μ.comap (fun x : ball (0 : V) ρ => C.expG x.1)).map Subtype.val
variable (μ : Measure G)
variable [IsTopologicalGroup G] [μ.IsHaarMeasure]
end Chart
end ReciprocityTheory.ChartRestriction.DS.HExp


