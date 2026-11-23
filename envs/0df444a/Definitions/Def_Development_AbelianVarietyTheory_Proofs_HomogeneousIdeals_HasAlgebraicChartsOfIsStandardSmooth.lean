-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:41.585451+00:00
-- url     : https://prove2.me/theorems/69bdd64d-fff2-4ca2-80a1-8809c1fba4fe
-- title:
--   Has Algebraic Charts Of Is Standard Smooth
-- statement:
--   Definitions and structural lemmas for Has Algebraic Charts Of Is Standard Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasAlgebraicChartsOfIsStandardSmooth.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial
open scoped Manifold ContDiff
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}
structure IsAlgebraicChart (e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜)) : Prop where
  exists_eq_div : ∃ (x : Fin d → A) (s : A), ∀ p ∈ e.source, p s ≠ 0 ∧ ∀ i, e p i = p (x i) / p s
  analyticOnNhd : ∀ a, AnalyticOnNhd 𝕜 (fun z => e.symm z a) e.target
variable (𝕜 A d) in

def HasAlgebraicCharts : Prop :=
  ∀ p : A →ₐ[𝕜] 𝕜, ∃ e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜),
    IsAlgebraicChart e ∧ p ∈ e.source
@[reducible]
noncomputable def HasAlgebraicCharts.chartedSpace (h : HasAlgebraicCharts 𝕜 A d) :
    ChartedSpace (Fin d → 𝕜) (A →ₐ[𝕜] 𝕜) where
  atlas := {e | IsAlgebraicChart e}
  chartAt p := (h p).choose
  mem_chart_source p := (h p).choose_spec.2
  chart_mem_atlas p := (h p).choose_spec.1
variable [CompleteSpace 𝕜]
section Detect
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
end Detect
end GlobalTheory.AffinePoints


