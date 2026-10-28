-- Prove2me | Definitions.Def_OAIQ070A008
-- name    : OAIQ070A008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T11:20:23.251394+00:00
-- url     : https://prove2.me/theorems/1d03416b-fefe-4c74-a27f-668199b65660
-- title:
--   Definitions bundle OAIQ070A008 of the split of OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 43 declarations of OpenAI's Lean: 41 definitions and 2 theorems. The definitions and types are `OAI.YauCounterexamples.sphericalExterior`, `OAI.YauCounterexamples.sphericalWeight`, `OAI.YauCounterexamples.spnFormSpace`, `OAI.YauCounterexamples.supportedPinningTensor`, `OAI.YauCounterexamples.threeAmbientNormedSpace'`, `OAI.YauCounterexamples.threeAnalyticNormedSpace`, `OAI.YauCounterexamples.threeAssemblyNormedSpace`, `OAI.YauCounterexamples.threeCenterNormedSpace`, `OAI.YauCounterexamples.threeCenteredWaveNormedSpace`, `OAI.YauCounterexamples.threeChartNormedSpace`, `OAI.YauCounterexamples.threeCircleDirection`, `OAI.YauCounterexamples.threeComplexPower`, `OAI.YauCounterexamples.threeCoupledNormedSpace`, `OAI.YauCounterexamples.threeFirstNormedSpace`, `OAI.YauCounterexamples.threeGlobalResidualNormedSpace`, `OAI.YauCounterexamples.threeInteriorMeridianAmbient`, `OAI.YauCounterexamples.threeInteriorMeridianNormedSpace`, `OAI.YauCounterexamples.threeJetDualNorm`, `OAI.YauCounterexamples.threeJetDualSpace`, `OAI.YauCounterexamples.threeLiftNormedSpace`, `OAI.YauCounterexamples.threeLocalNormedSpace`, `OAI.YauCounterexamples.threeLogNormedSpace`, `OAI.YauCounterexamples.threeModelNormedSpace`, `OAI.YauCounterexamples.threeModelNormedSpace'`, `OAI.YauCounterexamples.threeNbDualNorm`, `OAI.YauCounterexamples.threeNbDualSpace`, `OAI.YauCounterexamples.threeNbFormNorm`, `OAI.YauCounterexamples.threeNbFormSpace`, `OAI.YauCounterexamples.threeNeighborNormedSpace`, `OAI.YauCounterexamples.threeNoncancelNormedSpace`, `OAI.YauCounterexamples.threeNormalEnvelopeNormedSpace`, `OAI.YauCounterexamples.threePacketNormedSpace`, `OAI.YauCounterexamples.threePower`, `OAI.YauCounterexamples.threeProjectionNormedSpace`, `OAI.YauCounterexamples.threeRadiusNormedSpace`, `OAI.YauCounterexamples.threeResidualNormedSpace`, `OAI.YauCounterexamples.threeRobustNormedSpace`, `OAI.YauCounterexamples.threeRobustProfileNormedSpace`, `OAI.YauCounterexamples.threeSphereDirection`, `OAI.YauCounterexamples.threeWeightedNormedSpace` and 1 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `SmoothYau_Estimates_SphericalPinFormNorm`, `SmoothYau_Estimates_ThreeNoncancelNormedSpace`, `SmoothYau_Geometry_ThreeDirectionsNormedSpace`, `SmoothYau_Geometry_ThreeLogNormedSpace`, `SmoothYau_Geometry_ThreeProjectionNormedSpace`, `SmoothYau_Limits_CoordinateForm`, `SmoothYau_ProductMetric_ThreeInteriorMeridianNormedSpace`, `SmoothYau_Smoothness_BundleRankOne`, `SmoothYau_Smoothness_ContinuousCompactSmoothJets`, `SmoothYau_Smoothness_ThreeCoupledCleanChartJets`, `SmoothYau_Smoothness_ThreeFirstNormedSpace`, `SmoothYau_Smoothness_ThreeRadiusNormedSpace`, `SmoothYau_Spectrum_ProductFrequencyTop`, `SmoothYau_Spectrum_ThreeCoupledNormedSpace`, `SmoothYau_SphereMetric_ExistsThreeScalarProducer`, `SmoothYau_SphereMetric_FourThree`, `SmoothYau_SphereMetric_ThreeAnalyticNormedSpace`, `SmoothYau_SphereMetric_ThreeExceptional`, `SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace`.
--
--   **Imports.** It imports the published bundle `Def_SmoothYau`; the bundles `OAIQ070A002`, `OAIQ070A003` and `OAIQ070A004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ070A010`, `OAIQ070A012` and `OAIQ070A013`; the statements `OAI.YauCounterexamples.annular_eigenfunction_separating_tensor`, `OAI_YauCounterexamples_compact_normal_forward_bound`, `OAI.YauCounterexamples.exists_local_metric_radial_patch`, `OAI.YauCounterexamples.exists_spherical_global_quasimodes`, `OAI.YauCounterexamples.exists_supported_separating_tensor`, `OAI_YauCounterexamples_exists_threeCoupled_interior_gradient_rank`, `OAI_YauCounterexamples_exists_three_radial_cutoff`, `OAI_YauCounterexamples_four_signCertificate_bound`, `OAI_YauCounterexamples_source_baseProfile_sign_gradient`, `OAI_YauCounterexamples_sphere_quadratic_profile_hessian`, `OAI_YauCounterexamples_sphericalBaseProfile_neighborhood`, `OAI.YauCounterexamples.spherical_global_jet_lower`, `OAI_YauCounterexamples_spherical_sign_nodal_real`, `OAI.YauCounterexamples.spherical_wave_background_chart_bounds`, `OAI_YauCounterexamples_spherical_wave_lift_jets`, `OAI_YauCounterexamples_threeCoupled_clean_gradient_lower`, `OAI_YauCounterexamples_threeCoupled_gradient_chart_analytic`, `OAI_YauCounterexamples_threeCoupled_profile_rank_dense`, `OAI_YauCounterexamples_threePower_eigen` and `OAI.YauCounterexamples.three_rank_separating_tensor`; the proofs of `OAI.YauCounterexamples.annular_eigenfunction_separating_tensor`, `OAI.YauCounterexamples.exists_spherical_global_quasimodes`, `OAI.YauCounterexamples.exists_spherical_scalar_producer`, `OAI.YauCounterexamples.exists_supported_separating_tensor`, `OAI_YauCounterexamples_exists_three_radial_cutoff`, `OAI.YauCounterexamples.four_nodal_finite`, `OAI_YauCounterexamples_source_baseProfile_sign_gradient`, `OAI.YauCounterexamples.spherical_global_jet_lower`, `OAI_YauCounterexamples_spherical_sign_nodal_real`, `OAI.YauCounterexamples.spherical_wave_background_chart_bounds`, `OAI_YauCounterexamples_threeCoupled_clean_gradient_lower` and `OAI.YauCounterexamples.three_rank_separating_tensor`.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A002
import Definitions.Def_OAIQ070A003
import Definitions.Def_OAIQ070A004

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CoordinateForm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def twoCoframeForm (D : E →L[ℝ] (ℝ × ℝ)) : CoordinateForm E :=
  let l := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp D
  let r := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp D
  l.smulRight l + r.smulRight r

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContinuousCompactSmoothJets
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {n : ℕ}
attribute [local instance] OAI.YauCounterexamples.spnENorm
attribute [local instance] OAI.YauCounterexamples.spnESpace
attribute [local instance] OAI.YauCounterexamples.spnDualNorm
attribute [local instance] OAI.YauCounterexamples.spnDualSpace
local instance spnFormSpace : NormedSpace ℝ (CoordinateForm (Euclidean n)) := inferInstance


end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_BundleRankOne
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def supportedPinningTensor (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M) :
    TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x :=
  let p := fun x => bundleTransverse g u x (metricGradient g v x)
  χ x • (bundleRankOne g p x - (g.inner x (p x) (p x) /2) • bundleTransverse g u x)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_FourThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
local instance threeModelNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
lemma three_chart_target (p : ThreeManifold) : (chartAt ThreeModel p).target = univ := by
  change ( (chartAt ThreeProductModel p).trans threeModelEquiv.toHomeomorph.toOpenPartialHomeomorph ).target = _
  simp only [OpenPartialHomeomorph.trans_target,Homeomorph.toOpenPartialHomeomorph_target,
    univ_inter]
  have h : (chartAt ThreeProductModel p).target = univ := by
    change (chartAt (Euclidean 2) p.1).target ×ˢ (chartAt (Euclidean 1) p.2).target = univ
    have hc : (chartAt (Euclidean 1) p.2).target = univ := by
      change (stereographic' 1 (-p.2)).target = univ
      exact stereographic'_target (-p.2)
    rw [sphere_chart_target,hc,univ_prod_univ]
  rw [h,preimage_univ]
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ProductFrequencyTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
local instance threeModelNormedSpace' : NormedSpace ℝ ThreeModel := inferInstance

local instance threeAmbientNormedSpace' : NormedSpace ℝ ThreeAmbient := inferInstance


def threeComplexPower (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) : ℂ :=
  (planarLinear a b (p.1:Euclidean 3))^k*(p.2:ℂ)^k
def threePower (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) : ℝ :=
  (threeComplexPower a b k p).re
end


open Set Filter Function Manifold
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_SphericalPinFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions
def sphericalExterior (g₀ g : SmoothMetric (Euclidean 3) (Sphere 3)) (R : ℝ) : Prop :=
  ∀ q, R < sphericalRadius sourceAxisOne sourceAxisTwo q → g.inner q=g₀.inner q
lemma sphericalExterior_mono {g₀ g : SmoothMetric (Euclidean 3) (Sphere 3)}
    {R S : ℝ} (h : R ≤ S) (he : sphericalExterior g₀ g R) : sphericalExterior g₀ g S :=
  fun q hq => he q (h.trans_lt hq)
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeFirstNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeFirstNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ThreeCoupledNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeCoupledNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ThreeDirectionsNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
attribute [local instance] OAI.YauCounterexamples.threeDirections_dimension_fact
def threeSphereDirection (p : ThreeManifold) (i : Fin 3) : ThreeModel :=
  WithLp.toLp 2 (unitSphereCoordinates (n:=2) p.1 (productAxis i),0)
def threeCircleDirection (p : ThreeManifold) : ThreeModel :=
  WithLp.toLp 2 (0,unitSphereCoordinates (n:=1) p.2 (Complex.I*(p.2:ℂ)))
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ThreeNoncancelNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
local instance threeNoncancelNormedSpace : NormedSpace ℝ ThreeModel := inferInstance

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeRadiusNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
local instance threeChartNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
local instance threeRadiusNormedSpace : NormedSpace ℝ ThreeModel := inferInstance

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ThreeLogNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
local instance threeLogNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace

local instance threeLocalNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
end


section
open Set Filter Function Manifold MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
local instance threeCenterNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace
local instance threeNormalEnvelopeNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
end


section
open Set Filter Manifold Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise
local instance threeNeighborNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeNeighborContinuousSMul_r5c8d16_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance threeNbDualNorm : NormedAddCommGroup (ThreeModel →L[ℝ] ℝ) := inferInstance
local instance threeNbDualSpace : NormedSpace ℝ (ThreeModel →L[ℝ] ℝ) := inferInstance
local instance threeNbFormNorm : NormedAddCommGroup (CoordinateForm ThreeModel) := inferInstance
local instance threeNbFormSpace : NormedSpace ℝ (CoordinateForm ThreeModel) := inferInstance

end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace
local instance threeRobustNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace
local instance threeRobustProfileNormedSpace : NormedSpace ℝ ThreeModel := inferInstance

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ThreeProjectionNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
local instance threeProjectionNormedSpace : NormedSpace ℝ ThreeModel := inferInstance

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_ProductMetric_ThreeInteriorMeridianNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeInteriorMeridianNormedSpace : NormedSpace ℝ ThreeModel := inferInstance

def threeInteriorMeridianAmbient (t : ℝ) : Euclidean 3 := Real.cos t • productAxis 1+Real.sin t • productAxis 2

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeCoupledCleanChartJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Manifold
open scoped Topology ContDiff

def sphericalWeight (φ : Sphere 3 → ℝ) (n : ℕ) (q : Sphere 3) : ℝ :=
  Real.exp ((n:ℝ)*φ q)+‖planarLinear sourceAxisOne sourceAxisTwo q‖^n

end


section
open Set Filter Function Manifold Metric MeasureTheory
open scoped Topology ContDiff InnerProductSpace
local instance threeWeightedNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
local instance threeResidualNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeExceptional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
local instance threePacketNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
end


open Set Filter Function Manifold Metric
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ExistsThreeScalarProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
local instance threeLiftNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
local instance threeGlobalResidualNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
local instance threeAssemblyNormedSpace : NormedSpace ℝ ThreeModel := inferInstance

end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
local instance threeCenteredWaveNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
local instance threeJetDualNorm : NormedAddCommGroup (ThreeModel →L[ℝ] ℝ) := inferInstance
local instance threeJetDualSpace : NormedSpace ℝ (ThreeModel →L[ℝ] ℝ) := inferInstance
end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeAnalyticNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeAnalyticNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
end YauCounterexamples
end

end OAI
end


