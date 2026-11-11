-- Prove2me | Definitions.Def_OAIQ232A000
-- name    : OAIQ232A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:41:38.735203+00:00
-- url     : https://prove2.me/theorems/44d0117c-8a37-40e4-8dc5-cedd7e1ff473
-- title:
--   Definitions bundle OAIQ232A000 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 123 declarations of OpenAI's Lean: 60 definitions, 3 inductive types or structures, 6 instances and 54 theorems. The definitions and types are `Convexity.StdSimplex.equivIcc`, `Convexity.StdSimplex.homeomorphI`, `Convexity.StdSimplex.subBarycenter`, `Convexity.StdSimplex.topologicalSpaceInduced`, `OAI.WeakMTWTransport.CenterSequenceData`, `OAI.WeakMTWTransport.CenterSequenceData.comp`, `OAI.WeakMTWTransport.ChartFixedPrefixLimit`, `OAI.WeakMTWTransport.ConvexProximal.energy`, `OAI.WeakMTWTransport.ConvexProximal.prox`, `OAI.WeakMTWTransport.EnvelopeData`, `OAI.WeakMTWTransport.HasLowerSecondTaylor`, `OAI.WeakMTWTransport.HasPowerUpperBound`, `OAI.WeakMTWTransport.HasQuadraticExpansion`, `OAI.WeakMTWTransport.HasSecondTaylor`, `OAI.WeakMTWTransport.IsCostDualPair`, `OAI.WeakMTWTransport.IsMetricChain`, `OAI.WeakMTWTransport.IsSemiconvexSubgradientOn`, `OAI.WeakMTWTransport.IsSubgradientOn`, `OAI.WeakMTWTransport.TrueCenterRow`, `OAI.WeakMTWTransport.UnitTime`, `OAI.WeakMTWTransport.activeLogs`, `OAI.WeakMTWTransport.cTransform`, `OAI.WeakMTWTransport.chartFiberInverse`, `OAI.WeakMTWTransport.completeFlow`, `OAI.WeakMTWTransport.contactGap`, `OAI.WeakMTWTransport.coordinateBackward`, `OAI.WeakMTWTransport.coordinateCenterMatrix`, `OAI.WeakMTWTransport.coordinateChristoffel`, `OAI.WeakMTWTransport.coordinateGeodesicField`, `OAI.WeakMTWTransport.coordinatePoleMatrix`, `OAI.WeakMTWTransport.coordinateScalarSupport`, `OAI.WeakMTWTransport.coordinateTangentLift`, `OAI.WeakMTWTransport.fixedJoinAction`, `OAI.WeakMTWTransport.fixedJoinMiddle`, `OAI.WeakMTWTransport.geodesicSpray`, `OAI.WeakMTWTransport.graphBaseCoordinate`, `OAI.WeakMTWTransport.graphVelocityCoordinate`, `OAI.WeakMTWTransport.hopfLax`, `OAI.WeakMTWTransport.instNormedAddCommGroupContinuousLinearMapRealId_solutions`, `OAI.WeakMTWTransport.instNormedAddCommGroupContinuousLinearMapRealId_solutions_1` and 23 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Calculus_FullSet`, `BiholderTransport_Calculus_HopfGradient`, `BiholderTransport_Calculus_PartialDerivatives`, `BiholderTransport_Calculus_PathCalculus`, `BiholderTransport_Contact_CenterSupportFamily`, `BiholderTransport_Contact_CoordinateScalarSupport`, `BiholderTransport_Contact_GraphProjection`, `BiholderTransport_Contact_Subgradient`, `BiholderTransport_Contact_SubgradientDifferential`, `BiholderTransport_Convexity_ActualCenterSemibound`, `BiholderTransport_Convexity_EnvelopeData`, `BiholderTransport_Convexity_UniformEnvelope`, `BiholderTransport_Coordinates_ActiveHull`, `BiholderTransport_Coordinates_ChartTransition`, `BiholderTransport_Coordinates_CoordinateMatrices`, `BiholderTransport_Coordinates_CoordinatePole`, `BiholderTransport_Coordinates_Coordinates`, `BiholderTransport_Coordinates_GraphCoordinates`, `BiholderTransport_Coordinates_ManifoldMinimum`, `BiholderTransport_Coordinates_NormalCoordinates3`, `BiholderTransport_Coordinates_NormalEndpointJoin`, `BiholderTransport_Coordinates_NormalSubdifferential`, `BiholderTransport_Coordinates_PoleCoordinates`, `BiholderTransport_Coordinates_TangentLift`, `BiholderTransport_Geodesics_GeodesicBasics`, `BiholderTransport_Geodesics_GeodesicSpray`, `BiholderTransport_Geodesics_MetricSegments`, `BiholderTransport_LinearAlgebra_ChartFirstMatrix`, `BiholderTransport_LinearAlgebra_HessianMixedOperator`, `BiholderTransport_LinearAlgebra_LowerTaylor`, `BiholderTransport_LinearAlgebra_MixedOperator`, `BiholderTransport_LocalFlow_SmoothIntegralCurve`, `BiholderTransport_MinimizingVectors`, `BiholderTransport_Oscillation_SectionOscillation`, `BiholderTransport_Regularity_BundleSeparation`, `BiholderTransport_Regularity_CenterSequenceCompact`, `BiholderTransport_Regularity_EuclideanUpper`, `BiholderTransport_Regularity_MetricDefinitions`, `BiholderTransport_Regularity_MovingPrefix`, `BiholderTransport_Regularity_ShortForward`, `BiholderTransport_Regularity_StationaryPullback`, `BiholderTransport_Regularity_UnitTime`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ232A006`, `OAIQ232A007`, `OAIQ232A009`, `OAIQ232A011` and `OAIQ232A012`; the statements `OAI.WeakMTWTransport.CenterSequenceData.regular_compact`, `OAI.WeakMTWTransport.cTransform_ae_active_before_cut`, `OAI.WeakMTWTransport.cTransform_ae_normal_quadraticExpansion`, `OAI.WeakMTWTransport.exists_actual_center_sequential_gain`, `OAI.WeakMTWTransport.exists_reverse_exp_divided_isotropic_gain`, `OAI.WeakMTWTransport.exists_uniform_cost_upper_taylor`, `OAI.WeakMTWTransport.original_chart_good_null` and `OAI.WeakMTWTransport.uniform_family_short_mdifferentiable`.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport

section
-- module Solutions.OAIQ232_BH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_FullSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def HasSecondTaylor (f : E → ℝ) (l : E →L[ℝ] ℝ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  (fun h => f h-f 0-l h-B h h/2) =o[𝓝 0] (fun h : E => ‖h‖^2)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ManifoldMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma IsLocalMin.mfderiv_eq_zero {f : M → ℝ} {x : M}
    (h : IsLocalMin f x) (hd : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f x) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f x = 0 := by
  let c := extChartAt 𝓘(ℝ,E) x
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,E)) x
  have hc : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ c.symm (c x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (c.map_source hx))
  let F : E → ℝ := fun q => f (c.symm q)
  have hF : DifferentiableAt ℝ F (c x) := by
    have hd' : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f (c.symm (c x)) := by
      rw [c.left_inv hx]; exact hd
    exact (hd'.comp (c x) (hc.mdifferentiableAt (by simp))).differentiableAt
  have hmin : IsLocalMin F (c x) := by
    have hc' : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
      have H := hc.continuousAt.tendsto
      rw [c.left_inv hx] at H
      exact H
    filter_upwards [hc'.eventually h] with q hq
    simpa only [F,c.left_inv hx] using hq
  have hzero : HasFDerivAt F 0 (c x) :=
    hF.hasFDerivAt.congr_fderiv (hmin.hasFDerivAt_eq_zero hF.hasFDerivAt)
  have H := hzero.hasMFDerivAt.comp x
    (mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (show x ∈ (chartAt E x).source from mem_chart_source E x)).hasMFDerivAt
  have heq : f =ᶠ[𝓝 x] (fun y : M => F (c y)) := by
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ,E)) x] with y hy
    dsimp [F]; rw [c.left_inv hy]
  rw [(H.congr_of_eventuallyEq heq).mfderiv]
  ext v
  rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance instNormedSpaceReal_solutions : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_2 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_2 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def coordinateChristoffel (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x u v : E) : E :=
  (g x).inverse ((1/2:ℝ) •
    ((fderiv ℝ g x) u v + (fderiv ℝ g x) v u -
      (((fderiv ℝ g x).flip u).flip v)))

lemma coordinateChristoffel_metric (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u v w : E) (hg : (g x).IsInvertible) :
    2 * g x (coordinateChristoffel g x u v) w =
      (fderiv ℝ g x) u v w + (fderiv ℝ g x) v u w - (fderiv ℝ g x) w u v := by
  rw [coordinateChristoffel,hg.self_apply_inverse]
  simp only [smul_apply,sub_apply,add_apply,flip_apply,smul_eq_mul]
  ring

def coordinateGeodesicField (g : E → E →L[ℝ] E →L[ℝ] ℝ) (z : E × E) : E × E :=
  (z.2,-coordinateChristoffel g z.1 z.2 z.2)

lemma contDiffAt_coordinateChristoffel [CompleteSpace E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {x u v : E}
    (hg : ContDiffAt ℝ ∞ g x) (hi : (g x).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : E × E × E => coordinateChristoffel g z.1 z.2.1 z.2.2)
      (x,u,v) := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ g) x := hg.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hinv : ContDiffAt ℝ ∞ (fun x => (g x).inverse) x :=
    hi.contDiffAt_map_inverse.comp x hg
  have hf1 : ContDiffAt ℝ ∞ (fun x => (fderiv ℝ g x).flip) x :=
    hd.continuousLinearMap_comp
      (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearEquiv.toContinuousLinearMap
  have hx : ContDiffAt ℝ ∞ (fun z : E × E × E => z.1) (x,u,v) := contDiffAt_fst
  have hu : ContDiffAt ℝ ∞ (fun z : E × E × E => z.2.1) (x,u,v) :=
    contDiffAt_fst.comp (x,u,v) contDiffAt_snd
  have hv : ContDiffAt ℝ ∞ (fun z : E × E × E => z.2.2) (x,u,v) :=
    contDiffAt_snd.comp (x,u,v) contDiffAt_snd
  have hfc : ContDiffAt ℝ ∞ (fun z : E × E × E => (fderiv ℝ g z.1).flip)
      (x,u,v) := ContDiffAt.comp
        (g := fun y : E => (fderiv ℝ g y).flip)
        (f := fun z : E × E × E => z.1) (x,u,v) hf1 hx
  have hfu : ContDiffAt ℝ ∞ (fun z : E × E × E => (fderiv ℝ g z.1).flip z.2.1)
      (x,u,v) := hfc.clm_apply hu
  have hfu' : ContDiffAt ℝ ∞ (fun z : E × E × E => ((fderiv ℝ g z.1).flip z.2.1).flip)
      (x,u,v) := hfu.continuousLinearMap_comp
        (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hf2 : ContDiffAt ℝ ∞ (fun z : E × E × E =>
      (((fderiv ℝ g z.1).flip z.2.1).flip z.2.2)) (x,u,v) := hfu'.clm_apply hv
  have hduv : ContDiffAt ℝ ∞ (fun z : E × E × E => (fderiv ℝ g z.1) z.2.1 z.2.2)
      (x,u,v) := ((hd.comp (x,u,v) hx).clm_apply hu).clm_apply hv
  have hdvu : ContDiffAt ℝ ∞ (fun z : E × E × E => (fderiv ℝ g z.1) z.2.2 z.2.1)
      (x,u,v) := ((hd.comp (x,u,v) hx).clm_apply hv).clm_apply hu
  exact (hinv.comp (x,u,v) hx).clm_apply
    (((hduv.add hdvu).sub hf2).const_smul (1/2:ℝ))

lemma contDiffAt_coordinateGeodesicField [CompleteSpace E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {x v : E}
    (hg : ContDiffAt ℝ ∞ g x) (hi : (g x).IsInvertible) :
    ContDiffAt ℝ ∞ (coordinateGeodesicField g) (x,v) := by
  have hΓ : ContDiffAt ℝ ∞ (fun z : E × E => coordinateChristoffel g z.1 z.2 z.2) (x,v) :=
    (contDiffAt_coordinateChristoffel (u := v) (v := v) hg hi).comp (x,v)
      (contDiffAt_fst.prodMk (contDiffAt_snd.prodMk contDiffAt_snd))
  exact contDiffAt_snd.prodMk hΓ.neg

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_TangentLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance tangentLiftNormedSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance tangentLiftNormedAddCommGroupEndomorphism : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup

local instance tangentLiftNormedSpaceEndomorphism_r69274c_1 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance tangentLiftNormedSpaceDual_r69274c_1 : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance tangentLiftNormedAddCommGroupDual_r69274c_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance tangentLiftNormedAddCommGroupBilinear_r69274c_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance tangentLiftNormedSpaceBilinear_r69274c_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
def coordinateTangentLift (φ : E → E) (z : E × E) : E × E :=
  (φ z.1, fderiv ℝ φ z.1 z.2)

end

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

local instance tangentLiftContinuousAddCotangent : ∀ x : M, ContinuousAdd (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
  fun _ => inferInstance
local instance tangentLiftContinuousSMulCotangent : ∀ x : M, ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
  fun _ => inferInstance

def riemannianCoordinateMetric (a : M) (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let y := (extChartAt 𝓘(ℝ,E) a).symm z
  let L := (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ y
  (innerSL ℝ (E := TangentSpace 𝓘(ℝ,E) y)).bilinearComp L L

lemma riemannianCoordinateMetric_apply (a : M) (z u v : E) :
    riemannianCoordinateMetric a z u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) a).symm z) u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) a).symm z) v) := rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_PathCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
universe u w
variable {K : Type w} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance pathCalculusNormedAddCommGroupContinuousLinearMap :
    NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_UnitTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
abbrev UnitTime := Icc (0:ℝ) 1
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance instFactLeRealOfNat_solutions : Fact ((0:ℝ) ≤ 1) := ⟨zero_le_one⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma hasFDerivAt_chart_transition {a b x : M}
    (ha : x ∈ (extChartAt 𝓘(ℝ,E) a).source)
    (hb : x ∈ (extChartAt 𝓘(ℝ,E) b).source) :
    HasFDerivAt (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm)
      (tangentCoordChange 𝓘(ℝ,E) a b x) (extChartAt 𝓘(ℝ,E) a x) := by
  simpa only [ModelWithCorners.range_eq_univ,hasFDerivWithinAt_univ] using
    hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℝ,E)) ⟨ha,hb⟩

lemma contDiffAt_chart_transition {a b x : M}
    (ha : x ∈ (extChartAt 𝓘(ℝ,E) a).source)
    (hb : x ∈ (extChartAt 𝓘(ℝ,E) b).source) :
    ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm)
      (extChartAt 𝓘(ℝ,E) a x) := by
  have h1 := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) a).contMDiffAt
    ((isOpen_extChartAt_target a).mem_nhds ((extChartAt 𝓘(ℝ,E) a).map_source ha))
  have h2 := (contMDiffOn_extChartAt (I := 𝓘(ℝ,E)) (n := ∞) (x := b)).contMDiffAt
    (by simpa only [extChartAt_source] using ((isOpen_extChartAt_source b).mem_nhds hb))
  have h2' : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (extChartAt 𝓘(ℝ,E) b)
      ((extChartAt 𝓘(ℝ,E) a).symm (extChartAt 𝓘(ℝ,E) a x)) := by
    rwa [(extChartAt 𝓘(ℝ,E) a).left_inv ha]
  exact (h2'.comp _ h1).contDiffAt

lemma chart_transition_derivative_surjective {a b x : M}
    (ha : x ∈ (extChartAt 𝓘(ℝ,E) a).source)
    (hb : x ∈ (extChartAt 𝓘(ℝ,E) b).source) :
    Function.Surjective (fderiv ℝ
      (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm)
      (extChartAt 𝓘(ℝ,E) a x)) := by
  rw [(hasFDerivAt_chart_transition ha hb).fderiv]
  intro v
  refine ⟨tangentCoordChange 𝓘(ℝ,E) b a x v,?_⟩
  rw [tangentCoordChange_comp ⟨⟨hb,ha⟩,hb⟩,tangentCoordChange_self hb]

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_GeodesicBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold 𝓘(ℝ, Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]

omit [IsManifold 𝓘(ℝ, Model n) ∞ M] in
lemma isGeodesic_zero (x : M) : IsGeodesicWithInitialData (n := n) x 0 (fun _ => x) := by
  refine ⟨contMDiff_const, ?_, ?_⟩
  · simp only [mfderiv_const]
    rfl
  · intro t
    refine ⟨1, by norm_num, ?_⟩
    intro s u _ _
    simp

omit [IsManifold 𝓘(ℝ, Model n) ∞ M] in
lemma geodesic_initial_point {x : M} {v : TangentSpace 𝓘(ℝ, Model n) x}
    {gamma : ℝ → M} (h : IsGeodesicWithInitialData x v gamma) : gamma 0 = x := by
  exact congrArg (fun p : TangentBundle 𝓘(ℝ, Model n) M => p.proj) h.2.1

omit [IsManifold 𝓘(ℝ, Model n) ∞ M] in

lemma geodesic_zero_eq_const {x : M} {gamma : ℝ → M}
    (h : IsGeodesicWithInitialData (n := n) x 0 gamma) : gamma = fun _ => x := by
  have hl : IsLocallyConstant gamma := by
    rw [IsLocallyConstant.iff_exists_open]
    intro t
    obtain ⟨eps, heps, hh⟩ := h.2.2 t
    refine ⟨Metric.ball t eps, Metric.isOpen_ball, Metric.mem_ball_self heps, ?_⟩
    intro s hs
    apply dist_eq_zero.mp
    simpa only [norm_zero, mul_zero] using
      hh s t (by simpa only [Metric.mem_ball, Real.dist_eq] using hs) (by simpa using heps)
  funext t
  exact (hl.apply_eq_of_preconnectedSpace t 0).trans (geodesic_initial_point h)

omit [IsManifold 𝓘(ℝ, Model n) ∞ M] in
@[simp] lemma riemannianExp_zero (x : M) : riemannianExp (n := n) x 0 = x := by
  have hex : ∃ gamma, IsGeodesicWithInitialData (n := n) x 0 gamma := ⟨_, isGeodesic_zero (n := n) x⟩
  rw [riemannianExp, dite_eq_left hex]
  exact congrFun (geodesic_zero_eq_const (Classical.choose_spec hex)) 1

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_GeodesicSpray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

namespace WeakMTWTransport
open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

variable [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

def geodesicSpray (z : TangentBundle 𝓘(ℝ,E) M) :
    TangentSpace (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z :=
  coordinateGeodesicField (riemannianCoordinateMetric z.1)
    (extChartAt 𝓘(ℝ,E) z.1 z.1,z.2)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_BundleSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle

namespace WeakMTWTransport
variable {B F : Type*} [TopologicalSpace B] [T2Space B]
  [TopologicalSpace F] [T2Space F] {E : B → Type*} [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]

lemma bundle_totalSpace_t2 : T2Space (TotalSpace F E) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro x y hxy
  by_cases hb : x.proj = y.proj
  · let e := trivializationAt F E x.proj
    have hx : x ∈ e.source := e.mem_source.mpr (mem_baseSet_trivializationAt F E x.proj)
    have hy : y ∈ e.source := e.mem_source.mpr (hb ▸ mem_baseSet_trivializationAt F E x.proj)
    have he : e x ≠ e y := fun h => hxy (e.toOpenPartialHomeomorph.injOn hx hy h)
    exact (e.toOpenPartialHomeomorph.continuousAt hx).disjoint
      (disjoint_nhds_nhds.mpr he) (e.toOpenPartialHomeomorph.continuousAt hy)
  · exact (FiberBundle.continuous_proj F E).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hb) (FiberBundle.continuous_proj F E).continuousAt

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_SmoothIntegralCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [HasContDiffBump E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]
  {v : (x : M) → TangentSpace I x}

variable (hc : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)

omit [CompleteSpace E] [HasContDiffBump E] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
noncomputable def completeFlow (t : ℝ) (x : M) : M := Classical.choose (hc x) t

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_MinimizingVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold 𝓘(ℝ, Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]

def minimizingVectors (x : M) : Set (TangentSpace 𝓘(ℝ, Model n) x) :=
  {p | dist x (riemannianExp x p) = ‖p‖}

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_MetricSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

namespace WeakMTWTransport
variable {M : Type*} [MetricSpace M]

def IsMetricChain (x y : M) (A : Set (ℝ × M)) : Prop :=
  (0,x) ∈ A ∧ (dist x y,y) ∈ A ∧
  A ⊆ Icc 0 (dist x y) ×ˢ univ ∧
  ∀ u ∈ A, ∀ v ∈ A, dist u.2 v.2 = |u.1-v.1|

lemma IsMetricChain.closure {x y : M} {A : Set (ℝ × M)}
    (hA : IsMetricChain x y A) : IsMetricChain x y (closure A) := by
  refine ⟨subset_closure hA.1,subset_closure hA.2.1,
    closure_minimal hA.2.2.1 (isClosed_Icc.prod isClosed_univ),?_⟩
  intro u hu v hv
  have hvA (w : ℝ × M) (hw : w ∈ A) : dist w.2 v.2 = |w.1-v.1| := by
    have hc : IsClosed {v : ℝ × M | dist w.2 v.2 = |w.1-v.1|} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact closure_minimal (fun z hz => hA.2.2.2 w hw z hz) hc hv
  have hc : IsClosed {u : ℝ × M | dist u.2 v.2 = |u.1-v.1|} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  exact closure_minimal hvA hc hu

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MetricDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

variable {M : Type*} [MetricSpace M]

def cTransform (v : M → ℝ) (x : M) : ℝ :=
  sSup (Set.range (fun y => -cost x y - v y))

def IsCostDualPair (u v : M → ℝ) : Prop :=
  u = cTransform v ∧ v = cTransform u

def contactGap (u v : M → ℝ) (x y : M) : ℝ :=
  u x + cost x y + v y

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ActiveHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

def activeLogs (v : M → ℝ) (x : M) : Set (TangentSpace 𝓘(ℝ,Model n) x) :=
  {p | p ∈ minimizingVectors x ∧ contactGap (cTransform v) v x (riemannianExp x p)=0}

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalSubdifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

def normalSubdifferential (u : M → ℝ) (x : M) : Set (TangentSpace 𝓘(ℝ,Model n) x) :=
  {p | ∀ ε>0, ∀ᶠ h : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0,
    inner ℝ p h-ε*‖h‖≤u (riemannianExp x h)-u x}

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.StdSimplexCompat
attribute [-simp] _root_.OAI.ofNat_le_infty
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

namespace Convexity

namespace StdSimplex

section Semiring

variable {R : Type u} [PartialOrder R] [Semiring R] {X Y Z : Type*}

@[simp]
lemma total_of_fintype [Fintype X] (w : StdSimplex R X) :
    ∑ i, w.weights i = 1 := by
  have := w.total
  rwa [Finsupp.sum_fintype _ _ (by simp)] at this

@[simp]
lemma total_fin_two (w : StdSimplex R (Fin 2)) :
    w.weights 0 + w.weights 1 = 1 := by
  rw [← w.total_of_fintype, Fin.sum_univ_two]

lemma range_toFun_comp_weights [Fintype X] :
    Set.range (fun t ↦ t.weights : StdSimplex R X → (X → R)) =
    (⋂ (i : X), { s | 0 ≤ s i }) ∩ { s | ∑ i, s i = 1 } := by
  ext s
  simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.weights_nonneg, by simp⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨{
      weights := Finsupp.equivFunOnFinite.symm s
      nonneg m := by simpa using h₁ m
      total := by simpa [Finsupp.sum_fintype] }, by simp⟩

@[simp]
lemma weights_apply_eq_one [Subsingleton X] (s : StdSimplex R X) (m : X) :
    s.weights m = 1 := by
  rw [← s.total, Finsupp.sum_eq_single m
    (fun _ _ h ↦ (h (by subsingleton)).elim) (by simp)]

instance instSubsingleton [Subsingleton X] : Subsingleton (StdSimplex R X) where
  allEq := by
    intro a b
    ext m
    simp

variable [IsStrictOrderedRing R]

@[simp]
lemma weights_apply_le_one
    (s : StdSimplex R X) (m : X) : s.weights m ≤ 1 := by
  by_cases hm : s.weights m = 0
  · simpa only [hm] using zero_le_one' R
  · rw [← s.total, Finsupp.sum]
    exact Finset.single_le_sum (fun i _ => s.weights_nonneg i) (Finsupp.mem_support_iff.mpr hm)

instance instInhabited [Inhabited X] : Inhabited (StdSimplex R X) where
  default := .single default

instance instNonempty [Nonempty X] : Nonempty (StdSimplex R X) :=
  ⟨.single (Classical.arbitrary _)⟩

instance instUnique [Unique X] : Unique (StdSimplex R X) where
  uniq := by subsingleton

lemma map_id' : map (R := R) (id : X → X) = id := by
  funext f
  exact map_id f

end Semiring

section

variable {R' : Type*} [Ring R'] [PartialOrder R'] [IsStrictOrderedRing R']

/-- The bijection between the one dimensional standard simplex and the interval `[0, 1]`. -/
@[simps -isSimp]
def equivIcc : StdSimplex R' (Fin 2) ≃ Set.Icc (0 : R') 1 where
  toFun s := ⟨s.weights 1, s.weights_nonneg 1, s.weights_apply_le_one 1⟩
  invFun t := duple (s := 1 - t) (t := t) 0 1 (sub_nonneg.mpr t.2.2) t.2.1 (by simp)
  left_inv s := by
    ext i
    fin_cases i
    · have := s.total_fin_two
      simp
      exact (eq_sub_of_add_eq this).symm
    · simp
  right_inv t := by
    ext
    simp [Finsupp.single_apply]

attribute [local simp] equivIcc_apply_coe

@[simp]
lemma equivIcc_single_zero : equivIcc (.single (R := R') 0) = 0 := by
  ext
  simp [Finsupp.single_apply]

@[simp]
lemma equivIcc_single_one : equivIcc (.single (R := R') 1) = 1 := by
  ext
  simp

@[simp]
lemma equivIcc_symm_zero : equivIcc.symm 0 = .single (R := R') 0 :=
  equivIcc.injective (by simp)

@[simp]
lemma equivIcc_symm_one : equivIcc.symm 1 = .single (R := R') 1 :=
  equivIcc.injective (by simp)

end

section ConvexSpace

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {I : Type*}

@[simp]
lemma iConvexComb_single (x : StdSimplex R I) :
    x.iConvexComb single = x := by
  ext : 1
  simp [weights_iConvexComb, Finsupp.smul_single_one, Finsupp.sum_single]

end ConvexSpace

end StdSimplex

/-! ### Topology (Mathlib `d13f23b`, `Geometry/Convex/ConvexSpace/Topology.lean`) -/

namespace StdSimplex

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

/-- The topology on `StdSimplex R ι` that is induced by the embedding
`StdSimplex R ι → (ι → R)`. This is the correct topoplogy only when
`ι` is finite, see `StdSimplex.isEmbedding_toFun_comp_weights`. -/
abbrev topologicalSpaceInduced (ι : Type*) : TopologicalSpace (StdSimplex R ι) :=
  .induced (fun t ↦ t.weights : StdSimplex R ι → ι → R) inferInstance

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

lemma continuous_iff {T ι : Type*} [TopologicalSpace T] (f : T → StdSimplex R ι) :
    Continuous f ↔ ∀ (i : ι), Continuous (fun t ↦ (f t).weights i) := by
  rw [continuous_induced_rng]
  exact continuous_pi_iff

@[fun_prop]
lemma continuous_weights_apply {ι : Type*} (i : ι) :
    Continuous (fun (t : StdSimplex R ι) ↦ t.weights i) :=
  (continuous_apply i).comp (by rw [continuous_iff_le_induced])

open Classical in
@[fun_prop]
lemma continuous_map_weights_apply
    [IsStrictOrderedRing R] [IsTopologicalRing R] {ι₁ ι₂ : Type*}
    [Finite ι₁] (f : ι₁ → ι₂) (i₂ : ι₂) :
    Continuous (fun t ↦ (map (R := R) f t).weights i₂) := by
  have := Fintype.ofFinite ι₁
  have (t : StdSimplex R ι₁) :
      (map (R := R) f t).weights i₂ =
        ∑ i₁ with f i₁ = i₂, t.weights i₁ := by
    rw [weights_map, Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp),
      Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply, Finset.sum_filter]
  simp only [this]
  fun_prop

lemma continuous_map [IsStrictOrderedRing R] [IsTopologicalRing R]
    {ι₁ ι₂ : Type*} [Finite ι₁] (f : ι₁ → ι₂) :
    Continuous (map (R := R) f) := by
  rw [continuous_iff]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

attribute [local instance] topologicalSpaceInduced in
/-- The topology on `StdSimplex R M`: the supremum of the coinduced topologies for the maps
`StdSimplex.map f : StdSimplex R ι → StdSimplex R M` with `ι` finite. When `M` is finite it is the
topology induced by the embedding `StdSimplex R M → (M → R)`. -/
noncomputable instance topologicalSpace (M : Type v) :
    TopologicalSpace (StdSimplex R M) :=
  ⨆ (ι : Type v) (_ : Finite ι) (f : ι → M), .coinduced (map f) inferInstance

lemma topologicalSpace_eq (M : Type v) [Finite M] :
    topologicalSpace R M = topologicalSpaceInduced _ _ := by
  refine le_antisymm ?_ ?_
  · exact iSup_le (fun ι ↦ iSup_le (fun _ ↦ iSup_le
      (fun f ↦ (topologicalSpaceInduced.continuous_map R f).coinduced_le)))
  · refine le_trans ?_ (le_iSup _ M)
    refine le_trans ?_ (le_iSup _ (by assumption))
    refine le_trans ?_ (le_iSup _ id)
    rw [map_id']
    rfl

variable {R} in
lemma continuous_iff
    {M : Type v} {T : Type*} [TopologicalSpace T] (f : StdSimplex R M → T) :
    Continuous f ↔
      ∀ (ι : Type v) [Finite ι] (g : ι → M), Continuous (f ∘ map g) := by
  rw [continuous_iSup_dom]
  refine forall_congr' (fun ι ↦ ?_)
  rw [continuous_iSup_dom]
  refine forall_congr' (fun _ ↦ ?_)
  rw [continuous_iSup_dom]
  refine forall_congr' (fun M ↦ ?_)
  rw [continuous_coinduced_dom, topologicalSpace_eq]

open topologicalSpaceInduced in
@[fun_prop]
lemma continuous_weights_apply {M : Type*} (m : M) :
    Continuous (fun (t : StdSimplex R M) ↦ t.weights m) := by
  rw [continuous_iff]
  intro ι _ g
  rw [topologicalSpace_eq]
  exact continuous_map_weights_apply R g m

lemma isEmbedding_toFun_comp_weights (M : Type*) [Finite M] :
    IsEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  eq_induced := by rw [topologicalSpace_eq]
  injective _ _ h := by ext; apply congr_fun h

lemma isClosedEmbedding_toFun_comp_weights
    [OrderClosedTopology R] (M : Type*) [Finite M] :
    IsClosedEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  toIsEmbedding := isEmbedding_toFun_comp_weights R M
  isClosed_range := by
    have := Fintype.ofFinite M
    rw [range_toFun_comp_weights]
    refine IsClosed.inter (isClosed_iInter (fun _ ↦ isClosed_le ?_ ?_))
      (isClosed_eq ?_ ?_)
    all_goals fun_prop

end StdSimplex

/-! ### Compactness (Mathlib `d13f23b`, `CompactSpaceStdSimplex.lean`) -/

namespace StdSimplex

instance compactSpace (R M : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [PartialOrder R] [IsStrictOrderedRing R] [CompactIccSpace R] [OrderClosedTopology R]
    [Finite M] :
    CompactSpace (StdSimplex R M) where
  isCompact_univ := by
    rw [(isEmbedding_toFun_comp_weights R M).isCompact_iff, Set.image_univ]
    refine IsCompact.of_isClosed_subset (s := Set.Icc 0 1) isCompact_Icc
      (isClosedEmbedding_toFun_comp_weights R M).isClosed_range ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨fun i => x.weights_nonneg i, fun i => x.weights_apply_le_one i⟩

end StdSimplex

/-! ### Barycenters (Mathlib `d13f23b`, `Barycenter.lean`) -/

namespace StdSimplex

variable {K M : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]

/-- In the standard simplex with vertices `M`, the barycenter of a nonempty finite subset `S`. -/
@[simps -isSimp]
noncomputable def subBarycenter (S : Finset M) (hS : S.Nonempty) : StdSimplex K M where
  weights := S.sum (fun m ↦ .single m (S.card : K)⁻¹)
  nonneg := Finset.sum_nonneg (fun m _ => by
    classical
    intro i
    rw [Finsupp.single_apply]
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl)
  total := by
    rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
    simp only [Finsupp.sum_single_index, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Finset.card_pos.mpr hS).ne')

@[simp]
lemma subBarycenter_singleton (m : M) :
    subBarycenter (K := K) {m} (by simp) = .single m := by
  ext
  simp [weights_subBarycenter]

end StdSimplex

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

namespace StdSimplex

/-- The standard one-dimensional simplex is homeomorphic to the unit interval. -/
noncomputable def homeomorphI : StdSimplex ℝ (Fin 2) ≃ₜ unitInterval where
  toEquiv := equivIcc
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_weights_apply ℝ 1
  continuous_invFun := by
    rw [(isEmbedding_toFun_comp_weights ℝ (Fin 2)).continuous_iff]
    refine continuous_pi (fun i ↦ ?_)
    fin_cases i
    · simp [equivIcc, Finsupp.single_apply]
      fun_prop
    · simp [equivIcc, Finsupp.single_apply]
      fun_prop

@[local simp]
lemma homeomorphI_apply_coe (s : StdSimplex ℝ (Fin 2)) :
    (homeomorphI s).val = s.weights 1 := by
  rfl

@[simp]
lemma homeomorphI_single_zero : homeomorphI (.single 0) = 0 := by
  ext
  simp [Finsupp.single_apply]

@[simp]
lemma homeomorphI_single_one : homeomorphI (.single 1) = 1 := by
  ext
  simp

@[simp]
lemma homeomorphI_symm_zero : homeomorphI.symm 0 = .single 0 :=
  homeomorphI.injective (by simp)

@[simp]
lemma homeomorphI_symm_one : homeomorphI.symm 1 = .single 1 :=
  homeomorphI.injective (by simp)

end StdSimplex

end Convexity

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

end StdSimplexCompat
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_GraphProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

section
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

def subgradientGraph (u : M → ℝ) : Set (TangentBundle 𝓘(ℝ,Model n) M) :=
  {z | z.2∈normalSubdifferential (n := n) u z.1}

end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_PartialDerivatives
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {Q E F : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma ContDiffAt.partial_snd_fderiv {f : Q → E → F} {q:Q} {h:E}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (q,h)) :
    ContDiffAt ℝ ∞ (fun z : Q × E => fderiv ℝ (f z.1) z.2) (q,h) := by
  have H : ContDiffAt ℝ ∞ (Function.uncurry (fun z : Q × E => f z.1)) ((q,h),h) := by
    exact hf.comp ((q,h),h) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact H.fderiv contDiffAt_snd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

lemma ContDiffAt.partial_snd_fderiv_two {f : Q → E → F} {q:Q} {h:E}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (q,h)) :
    ContDiffAt ℝ ∞ (fun z : Q × E => fderiv ℝ (fderiv ℝ (f z.1)) z.2) (q,h) := by
  apply ContDiffAt.partial_snd_fderiv (f := fun q => fderiv ℝ (f q))
  exact ContDiffAt.partial_snd_fderiv hf

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalCoordinates3
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def movingNormal (a : M) (q : Model n × Model n) : M :=
  let z := (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)).symm q
  riemannianExp z.1 z.2

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_EnvelopeData
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

abbrev EnvelopeData (E ι : Type*) := (E × (ι → E)) × ((ι → ℝ) × ℝ)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_UniformEnvelope
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

abbrev chartFiberInverse (a : M) (b : Model n) :=
  (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
    ((extChartAt 𝓘(ℝ,Model n) a).symm b)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_EuclideanUpper
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

def hopfLax (t : ℝ) (u : M → ℝ) (z : M) : ℝ :=
  sInf (Set.range (fun x => u x + cost x z / t))

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_HopfGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def riemannianGradient (f : M → ℝ) (x : M) : TangentSpace 𝓘(ℝ,Model n) x := by
  letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  exact (InnerProductSpace.toDual ℝ (TangentSpace 𝓘(ℝ,Model n) x)).symm
    (mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f x)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CoordinateScalarSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def coordinateScalarSupport (a : M) (φ : ℝ → ℝ)
    (q : ((ℝ×ℝ)×(Model n×Model n))×Model n) : ℝ :=
  φ (q.1.1.1+cost ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.2.1)
      (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))/q.1.1.2-
    cost ((extChartAt 𝓘(ℝ,Model n) a).symm q.2)
      (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))/q.1.1.2)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_StationaryPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def fixedJoinAction (x : M) (h T : ℝ) (p : TangentSpace 𝓘(ℝ,Model n) x)
    (z : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  cost (riemannianExp x z.1) (riemannianExp x (h • z.2))/h+
    cost (riemannianExp x (h • z.2)) (riemannianExp x (T • p))/(T-h)

def fixedJoinMiddle (x : M) (h T : ℝ) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ :=
  let I : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ]
      TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x :=
    (0 : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x).prod
      (ContinuousLinearMap.id ℝ _)
  ((fderiv ℝ (fderiv ℝ (fixedJoinAction x h T p)) (0,p)).comp I).flip.comp I |>.flip

section
omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

@[simp] lemma fixedJoinMiddle_apply (x : M) (h T : ℝ)
    (p d k : TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinMiddle x h T p d k =
      fderiv ℝ (fderiv ℝ (fixedJoinAction x h T p)) (0,p) (0,d) (0,k) := rfl

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MovingPrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def movingPrefix (a : M) (t : ℝ) (b p : Model n) : M := movingNormal a (b,t • p)
def movingPrefixEnergy (a : M) (t : ℝ) (b p : Model n) : ℝ :=
  cost (movingNormal a (b,0)) (movingPrefix a t b p)/t

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_GraphCoordinates
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

def graphBaseCoordinate (a : M) (q : TangentBundle 𝓘(ℝ,Model n) M) : Model n :=
  extChartAt 𝓘(ℝ,Model n) a q.1

def graphVelocityCoordinate (a : M) (q : TangentBundle 𝓘(ℝ,Model n) M) : Model n :=
  (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) q).2

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_PoleCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def coordinateBackward (a : M) (q : ℝ × Model n × (Model n →L[ℝ] ℝ)) : M :=
  movingNormal a (q.2.1,-q.1 • (riemannianCoordinateMetric a q.2.1).inverse q.2.2)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ShortForward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def shortForward (a : M) (ψ : Model n → ℝ) (q : ℝ×Model n) : Model n :=
  extChartAt 𝓘(ℝ,Model n) a (coordinateBackward a (-1,q.2,q.1 • fderiv ℝ ψ q.2))

end WeakMTWTransport

end



end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CenterSupportFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

structure TrueCenterRow (c : M) (u v : M → ℝ) (φ : ℝ → ℝ)
    (x : Model n) (z : M) (τ l : ℝ) where
  r : Model n
  chart : x∈(extChartAt 𝓘(ℝ,Model n) c).target
  minimizing : chartFiberInverse c x r∈minimizingVectors ((extChartAt 𝓘(ℝ,Model n) c).symm x)
  contact : contactGap v u ((extChartAt 𝓘(ℝ,Model n) c).symm x) (movingNormal c (x,r))=0
  modifiedRegular : l • chartFiberInverse c x r∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) c).symm x)
  ray : riemannianExp ((extChartAt 𝓘(ℝ,Model n) c).symm x) ((τ*l) • chartFiberInverse c x r)=z
  below : ∀ w,coordinateScalarSupport c φ
    (((v ((extChartAt 𝓘(ℝ,Model n) c).symm x),(1+l)/2),(x,r)),w)≤
      φ (v ((extChartAt 𝓘(ℝ,Model n) c).symm w))
  touching : coordinateScalarSupport c φ
    (((v ((extChartAt 𝓘(ℝ,Model n) c).symm x),(1+l)/2),(x,r)),x)=
      φ (v ((extChartAt 𝓘(ℝ,Model n) c).symm x))
  forward : shortForward c (fun w=>coordinateScalarSupport c φ
    (((v ((extChartAt 𝓘(ℝ,Model n) c).symm x),(1+l)/2),(x,r)),w)) (τ,x)=
      extChartAt 𝓘(ℝ,Model n) c z

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_Subgradient
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def IsSubgradientOn (f : E → ℝ) (s : Set E) (h zeta : E) : Prop :=
  ∀ y ∈ s, f h + inner ℝ zeta (y - h) ≤ f y

def quadraticTaylor (f0 : ℝ) (p : E) (A : E →L[ℝ] E) (h : E) : ℝ :=
  f0 + inner ℝ p h + inner ℝ (A h) h / 2

def HasQuadraticExpansion (f : E → ℝ) (p : E) (A : E →L[ℝ] E) : Prop :=
  ∀ w : ℝ, 0 < w → ∃ delta : ℝ, 0 < delta ∧
    ∀ z : E, ‖z‖ < delta →
      |f z - quadraticTaylor (f 0) p A z| ≤ w * ‖z‖ ^ 2

open MeasureTheory

namespace ConvexProximal

def energy (f : E → ℝ) (y x : E) : ℝ := f x + ‖x-y‖^2/2

variable [FiniteDimensional ℝ E]

lemma exists_minimizer {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (y : E) :
    ∃ x, ∀ v, energy f y x ≤ energy f y v := by
  let R : ℝ := 2*(L:ℝ)+1
  have hR : 0 ≤ R := by dsimp [R] <;> positivity
  have hfc := hf.continuous
  have hc : Continuous (energy f y) := by unfold energy; fun_prop
  obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall y R).exists_isMinOn
    ⟨y, Metric.mem_closedBall_self hR⟩ hc.continuousOn
  refine ⟨x, fun v => ?_⟩
  by_cases hv : v ∈ Metric.closedBall y R
  · exact hmin hv
  have hvR : R < ‖v-y‖ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hv
  have hh : f y - (L:ℝ)*‖v-y‖ ≤ f v := by
    have hl := hf.dist_le_mul v y
    rw [Real.dist_eq, dist_eq_norm] at hl
    have hl' := (abs_le.mp hl).1
    linarith
  have hpos : f y < energy f y v := by
    dsimp [R] at hvR
    unfold energy
    nlinarith [show (0:ℝ) ≤ L from L.coe_nonneg]
  have hxy : energy f y x ≤ energy f y y := hmin (Metric.mem_closedBall_self hR)
  have ey : energy f y y = f y := by simp [energy]
  rw [ey] at hxy
  exact hxy.trans hpos.le

def prox (f : E → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) (y : E) : E :=
  Classical.choose (exists_minimizer hf y)

end ConvexProximal
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_SubgradientDifferential
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def IsSemiconvexSubgradientOn (f : E → ℝ) (s : Set E) (K : ℝ)
    (h zeta : E) : Prop :=
  ∀ y ∈ s, f h + inner ℝ zeta (y - h) - K / 2 * ‖y - h‖ ^ 2 ≤ f y


end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_LowerTaylor
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def HasLowerSecondTaylor (f : E → ℝ) (l : E →L[ℝ] ℝ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝 (0:E), f 0+l h+B h h/2-ε*‖h‖^2≤f h

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinatePole
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def coordinatePoleMatrix (a : M) (t : ℝ) (v : M → ℝ) (b p : Model n) :
    Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p-
    fderiv ℝ (fderiv ℝ (fun q=>hopfLax t (cTransform v) (movingPrefix a t b q))) p

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinateMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def coordinateCenterMatrix (a : M) (t : ℝ) (G : M → ℝ) (b p : Model n) :
    Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p+
    fderiv ℝ (fderiv ℝ (fun q=>G (movingPrefix a t b q))) p

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalEndpointJoin
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteNormalEndpoint_r69274c_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
def normalEndpointJoinAction (x y : M) (h : ℝ)
    (q : TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  cost x (riemannianExp x (h • q.2))/h+
    cost (riemannianExp x (h • q.2)) (riemannianExp y q.1)/(1-h)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MixedOperator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

def mixedOperator (B : F →L[ℝ] E →L[ℝ] ℝ) : F →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B

omit [CompleteSpace F] in
@[simp] lemma mixedOperator_inner (B : F →L[ℝ] E →L[ℝ] ℝ) (v : F) (w : E) :
    inner ℝ (mixedOperator B v) w=B v w :=
  InnerProductSpace.toDual_symm_apply

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_HessianMixedOperator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local instance productNormedSpace : NormedSpace ℝ (F×E) := Prod.normedSpace

local instance productNormedGroup_r69274c_1 : NormedAddCommGroup (F×E) := Prod.normedAddCommGroup
local instance productDualNormedSpace_r69274c_1 : NormedSpace ℝ ((F×E) →L[ℝ] ℝ) := inferInstance
def negativeMixedForm (H : (F×E) →L[ℝ] (F×E) →L[ℝ] ℝ) : F →L[ℝ] E →L[ℝ] ℝ := by
  let I : F →L[ℝ] F×E := (ContinuousLinearMap.id ℝ F).prod 0
  let K : E →L[ℝ] F×E := (0:E →L[ℝ] F).prod (ContinuousLinearMap.id ℝ E)
  exact -((H.comp I).flip.comp K).flip

@[simp] lemma negativeMixedForm_apply (H : (F×E) →L[ℝ] (F×E) →L[ℝ] ℝ)
    (v : F) (w : E) : negativeMixedForm H v w= -H (v,0) (0,w) := rfl
end WeakMTWTransport




open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

local instance tangentFiniteNormalMixed (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

local instance endpointProductNormedGroup_r69274c_1 (x y : M) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) :=
  Prod.normedAddCommGroup
local instance endpointProductNormedSpace_r69274c_1 (x y : M) :
    NormedSpace ℝ (TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) :=
  Prod.normedSpace
local instance endpointDualNormedGroup_r69274c_1 (x y : M) :
    NormedAddCommGroup ((TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ) :=
  inferInstance
local instance endpointDualNormedSpace_r69274c_1 (x y : M) :
    NormedSpace ℝ ((TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ) :=
  inferInstance
def normalEndpointMixedOperator (x y : M) (h : ℝ)
    (p : TangentSpace 𝓘(ℝ,Model n) x) :
    TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x :=
  mixedOperator (negativeMixedForm
    (fderiv ℝ (fderiv ℝ (normalEndpointJoinAction x y h)) (0,p)))

@[simp] lemma normalEndpointMixedOperator_inner (x y : M) (h : ℝ)
    (p k : TangentSpace 𝓘(ℝ,Model n) x) (d : TangentSpace 𝓘(ℝ,Model n) y) :
    inner ℝ (normalEndpointMixedOperator x y h p d) k=
      -fderiv ℝ (fderiv ℝ (normalEndpointJoinAction x y h)) (0,p) (d,0) (0,k) := by
  rw [normalEndpointMixedOperator,mixedOperator_inner,negativeMixedForm_apply]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ActualCenterSemibound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section ActualCenterSemibound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

structure CenterSequenceData (a c : M) (u v : M → ℝ) (Φ : ℝ×ℝ → ℝ)
    (γj lj τj tj : ℕ → ℝ) (xj bj qj : ℕ → Model n) (zj : ℕ → M)
    (F : ℕ → Model n → ℝ) where
  row : ∀ i,TrueCenterRow c u v (fun s=>Φ (γj i,s)) (xj i) (zj i) (τj i) (lj i)
  endpoint : ∀ i,movingPrefix a (tj i) (bj i) (qj i)=zj i
  derivative : ∀ᶠ i in atTop,
    (∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ,Model n) c (zj i)),DifferentiableAt ℝ
      (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y)) ((extChartAt 𝓘(ℝ,Model n) c).symm z)) z) ∧
    DifferentiableAt ℝ (fderiv ℝ
      (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y)) ((extChartAt 𝓘(ℝ,Model n) c).symm z)))
        (extChartAt 𝓘(ℝ,Model n) c (zj i))
  gradient : Tendsto (fun i=>fderiv ℝ (F i) (extChartAt 𝓘(ℝ,Model n) c (zj i))+
    fderiv ℝ (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y)) ((extChartAt 𝓘(ℝ,Model n) c).symm z))
      (extChartAt 𝓘(ℝ,Model n) c (zj i))) atTop (𝓝 0)
  backward : ∀ᶠ i in atTop,coordinateBackward c (tj i,extChartAt 𝓘(ℝ,Model n) c (zj i),
    fderiv ℝ (F i) (extChartAt 𝓘(ℝ,Model n) c (zj i)))=
      (extChartAt 𝓘(ℝ,Model n) a).symm (bj i)

end ActualCenterSemibound
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ChartFirstMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

structure ChartFixedPrefixLimit (a : M) (v G : M → ℝ) (t : ℝ)
    (q : ℕ → subgradientGraph (n := n) (cTransform v))
    (q₀ : subgradientGraph (n := n) (cTransform v)) where
  σ : ℕ → ℕ
  strictMono : StrictMono σ
  pj : ℕ → Fin (Module.finrank ℝ (Model n)+1) → Model n
  w : ℕ → Fin (Module.finrank ℝ (Model n)+1) → ℝ
  pj₀ : Fin (Module.finrank ℝ (Model n)+1) → Model n
  w₀ : Fin (Module.finrank ℝ (Model n)+1) → ℝ
  H : Model n →L[ℝ] Model n →L[ℝ] ℝ
  L : Model n →L[ℝ] Model n →L[ℝ] ℝ
  activeLimit : ∀ i,chartFiberInverse a (graphBaseCoordinate a q₀.1) (pj₀ i)∈
    activeLogs v ((extChartAt 𝓘(ℝ,Model n) a).symm (graphBaseCoordinate a q₀.1))
  nonnegLimit : ∀ i,0≤w₀ i
  totalLimit : ∑ i,w₀ i=1
  baryLimit : ∑ i,w₀ i • pj₀ i=graphVelocityCoordinate a q₀.1
  pjLimit : Tendsto pj atTop (𝓝 pj₀)
  wLimit : Tendsto w atTop (𝓝 w₀)
  HLimit : Tendsto (fun k=>coordinateCenterMatrix a t G
    (graphBaseCoordinate a (q (σ k)).1)
    (graphVelocityCoordinate a (q (σ k)).1)) atTop (𝓝 H)
  LLimit : Tendsto (fun k=>coordinatePoleMatrix a t v
    (graphBaseCoordinate a (q (σ k)).1)
    (graphVelocityCoordinate a (q (σ k)).1)) atTop (𝓝 L)
  positive : ∀ d:Model n,0≤L d d
  symmetric : ∀ d e:Model n,L d e=L e d
  kernel : ∀ i,∀ d:Model n,L (pj₀ i-graphVelocityCoordinate a q₀.1) d=0
  upper : ∀ d:Model n,H d d≤L d d
  samples : ∀ᶠ k in atTop,
    let b := graphBaseCoordinate a (q (σ k)).1
    let p := graphVelocityCoordinate a (q (σ k)).1
    let A := chartFiberInverse a b
    (∀ i,0≤w k i) ∧ (∑ i,w k i=1) ∧ (∑ i,w k i • pj k i=p) ∧
    (∀ i,A (pj k i)∈activeLogs v ((extChartAt 𝓘(ℝ,Model n) a).symm b)) ∧
    (∀ i,0<w k i → HasLowerSecondTaylor
      (fun r:Model n=>v (movingNormal a (b,pj k i+r))+‖A (pj k i+r)‖^2/2) 0
      (w k i • coordinatePoleMatrix a t v b p))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SectionOscillation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

open Filter

def HasPowerUpperBound (F : ℝ → ℝ) : Prop :=
  ∃ beta C r0 : ℝ, 0 < beta ∧ 0 < C ∧ 0 < r0 ∧
    ∀ r : ℝ, 0 < r → r < r0 → F r ≤ C * r ^ beta

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenterSequenceCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section CenterSequenceCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def CenterSequenceData.comp {a c : M} {u v : M → ℝ} {Φ : ℝ×ℝ → ℝ}
    {γj lj τj tj : ℕ → ℝ} {xj bj qj : ℕ → Model n} {zj : ℕ → M}
    {F : ℕ → Model n → ℝ}
    (D : CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F)
    (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop) :
    CenterSequenceData a c u v Φ (γj ∘ σ) (lj ∘ σ) (τj ∘ σ) (tj ∘ σ)
      (xj ∘ σ) (bj ∘ σ) (qj ∘ σ) (zj ∘ σ) (F ∘ σ) where
  row i := D.row (σ i)
  endpoint i := D.endpoint (σ i)
  derivative := hσ.eventually D.derivative
  gradient := D.gradient.comp hσ
  backward := hσ.eventually D.backward

end CenterSequenceCompact
end WeakMTWTransport

end
end

end OAI
end


