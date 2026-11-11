-- Prove2me | Definitions.Def_OAIQ232A001
-- name    : OAIQ232A001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:41:04.241004+00:00
-- url     : https://prove2.me/theorems/37f4dd18-8202-4819-bd15-00c3b9085f20
-- title:
--   Definitions bundle OAIQ232A001 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 71 declarations of OpenAI's Lean: 24 definitions and 47 theorems. The definitions and types are `OAI.WeakMTWTransport.actionKernelBilinearNormedSpace`, `OAI.WeakMTWTransport.actionKernelDualNormedSpace`, `OAI.WeakMTWTransport.directionalDerivative`, `OAI.WeakMTWTransport.gaussLemmaBilinearNormedAddCommGroup`, `OAI.WeakMTWTransport.gaussLemmaBilinearNormedSpace`, `OAI.WeakMTWTransport.gaussLemmaDualNormedAddCommGroup`, `OAI.WeakMTWTransport.gaussLemmaDualNormedSpace`, `OAI.WeakMTWTransport.gaussLemmaNormedSpace`, `OAI.WeakMTWTransport.globalPairingNormedSpace`, `OAI.WeakMTWTransport.hessianValue`, `OAI.WeakMTWTransport.instNormedSpaceReal_solutions_1`, `OAI.WeakMTWTransport.modifiedDatum`, `OAI.WeakMTWTransport.normalCoordinatesBilinearNormedAddCommGroup`, `OAI.WeakMTWTransport.normalCoordinatesBilinearNormedSpace`, `OAI.WeakMTWTransport.normalCoordinatesDualNormedAddCommGroup`, `OAI.WeakMTWTransport.normalCoordinatesDualNormedSpace`, `OAI.WeakMTWTransport.normalCoordinatesNormedSpace`, `OAI.WeakMTWTransport.parameterPenalty`, `OAI.WeakMTWTransport.pathCalculusNormedSpaceContinuousLinearMap`, `OAI.WeakMTWTransport.smoothDistanceNormedAddCommGroupBilinear`, `OAI.WeakMTWTransport.smoothDistanceNormedAddCommGroupDual`, `OAI.WeakMTWTransport.smoothDistanceNormedSpace`, `OAI.WeakMTWTransport.smoothDistanceNormedSpaceBilinear`, `OAI.WeakMTWTransport.smoothDistanceNormedSpaceDual`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Calculus_ActionCalculus`, `BiholderTransport_Calculus_ImplicitNeighborhood`, `BiholderTransport_Calculus_PartialCalculus`, `BiholderTransport_Calculus_PathCalculus`, `BiholderTransport_Calculus_RiemannianContinuous`, `BiholderTransport_Calculus_SmoothDistance`, `BiholderTransport_Calculus_SmoothExtensionNear`, `BiholderTransport_Coordinates_ChartTransition`, `BiholderTransport_Coordinates_CoordinateGradient`, `BiholderTransport_Coordinates_CoordinateMetricNorm`, `BiholderTransport_Coordinates_CoordinateVariation`, `BiholderTransport_Coordinates_IntrinsicGradient`, `BiholderTransport_Coordinates_NormalCoordinates`, `BiholderTransport_Coordinates_NormalRigidity`, `BiholderTransport_CostGeometry_LinearRadialDerivative`, `BiholderTransport_CostGeometry_RadialVelocityMetricEqualities`, `BiholderTransport_Geodesics_EndpointIdentity`, `BiholderTransport_Geodesics_GaussLemma`, `BiholderTransport_Geodesics_GeodesicSpray`, `BiholderTransport_Geodesics_GlobalGauss`, `BiholderTransport_Geodesics_MetricGeodesicLift`, `BiholderTransport_Geodesics_ShortGradient`, `BiholderTransport_Geodesics_SprayProjection`, `BiholderTransport_LinearAlgebra_BilinearMetricSpeedSquare`, `BiholderTransport_LinearAlgebra_TransverseConcavity`, `BiholderTransport_LocalFlow_ImplicitODE`, `BiholderTransport_LocalFlow_MIntegralCurveUniformInvariant`, `BiholderTransport_Regularity_ActionKernel`, `BiholderTransport_Regularity_ActualParameter`, `BiholderTransport_Regularity_CompactDisk`, `BiholderTransport_Regularity_ContDiffUncurryIterated`, `BiholderTransport_Regularity_MetricDefinitions`, `BiholderTransport_Regularity_SmallAffineTimeTube`, `BiholderTransport_Volume_RadialNull`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ232A006`, `OAIQ232A007`, `OAIQ232A008`, `OAIQ232A009`, `OAIQ232A011` and `OAIQ232A012`; the statements `OAI.WeakMTWTransport.exists_reverse_exp_divided_isotropic_gain` and `OAI.WeakMTWTransport.exists_uniform_divided_hessian_gap`.
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
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ActionCalculus
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

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma fderiv_fst_eq_of_line_stationary {B : E×F → ℝ} {v a : E} {q : F}
    (hB : DifferentiableAt ℝ B (v,q))
    (hline : HasDerivAt (fun s : ℝ => B (v+s • a,q)) 0 0) :
    fderiv ℝ B (v,q) (a,0) = 0 := by
  have hp : HasDerivAt (fun s : ℝ => (v+s • a,q)) (a,0) 0 := by
    convert! (((hasDerivAt_const (0:ℝ) v).add ((hasDerivAt_id (0:ℝ)).smul_const a)).prodMk
      (hasDerivAt_const (0:ℝ) q)) using 1; simp
  have hb : HasFDerivAt B (fderiv ℝ B (v,q)) (v+(0:ℝ) • a,q) := by simpa using hB.hasFDerivAt
  have h := hb.comp_hasDerivAt 0 hp
  exact h.unique hline

lemma fderiv_snd_eq_of_partial {B : E×F → ℝ} {v : E} {q : F} {D : F →L[ℝ] ℝ}
    (hB : DifferentiableAt ℝ B (v,q))
    (hpart : HasFDerivAt (fun y : F => B (v,y)) D q) (u : F) :
    fderiv ℝ B (v,q) (0,u) = D u := by
  have hp := (hasFDerivAt_const v q).prodMk (hasFDerivAt_id (𝕜 := ℝ) q)
  have h := hB.hasFDerivAt.comp q hp
  have heq := h.unique hpart
  exact congrArg (fun A : F →L[ℝ] ℝ => A u) heq

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ImplicitNeighborhood
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

namespace WeakMTWTransport
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma endomorphism_isInvertible_iff_isUnit (L : Y →L[ℝ] Y) : L.IsInvertible ↔ IsUnit L := by
  constructor
  · rintro ⟨e,rfl⟩
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr e.bijective
  · intro h
    have hb := ContinuousLinearMap.isUnit_iff_bijective.mp h
    exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hb.1)
      (LinearMap.range_eq_top.mpr hb.2),rfl⟩

lemma isOpen_invertible_endomorphism : IsOpen {L : Y →L[ℝ] Y | L.IsInvertible} := by
  simpa only [endomorphism_isInvertible_iff_isUnit] using
    (Units.isOpen : IsOpen {L : Y →L[ℝ] Y | IsUnit L})

lemma exists_smooth_implicit_neighborhood (F : X × Y → Y) (hF : ContDiff ℝ ∞ F)
    (a : X) (b : Y) (hi : (fderiv ℝ F (a,b) ∘L inr ℝ X Y).IsInvertible) :
    ∃ U : X → Y, ∃ S : Set X, IsOpen S ∧ a ∈ S ∧ ContDiffOn ℝ ∞ U S ∧ U a = b ∧
      ∀ x ∈ S, F (x,U x) = F (a,b) := by
  let U := hF.contDiffAt.implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi
  have hU : ContDiffAt ℝ ∞ U a := hF.contDiffAt.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi
  have hb : U a = b := hF.contDiffAt.implicitFunction_apply_self (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi
  have hc : ∀ᶠ x in 𝓝 a, ContDiffAt ℝ 1 U x :=
    (hU.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1:ℕ∞ω) ≤ (∞:ℕ∞ω))).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hid : Continuous (fun p : X × Y => fderiv ℝ F p ∘L inr ℝ X Y) :=
    (hF.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp continuous_const
  have hin : ∀ᶠ p in 𝓝 (a,b), (fderiv ℝ F p ∘L inr ℝ X Y).IsInvertible :=
    hid.continuousAt (isOpen_invertible_endomorphism.mem_nhds hi)
  have hgraph : ContinuousAt (fun x => (x,U x)) a := continuousAt_id.prodMk hU.continuousAt
  have hgi : ∀ᶠ x in 𝓝 a, (fderiv ℝ F (x,U x) ∘L inr ℝ X Y).IsInvertible :=
    hgraph (by simpa only [hb] using! hin)
  have heq : ∀ᶠ x in 𝓝 a, F (x,U x) = F (a,b) :=
    hF.contDiffAt.eventually_apply_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi
  obtain ⟨V,hVsub,hV,hbase⟩ := mem_nhds_iff.mp
    (hF.contDiffAt.eventually_apply_eq_iff_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi)
  have hgin : ∀ᶠ x in 𝓝 a, (x,U x) ∈ V :=
    hgraph (by simpa only [hb] using! hV.mem_nhds hbase)
  obtain ⟨S,hSsub,hS,ha⟩ := mem_nhds_iff.mp (hc.and (hgi.and (heq.and hgin)))
  refine ⟨U,S,hS,ha,?_,hb,fun x hx => (hSsub hx).2.2.1⟩
  intro x hx
  have hh := hSsub hx
  let W := hF.contDiffAt.implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hh.2.1
  have hW : ContDiffAt ℝ ∞ W x := hF.contDiffAt.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hh.2.1
  have hwx : W x = U x := hF.contDiffAt.implicitFunction_apply_self (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hh.2.1
  have hWgraph : ContinuousAt (fun z => (z,W z)) x := continuousAt_id.prodMk hW.continuousAt
  have hWV : ∀ᶠ z in 𝓝 x, (z,W z) ∈ V := hWgraph (by simpa only [hwx] using hV.mem_nhds hh.2.2.2)
  have hev : U =ᶠ[𝓝 x] W := by
    filter_upwards [hWV,hF.contDiffAt.eventually_apply_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hh.2.1] with z hz hz'
    apply (hVsub hz).mp
    exact hz'.trans hh.2.2.1
  exact (hW.congr_of_eventuallyEq hev).contDiffWithinAt

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_PartialCalculus
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

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup F] [NormedSpace ℝ F]

def directionalDerivative (f : E → F) (v : E) (x : E) : F := fderiv ℝ f x v

lemma hasFDerivAt_directionalDerivative {f : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (v : E) :
    HasFDerivAt (directionalDerivative f v)
      ((ContinuousLinearMap.apply ℝ F v) ∘L fderiv ℝ (fderiv ℝ f) x) x := by
  exact (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x
    ((hf.fderiv_right (m := (∞ : ℕ∞ω)) (by simp)).differentiableAt (by simp)).hasFDerivAt

lemma contDiffAt_directionalDerivative {f : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (v : E) :
    ContDiffAt ℝ ∞ (directionalDerivative f v) x :=
  (ContinuousLinearMap.apply ℝ F v).contDiff.contDiffAt.comp x
    (hf.fderiv_right (m := (∞ : ℕ∞ω)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

lemma hasDerivAt_slice_left {f : ℝ × ℝ → F} {t s : ℝ}
    (hf : DifferentiableAt ℝ f (t,s)) :
    HasDerivAt (fun q => f (q,s)) (directionalDerivative f (1,0) (t,s)) t := by
  exact hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t s))

lemma hasDerivAt_slice_right {f : ℝ × ℝ → F} {t s : ℝ}
    (hf : DifferentiableAt ℝ f (t,s)) :
    HasDerivAt (fun q => f (t,q)) (directionalDerivative f (0,1) (t,s)) s := by
  exact hf.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_const s t).prodMk (hasDerivAt_id s))

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

local instance pathCalculusNormedSpaceContinuousLinearMap :
    NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_RiemannianContinuous
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
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [h : IsContMDiffRiemannianBundle IB ∞ F E]

include h in
lemma continuousRiemannianBundle_of_smooth : IsContinuousRiemannianBundle F E := by
  obtain ⟨g,hg,hge⟩ := IsContMDiffRiemannianBundle.exists_contMDiff (IB := IB) (n := ∞) (F := F) (E := E)
  exact ⟨g,hg.continuous,hge⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SmoothDistance
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance smoothDistanceNormedSpace : NormedSpace ℝ E :=
  InnerProductSpace.toNormedSpace
local instance smoothDistanceNormedAddCommGroupEndomorphism_r902208_1 :
    NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance smoothDistanceNormedSpaceEndomorphism_r902208_1 :
    NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance smoothDistanceNormedAddCommGroupDual :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance smoothDistanceNormedSpaceDual :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance smoothDistanceNormedAddCommGroupBilinear :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance smoothDistanceNormedSpaceBilinear :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

lemma derivative_pullback_metric
    {g h : E → E →L[ℝ] E →L[ℝ] ℝ} {φ : E → E} {x : E}
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h (φ x))
    (hφ : DifferentiableAt ℝ φ x) (hDφ : DifferentiableAt ℝ (fderiv ℝ φ) x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v, g y u v = h (φ y) (fderiv ℝ φ y u) (fderiv ℝ φ y v))
    (w u v : E) :
    fderiv ℝ g x w u v =
      fderiv ℝ h (φ x) (fderiv ℝ φ x w) (fderiv ℝ φ x u) (fderiv ℝ φ x v) +
      h (φ x) (fderiv ℝ (fderiv ℝ φ) x w u) (fderiv ℝ φ x v) +
      h (φ x) (fderiv ℝ φ x u) (fderiv ℝ (fderiv ℝ φ) x w v) := by
  have hleft := (hg.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).clm_apply
    (hasFDerivAt_const v x)
  have hright := ((hh.hasFDerivAt.comp x hφ.hasFDerivAt).clm_apply
    (hDφ.hasFDerivAt.clm_apply (hasFDerivAt_const u x))).clm_apply
    (hDφ.hasFDerivAt.clm_apply (hasFDerivAt_const v x))
  have heq : (fun y => g y u v) =ᶠ[𝓝 x]
      (fun y => h (φ y) (fderiv ℝ φ y u) (fderiv ℝ φ y v)) := by
    filter_upwards [hmetric] with y hy; exact hy u v
  have he := congrArg (fun L : E →L[ℝ] ℝ => L w)
    ((hleft.congr_of_eventuallyEq heq.symm).unique hright)
  simpa [add_assoc,add_comm,add_left_comm] using he

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SmoothExtensionNear
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

namespace WeakMTWTransport

lemma exists_smooth_extension_near {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S : Set E} (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S)
    {a : E} (ha : a ∈ S) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 a] f := by
  obtain ⟨r,hr,hrS⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds ha)
  let b : ContDiffBump a := ⟨r/4,r/2,by positivity,by linarith⟩
  let g : E → F := fun x => b x • f x
  have hbS : tsupport b ⊆ S := by
    rw [b.tsupport_eq]
    intro x hx
    apply hrS
    change dist x a < r
    have h : dist x a ≤ r/2 := hx
    linarith
  refine ⟨g,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact b.contDiff.contDiffAt.smul (hf.contDiffAt (hS.mem_nhds (hbS hx)))
    · have heq : g =ᶠ[𝓝 x] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        change b y • f y = 0
        simp only [hy,Pi.zero_apply,zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · filter_upwards [b.eventuallyEq_one] with x hx
    change b x • f x = f x
    simpa only [Pi.one_apply,one_smul] using congrArg (fun z : ℝ => z • f x) hx

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

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

lemma tangent_chart_apply (c z : TangentBundle 𝓘(ℝ,E) M) :
    extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) c z =
      (extChartAt 𝓘(ℝ,E) c.1 z.1, tangentCoordChange 𝓘(ℝ,E) z.1 c.1 z.1 z.2) := by
  rfl

lemma tangent_chart_symm_base (c : TangentBundle 𝓘(ℝ,E) M) (z : E × E) :
    ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) c).symm z).1 = (extChartAt 𝓘(ℝ,E) c.1).symm z.1 := by
  rfl

lemma tangent_chart_symm_fiber (c : TangentBundle 𝓘(ℝ,E) M) (z : E × E) :
    ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) c).symm z).2 =
      tangentCoordChange 𝓘(ℝ,E) c.1 ((extChartAt 𝓘(ℝ,E) c.1).symm z.1)
        ((extChartAt 𝓘(ℝ,E) c.1).symm z.1) z.2 := by
  rfl

lemma tangent_chart_transition_apply (a b : TangentBundle 𝓘(ℝ,E) M) (z : E × E)
    (ha : z.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target)
    (hb : (extChartAt 𝓘(ℝ,E) a.1).symm z.1 ∈ (extChartAt 𝓘(ℝ,E) b.1).source) :
    extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) b ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm z) =
      ((extChartAt 𝓘(ℝ,E) b.1 ∘ (extChartAt 𝓘(ℝ,E) a.1).symm) z.1,
        fderiv ℝ (extChartAt 𝓘(ℝ,E) b.1 ∘ (extChartAt 𝓘(ℝ,E) a.1).symm) z.1 z.2) := by
  rw [tangent_chart_apply,tangent_chart_symm_base,tangent_chart_symm_fiber]
  apply Prod.ext
  · rfl
  · have hsrc := (extChartAt 𝓘(ℝ,E) a.1).map_target ha
    rw [tangentCoordChange_comp ⟨⟨hsrc,mem_extChartAt_source _⟩,hb⟩]
    simp only [tangentCoordChange_def,ModelWithCorners.range_eq_univ,fderivWithin_univ,
      (extChartAt 𝓘(ℝ,E) a.1).right_inv ha]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_IntrinsicGradient
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma mfderiv_extChartAt_eq_tangentCoordChange {a y : M}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) a).source) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a) y =
      tangentCoordChange 𝓘(ℝ,E) y a y := by
  have hy' : y ∈ (chartAt E a).source := by simpa only [extChartAt_source] using hy
  rw [(hasMFDerivAt_extChartAt (I := 𝓘(ℝ,E)) hy').mfderiv,
    mfderiv_chartAt_eq_tangentCoordChange hy']

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinateGradient
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

namespace WeakMTWTransport

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma coordinate_cost_contDiffAt {a : M} {δ : ℝ}
    (hC : ContMDiffOn (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => dist z.1 z.2^2/2) (Metric.ball a δ ×ˢ Metric.ball a δ))
    {b : F → M} {v : F} {q : E}
    (hb : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ b v)
    (hbδ : b v ∈ Metric.ball a δ)
    (hq : q ∈ (extChartAt 𝓘(ℝ,E) a).target)
    (hqδ : (extChartAt 𝓘(ℝ,E) a).symm q ∈ Metric.ball a δ) :
    ContDiffAt ℝ ∞ (fun z : F×E => dist (b z.1) ((extChartAt 𝓘(ℝ,E) a).symm z.2)^2/2) (v,q) := by
  have hc : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (extChartAt 𝓘(ℝ,E) a).symm q :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds hq)
  have hcost := hC.contMDiffAt ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds (show (b v,(extChartAt 𝓘(ℝ,E) a).symm q) ∈ Metric.ball a δ ×ˢ Metric.ball a δ from ⟨hbδ,hqδ⟩))
  exact (hcost.comp (v,q) ((hb.comp (v,q) contDiffAt_fst.contMDiffAt).prodMk
    (hc.comp (v,q) contDiffAt_snd.contMDiffAt))).contDiffAt

lemma coordinate_outgoing_cost_contDiffAt {a y : M} {δ : ℝ}
    (hC : ContMDiffOn (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => dist z.1 z.2^2/2) (Metric.ball a δ ×ˢ Metric.ball a δ))
    {q : E} (hy : y ∈ Metric.ball a δ)
    (hq : q ∈ (extChartAt 𝓘(ℝ,E) a).target)
    (hqδ : (extChartAt 𝓘(ℝ,E) a).symm q ∈ Metric.ball a δ) :
    ContDiffAt ℝ ∞ (fun q : E => dist ((extChartAt 𝓘(ℝ,E) a).symm q) y^2/2) q := by
  have hc : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (extChartAt 𝓘(ℝ,E) a).symm q :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds hq)
  have hcost := hC.contMDiffAt ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds (show ((extChartAt 𝓘(ℝ,E) a).symm q,y) ∈ Metric.ball a δ ×ˢ Metric.ball a δ from ⟨hqδ,hy⟩))
  exact (hcost.comp q (hc.prodMk contMDiffAt_const)).contDiffAt

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinateMetricNorm
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma coordinate_metric_chart_derivative_norm {a y : M}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) a).source)
    {g : E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ∀ u v : E, g u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ y u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ y v))
    (v : TangentSpace 𝓘(ℝ,E) y) :
    Real.sqrt (g (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a) y v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a) y v)) = ‖v‖ := by
  let w : E := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a) y v
  change Real.sqrt (g w w) = ‖v‖
  have hy' : y ∈ (chartAt E a).source := by simpa only [extChartAt_source] using hy
  have hbase : y ∈ (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).baseSet := hy'
  have hv := (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL_continuousLinearMapAt (R := ℝ) hbase v
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hy'] at hv
  change (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ y w = v at hv
  rw [hg,hv,real_inner_self_eq_norm_sq,Real.sqrt_sq_eq_abs,abs_norm]

lemma coordinate_path_length {c : M} {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1 γ (Icc a b))
    (himg : MapsTo γ (Icc a b) (extChartAt 𝓘(ℝ,E) c).source)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ t ∈ Icc a b, ∀ u v : E, g (extChartAt 𝓘(ℝ,E) c (γ t)) u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ (γ t) u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ (γ t) v)) :
    pathELength 𝓘(ℝ,E) γ a b =
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (g (extChartAt 𝓘(ℝ,E) c (γ t))
        (deriv ((extChartAt 𝓘(ℝ,E) c) ∘ γ) t)
        (deriv ((extChartAt 𝓘(ℝ,E) c) ∘ γ) t))) := by
  rw [pathELength_eq_lintegral_mfderiv_Ioo,←restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hγd := (hγ t ht').contMDiffAt (Icc_mem_nhds ht.1 ht.2) |>.mdifferentiableAt one_ne_zero
  have hsrc' : γ t ∈ (chartAt E c).source := by simpa only [extChartAt_source] using himg ht'
  have hχd := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) hsrc'
  have hcomp := mfderiv_comp t hχd hγd
  rw [mfderiv_eq_fderiv] at hcomp
  have hval : deriv ((extChartAt 𝓘(ℝ,E) c) ∘ γ) t =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c) (γ t))
        (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1) := by
    change (fderiv ℝ ((extChartAt 𝓘(ℝ,E) c) ∘ γ) t) 1 = _
    exact congrArg (fun L : ℝ →L[ℝ] E => L 1) hcomp
  have hn := coordinate_metric_chart_derivative_norm (himg ht') (hg t ht')
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1)
  dsimp only
  rw [←ofReal_norm]
  congr 1
  rw [hval]
  exact hn.symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinateVariation
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance instNormedSpaceReal_solutions_1 : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_GaussLemma
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance gaussLemmaNormedSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance gaussLemmaDualNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance gaussLemmaDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance gaussLemmaBilinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance gaussLemmaBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalCoordinates
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance normalCoordinatesNormedSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance normalCoordinatesDualNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance normalCoordinatesDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance normalCoordinatesBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance normalCoordinatesBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_LinearRadialDerivative
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma linear_of_radial_derivative {f : ℝ → E} {l r a : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo l r)) (ha : a ∈ Ioo l r)
    (he : ∀ s ∈ Ioo l r, (s-a) • deriv f s = f s) :
    ∀ s ∈ Ioo l r, f s = (s-a) • deriv f a := by
  have hfd : ∀ s ∈ Ioo l r, ContDiffAt ℝ ∞ f s :=
    fun s hs => hf.contDiffAt (isOpen_Ioo.mem_nhds hs)
  have hdd : ∀ s ∈ Ioo l r, ContDiffAt ℝ ∞ (deriv f) s :=
    fun s hs => (hfd s hs).derivWithin (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hddd : ∀ s ∈ Ioo l r, ContDiffAt ℝ ∞ (deriv (deriv f)) s :=
    fun s hs => (hdd s hs).derivWithin (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdz : ∀ s ∈ Ioo l r, s ≠ a → deriv (deriv f) s = 0 := by
    intro s hs hsa
    have hL := ((hasDerivAt_id s).sub_const a).smul
      ((hdd s hs).differentiableAt (by simp)).hasDerivAt
    have heq : (fun u => (u-a) • deriv f u) =ᶠ[𝓝 s] f := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
      exact he u hu
    have H := (hL.congr_of_eventuallyEq heq.symm).unique
      ((hfd s hs).differentiableAt (by simp)).hasDerivAt
    simp only [one_smul,id_eq] at H
    have hz : (s-a) • deriv (deriv f) s = 0 := by
      have H' : deriv f s + (s-a) • deriv (deriv f) s = deriv f s := by
        simpa only [add_comm] using H
      exact add_eq_left.mp H'
    exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hsa)
  have hdza : deriv (deriv f) a = 0 := by
    have hnear : deriv (deriv f) =ᶠ[𝓝[≠] a] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ha)] with s hsa hs
      exact hdz s hs hsa
    exact tendsto_nhds_unique ((hddd a ha).continuousAt.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hnear.symm)
  have hdzall : ∀ s ∈ Ioo l r, deriv (deriv f) s = 0 := by
    intro s hs
    by_cases hsa : s = a
    · simpa only [hsa] using hdza
    · exact hdz s hs hsa
  have hconstant : ∀ s ∈ Ioo l r, deriv f s = deriv f a := by
    intro s hs
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo l r).isPreconnected
      (fun u hu => ((hdd u hu).differentiableAt (by simp)).differentiableWithinAt) hdzall hs ha
  intro s hs
  calc
    f s = (s-a) • deriv f s := (he s hs).symm
    _ = _ := by rw [hconstant s hs]
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_RadialVelocityMetricEqualities
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma radial_velocity_of_metric_equalities {g : E →L[ℝ] E →L[ℝ] ℝ}
    (hp : ∀ v : E, v ≠ 0 → 0 < g v v) (hs : ∀ v w, g v w = g w v)
    {u V : E} {s τ k : ℝ} (hu : g u u = k^2)
    (hV : τ^2*g V V = s^2*k^2) (hm : τ*g V u = s*k^2) :
    s • u = τ • V := by
  have hz : g (s • u - τ • V) (s • u - τ • V) = 0 := by
    simp only [map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul]
    rw [hs u V,hu]
    nlinarith [congrArg (fun z : ℝ => s*z) hm]
  by_contra he
  have hpos := hp (s • u - τ • V) (sub_ne_zero.mpr he)
  linarith

lemma bilinear_metric_radial_derivative {g : E →L[ℝ] E →L[ℝ] ℝ}
    (hs : ∀ u v, g u v = g v u) {f : ℝ → E} {s a τ k : ℝ}
    (hf : DifferentiableAt ℝ f s)
    (he : (fun t => τ^2*g (f t) (f t)) =ᶠ[𝓝 s] (fun t => (t-a)^2*k^2)) :
    τ^2*g (f s) (deriv f s) = (s-a)*k^2 := by
  have hL := (((g.hasFDerivAt.comp_hasDerivAt s hf.hasDerivAt).clm_apply
    hf.hasDerivAt).const_mul (τ^2))
  have hR := (((hasDerivAt_id s).sub_const a).pow 2).mul_const (k^2)
  have H := (hL.congr_of_eventuallyEq he.symm).unique hR
  simp only [Function.comp_apply, Nat.reduceSub, pow_one, id_eq, mul_one,
    Nat.cast_ofNat] at H
  rw [hs (deriv f s) (f s)] at H
  linarith
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalRigidity
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

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

omit [FiniteDimensional ℝ E] [IsRiemannianManifold 𝓘(ℝ,E) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma coordinate_curve_derivative_at_center {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t) :
    deriv (extChartAt 𝓘(ℝ,E) (γ t) ∘ γ) t =
      mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ) := by
  have H := mfderiv_comp t (mdifferentiableAt_extChartAt
    (I := 𝓘(ℝ,E)) (mem_chart_source E (γ t))) hγ
  rw [mfderiv_eq_fderiv,mfderiv_extChartAt_self] at H
  exact congrArg (fun L : ℝ →L[ℝ] E => L 1) H

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

lemma tangent_chart_source_iff (a z : TangentBundle 𝓘(ℝ,E) M) :
    z ∈ (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).source ↔
      z.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).source := by
  rw [FiberBundle.extChartAt]
  simp only [PartialEquiv.trans_source,PartialEquiv.prod_source,PartialEquiv.refl_source,
    Trivialization.source_eq,mem_inter_iff,mem_preimage,
    mem_prod,mem_univ,and_true,TangentBundle.trivializationAt_baseSet]
  simp only [extChartAt_source]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h,?_⟩
    change (trivializationAt E (TangentSpace 𝓘(ℝ,E)) a.1 z).1 ∈ (chartAt E a.1).source
    rwa [TangentBundle.trivializationAt_apply]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_ImplicitODE
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

section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

section ImplicitODE
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

lemma exists_smooth_rescaled_equation_on (N : P → P) (hN : ContDiff ℝ ∞ N)
    (c : E →L[ℝ] P) (A : P →L[ℝ] P) (a : E) :
    ∃ U : (ℝ × E) → P, ∃ S : Set (ℝ × E), IsOpen S ∧ (0,a) ∈ S ∧
      ContDiffOn ℝ ∞ U S ∧ U (0,a) = c a ∧
      ∀ z ∈ S, U z = c z.2 + z.1 • A (N (U z)) := by
  let F : (ℝ × E) × P → P := fun z => z.2 - c z.1.2 - z.1.1 • A (N z.2)
  let b : P := c a
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_snd.sub (c.contDiff.comp (contDiff_snd.comp contDiff_fst))).sub
      ((contDiff_fst.comp contDiff_fst).smul (A.contDiff.comp (hN.comp contDiff_snd)))
  have hpart : fderiv ℝ F ((0,a),b) ∘L inr ℝ (ℝ × E) P = ContinuousLinearMap.id ℝ P := by
    have hpair : HasFDerivAt (fun p : P => ((0,a),p)) (inr ℝ (ℝ × E) P) b :=
      (hasFDerivAt_const ((0:ℝ),a) b).prodMk (hasFDerivAt_id b)
    have hc := (hF.differentiable (by simp) ((0,a),b)).hasFDerivAt.comp b hpair
    have hd : HasFDerivAt (fun p : P => F ((0,a),p)) (ContinuousLinearMap.id ℝ P) b := by
      simpa only [F,zero_smul,sub_zero,id_eq] using (hasFDerivAt_id b).sub_const (c a)
    exact hc.unique hd
  have hi : (fderiv ℝ F ((0,a),b) ∘L inr ℝ (ℝ × E) P).IsInvertible := by
    rw [hpart]
    exact ⟨ContinuousLinearEquiv.refl ℝ P,rfl⟩
  obtain ⟨U,S,hS,ha,hU,hb,hEq⟩ := exists_smooth_implicit_neighborhood F hF (0,a) b hi
  refine ⟨U,S,hS,ha,hU,hb,?_⟩
  intro z hz
  have hz' : U z - c z.2 - z.1 • A (N (U z)) = 0 := by
    simpa only [F,b,zero_smul,sub_self,sub_zero] using hEq z hz
  simpa only [add_comm] using eq_add_of_sub_eq (sub_eq_zero.mp hz')

end ImplicitODE
universe u

end

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma lipschitzOnWith_const_smul {f : E → E} {K : ℝ≥0} {B : Set E}
    (hf : LipschitzOnWith K f B) (t : ℝ) :
    LipschitzOnWith (‖t‖₊ * K) (fun x => t • f x) B := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm,←smul_sub,norm_smul,NNReal.coe_mul,coe_nnnorm,mul_assoc]
  simpa only [dist_eq_norm] using
    mul_le_mul_of_nonneg_left (hf.dist_le_mul x hx y hy) (norm_nonneg t)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_MIntegralCurveUniformInvariant
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

lemma hasMFDerivAt_of_chart_ode {v : (x : M) → TangentSpace I x}
    (a : M) {f : ℝ → E} {t : ℝ}
    (ht : f t ∈ (extChartAt I a).target)
    (hf : HasDerivAt f
      (tangentCoordChange I ((extChartAt I a).symm (f t)) a
        ((extChartAt I a).symm (f t)) (v ((extChartAt I a).symm (f t)))) t) :
    HasMFDerivAt 𝓘(ℝ,ℝ) I ((extChartAt I a).symm ∘ f) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v ((extChartAt I a).symm (f t)))) := by
  let xₜ := (extChartAt I a).symm (f t)
  have hft1 := (extChartAt I a).map_target ht
  have hft2 := mem_extChartAt_source (I := I) xₜ
  let w : E := v xₜ
  change HasDerivAt f (tangentCoordChange I xₜ a xₜ w) t at hf
  have hder : HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I a).symm) ∘ f)
      w t := by
    have he : tangentCoordChange I a xₜ xₜ (tangentCoordChange I xₜ a xₜ w) = w := by
      rw [tangentCoordChange_comp ⟨⟨hft2,hft1⟩,hft2⟩,tangentCoordChange_self hft2]
    rw [← he]
    apply HasFDerivAt.comp_hasDerivAt _ _ hf
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _
      (by simp only [ModelWithCorners.range_eq_univ,univ_mem])
    rw [← (extChartAt I a).right_inv ht]
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1,hft2⟩
  refine ⟨(continuousAt_extChartAt_symm'' ht).comp hf.continuousAt,?_⟩
  rw [writtenInExtChartAt,extChartAt_model_space_eq_id,ModelWithCorners.range_eq_univ]
  change HasFDerivWithinAt ((extChartAt I xₜ ∘ (extChartAt I a).symm) ∘ f)
    ((1 : ℝ →L[ℝ] ℝ).smulRight w) univ t
  rw [hasFDerivWithinAt_univ]
  convert! hder.hasFDerivAt using 1
  all_goals try with_reducible_and_instances rfl

omit [I.Boundaryless] in
lemma contDiffOn_coordinate_vectorField {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) ∞
      (fun x => (⟨x,v x⟩ : TangentBundle I M))) (a : M) :
    ContDiffOn ℝ ∞ (fun y => tangentCoordChange I ((extChartAt I a).symm y) a
      ((extChartAt I a).symm y) (v ((extChartAt I a).symm y))) (extChartAt I a).target := by
  let e := trivializationAt E (fun x : M => TangentSpace I x) a
  have hc : ContMDiffOn I 𝓘(ℝ,E) ∞ (fun x => (e ⟨x,v x⟩).2) e.baseSet := by
    intro x hx
    exact ((e.contMDiffAt_section_iff hx).mp (hv x)).contMDiffWithinAt
  have hmaps : MapsTo (extChartAt I a).symm (extChartAt I a).target e.baseSet := by
    intro y hy
    change (extChartAt I a).symm y ∈ (chartAt H a).source
    simpa only [extChartAt_source] using (extChartAt I a).map_target hy
  exact contMDiffOn_iff_contDiffOn.mp (hc.comp (contMDiffOn_extChartAt_symm a) hmaps)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CompactDisk
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

namespace WeakMTWTransport
variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

lemma continuous_bundle_norm : Continuous (fun z : TotalSpace F E => ‖z.2‖) := by
  have h : Continuous (fun z : TotalSpace F E => inner ℝ z.2 z.2) :=
    (continuous_id : Continuous (id : TotalSpace F E → _)).inner_bundle continuous_id
  simpa only [← norm_eq_sqrt_real_inner] using h.sqrt

lemma isCompact_bundle_disk [CompactSpace B] [T2Space B]
    [FiniteDimensional ℝ F] (R : ℝ) :
    IsCompact {z : TotalSpace F E | ‖z.2‖ ≤ R} := by
  classical
  have hsclosed : IsClosed {z : TotalSpace F E | ‖z.2‖ ≤ R} :=
    isClosed_le continuous_bundle_norm continuous_const
  by_cases hR : R < 0
  · have : {z : TotalSpace F E | ‖z.2‖ ≤ R} = ∅ := by
      ext z
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
      exact not_le.mpr ((hR.trans_le (norm_nonneg _)))
    rw [this]
    exact isCompact_empty
  have hlocal (x : B) : ∃ C : ℝ, 0 < C ∧ ∃ K : Set B,
      K ∈ 𝓝 x ∧ IsCompact K ∧ K ⊆ (trivializationAt F E x).baseSet ∧
      ∀ y ∈ K, ‖(trivializationAt F E x).continuousLinearMapAt ℝ y‖ < C := by
    obtain ⟨C,hC,hbound⟩ := eventually_norm_trivializationAt_lt F E x
    obtain ⟨K,hK,hKs,hKc⟩ := local_compact_nhds
      (inter_mem ((trivializationAt F E x).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F E x)) hbound)
    exact ⟨C,hC,K,hK,hKc,fun y hy => (hKs hy).1,fun y hy => (hKs hy).2⟩
  choose C hC K hKn hKc hKb hKC using hlocal
  let L (x : B) : Set (TotalSpace F E) :=
    (trivializationAt F E x).toOpenPartialHomeomorph.symm ''
      (K x ×ˢ Metric.closedBall (0 : F) (C x * R))
  have hLc (x : B) : IsCompact (L x) := by
    apply ((hKc x).prod (isCompact_closedBall (0 : F) (C x * R))).image_of_continuousOn
    apply (trivializationAt F E x).toOpenPartialHomeomorph.continuousOn_symm.mono
    intro y hy
    change y ∈ (trivializationAt F E x).target
    exact (trivializationAt F E x).mem_target.mpr (hKb x hy.1)
  obtain ⟨t,ht⟩ := finite_cover_nhds hKn
  apply (t.isCompact_biUnion (fun x _ => hLc x)).of_isClosed_subset hsclosed
  intro z hz
  have hzm : z.1 ∈ ⋃ x ∈ t, K x := by rw [ht]; trivial
  obtain ⟨x,hx,hzK⟩ := mem_iUnion₂.mp hzm
  apply mem_iUnion₂.mpr ⟨x,hx,?_⟩
  have hzb := hKb x hzK
  have hzs : z ∈ (trivializationAt F E x).source :=
    (trivializationAt F E x).mem_source.mpr hzb
  refine ⟨(trivializationAt F E x) z,?_,?_⟩
  · refine ⟨?_,?_⟩
    · rwa [Trivialization.coe_fst _ hzs]
    · rw [Metric.mem_closedBall,dist_zero_right]
      have he : (trivializationAt F E x z).2 =
          (trivializationAt F E x).continuousLinearMapAt ℝ z.1 z.2 := by
        rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hzb]
      rw [he]
      calc
        _ ≤ ‖(trivializationAt F E x).continuousLinearMapAt ℝ z.1‖ * ‖z.2‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ C x * R := mul_le_mul (hKC x z.1 hzK).le hz (norm_nonneg _) (hC x).le
  · exact (trivializationAt F E x).left_inv hzs

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayProjection
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

omit [FiniteDimensional ℝ E] in
lemma tangent_chart_target_iff (a : TangentBundle 𝓘(ℝ,E) M) (q : E × E) :
    q ∈ (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).target ↔
      q.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target := by
  rw [FiberBundle.extChartAt_target]
  constructor
  · exact fun h => h.1.1
  · intro h
    refine ⟨⟨h,?_⟩,mem_univ _⟩
    simpa only [TangentBundle.trivializationAt_baseSet,← extChartAt_source 𝓘(ℝ,E),mem_preimage] using
      (extChartAt 𝓘(ℝ,E) a.1).map_target h

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_EndpointIdentity
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma tangent_chart_at_self_base (a : TangentBundle 𝓘(ℝ,E) M) (v : E) :
    extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a ⟨a.1,v⟩ = (extChartAt 𝓘(ℝ,E) a.1 a.1,v) := by
  rw [tangent_chart_apply,tangentCoordChange_self (mem_extChartAt_source (I := 𝓘(ℝ,E)) a.1)]

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma tangent_chart_at_self_base_symm (a : TangentBundle 𝓘(ℝ,E) M) (v : E) :
    (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm (extChartAt 𝓘(ℝ,E) a.1 a.1,v) = ⟨a.1,v⟩ := by
  rw [←tangent_chart_at_self_base a v]
  exact (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).left_inv
    ((tangent_chart_source_iff a _).mpr (mem_extChartAt_source (I := 𝓘(ℝ,E)) a.1))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_GlobalGauss
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

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

local instance globalPairingNormedSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_SmallAffineTimeTube
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

namespace WeakMTWTransport
lemma exists_small_affine_time_tube (a : ℝ) {h τ r η : ℝ}
    (hh : 0 < h) (hτ : 0 < τ) (hr : 0 < r) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ η ∧ ε ≤ h ∧
      ∀ s u t : ℝ, |s-a| < ε → |u-a| < ε → |t| < r →
        |s + (u-s)/τ*t-a| < h := by
  let ε := min (h/4) (min η (h*τ/(8*r)))
  have hε : 0 < ε := lt_min (by positivity)
    (lt_min hη (div_pos (mul_pos hh hτ) (by positivity)))
  have hεh : ε ≤ h/4 := min_le_left _ _
  have hεη : ε ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hεr : ε ≤ h*τ/(8*r) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε,hε,hεη,by linarith,?_⟩
  intro s u t hs hu ht
  have hus : |u-s| < 2*ε := by
    calc
      |u-s| = |(u-a)+(a-s)| := by congr 1; ring
      _ ≤ |u-a|+|a-s| := abs_add_le _ _
      _ < ε+ε := add_lt_add hu (by simpa only [abs_sub_comm] using hs)
      _ = 2*ε := by ring
  have hm : 2*ε/τ*r ≤ h/4 := by
    have hmul := (le_div_iff₀ (show 0 < 8*r by positivity)).mp hεr
    rw [div_mul_eq_mul_div,div_le_iff₀ hτ]
    nlinarith
  calc
    |s+(u-s)/τ*t-a| = |(s-a)+(u-s)/τ*t| := by congr 1; ring
    _ ≤ |s-a| + |(u-s)/τ*t| := abs_add_le _ _
    _ = |s-a| + |u-s|/τ*|t| := by rw [abs_mul,abs_div,abs_of_pos hτ]
    _ ≤ |s-a| + 2*ε/τ*r := by
      have H := mul_le_mul (div_le_div_of_nonneg_right hus.le hτ.le) ht.le
        (abs_nonneg t) (show 0 ≤ 2*ε/τ by positivity)
      linarith
    _ < ε + 2*ε/τ*r := by linarith
    _ ≤ h/4+h/4 := add_le_add hεh hm
    _ < h := by linarith
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearMetricSpeedSquare
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma bilinear_metric_speed_of_square {g : E →L[ℝ] E →L[ℝ] ℝ}
    {f : ℝ → E} {a k : ℝ} (hf : ContDiffAt ℝ ∞ f a) (h0 : f a = 0)
    (he : (fun t => g (f t) (f t)) =ᶠ[𝓝 a] (fun t => k*(t-a)^2)) :
    g (deriv f a) (deriv f a) = k := by
  have hfd : ∀ᶠ t in 𝓝 a, DifferentiableAt ℝ f t := ((hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mono
    (fun _ ht => ht.differentiableAt (by norm_num))
  have hde : (fun t => g (f t) (deriv f t) + g (deriv f t) (f t)) =ᶠ[𝓝 a]
      (fun t => 2*k*(t-a)) := by
    filter_upwards [hfd,he.eventuallyEq_nhds] with t ht heq
    have h₁ := ((g.hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt).clm_apply ht.hasDerivAt)
    have h₂ := ((((hasDerivAt_id t).sub_const a).pow 2).const_mul k)
    have hh := (h₁.congr_of_eventuallyEq heq.symm).unique h₂
    norm_num only [Function.comp_apply, Nat.reduceSub, pow_one, id_eq, mul_one, Nat.cast_ofNat] at hh
    linarith
  have hd : HasDerivAt (deriv f) (deriv (deriv f) a) a :=
    ((hf.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hf' := (hf.differentiableAt (by simp)).hasDerivAt
  have h₁ := ((g.hasFDerivAt.comp_hasDerivAt a hf').clm_apply hd).add
    ((g.hasFDerivAt.comp_hasDerivAt a hd).clm_apply hf')
  have h₂ := (((hasDerivAt_id a).sub_const a).const_mul (2*k))
  have hh := (h₁.congr_of_eventuallyEq hde.symm).unique h₂
  simp only [Function.comp_apply,h0,map_zero,zero_apply,add_zero,zero_add,mul_one] at hh
  linarith
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_MetricGeodesicLift
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

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

omit [FiniteDimensional ℝ E] [CompactSpace M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma velocity_lift_eq_of_eventuallyEq {γ δ : ℝ → M} {t : ℝ}
    (he : γ =ᶠ[𝓝 t] δ) :
    (⟨γ t,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ)⟩ : TangentBundle 𝓘(ℝ,E) M) =
      ⟨δ t,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) δ t (1:ℝ)⟩ := by
  refine TotalSpace.ext he.self_of_nhds ?_
  exact heq_of_eq (DFunLike.congr_fun he.mfderiv_eq (1 : ℝ))

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_ShortGradient
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

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

omit [FiniteDimensional ℝ E] [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma contMDiff_fiber_embedding (x : M) :
    ContMDiff 𝓘(ℝ,TangentSpace 𝓘(ℝ,E) x) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun v : TangentSpace 𝓘(ℝ,E) x => (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)) := by
  intro v
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_const,?_⟩
  let e := trivializationAt E (fun y : M => TangentSpace 𝓘(ℝ,E) y) x
  let L : TangentSpace 𝓘(ℝ,E) x →L[ℝ] E := e.continuousLinearMapAt ℝ x
  have heq : (fun w : TangentSpace 𝓘(ℝ,E) x => (e (⟨x,w⟩ : TangentBundle 𝓘(ℝ,E) M)).2) = L := by
    funext w
    exact (e.continuousLinearMapAt_apply_of_mem ℝ (mem_baseSet_trivializationAt E _ x) _).symm
  change ContMDiffAt 𝓘(ℝ,TangentSpace 𝓘(ℝ,E) x) 𝓘(ℝ,E) ∞
    (fun w => (e ⟨x,w⟩).2) v
  rw [heq]
  exact L.contDiff.contDiffAt.contMDiffAt

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_TransverseConcavity
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

variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]

def hessianValue (x : M) (p xi : TangentSpace 𝓘(ℝ, Model n) x) : ℝ :=
  iteratedDeriv 2 (fun t : ℝ =>
    cost (riemannianExp x (t • xi)) (riemannianExp x p)) 0

lemma mtw_affine_line (x : M) (p xi eta : TangentSpace 𝓘(ℝ, Model n) x)
    (s : ℝ) :
    mtw x (p + s • eta) xi eta = -(3 / 2 : ℝ) *
      iteratedDeriv 2 (fun t : ℝ => hessianValue x (p + t • eta) xi) s := by
  have hshift : (fun r : ℝ => hessianValue x ((p + s • eta) + r • eta) xi) =
      (fun r : ℝ => hessianValue x (p + (s + r) • eta) xi) := by
    ext r
    rw [add_smul, add_assoc]
  change -(3 / 2 : ℝ) * iteratedDeriv 2
    (fun r : ℝ => hessianValue x ((p + s • eta) + r • eta) xi) 0 = _
  rw [hshift, iteratedDeriv_comp_const_add 2
    (fun t : ℝ => hessianValue x (p + t • eta) xi) s]
  simp only [add_zero]

lemma WeakMTW.transverse_second_nonpos (hmtw : WeakMTW (n := n) (M := M))
    (x : M) (p xi eta : TangentSpace 𝓘(ℝ, Model n) x) (s : ℝ)
    (hs : p + s • eta ∈ injectivityDomain x) (hortho : inner ℝ xi eta = 0) :
    iteratedDeriv 2 (fun t : ℝ => hessianValue x (p + t • eta) xi) s ≤ 0 := by
  have hh := hmtw x (p + s • eta) hs xi eta hortho
  rw [mtw_affine_line] at hh
  linarith

lemma WeakMTW.transverse_concaveOn (hmtw : WeakMTW (n := n) (M := M))
    (x : M) (p xi eta : TangentSpace 𝓘(ℝ, Model n) x)
    {D : Set ℝ} (hD : Convex ℝ D)
    (hline : ∀ s ∈ interior D, p + s • eta ∈ injectivityDomain x)
    (hortho : inner ℝ xi eta = 0)
    (hcont : ContinuousOn (fun t : ℝ => hessianValue x (p + t • eta) xi) D)
    (hsmooth : ContDiffOn ℝ 2 (fun t : ℝ => hessianValue x (p + t • eta) xi)
      (interior D)) :
    ConcaveOn ℝ D (fun t : ℝ => hessianValue x (p + t • eta) xi) := by
  apply concaveOn_of_deriv2_nonpos hD hcont (hsmooth.differentiableOn (by norm_num))
  · exact (hsmooth.deriv_of_isOpen isOpen_interior (m := 1) (by norm_num)).differentiableOn
      (by norm_num)
  · intro s hs
    rw [← iteratedDeriv_eq_iterate]
    exact hmtw.transverse_second_nonpos x p xi eta s (hline s hs) hortho

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActionKernel
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

namespace WeakMTWTransport

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance actionKernelDualNormedSpace : NormedSpace ℝ (F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance actionKernelDualNormedAddCommGroup_r902208_1 : NormedAddCommGroup (F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance actionKernelBilinearNormedAddCommGroup_r902208_1 : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance actionKernelBilinearNormedSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ContDiffUncurryIterated
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

namespace WeakMTWTransport

lemma contDiffAt_uncurry_iteratedDeriv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → ℝ → F} {x : E} {t : ℝ}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x,t)) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun q : E×ℝ => iteratedDeriv k (f q.1) q.2) (x,t) := by
  induction k with
  | zero =>
    apply hf.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun q => congrFun (iteratedDeriv_zero (f := f q.1)) q.2)
  | succ k ih =>
    have hcomp : ContDiffAt ℝ ∞
        (Function.uncurry (fun q : E×ℝ => fun s : ℝ => iteratedDeriv k (f q.1) s)) ((x,t),t) :=
      ih.comp ((x,t),t) ((contDiffAt_fst.fst).prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞
        (fun q : E×ℝ => fderiv ℝ (iteratedDeriv k (f q.1)) q.2) (x,t) :=
      hcomp.fderiv contDiffAt_snd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [iteratedDeriv_succ,deriv] using hd.clm_apply (contDiffAt_const (c := (1:ℝ)))

lemma contDiffAt_iteratedDeriv_parameter {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → ℝ → F} {x : E} {t : ℝ}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x,t)) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun q : E => iteratedDeriv k (f q) t) x :=
  (contDiffAt_uncurry_iteratedDeriv hf k).comp x (contDiffAt_id.prodMk contDiffAt_const)

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

lemma continuous_cost_left (y : M) : Continuous (fun x => cost x y) := by
  exact ((continuous_id.dist continuous_const).pow 2).div_const 2

lemma continuous_cost_right (x : M) : Continuous (cost x) := by
  exact ((continuous_const.dist continuous_id).pow 2).div_const 2

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_RadialNull
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

lemma convex_linear_bound {f : ℝ → ℝ} {l C : ℝ} (hl : 0 < l)
    (hf : ConvexOn ℝ (Icc 0 l) f) (hzero : f 0 = 0) (hend : f l ≤ C * l)
    {t : ℝ} (ht : t ∈ Icc 0 l) : f t ≤ C * t := by
  have htl : 0 ≤ t / l := div_nonneg ht.1 hl.le
  have htl1 : t / l ≤ 1 := (div_le_one hl).mpr ht.2
  have hh := hf.2 (show (0 : ℝ) ∈ Icc 0 l from ⟨le_rfl, hl.le⟩)
    (show l ∈ Icc 0 l from ⟨hl.le, le_rfl⟩)
    (show 0 ≤ 1 - t / l from sub_nonneg.mpr htl1) htl (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, hzero] at hh
  have hcancel : t / l * l = t := div_mul_cancel₀ t hl.ne'
  rw [hcancel] at hh
  have hmul := mul_le_mul_of_nonneg_left hend htl
  apply hh.trans
  calc
    t / l * f l ≤ t / l * (C * l) := hmul
    _ = C * (t / l * l) := by ring
    _ = C * t := by rw [hcancel]

open scoped BoundedContinuousFunction

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActualParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set Filter Manifold Bundle
open scoped Topology ContDiff

section CompactEnvelopes
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

def modifiedDatum (v : M → ℝ) (a D b : ℝ) (B : ℝ → ℝ) (y : M) : ℝ :=
  v y+b*B ((v y-a)/D)

def parameterPenalty (bplus b : ℝ) : ℝ := b/4096+2*b^2/bplus

end CompactEnvelopes

end WeakMTWTransport

end

end OAI
end


