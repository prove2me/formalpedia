-- Prove2me | Definitions.Def_OAIQ240Bp007
-- name    : OAIQ240Bp007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:47:08.961746+00:00
-- url     : https://prove2.me/theorems/342f7d0c-8a7a-4bc7-ad29-4c5730b4c8fd
-- title:
--   Definitions bundle OAIQ240Bp007 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 182 declarations of OpenAI's Lean: 93 definitions, 3 instances and 86 theorems. The definitions and types are `OAI.PackingSufficiencySupport.Hamiltonian.ParametricDiskEmbedding.NestedOn`, `OAI.PackingSufficiencySupport.Hamiltonian.ParametricDiskEmbedding.pull`, `OAI.PackingSufficiencySupport.Hamiltonian.ParametricDiskEmbedding.restrictParam`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanarDiskEmbedding.Nested`, `OAI.PackingSufficiencySupport.Hamiltonian.PositivePartialChart`, `OAI.PackingSufficiencySupport.Hamiltonian.PositivePlaneTransitions`, `OAI.PackingSufficiencySupport.Hamiltonian.PreservesTwoFormOn`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothCircleAction.average`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothCircleAction.differential`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothCircleAction.generator`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothTwoFormFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothlyAmbientRelated`, `OAI.PackingSufficiencySupport.Hamiltonian.SupportedSmoothIsotopy.mono`, `OAI.PackingSufficiencySupport.Hamiltonian.SupportedSmoothIsotopy.trans`, `OAI.PackingSufficiencySupport.Hamiltonian.SupportedSmoothIsotopyFamily.conjugate`, `OAI.PackingSufficiencySupport.Hamiltonian.SupportedSmoothIsotopyFamily.constant`, `OAI.PackingSufficiencySupport.Hamiltonian.SupportedSmoothIsotopyFamily.eval`, `OAI.PackingSufficiencySupport.Hamiltonian.SupportedSmoothIsotopyFamily.mono`, `OAI.PackingSufficiencySupport.Hamiltonian.SupportedSmoothIsotopyFamily.refl`, `OAI.PackingSufficiencySupport.Hamiltonian.SupportedSmoothIsotopyFamily.timeCutoff`, `OAI.PackingSufficiencySupport.Hamiltonian.SupportedSmoothIsotopyFamily.trans`, `OAI.PackingSufficiencySupport.Hamiltonian.SurfaceCoordinateBox.compactCarrier`, `OAI.PackingSufficiencySupport.Hamiltonian.angularExtension`, `OAI.PackingSufficiencySupport.Hamiltonian.angularOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.areaPolar`, `OAI.PackingSufficiencySupport.Hamiltonian.areaPolarRadial`, `OAI.PackingSufficiencySupport.Hamiltonian.backgroundDensity`, `OAI.PackingSufficiencySupport.Hamiltonian.backgroundField`, `OAI.PackingSufficiencySupport.Hamiltonian.baseFiberField`, `OAI.PackingSufficiencySupport.Hamiltonian.chartSupportedOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.chartSupportedTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.circleClockDensity`, `OAI.PackingSufficiencySupport.Hamiltonian.circleFamilyDescent`, `OAI.PackingSufficiencySupport.Hamiltonian.circlePeriodicDescent`, `OAI.PackingSufficiencySupport.Hamiltonian.circlePullback`, `OAI.PackingSufficiencySupport.Hamiltonian.complexMonomialDerivative`, `OAI.PackingSufficiencySupport.Hamiltonian.cutoffWedge`, `OAI.PackingSufficiencySupport.Hamiltonian.familyGenerator`, `OAI.PackingSufficiencySupport.Hamiltonian.fsBallDifferential`, `OAI.PackingSufficiencySupport.Hamiltonian.joinedVeronese` and 53 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `BallPacking_Annuli_AnnularHandleCurvature`, `BallPacking_Annuli_BaseHorizontalForms`, `BallPacking_Annuli_CircleHandleBump`, `BallPacking_Annuli_CylinderAnnularNormalization`, `BallPacking_CircleAction_CircleRelativeOneForm`, `BallPacking_DiskMaps_CompactEmbeddingIsotopy`, `BallPacking_DiskMaps_FlatIsotopy`, `BallPacking_DiskMaps_NormalizedRoundedBoxes`, `BallPacking_DiskMaps_ParameterRelativeDiskMoser`, `BallPacking_Flows_ManifoldFormTransport`, `BallPacking_Flows_NonautonomousManifoldFlow`, `BallPacking_Flows_TimeSteps`, `BallPacking_Forms_ChartSupportedDensity`, `BallPacking_Forms_FixedSpatialIntegral`, `BallPacking_Forms_HorizontalCoupling`, `BallPacking_Forms_ManifoldFormTransport`, `BallPacking_Forms_QuadricInfinityPrimitive`, `BallPacking_Forms_SpatialOneForm`, `BallPacking_Fredholm_NonlinearReduction`, `BallPacking_Fredholm_SurjectiveParametricReduction`, `BallPacking_Hamiltonian_LiftedCompact`, `BallPacking_Kahler_PhaseArea`, `BallPacking_Layers_ParametricNestedDisks`, `BallPacking_Models_BallVolume`, `BallPacking_Moments_ConvexRearrangement`, `BallPacking_Moments_PolytopeSlices`, `BallPacking_Moments_RearrangementBounds`, `BallPacking_Moser_AnnularFinalPacking`, `BallPacking_Moser_BackgroundDensity`, `BallPacking_Moser_CircleCorrection`, `BallPacking_Moser_DiskMoser`, `BallPacking_Moser_ManifoldMoserField`, `BallPacking_Moser_ParametricMoser`, `BallPacking_Moser_PlanarCorrection`, `BallPacking_Moser_PlanarCovectorPrimitive`, `BallPacking_Moser_RelativeForms`, `BallPacking_Moser_SmoothManifoldIntegral`, `BallPacking_Moser_SymplecticFamily`, `BallPacking_Normal_TailLineCoordinates`, `BallPacking_Projective_CubicEndCoordinates`, `BallPacking_RelativeJets_SymplecticProjectionNaturality`, `BallPacking_Residues_AreaPolarChart`, `BallPacking_SurfaceArea_QuadricEndResidueMass`, `BallPacking_SurfaceArea_SurfacePrimitiveOperator`, `BallPacking_Surfaces_DiagonalQuadric`, `BallPacking_Surfaces_QuadricOrientation`, `BallPacking_Toric_SixModelComparisonData`.
--
--   **Imports.** It imports the bundles `OAIQ240Bp000`, `OAIQ240Bp002`, `OAIQ240Bp003` and `OAIQ240Bp004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp009` and `OAIQ240Bp010`; the statements `OAI.PackingSufficiencySupport.Hamiltonian.manifold_exact_sublevel_moser_bp240`, `OAI_PackingSufficiencySupport_actual_complement_packing`, `OAI.PackingSufficiencySupport.actual_complement_packing_bp240`, `OAI_PackingSufficiencySupport_hasPacking_six_large_normalized` and `OAI.PackingSufficiencySupport.hasPacking_six_large_normalized_bp240`; the proofs of `OAI_HigherDimensionalBallPacking_Rigidity_augment_fredholm` and `OAI.HigherDimensionalBallPacking.Rigidity.augment_fredholm_bp240`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ240Bp000
import Definitions.Def_OAIQ240Bp002
import Definitions.Def_OAIQ240Bp003
import Definitions.Def_OAIQ240Bp004

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_RelativeForms
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology NNReal

open scoped ContDiff Topology
open Set Metric

open scoped ContDiff Topology
open Set Metric

namespace PackingSufficiencySupport.Hamiltonian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


open scoped NNReal

theorem localPath_fixed {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {p : E × ℝ} (hp : p ∈ picardDomain L) :
    picard X p (localPath X hX p) = localPath X hX p := by
  simp only [localPath, dite_eq_left hp]
  exact (picard_contracts X hX hp).fixedPoint_isFixedPt

theorem localPath_smooth [FiniteDimensional ℝ E] {L : ℝ≥0}
    (X : C(E,E)) (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X) :
    ContDiffOn ℝ ∞ (localPath X hX) (picardDomain L) := by
  apply smoothOn_contraction_solution (picardDomain_open L) (picard_contDiff X hXs)
  · intro p hp
    exact ⟨_,picard_contracts X hX hp⟩
  · exact fun _ hp => localPath_fixed X hX hp

theorem fixedStep_smooth [FiniteDimensional ℝ E] {L : ℝ≥0}
    (X : C(E,E)) (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ} (hh : ‖h‖ * L < 1) : ContDiff ℝ ∞ (fixedStep X hX h) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact ((localPath_smooth X hX hXs).contDiffAt
    ((picardDomain_open L).mem_nhds hh)).comp x
      (contDiff_id.prodMk contDiff_const).contDiffAt

theorem fixedStep_equation {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (x : E) :
    fixedStep X hX h x = constantPath x + h • pathIntegral (X.comp (fixedStep X hX h x)) :=
  (localPath_fixed X hX (p := (x,h)) hh).symm

@[simp] theorem fixedStep_initial {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (x : E) :
    fixedStep X hX h x ⟨0,by simp⟩ = x := by
  have he := congrArg (fun u : C(Time,E) => u ⟨0,by simp⟩) (fixedStep_equation X hX hh x)
  simpa using he

theorem fixedStep_variation [FiniteDimensional ℝ E] {L : ℝ≥0}
    (X : C(E,E)) (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (x : E) :
    fderiv ℝ (fixedStep X hX h) x = constantPath +
      h • pathIntegral ∘L pathLinear
        ⟨fun t => fderiv ℝ X (fixedStep X hX h x t),
          (hXs.continuous_fderiv (by simp)).comp (fixedStep X hX h x).continuous⟩ ∘L
        fderiv ℝ (fixedStep X hX h) x := by
  let u := fixedStep X hX h
  have hu : HasFDerivAt u (fderiv ℝ u x) x :=
    ((fixedStep_smooth X hX hXs hh).differentiable (by simp) x).hasFDerivAt
  have hN := (postcomp_hasFDerivAt (hXs.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (u x)).comp x hu
  have hI := (pathIntegral (E := E)).hasFDerivAt.comp x hN
  have hR := (constantPath (E := E)).hasFDerivAt.add (hI.const_smul h)
  have heq : (fun y => constantPath y + h • pathIntegral (X.comp (u y))) = u := by
    funext y
    exact (fixedStep_equation X hX hh y).symm
  change HasFDerivAt (fun y => constantPath y + h • pathIntegral (X.comp (u y))) _ x at hR
  rw [heq] at hR
  exact hu.unique hR

theorem path_equation_derivative (u v : C(Time,E)) (a : E) (h : ℝ)
    (hu : u = constantPath a + h • pathIntegral v)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (extendPath u) (h • extendPath v s) (Icc (0 : ℝ) 1) s := by
  have hi := intervalIntegral.integral_hasDerivAt_right
    ((extendPath v).continuous.intervalIntegrable 0 s)
    (extendPath v).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    (extendPath v).continuous.continuousAt
  have hd := (hasDerivAt_const s a).add (HasDerivAt.const_smul h hi)
  simp only [zero_add] at hd
  apply hd.hasDerivWithinAt.congr_of_mem _ hs
  intro t ht
  have he := congrArg (fun w : C(Time,E) => w ⟨t,ht⟩) hu
  rw [show extendPath u t = u ⟨t,ht⟩ from extendPath_coe u ⟨t,ht⟩]
  exact he

theorem fixedStep_derivative {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (x : E) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (extendPath (fixedStep X hX h x))
      (h • X (extendPath (fixedStep X hX h x) s)) (Icc (0 : ℝ) 1) s :=
  path_equation_derivative _ _ x h (fixedStep_equation X hX hh x) hs

def stepEndpoint {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X) (h : ℝ) (x : E) : E :=
  fixedStep X hX h x ⟨1,by simp⟩

theorem stepEndpoint_smooth [FiniteDimensional ℝ E] {L : ℝ≥0}
    (X : C(E,E)) (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ} (hh : ‖h‖ * L < 1) : ContDiff ℝ ∞ (stepEndpoint X hX h) :=
  (ContinuousMap.evalCLM (M := E) ℝ (⟨1,by simp⟩ : Time)).contDiff.comp
    (fixedStep_smooth X hX hXs hh)

theorem stepEndpoint_fderiv [FiniteDimensional ℝ E] {L : ℝ≥0}
    (X : C(E,E)) (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (x : E) :
    fderiv ℝ (stepEndpoint X hX h) x =
      (ContinuousMap.evalCLM (M := E) ℝ (⟨1,by simp⟩ : Time)).comp
        (fderiv ℝ (fixedStep X hX h) x) := by
  exact ((ContinuousMap.evalCLM (M := E) ℝ (⟨1,by simp⟩ : Time)).hasFDerivAt.comp x
    (((fixedStep_smooth X hX hXs hh).differentiable (by simp) x).hasFDerivAt)).fderiv

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def reverseTime (s : Time) : Time :=
  ⟨1 - (s : ℝ), sub_nonneg.mpr s.property.2, sub_le_self 1 s.property.1⟩

def reversePath (u : C(Time,E)) : C(Time,E) :=
  u.comp ⟨reverseTime, (continuous_const.sub continuous_subtype_val).subtype_mk _⟩

omit [CompleteSpace E] in
theorem reversePath_integral (X : C(E,E)) (u : C(Time,E)) (s : Time) :
    (∫ t in 0..(s : ℝ), extendPath (X.comp (reversePath u)) t) =
      ∫ t in 1 - (s : ℝ)..1, extendPath (X.comp u) t := by
  have he : (∫ t in 0..(s : ℝ), extendPath (X.comp (reversePath u)) t) =
      ∫ t in 0..(s : ℝ), extendPath (X.comp u) (1 - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le s.property.1] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans s.property.2⟩
    have ht'' : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht'.1,ht'.2]
    change extendPath (X.comp (reversePath u)) t = extendPath (X.comp u) (1-t)
    rw [show extendPath (X.comp (reversePath u)) t = (X.comp (reversePath u)) ⟨t,ht'⟩
      from extendPath_coe _ ⟨t,ht'⟩,
      show extendPath (X.comp u) (1-t) = (X.comp u) ⟨1-t,ht''⟩
      from extendPath_coe _ ⟨1-t,ht''⟩]
    rfl
  rw [he, intervalIntegral.integral_comp_sub_left]
  simp

theorem fixedStep_reverse {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (x : E) :
    fixedStep X hX (-h) (stepEndpoint X hX h x) = reversePath (fixedStep X hX h x) := by
  let u := fixedStep X hX h x
  have hh' : ‖-h‖ * L < 1 := by simpa using hh
  apply (picard_contracts X hX (p := (stepEndpoint X hX h x,-h)) hh').fixedPoint_unique'
    (localPath_fixed X hX (p := (stepEndpoint X hX h x,-h)) hh')
  ext s
  change stepEndpoint X hX h x + (-h) •
    (∫ t in 0..(s : ℝ), extendPath (X.comp (reversePath u)) t) = reversePath u s
  rw [reversePath_integral]
  have hs : 1 - (s : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [s.property.1,s.property.2]
  have h1 := congrArg (fun v : C(Time,E) => v ⟨1,by simp⟩) (fixedStep_equation X hX hh x)
  have h2 := congrArg (fun v : C(Time,E) => v ⟨1-(s:ℝ),hs⟩) (fixedStep_equation X hX hh x)
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    ((extendPath (X.comp u)).continuous.intervalIntegrable 0 (1-(s:ℝ)))
    ((extendPath (X.comp u)).continuous.intervalIntegrable (1-(s:ℝ)) 1)
  change u ⟨1,by simp⟩ = x + h • (∫ t in 0..1, extendPath (X.comp u) t) at h1
  change u ⟨1-(s:ℝ),hs⟩ = x + h • (∫ t in 0..1-(s:ℝ), extendPath (X.comp u) t) at h2
  change u ⟨1,by simp⟩ + _ = u ⟨1-(s:ℝ),hs⟩
  rw [h1,h2,← hi, smul_add,neg_smul]
  abel

theorem stepEndpoint_neg_leftInverse {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) :
    Function.LeftInverse (stepEndpoint X hX (-h)) (stepEndpoint X hX h) := by
  intro x
  change fixedStep X hX (-h) (stepEndpoint X hX h x) ⟨1,by simp⟩ = x
  rw [fixedStep_reverse X hX hh]
  change fixedStep X hX h x ⟨1-1,by norm_num⟩ = x
  convert fixedStep_initial X hX hh x using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_TimeSteps
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology NNReal
open scoped ContDiff Topology
open Set Metric
open scoped ContDiff Topology
open Set Metric
namespace PackingSufficiencySupport.Hamiltonian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem fixedStep_clock {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (p : ℝ × E) (s : Time) :
    (fixedStep (clockField X) (clockField_lipschitz X hX) h p s).1 = p.1 + h * (s : ℝ) := by
  let u := fixedStep (clockField X) (clockField_lipschitz X hX) h p
  have he := congrArg (fun v : C(Time,ℝ × E) => (v s).1)
    (fixedStep_equation (clockField X) (clockField_lipschitz X hX) hh p)
  have hi := (ContinuousLinearMap.fst ℝ ℝ E).intervalIntegral_comp_comm (μ := MeasureTheory.volume)
    ((extendPath ((clockField X).comp u)).continuous.intervalIntegrable 0 (s:ℝ))
  have hc : (fun t : ℝ => (extendPath ((clockField X).comp u) t).1) = fun _ => (1:ℝ) := by
    funext t
    rfl
  change (∫ t in 0..(s:ℝ), (extendPath ((clockField X).comp u) t).1) =
    (∫ t in 0..(s:ℝ), extendPath ((clockField X).comp u) t).1 at hi
  rw [hc] at hi
  change (u s).1 = p.1 + h * (∫ t in 0..(s:ℝ), extendPath ((clockField X).comp u) t).1 at he
  rw [← hi] at he
  simpa using he

@[simp] theorem stepEndpoint_clock {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (p : ℝ × E) :
    (stepEndpoint (clockField X) (clockField_lipschitz X hX) h p).1 = p.1 + h := by
  simpa only [stepEndpoint,mul_one] using fixedStep_clock X hX hh p ⟨1,by simp⟩

def timeStep {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X) (h t : ℝ) (x : E) : E :=
  (stepEndpoint (clockField X) (clockField_lipschitz X hX) h (t,x)).2

theorem timeStep_smooth [FiniteDimensional ℝ E] {L : ℝ≥0}
    (X : C(ℝ × E,E)) (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) : ContDiff ℝ ∞ (timeStep X hX h t) :=
  ((stepEndpoint_smooth (clockField X) (clockField_lipschitz X hX)
    (clockField_smooth X hXs) hh).comp (contDiff_const.prodMk contDiff_id)).snd

theorem timeStep_inverse {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) :
    Function.LeftInverse (timeStep X hX (-h) (t+h)) (timeStep X hX h t) := by
  intro x
  have he := congrArg Prod.snd (stepEndpoint_neg_leftInverse (clockField X)
    (clockField_lipschitz X hX) hh (t,x))
  have hp : stepEndpoint (clockField X) (clockField_lipschitz X hX) h (t,x) =
      (t+h,timeStep X hX h t x) := by
    apply Prod.ext
    · exact stepEndpoint_clock X hX hh (t,x)
    · rfl
  rw [hp] at he
  exact he

def timeStepHomeomorph [FiniteDimensional ℝ E] {L : ℝ≥0}
    (X : C(ℝ × E,E)) (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) : E ≃ₜ E where
  toFun := timeStep X hX h t
  invFun := timeStep X hX (-h) (t+h)
  left_inv := timeStep_inverse X hX hh t
  right_inv := by
    intro x
    simpa only [neg_neg, add_neg_cancel_right] using
      timeStep_inverse X hX (h := -h) (by simpa using hh) (t+h) x
  continuous_toFun := (timeStep_smooth X hX hXs hh t).continuous
  continuous_invFun := (timeStep_smooth X hX hXs (h := -h) (by simpa using hh) (t+h)).continuous

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem fixedStep_variation_clock {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖ * L < 1)
    (p : ℝ × E) (v : E) (s : Time) :
    ((fderiv ℝ (fixedStep (clockField X) (clockField_lipschitz X hX) h) p (0,v)) s).1 = 0 := by
  let u := fixedStep (clockField X) (clockField_lipschitz X hX) h
  have hu := ((fixedStep_smooth (clockField X) (clockField_lipschitz X hX)
    (clockField_smooth X hXs) hh).differentiable (by simp) p).hasFDerivAt
  have hd := (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp p
    ((ContinuousMap.evalCLM (M := ℝ × E) ℝ s).hasFDerivAt.comp p hu)
  have he : (fun q => (u q s).1) = fun q : ℝ × E => q.1 + h * (s:ℝ) := by
    funext q
    exact fixedStep_clock X hX hh q s
  change HasFDerivAt (fun q => (u q s).1) _ p at hd
  rw [he] at hd
  have hd' := (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.add_const (h * (s:ℝ)) (x := p)
  have huniq := congrArg (fun A : (ℝ × E) →L[ℝ] ℝ => A (0,v)) (hd.unique hd')
  exact huniq

theorem timeStep_fderiv {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (x v : E) :
    fderiv ℝ (timeStep X hX h t) x v =
      (fderiv ℝ (stepEndpoint (clockField X) (clockField_lipschitz X hX) h) (t,x) (0,v)).2 := by
  have hs := ((stepEndpoint_smooth (clockField X) (clockField_lipschitz X hX)
    (clockField_smooth X hXs) hh).differentiable (by simp) (t,x)).hasFDerivAt
  have hp : HasFDerivAt (fun x : E => (t,x)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hd := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp x (hs.comp x hp)
  exact congrArg (fun A : E →L[ℝ] E => A v) hd.fderiv


omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem clockField_fderiv {X : C(ℝ × E,E)} (hXs : ContDiff ℝ ∞ X) (p v : ℝ × E) :
    fderiv ℝ (clockField X) p v = (0, fderiv ℝ X p v) := by
  have hd := (hasFDerivAt_const (1:ℝ) p).prodMk
    ((hXs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt)
  exact congrArg (fun A : (ℝ × E) →L[ℝ] (ℝ × E) => A v) hd.fderiv

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem timeStep_of_stationary {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) {x : E} (hx : ∀ s, X (s,x) = 0) :
    timeStep X hX h t x = x := by
  let q : C(Time,ℝ × E) := constantPath (t,x) + h • pathIntegral (constantPath (1,0))
  have hq (s : Time) : q s = (t+h*(s:ℝ),x) := by
    change (t,x) + h • (∫ a in (0:ℝ)..(s:ℝ), extendPath (constantPath (1,0)) a) = _
    have he : (fun a : ℝ => extendPath (constantPath ((1:ℝ),(0:E))) a) = fun _ => ((1:ℝ),(0:E)) := rfl
    rw [he,intervalIntegral.integral_const]
    simp
  have hy : (clockField X).comp q = constantPath (1,0) := by
    apply ContinuousMap.ext
    intro s
    change clockField X (q s) = (1,0)
    rw [hq,clockField_apply,hx]
  have hu : fixedStep (clockField X) (clockField_lipschitz X hX) h (t,x) = q := by
    apply (picard_contracts (clockField X) (clockField_lipschitz X hX) (p := ((t,x),h)) hh).fixedPoint_unique'
      (localPath_fixed (clockField X) (clockField_lipschitz X hX) (p := ((t,x),h)) hh)
    change constantPath (t,x) + h • pathIntegral ((clockField X).comp q) = q
    rw [hy]
  change (fixedStep (clockField X) (clockField_lipschitz X hX) h (t,x) ⟨1,by simp⟩).2 = x
  rw [hu,hq]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

def timeSteps {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) : ℕ → E ≃ₜ E
  | 0 => Homeomorph.refl E
  | N+1 => (timeSteps X hX hXs hh t N).trans (timeStepHomeomorph X hX hXs hh (t+N*h))

theorem timeSteps_smooth {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (timeSteps X hX hXs hh t N) ∧
      ContDiff ℝ ∞ (timeSteps X hX hXs hh t N).symm := by
  induction N with
  | zero => exact ⟨contDiff_id,contDiff_id⟩
  | succ N ih =>
    constructor
    · exact (timeStep_smooth X hX hXs hh (t+N*h)).comp ih.1
    · exact ih.2.comp (timeStep_smooth X hX hXs (h := -h) (by simpa using hh) ((t+N*h)+h))

theorem timeSteps_of_stationary {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (N : ℕ)
    {x : E} (hx : ∀ s, X (s,x) = 0) : timeSteps X hX hXs hh t N x = x := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change timeStep X hX h (t+N*h) (timeSteps X hX hXs hh t N x) = x
    rw [ih,timeStep_of_stationary X hX hh _ hx]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian

def segmentLinear : (ℝ × ℝ) →L[ℝ] C(Time,ℝ × ℝ) :=
  LinearMap.mkContinuous {
    toFun := fun p => ⟨fun s => ((s : ℝ) * p.1,p.2),
      (continuous_subtype_val.mul continuous_const).prodMk continuous_const⟩
    map_add' := by intros; ext s <;> simp [mul_add]
    map_smul' := by intros; ext s <;> simp [mul_left_comm] }
    1 (by
      intro p
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg p)).mpr
      intro s
      change ‖((s:ℝ)*p.1,p.2)‖ ≤ ‖p‖
      simp only [Prod.norm_def, norm_mul, Real.norm_eq_abs, abs_of_nonneg s.property.1]
      apply max_le
      · exact (mul_le_of_le_one_left (abs_nonneg p.1)
          (by simpa only [abs_of_nonneg s.property.1] using s.property.2)).trans (le_max_left _ _)
      · exact le_max_right _ _)

def segmentPath (a : ℝ) (p : ℝ × ℝ) : C(Time,ℝ × ℝ) :=
  constantPath (a,0) + segmentLinear (p - (a,0))

@[simp] theorem segmentPath_apply (a : ℝ) (p : ℝ × ℝ) (s : Time) :
    segmentPath a p s = (a + (s : ℝ) * (p.1-a),p.2) := by
  change (a + (s:ℝ)*(p.1-a),0+(p.2-0)) = _
  simp

def pathAverage : C(Time,ℝ) →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ (⟨1,by simp⟩ : Time)).comp pathIntegral

open MeasureTheory Function

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_PlanarCorrection
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Metric
open MeasureTheory Function
open scoped Classical

def planarCurl (alpha : Plane → Plane →L[ℝ] ℝ) (p : Plane) : ℝ :=
  fderiv ℝ alpha p (1,0) (0,1) - fderiv ℝ alpha p (0,1) (1,0)

def pullbackForm (phi : Plane → Plane) (alpha : Plane → Plane →L[ℝ] ℝ)
    (p : Plane) : Plane →L[ℝ] ℝ := (alpha (phi p)).comp (fderiv ℝ phi p)

def angularExtension (R delta : ℝ) (hd : 0 < delta) (h : ℝ → ℝ) (p : Plane) : ℝ :=
  let b : ContDiffBump (R^2) := ⟨delta/2,delta,by positivity,by linarith⟩
  b (radiusSq p) * h (Complex.arg (Complex.equivRealProdCLM.symm p))

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_CircleCorrection
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Metric
open scoped Classical
open Function MeasureTheory
def circlePullback (alpha : Plane → Plane →L[ℝ] ℝ) (R t : ℝ) : ℝ :=
  alpha (polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t)

def radialDrift (X : ℝ × Plane → Plane) (p : ℝ × Plane) : ℝ :=
  2*(p.2.1*(X p).1+p.2.2*(X p).2)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_BackgroundDensity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology NNReal
open scoped ContDiff Topology
open Set Metric
open scoped ContDiff Topology
open Set Metric
open scoped ContDiff Classical
open Set Function MeasureTheory
open scoped ContDiff Topology Classical NNReal
open Set Function MeasureTheory

def backgroundDensity (g f : Plane → ℝ) (p : ℝ × Plane) : ℝ :=
  g p.2 + Real.smoothTransition p.1 * f p.2

def backgroundField (g f U V : Plane → ℝ) (p : ℝ × Plane) : Plane :=
  (-(deriv Real.smoothTransition p.1) * V p.2 / backgroundDensity g f p,
    (deriv Real.smoothTransition p.1) * U p.2 / backgroundDensity g f p)


end

section
open scoped ContDiff Topology NNReal
open Set Function MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def parameterSegmentLinear : (P × ℝ) →L[ℝ] C(Time,P × ℝ) :=
  LinearMap.mkContinuous {
    toFun := fun p => ⟨fun s => (p.1,(s:ℝ)*p.2),
      continuous_const.prodMk (continuous_subtype_val.mul continuous_const)⟩
    map_add' := by intros; ext s <;> simp [mul_add]
    map_smul' := by intros; ext s <;> simp [mul_left_comm] }
    1 (by
      intro p
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg p)).mpr
      intro s
      change ‖(p.1,(s:ℝ)*p.2)‖ ≤ ‖p‖
      simp only [Prod.norm_def,norm_mul,Real.norm_eq_abs,abs_of_nonneg s.property.1]
      apply max_le
      · exact le_max_left _ _
      · exact (mul_le_of_le_one_left (abs_nonneg p.2) s.property.2).trans (le_max_right _ _))

def parameterSegmentPath (a : ℝ) (p : P × ℝ) : C(Time,P × ℝ) :=
  constantPath (0,a) + parameterSegmentLinear (p-(0,a))

@[simp] theorem parameterSegmentPath_apply (a : ℝ) (p : P × ℝ) (s : Time) :
    parameterSegmentPath a p s = (p.1,a+(s:ℝ)*(p.2-a)) := by
  change (0+(p.1-0),a+(s:ℝ)*(p.2-a)) = _
  simp


end

open scoped ContDiff



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_PlanarCovectorPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def timeChartField (V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2)
    (c : M) (p : ℝ × E) : E :=
  let z := (extChartAt 𝓘(ℝ,E) c).symm p.2
  chartDifferential c z (V (p.1,z))



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ManifoldMoserField
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open scoped NNReal
open MeasureTheory
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def manifoldMoserField (Ω : ℝ → ManifoldTwoForm E M)
    (α : ℝ → ManifoldOneForm E M) (p : ℝ × M) : TangentSpace 𝓘(ℝ,E) p.2 :=
  -(Ω p.1 p.2).inverse (α p.1 p.2)

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ParametricMoser
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Function MeasureTheory

def radialDiskDensity (R : ℝ) (p : Plane) : ℝ := R^2/(1+radiusSq p)^2

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_DiskMoser
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def spatialJacobian (F : P × Plane → Plane) (p : P × Plane) : ℝ :=
  (fderiv ℝ (fun x => F (p.1,x)) p.2).det

variable [FiniteDimensional ℝ P]

def rectangularPotential (B : ℝ) (α : P × Plane → Plane →L[ℝ] ℝ) (p : P × Plane) : ℝ :=
  (∫ t in B..p.2.1, α (p.1,(t,B)) (1,0)) +
    ∫ t in B..p.2.2, α (p.1,(p.2.1,t)) (0,1)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_SymplecticFamily
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def familyGenerator (φ : P → Plane ≃ₜ Plane) (v : P) (p : P × Plane) : Plane :=
  fderiv ℝ (fun q : P × Plane => φ q.1 q.2) (p.1,(φ p.1).symm p.2) (v,0)


end

section
open scoped ContDiff Topology NNReal
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem timeStep_preserves_form {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (hΩ : ContDiff ℝ ∞ Ω)
    (hPDE : ∀ p v w, fderiv ℝ Ω p (1,X p) v w +
      Ω p (fderiv ℝ X p (0,v)) w + Ω p v (fderiv ℝ X p (0,w)) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (x v w : E) :
    Ω (t+h,timeStep X hX h t x)
      (fderiv ℝ (timeStep X hX h t) x v) (fderiv ℝ (timeStep X hX h t) x w) =
      Ω (t,x) v w := by
  let Y := clockField X
  let hY := clockField_lipschitz X hX
  let u := fixedStep Y hY h (t,x)
  let A := fderiv ℝ (fixedStep Y hY h) (t,x)
  let D : C(Time,(ℝ × E) →L[ℝ] (ℝ × E)) :=
    ⟨fun s => fderiv ℝ Y (u s),
      ((clockField_smooth X hXs).continuous_fderiv (by simp)).comp u.continuous⟩
  have hA (z : ℝ × E) : A z = constantPath z + h • pathIntegral (pathLinear D (A z)) :=
    congrArg (fun T : (ℝ × E) →L[ℝ] C(Time,ℝ × E) => T z)
      (fixedStep_variation Y hY (clockField_smooth X hXs) hh (t,x))
  have hA0 (z : ℝ × E) : extendPath (A z) 0 = z := by
    have he := congrArg (fun V : C(Time,ℝ × E) => V ⟨0,by simp⟩) (hA z)
    exact (extendPath_coe (A z) ⟨0,by simp⟩).trans (by simpa using he)
  let V : E → ℝ → E := fun z s => (extendPath (A (0,z)) s).2
  have hhor (z : E) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      extendPath (A (0,z)) s = (0,V z s) := by
    apply Prod.ext
    · rw [show extendPath (A (0,z)) s = A (0,z) ⟨s,hs⟩ from extendPath_coe _ ⟨s,hs⟩]
      exact fixedStep_variation_clock X hX hXs hh (t,x) z ⟨s,hs⟩
    · rfl
  have hVd (z : E) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt (V z) (h • fderiv ℝ X (extendPath u s) (0,V z s)) (Icc (0:ℝ) 1) s := by
    have hd := (path_equation_derivative _ _ (0,z) h (hA (0,z)) hs).snd
    change HasDerivWithinAt (V z)
      (h • (fderiv ℝ Y (extendPath u s) (extendPath (A (0,z)) s)).2) _ s at hd
    rw [hhor z s hs,clockField_fderiv hXs] at hd
    exact hd
  let F : ℝ → ℝ := fun s => Ω (extendPath u s) (V v s) (V w s)
  have hFc : Continuous F := ((hΩ.continuous.comp (extendPath u).continuous).clm_apply
    (extendPath (A (0,v))).continuous.snd).clm_apply (extendPath (A (0,w))).continuous.snd
  have hFd (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) : HasDerivAt F 0 s := by
    have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1.le,hs.2.le⟩
    have hUd := fixedStep_derivative Y hY hh (t,x) hs'
    have hΩd := ((hΩ.differentiable (by simp) (extendPath u s)).hasFDerivAt).comp_hasDerivWithinAt s hUd
    have hd := (hΩd.clm_apply (hVd v s hs')).clm_apply (hVd w s hs')
    have hz : (fderiv ℝ Ω (extendPath u s) (h • Y (extendPath u s)) (V v s) +
        Ω (extendPath u s) (h • fderiv ℝ X (extendPath u s) (0,V v s))) (V w s) +
        Ω (extendPath u s) (V v s) (h • fderiv ℝ X (extendPath u s) (0,V w s)) = 0 := by
      simp only [map_smul,smul_apply,smul_eq_mul,add_apply]
      have he := hPDE (extendPath u s) (V v s) (V w s)
      change fderiv ℝ Ω (extendPath u s) (Y (extendPath u s)) (V v s) (V w s) +
        Ω (extendPath u s) (fderiv ℝ X (extendPath u s) (0,V v s)) (V w s) +
        Ω (extendPath u s) (V v s) (fderiv ℝ X (extendPath u s) (0,V w s)) = 0 at he
      linear_combination h * he
    have hd0 : HasDerivWithinAt F 0 (Icc (0:ℝ) 1) s := hd.congr_deriv hz
    exact hd0.hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    hFc.continuousOn hFd (intervalIntegrable_const (c := (0:ℝ)))
  have hend : F 1 = F 0 := sub_eq_zero.mp (by simpa using hi.symm)
  have hzero : F 0 = Ω (t,x) v w := by
    change Ω (extendPath u 0) (extendPath (A (0,v)) 0).2 (extendPath (A (0,w)) 0).2 = _
    rw [hA0,hA0,show extendPath u 0 = (t,x) from
      (extendPath_coe u ⟨0,by simp⟩).trans (fixedStep_initial Y hY hh (t,x))]
  have hfinal : extendPath u 1 = (t+h,timeStep X hX h t x) := by
    rw [show extendPath u 1 = u ⟨1,by simp⟩ from extendPath_coe u ⟨1,by simp⟩]
    exact Prod.ext (stepEndpoint_clock X hX hh (t,x)) rfl
  have hfinalV (z : E) : V z 1 = fderiv ℝ (timeStep X hX h t) x z := by
    rw [timeStep_fderiv X hX hXs hh, stepEndpoint_fderiv Y hY (clockField_smooth X hXs) hh]
    exact congrArg Prod.snd (extendPath_coe (A (0,z)) ⟨1,by simp⟩)
  have hone : F 1 = Ω (t+h,timeStep X hX h t x) (fderiv ℝ (timeStep X hX h t) x v) (fderiv ℝ (timeStep X hX h t) x w) := by
    change Ω (extendPath u 1) (V v 1) (V w 1) = _
    rw [hfinal,hfinalV,hfinalV]
  exact hone.symm.trans (hend.trans hzero)

theorem timeSteps_preserves_form {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (hΩ : ContDiff ℝ ∞ Ω)
    (hPDE : ∀ p v w, fderiv ℝ Ω p (1,X p) v w +
      Ω p (fderiv ℝ X p (0,v)) w + Ω p v (fderiv ℝ X p (0,w)) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (N : ℕ) (x v w : E) :
    Ω (t+N*h,timeSteps X hX hXs hh t N x)
      (fderiv ℝ (timeSteps X hX hXs hh t N) x v)
      (fderiv ℝ (timeSteps X hX hXs hh t N) x w) = Ω (t,x) v w := by
  induction N with
  | zero => simp [timeSteps]
  | succ N ih =>
    let F := timeSteps X hX hXs hh t N
    let G := timeStep X hX h (t+N*h)
    have hF : Differentiable ℝ F := (timeSteps_smooth X hX hXs hh t N).1.differentiable (by simp)
    have hG : Differentiable ℝ G := (timeStep_smooth X hX hXs hh (t+N*h)).differentiable (by simp)
    change Ω (t+(N+1:ℕ)*h,G (F x))
      (fderiv ℝ (G ∘ F) x v) (fderiv ℝ (G ∘ F) x w) = _
    rw [fderiv_comp x (hG (F x)) (hF x)]
    have ht : t + (N+1:ℕ)*h = (t+N*h)+h := by push_cast <;> ring
    rw [ht]
    exact (timeStep_preserves_form X hX hXs Ω hΩ hPDE hh (t+N*h) (F x)
      (fderiv ℝ F x v) (fderiv ℝ F x w)).trans ih


end

section
open scoped ContDiff Topology NNReal
open Set Function

variable {E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup Q] [NormedSpace ℝ Q]

omit [FiniteDimensional ℝ E] in
@[simp] theorem timeStep_zero {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (t : ℝ) (x : E) : timeStep X hX 0 t x = x := by
  have he := fixedStep_equation (clockField X) (clockField_lipschitz X hX)
    (h := 0) (by simp) (t,x)
  simp only [zero_smul,add_zero] at he
  change (fixedStep (clockField X) (clockField_lipschitz X hX) 0 (t,x) ⟨1,by simp⟩).2 = x
  rw [he]
  rfl

@[simp] theorem timeSteps_zero {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (t : ℝ) (N : ℕ) (x : E) :
    timeSteps X hX hXs (h := 0) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t N x = x := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change timeStep X hX 0 (t+N*0) (timeSteps X hX hXs (h := 0) (by simp) t N x) = x
    rw [timeStep_zero,ih]

omit [FiniteDimensional ℝ E] in

theorem fixedStep_eq_solution {L : ℝ≥0} (X : C(E,E))
    (hX : LipschitzWith L X) {h : ℝ} (hh : ‖h‖ * L < 1)
    (u : C(Time,E)) (x : E) (hu0 : u ⟨0,by simp⟩ = x)
    (hud : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (extendPath u) (h • X (extendPath u s)) s) :
    fixedStep X hX h x = u := by
  apply (picard_contracts X hX (p := (x,h)) hh).fixedPoint_unique'
    (localPath_fixed X hX (p := (x,h)) hh)
  ext s
  change x + h • (∫ t in 0..(s : ℝ), extendPath (X.comp u) t) = u s
  have hd (t : ℝ) (ht : t ∈ Ioo 0 (s : ℝ)) :
      HasDerivAt (extendPath u) (h • extendPath (X.comp u) t) t := by
    exact hud t ⟨ht.1,ht.2.trans_le s.property.2⟩
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le s.property.1
    (extendPath u).continuous.continuousOn hd
    ((continuous_const.smul (extendPath (X.comp u)).continuous).intervalIntegrable 0 s)
  rw [intervalIntegral.integral_smul,extendPath_coe u s,
    extendPath_coe u ⟨0,by simp⟩,hu0] at hi
  rw [hi]
  abel

omit [FiniteDimensional ℝ E] in

theorem timeStep_eq_solution {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) {h : ℝ} (hh : ‖h‖ * L < 1)
    (u : ℝ → E) (hu : Continuous u)
    (hud : ∀ s, HasDerivAt u (X (s,u s)) s) (t : ℝ) :
    timeStep X hX h t (u t) = u (t+h) := by
  let v : C(Time,ℝ × E) := ⟨fun s => (t+h*(s:ℝ),u (t+h*(s:ℝ))),
    (continuous_const.add (continuous_const.mul continuous_subtype_val)).prodMk
      (hu.comp (continuous_const.add (continuous_const.mul continuous_subtype_val)))⟩
  have hv0 : v ⟨0,by simp⟩ = (t,u t) := by simp [v]
  have hvd (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (extendPath v)
        (h • clockField X (extendPath v s)) s := by
    have he : extendPath v =ᶠ[𝓝 s] (fun r => (t+h*r,u (t+h*r))) := by
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
      exact extendPath_coe v ⟨r,hr⟩
    have ha : HasDerivAt (fun r : ℝ => t+h*r) h s := by
      exact (hasDerivAt_const_mul h).const_add t
    have huc := (hud (t+h*s)).scomp s ha
    have hv := ha.prodMk huc
    have hp : extendPath v s = (t+h*s,u (t+h*s)) := he.eq_of_nhds
    rw [hp,clockField_apply]
    simpa only [Prod.smul_mk,smul_eq_mul,mul_one] using hv.congr_of_eventuallyEq he
  have he := fixedStep_eq_solution (clockField X) (clockField_lipschitz X hX)
    hh v (t,u t) hv0 hvd
  change (fixedStep (clockField X) (clockField_lipschitz X hX) h (t,u t) ⟨1,by simp⟩).2 = _
  rw [he]
  simp [v]

theorem timeSteps_eq_solution {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (u : ℝ → E) (hu : Continuous u)
    (hud : ∀ s, HasDerivAt u (X (s,u s)) s) (t : ℝ) (N : ℕ) :
    timeSteps X hX hXs hh t N (u t) = u (t+N*h) := by
  induction N with
  | zero => simp [timeSteps]
  | succ N ih =>
    change timeStep X hX h (t+N*h) (timeSteps X hX hXs hh t N (u t)) = _
    rw [ih,timeStep_eq_solution X hX hh u hu hud]
    congr 1
    push_cast
    ring


end

open scoped ContDiff Topology NNReal
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [CompleteSpace E]

variable [FiniteDimensional ℝ E]

theorem exists_hamiltonian_endpoint {A : E →L[ℝ] E →L[ℝ] ℝ}
    (hA : A.IsInvertible) (hskew : ∀ v w, A v w = -A w v)
    {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H)
    (t T : ℝ) : ∃ Φ : E ≃ₜ E, ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
      (∀ x, x ∉ Prod.snd '' tsupport H → Φ x = x) ∧
      HasCompactSupport (fun x => Φ x-x) ∧
      (∀ x v w, A (fderiv ℝ Φ x v) (fderiv ℝ Φ x w) = A v w) ∧
      (∀ (u : ℝ → E), Continuous u →
        (∀ s, HasDerivAt u (hamiltonianField A H (s,u s)) s) → Φ (u t) = u (t+T)) := by
  have hXs := hamiltonianField_smooth hA hH
  let X : C(ℝ × E,E) := ⟨hamiltonianField A H,hXs.continuous⟩
  have hXc : HasCompactSupport X := hHc.of_isClosed_subset (isClosed_tsupport _)
    (hamiltonianField_support A H)
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨N,hN⟩ := exists_nat_gt (‖T‖ * L)
  have hN0 : (0:ℝ) < N := (mul_nonneg (norm_nonneg _) L.coe_nonneg).trans_lt hN
  let h := T / N
  have hh : ‖h‖ * L < 1 := by
    change ‖T / (N:ℝ)‖ * L < 1
    rw [norm_div,Real.norm_of_nonneg hN0.le, div_mul_eq_mul_div]
    exact (div_lt_one hN0).mpr hN
  have he : (N:ℝ) * h = T := by dsimp [h]; field_simp
  let Φ := timeSteps X hL hXs hh t N
  have hfix (x : E) (hx : x ∉ Prod.snd '' tsupport H) : Φ x = x := by
    apply timeSteps_of_stationary X hL hXs hh t N
    intro s
    apply image_eq_zero_of_notMem_tsupport
    intro hp
    exact hx ⟨(s,x),hamiltonianField_support A H hp,rfl⟩
  refine ⟨Φ,(timeSteps_smooth X hL hXs hh t N).1,
    (timeSteps_smooth X hL hXs hh t N).2,hfix,?_,?_,?_⟩
  · exact HasCompactSupport.intro (hHc.image continuous_snd)
      (fun x hx => sub_eq_zero.mpr (hfix x hx))
  · intro x v w
    apply timeSteps_preserves_form X hL hXs (fun _ => A) contDiff_const _ hh t N x v w
    intro p v w
    simpa only [X,ContinuousMap.coe_mk,fderiv_const_apply,zero_apply,zero_add] using
      hamiltonianField_transport_equation hA hskew hH p v w
  · intro u hu hud
    simpa only [he] using timeSteps_eq_solution X hL hXs hh u hu hud t N



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_SpatialOneForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def chartSupportedOneForm (c : M) (α : E → E →L[ℝ] ℝ) : ManifoldOneForm E M := by
  classical
  exact fun x => if x ∈ (extChartAt 𝓘(ℝ,E) c).source then
    (α (extChartAt 𝓘(ℝ,E) c x)).comp (chartDifferential c x) else 0



def chartSupportedTwoForm (c : M) (α : E → E →L[ℝ] E →L[ℝ] ℝ) : ManifoldTwoForm E M := by
  classical
  exact fun x => if x ∈ (extChartAt 𝓘(ℝ,E) c).source then
    (α (extChartAt 𝓘(ℝ,E) c x)).bilinearComp (chartDifferential c x) (chartDifferential c x) else 0


end

open scoped ContDiff Manifold Topology
open MeasureTheory Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_FixedSpatialIntegral
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

namespace SurfaceCoordinateBox

def compactCarrier (B : SurfaceCoordinateBox M) : Set M :=
  (extChartAt 𝓘(ℝ,Plane) B.center).symm '' Metric.closedBall B.point B.radius

theorem isOpen_carrier (B : SurfaceCoordinateBox M) : IsOpen B.carrier := by
  exact (continuousOn_extChartAt B.center).isOpen_inter_preimage
    (isOpen_extChartAt_source B.center) Metric.isOpen_ball

theorem exists_mem (x : M) : ∃ B : SurfaceCoordinateBox M, x ∈ B.carrier := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,Plane)) x
  have hy := (extChartAt 𝓘(ℝ,Plane) x).map_source hx
  obtain ⟨r,hr,hrsub⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := 𝓘(ℝ,Plane)) x)
    _ hy
  have hs : Metric.closedBall (extChartAt 𝓘(ℝ,Plane) x x) (r/2) ⊆
      (extChartAt 𝓘(ℝ,Plane) x).target := by
    apply Subset.trans (Metric.closedBall_subset_ball (by linarith)) hrsub
  refine ⟨⟨x,extChartAt 𝓘(ℝ,Plane) x x,r/2,by positivity,hs⟩,hx,?_⟩
  exact Metric.mem_ball_self (by positivity)

theorem finite_partition [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [SigmaCompactSpace M]
    {K : Set M} (hK : IsCompact K) :
    ∃ (s : Finset (SurfaceCoordinateBox M))
      (ρ : SmoothPartitionOfUnity s 𝓘(ℝ,Plane) M K),
        ρ.IsSubordinate (fun B => B.1.carrier) := by
  classical
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun B : SurfaceCoordinateBox M => B.carrier)
    isOpen_carrier (fun x _ => mem_iUnion.mpr (exists_mem x))
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,Plane) hK.isClosed
    (fun B : s => B.1.carrier) (fun B => B.1.isOpen_carrier) (by
      intro x hx
      obtain ⟨B,hBs,hxB⟩ := mem_iUnion₂.mp (hs hx)
      exact mem_iUnion.mpr ⟨⟨B,hBs⟩,hxB⟩)
  exact ⟨s,ρ,hρ⟩

end SurfaceCoordinateBox

end

section
open scoped ContDiff Topology
open Set
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem spatialZeroExtension_smooth {S K : Set E} (hS : IsOpen S) (hK : IsClosed K)
    (hKS : K ⊆ S) {f : P × E → F} (hf : ContDiffOn ℝ ∞ f (univ ×ˢ S))
    (hz : ∀ p x, x ∈ S → x ∉ K → f (p,x)=0) :
    ContDiff ℝ ∞ (spatialZeroExtension S f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.2 ∈ S
  · have hs := hf.contDiffAt ((isOpen_univ.prod hS).mem_nhds ⟨mem_univ _,hp⟩)
    apply hs.congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.preimage_mem_nhds (hS.mem_nhds hp)] with q hq
    exact ite_eq_left hq
  · have hpk : p.2 ∉ K := fun hk => hp (hKS hk)
    apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hpk)] with q hq
    unfold spatialZeroExtension
    split_ifs with hqS
    · exact hz q.1 q.2 hqS hq
    · rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem spatialZeroExtension_zero {S K : Set E} {f : P × E → F}
    (hz : ∀ p x, x ∈ S → x ∉ K → f (p,x)=0) (p : P) {x : E} (hx : x ∉ K) :
    spatialZeroExtension S f (p,x)=0 := by
  unfold spatialZeroExtension
  split_ifs with hxS
  · exact hz p x hxS hx
  · rfl


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem chartCoefficient_zero {c : M} {Ω : P → ManifoldTwoForm Plane M} {K : Set M}
    (hz : ∀ p x, x ∉ K → Ω p x=0) (p : P) {y : Plane}
    (hy : y ∈ (extChartAt 𝓘(ℝ,Plane) c).target)
    (hyk : y ∉ extChartAt 𝓘(ℝ,Plane) c '' K) :
    chartTwoForm (Ω p) c y (1,0) (0,1)=0 := by
  have hx : (extChartAt 𝓘(ℝ,Plane) c).symm y ∉ K := by
    intro hk
    exact hyk ⟨_,hk,(extChartAt 𝓘(ℝ,Plane) c).right_inv hy⟩
  simp only [chartTwoForm,hz p _ hx,ContinuousLinearMap.bilinearComp_apply,
    zero_apply]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem extendedChartCoefficient_zero {c : M} {Ω : P → ManifoldTwoForm Plane M} {K : Set M}
    (hz : ∀ p x, x ∉ K → Ω p x=0) (p : P) {y : Plane}
    (hy : y ∉ extChartAt 𝓘(ℝ,Plane) c '' K) : extendedChartCoefficient c Ω (p,y)=0 := by
  exact spatialZeroExtension_zero (fun p y hy hk => chartCoefficient_zero hz p hy hk) p hy

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in

theorem extendedChartCoefficient_smooth {c : M} {Ω : P → ManifoldTwoForm Plane M}
    (hΩ : ContDiffOn ℝ ∞ (fun q : P × Plane => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,Plane) c).target))
    {K : Set M} (hK : IsCompact K) (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ p x, x ∉ K → Ω p x=0) : ContDiff ℝ ∞ (extendedChartCoefficient c Ω) := by
  have hcK := hK.image_of_continuousOn
    ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) c).mono hKc)
  apply spatialZeroExtension_smooth (isOpen_extChartAt_target c) hcK.isClosed
  · rintro y ⟨x,hx,rfl⟩
    exact (extChartAt 𝓘(ℝ,Plane) c).map_source (hKc hx)
  · exact (hΩ.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  · intro p y hy hk
    exact chartCoefficient_zero hz p hy hk


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ChartSupportedDensity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem chartCoefficient_integrable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {c : M} {Ω : P → ManifoldTwoForm Plane M}
    (hΩ : ContDiffOn ℝ ∞ (fun q : P × Plane => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,Plane) c).target))
    {K : Set M} (hK : IsCompact K) (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ p x, x ∉ K → Ω p x=0) (p : P) :
    Integrable (fun y => extendedChartCoefficient c Ω (p,y)) := by
  have hf := extendedChartCoefficient_smooth hΩ hK hKc hz
  have hc : HasCompactSupport (fun y => extendedChartCoefficient c Ω (p,y)) := by
    apply HasCompactSupport.intro (hK.image_of_continuousOn
      ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) c).mono hKc))
    exact fun y hy => extendedChartCoefficient_zero hz p hy
  exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport hc

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem extendedChartCoefficient_add (c : M) (Ω Λ : ManifoldTwoForm Plane M) (y : Plane) :
    extendedChartCoefficient c (fun _ : ℝ => Ω+Λ) (0,y) =
      extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y)+extendedChartCoefficient c (fun _ : ℝ => Λ) (0,y) := by
  unfold extendedChartCoefficient spatialZeroExtension
  split_ifs <;> simp only [chartTwoForm_add,add_apply,zero_add]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem chartMass_add {c : M} {Ω Λ : ManifoldTwoForm Plane M}
    (hΩ : Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y)))
    (hΛ : Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => Λ) (0,y))) :
    chartMass c (Ω+Λ) = chartMass c Ω + chartMass c Λ := by
  unfold chartMass
  simp_rw [extendedChartCoefficient_add]
  exact integral_add hΩ hΛ

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem chartMass_smul (c : M) (a : ℝ) (Ω : ManifoldTwoForm Plane M) :
    chartMass c (a • Ω) = a*chartMass c Ω := by
  have he (y : Plane) : extendedChartCoefficient c (fun _ : ℝ => a • Ω) (0,y) =
      a*extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y) := by
    unfold extendedChartCoefficient spatialZeroExtension
    split_ifs <;> simp only [chartTwoForm_smul,smul_apply,smul_eq_mul,mul_zero]
  unfold chartMass
  simp_rw [he]
  exact integral_const_mul a _


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

def SmoothTwoFormFamily (Ω : P → ManifoldTwoForm E M) : Prop :=
  ∀ c, ContDiffOn ℝ ∞ (fun q : P × E => chartTwoForm (Ω q.1) c q.2)
    (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)

theorem SmoothTwoFormFamily.const {Ω : ManifoldTwoForm E M} (hΩ : SmoothTwoForm Ω) :
    SmoothTwoFormFamily (fun _ : P => Ω) := by
  intro c
  exact (hΩ c).comp contDiffOn_snd (fun _ hq => hq.2)

theorem SmoothTwoFormFamily.eval {Ω : P → ManifoldTwoForm E M}
    (hΩ : SmoothTwoFormFamily Ω) (p : P) : SmoothTwoForm (Ω p) := by
  intro c
  apply (hΩ c).comp (f := fun y : E => (p,y))
    (contDiffOn_const.prodMk contDiffOn_id)
  exact fun y hy => ⟨mem_univ p,hy⟩

theorem SmoothTwoFormFamily.add {Ω Λ : P → ManifoldTwoForm E M}
    (hΩ : SmoothTwoFormFamily Ω) (hΛ : SmoothTwoFormFamily Λ) : SmoothTwoFormFamily (Ω+Λ) := by
  intro c
  simpa only [Pi.add_apply,chartTwoForm_add] using (hΩ c).add (hΛ c)

theorem SmoothTwoFormFamily.smul {Ω : P → ManifoldTwoForm E M}
    (hΩ : SmoothTwoFormFamily Ω) {f : P → ℝ} (hf : ContDiff ℝ ∞ f) :
    SmoothTwoFormFamily (fun p => f p • Ω p) := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) := NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  intro c
  simpa only [chartTwoForm_smul,Function.comp_apply,Pi.smul_def'] using
    (hf.comp contDiff_fst).contDiffOn.smul (hΩ c)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem chartTwoForm_spatial_smul (ρ : M → ℝ) (Ω : ManifoldTwoForm E M) (c : M) (y : E) :
    chartTwoForm (fun x => ρ x • Ω x) c y =
      ρ ((extChartAt 𝓘(ℝ,E) c).symm y) • chartTwoForm Ω c y := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem SmoothTwoFormFamily.spatial_smul [IsManifold 𝓘(ℝ,E) ∞ M]
    {Ω : P → ManifoldTwoForm E M} (hΩ : SmoothTwoFormFamily Ω) {ρ : M → ℝ}
    (hρ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ ρ) :
    SmoothTwoFormFamily (fun p x => ρ x • Ω p x) := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) := NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  intro c q hq
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hq.2)
  have hrs := (hρ.contMDiffAt.comp q.2 hi).contDiffAt.comp q contDiffAt_snd
  have hfs := (hΩ c).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds hq)
  simpa only [chartTwoForm_spatial_smul,Pi.smul_def',Function.comp_apply] using (hrs.smul hfs).contDiffWithinAt


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

def PositivePlaneTransitions (M : Type*) [TopologicalSpace M] [ChartedSpace Plane M] : Prop :=
  ∀ (b c : M) (y : Plane), y ∈ (extChartAt 𝓘(ℝ,Plane) b).target →
    (extChartAt 𝓘(ℝ,Plane) b).symm y ∈ (extChartAt 𝓘(ℝ,Plane) c).source →
      0 < (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y).det



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_DiagonalQuadric
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function

variable {m : ℕ}

namespace Explicit
variable (m : ℕ)

theorem annulusPoint_mem {s : ℂ} (hs : s≠0) : annulusPoint m s∈locus (parameters m) := by
  rw [mem_locus]
  intro j
  change (annulusPoint m s).2 j^2=Complex.sqrt (baseSquare s)^2-parameters m j
  rw [sqrt_sq_complex]
  by_cases hj0 : j=0
  · subst j
    simp [baseSquare]
  by_cases hj1 : j=1
  · subst j
    have he := plus_sq_sub_minus_sq hs
    simp only [annulusPoint_one,parameters_one,baseSquare]
    linear_combination -he
  · simp only [annulusPoint,ite_eq_right hj0,ite_eq_right hj1,mul_pow,Complex.I_sq,sqrt_sq_complex]
    ring

end Explicit

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricOrientation
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
namespace PackingSufficiencySupport.Hamiltonian
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem SmoothTwoForm.coefficient_integrable {Ω : ManifoldTwoForm Plane M}
    (hΩ : SmoothTwoForm Ω) (c : M) {K : Set M} (hK : IsCompact K)
    (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ x, x ∉ K → Ω x=0) :
    Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y)) :=
  chartCoefficient_integrable (P := ℝ) (M := M) (c := c) (Ω := fun _ : ℝ => Ω)
    (SmoothTwoFormFamily.const (P := ℝ) (M := M) hΩ c) (K := K) hK hKc
    (fun _ x hx => hz x hx) 0

end PackingSufficiencySupport.Hamiltonian



namespace PackingSufficiencySupport.Hamiltonian
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {I : Type*} [Fintype I] {K : Set M}

def partitionTwoForm (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (Ω : P → ManifoldTwoForm Plane M) (i : I) (p : P) : ManifoldTwoForm Plane M :=
  fun x => ρ i x • Ω p x

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,Plane) ∞ M] [Fintype I] in
theorem partitionTwoForm_zero (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {Ω : P → ManifoldTwoForm Plane M} (hz : ∀ p x, x ∉ K → Ω p x=0)
    (i : I) (p : P) (x : M) (hx : x ∉ K ∩ tsupport (ρ i)) :
    partitionTwoForm ρ Ω i p x=0 := by
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  by_cases hk : x ∈ K
  · have hρ : ρ i x=0 := image_eq_zero_of_notMem_tsupport (fun ht => hx ⟨hk,ht⟩)
    change ρ i x • Ω p x=0
    rw [hρ,zero_smul]
  · change ρ i x • Ω p x=0
    rw [hz p x hk,MulActionWithZero.smul_zero]

end PackingSufficiencySupport.Hamiltonian



namespace PackingSufficiencySupport.Hamiltonian
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [PreconnectedSpace M]
  {I : Type*} [Fintype I] {K : Set M}

def partitionFormMass (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (Ω : ManifoldTwoForm Plane M) : ℝ :=
  ∑ i, chartMass (B i).center (fun x => ρ i x • Ω x)

end PackingSufficiencySupport.Hamiltonian



namespace PackingSufficiencySupport.Hamiltonian
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

def PositivePartialChart
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞) : Prop :=
  ∀ c y,y∈e.source→e y∈(extChartAt 𝓘(ℝ,Plane) c).source→
    0<(fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ e) y).det

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Residues_AreaPolarChart
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology ENNReal
open Set Function MeasureTheory
open Filter
open scoped Manifold

def areaPolarRadial (p : Plane) : Plane :=
  (Real.sqrt (p.1/Real.pi),2*Real.pi*(p.2-1/2))

def areaPolar (p : Plane) : Plane := polarCoord.symm (areaPolarRadial p)

def angularOneForm (z : Plane) : Plane →L[ℝ] ℝ := (radiusSq z)⁻¹ • planarArea z

def cutoffWedge (f : Plane → ℝ) (β : Plane → Plane →L[ℝ] ℝ) (z : Plane) : ℝ :=
  fderiv ℝ f z (1,0)*β z (0,1)-fderiv ℝ f z (0,1)*β z (1,0)

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_FlatIsotopy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory
open scoped ComplexConjugate
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SupportedSmoothIsotopy

 def trans {W : Set E} (Φ Ψ : SupportedSmoothIsotopy W) : SupportedSmoothIsotopy W where
  map := fun t => (Φ.map t).trans (Ψ.map t)
  smooth := Ψ.smooth.comp (contDiff_fst.prodMk Φ.smooth)
  inverse_smooth := Φ.inverse_smooth.comp (contDiff_fst.prodMk Ψ.inverse_smooth)
  zero := by rw [Φ.zero,Ψ.zero]; rfl
  support := Φ.support ∪ Ψ.support
  compact_support := Φ.compact_support.union Ψ.compact_support
  support_subset := union_subset Φ.support_subset Ψ.support_subset
  fixed := by
    intro t x hx
    have hx' : x ∉ Φ.support ∧ x ∉ Ψ.support := by simpa only [mem_union,not_or] using hx
    change Ψ.map t (Φ.map t x) = x
    rw [Φ.fixed t x hx'.1,Ψ.fixed t x hx'.2]

end SupportedSmoothIsotopy

def SmoothlyAmbientRelated (W K : Set E) (f g : E → E) : Prop :=
  ∃ Φ : SupportedSmoothIsotopy W, ∀ x ∈ K, Φ.map 1 (f x) = g x

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Kahler_PhaseArea
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Topology
section

variable {ι : Type*} [Fintype ι]

theorem fsAffineMap_smoothOn (a : ℝ) :
    ContDiffOn ℝ ∞ (fsAffineMap (ι := ι) a) (phaseOpenBall a) := by
  change ContDiffOn ℝ ∞ ((fun z : PlanePhase ι => (Real.sqrt (a-phaseSq z))⁻¹) • (id : PlanePhase ι → PlanePhase ι)) (phaseOpenBall a)
  apply ContDiffOn.smul
  · apply ContDiffOn.inv
    · exact (contDiffOn_const.sub phaseSq_smooth.contDiffOn).sqrt
        (fun z hz => (sub_pos.2 hz).ne')
    · intro z hz
      exact (Real.sqrt_pos.2 (sub_pos.2 hz)).ne'
  · exact contDiffOn_id

theorem fsBallMap_mem {a : ℝ} (ha : 0 < a) (z : PlanePhase ι) :
    fsBallMap a z ∈ phaseOpenBall a := by
  change phaseSq (fsBallMap a z) < a
  have h := div_pos ha (fs_den_pos z)
  rw [←fsBallMap_gap ha.le] at h
  exact sub_pos.1 h

def fsBallDifferential (a : ℝ) (z : PlanePhase ι) : PlanePhase ι →L[ℝ] PlanePhase ι :=
  (Real.sqrt a / Real.sqrt (1+phaseSq z)) •
    (ContinuousLinearMap.id ℝ _ - ((1+phaseSq z)⁻¹ • phaseDot z).smulRight z)

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldFormTransport
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold
open scoped ContDiff Manifold Topology

section

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def parameterEuclideanPullbackOneForm (α : P → ManifoldOneForm E M) (g : F → M)
    (p : P × F) : F →L[ℝ] ℝ :=
  (α p.1 (g p.2)).comp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)

end

section

variable {P E V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

instance (priority := 50) flatProduct_manifold [IsManifold 𝓘(ℝ,E) ∞ M] :
    IsManifold 𝓘(ℝ,E × V) ∞ (M × V) := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact IsManifold.prod M V

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_QuadricInfinityPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Manifold Topology
open Manifold
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def parameterPullbackOneForm (α : ℝ → ManifoldOneForm E M) (g : ℝ × N → M)
    (s t : ℝ) : ManifoldOneForm F N :=
  manifoldPullbackOneForm α (fun x => g (s,x)) t

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 def movingPrimitivePullback (α : F → F →L[ℝ] ℝ) (g : ℝ × M → F)
    (t : ℝ) : ManifoldOneForm E M :=
  manifoldPullbackOneForm (fun _ => α) (fun x => g (t,x)) 0

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_HorizontalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[fun_prop] theorem pathSpatialExterior_smooth {Γ : ℝ × E → E →L[ℝ] ℝ}
    (hΓ : ContDiff ℝ ∞ Γ) : ContDiff ℝ ∞ (pathSpatialExterior Γ) := by
  have hd : ContDiff ℝ ∞ (fun p => (fderiv ℝ Γ p).comp (ContinuousLinearMap.inr ℝ ℝ E)) :=
    (hΓ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp contDiff_const
  have hflip : ContDiff ℝ ∞ (fun L : E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ)
  exact hd.sub (hflip.comp hd)

@[fun_prop] theorem pathTimePrimitive_smooth {Γ : ℝ × E → E →L[ℝ] ℝ}
    (hΓ : ContDiff ℝ ∞ Γ) : ContDiff ℝ ∞ (pathTimePrimitive Γ) :=
  (hΓ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const



@[fun_prop] theorem pathSpatialExterior_smoothAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) : ContDiffAt ℝ ∞ (pathSpatialExterior Γ) p := by
  have hd : ContDiffAt ℝ ∞ (fun q => (fderiv ℝ Γ q).comp (ContinuousLinearMap.inr ℝ ℝ E)) p :=
    (hΓ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp contDiffAt_const
  have hflip : ContDiff ℝ ∞ (fun L : E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ)
  exact hd.sub (hflip.contDiffAt.comp p hd)

@[fun_prop] theorem pathTimePrimitive_smoothAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) : ContDiffAt ℝ ∞ (pathTimePrimitive Γ) p :=
  (hΓ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffAt_const


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_CubicEndCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators

variable {ι : Type*} [Fintype ι]

def veroneseDerivative (z : ι → ℂ) : (ι → ℂ) →L[ℂ] (VeroneseIndex ι → ℂ) :=
  ContinuousLinearMap.pi fun i => match i with
    | .inl i => ContinuousLinearMap.proj i.2
    | .inr i => z i.1 • ContinuousLinearMap.proj i.2+z i.2 • ContinuousLinearMap.proj i.1

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_SurfacePrimitiveOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold MeasureTheory
open scoped ContDiff Manifold Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

def smoothSupportedTwoForms (K : Set M) : Submodule ℝ (ManifoldTwoForm E M) where
  carrier := {Ω | SmoothTwoForm Ω ∧ (∀ x u v, Ω x u v = -Ω x v u) ∧ ∀ x, x ∉ K → Ω x=0}
  zero_mem' := by
    refine ⟨?_,?_,?_⟩
    · intro c
      rw [show chartTwoForm (0 : ManifoldTwoForm E M) c = fun _ => 0 from
        funext (fun y => chartTwoForm_zero c y)]
      exact contDiffOn_const
    · intro x u v
      simp only [Pi.zero_apply,zero_apply,neg_zero]
    · intro x _
      rfl
  add_mem' := by
    intro Ω Λ hΩ hΛ
    refine ⟨((SmoothTwoFormFamily.const (P := ℝ) hΩ.1).add
      (SmoothTwoFormFamily.const (P := ℝ) hΛ.1)).eval 0,?_,?_⟩
    · intro x u v
      change Ω x u v+Λ x u v = -(Ω x v u+Λ x v u)
      rw [hΩ.2.1 x u v,hΛ.2.1 x u v,neg_add]
    · intro x hx
      change Ω x+Λ x=0
      rw [hΩ.2.2 x hx,hΛ.2.2 x hx]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      exact zero_add (0 : ℝ)
  smul_mem' := by
    intro a Ω hΩ
    refine ⟨((SmoothTwoFormFamily.const (P := ℝ) hΩ.1).smul
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => a))).eval 0,?_,?_⟩
    · intro x u v
      change a*Ω x u v = -(a*Ω x v u)
      rw [hΩ.2.1 x u v,mul_neg]
    · intro x hx
      change a • Ω x=0
      rw [hΩ.2.2 x hx]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      exact mul_zero a

theorem smoothSupportedTwoForms.smooth {K : Set M} (Ω : smoothSupportedTwoForms (E := E) K) :
    SmoothTwoForm (Ω : ManifoldTwoForm E M) := Ω.property.1

theorem smoothSupportedTwoForms.zero_off {K : Set M} (Ω : smoothSupportedTwoForms (E := E) K)
    (x : M) (hx : x ∉ K) : (Ω : ManifoldTwoForm E M) x=0 := Ω.property.2.2 x hx

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricEndResidueMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped ContDiff Manifold Topology
open Set Function Manifold

def diskBoundaryMap (R : ℝ) (p q : DiskPlane) : DiskPlane :=
  (p.1*q.2-p.2*q.1,R^2-(q.1^2+q.2^2))

def diskBoundaryDerivative (p q : DiskPlane) : DiskPlane →L[ℝ] DiskPlane :=
  (p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ - p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((-2*q.1) • ContinuousLinearMap.fst ℝ ℝ ℝ+(-2*q.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)

end PackingSufficiencySupport

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CompactEmbeddingIsotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory
section

variable (P E : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {P E}
namespace SupportedSmoothIsotopyFamily

def eval {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W) (y : P) :
    SupportedSmoothIsotopy W where
  map := Φ.map y
  smooth := Φ.smooth.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
  inverse_smooth := Φ.inverse_smooth.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
  zero := Φ.zero y
  support := Φ.support
  compact_support := Φ.compact_support
  support_subset := Φ.support_subset
  fixed := Φ.fixed y

def constant {W : Set E} (Φ : SupportedSmoothIsotopy W) : SupportedSmoothIsotopyFamily P E W where
  map := fun _ => Φ.map
  smooth := Φ.smooth.comp (contDiff_fst.snd.prodMk contDiff_snd)
  inverse_smooth := Φ.inverse_smooth.comp (contDiff_fst.snd.prodMk contDiff_snd)
  zero := fun _ => Φ.zero
  support := Φ.support
  compact_support := Φ.compact_support
  support_subset := Φ.support_subset
  fixed := fun _ => Φ.fixed

def refl (W : Set E) : SupportedSmoothIsotopyFamily P E W := constant (SupportedSmoothIsotopy.refl W)

def trans {W : Set E} (Φ Ψ : SupportedSmoothIsotopyFamily P E W) :
    SupportedSmoothIsotopyFamily P E W where
  map := fun y t => (Φ.map y t).trans (Ψ.map y t)
  smooth := Ψ.smooth.comp (contDiff_fst.prodMk Φ.smooth)
  inverse_smooth := Φ.inverse_smooth.comp (contDiff_fst.prodMk Ψ.inverse_smooth)
  zero := fun y => by rw [Φ.zero y,Ψ.zero y]; rfl
  support := Φ.support ∪ Ψ.support
  compact_support := Φ.compact_support.union Ψ.compact_support
  support_subset := union_subset Φ.support_subset Ψ.support_subset
  fixed := by
    intro y t x hx
    have hx' : x ∉ Φ.support ∧ x ∉ Ψ.support := by simpa only [mem_union,not_or] using hx
    change Ψ.map y t (Φ.map y t x) = x
    rw [Φ.fixed y t x hx'.1,Ψ.fixed y t x hx'.2]

def mono {U W : Set E} (Φ : SupportedSmoothIsotopyFamily P E U) (hUW : U ⊆ W) :
    SupportedSmoothIsotopyFamily P E W where
  map := Φ.map
  smooth := Φ.smooth
  inverse_smooth := Φ.inverse_smooth
  zero := Φ.zero
  support := Φ.support
  compact_support := Φ.compact_support
  support_subset := Φ.support_subset.trans hUW
  fixed := Φ.fixed

end SupportedSmoothIsotopyFamily

end
section

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SupportedSmoothIsotopyFamily

def conjugate {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W)
    (e : E ≃L[ℝ] F) : SupportedSmoothIsotopyFamily P F (e '' W) where
  map := fun y t => e.toHomeomorph.symm.trans ((Φ.map y t).trans e.toHomeomorph)
  smooth := e.contDiff.comp (Φ.smooth.comp
    (contDiff_fst.prodMk (e.symm.contDiff.comp contDiff_snd)))
  inverse_smooth := e.contDiff.comp (Φ.inverse_smooth.comp
    (contDiff_fst.prodMk (e.symm.contDiff.comp contDiff_snd)))
  zero := by intro y; ext x; change e (Φ.map y 0 (e.symm x)) = x; rw [Φ.zero]; exact e.apply_symm_apply x
  support := e '' Φ.support
  compact_support := Φ.compact_support.image e.continuous
  support_subset := image_mono Φ.support_subset
  fixed := by
    intro y t x hx
    have hn : e.symm x ∉ Φ.support := fun h => hx ⟨e.symm x,h,e.apply_symm_apply x⟩
    change e (Φ.map y t (e.symm x)) = x
    rw [Φ.fixed y t _ hn,e.apply_symm_apply]

end SupportedSmoothIsotopyFamily

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_NormalizedRoundedBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]


namespace SupportedSmoothIsotopyFamily

def timeCutoff {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W)
    (ρ : P × ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) : SupportedSmoothIsotopyFamily P E W where
  map := fun y t => Φ.map y (ρ (y,t)*t)
  smooth := Φ.smooth.comp ((contDiff_fst.fst.prodMk
    ((hρ.comp contDiff_fst).mul contDiff_fst.snd)).prodMk contDiff_snd)
  inverse_smooth := Φ.inverse_smooth.comp ((contDiff_fst.fst.prodMk
    ((hρ.comp contDiff_fst).mul contDiff_fst.snd)).prodMk contDiff_snd)
  zero := fun y => by simp only [mul_zero,Φ.zero]
  support := Φ.support
  compact_support := Φ.compact_support
  support_subset := Φ.support_subset
  fixed := fun y t x hx => Φ.fixed y (ρ (y,t)*t) x hx

end SupportedSmoothIsotopyFamily

end

open scoped ContDiff Topology NNReal
open Set Function MeasureTheory



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_ParameterRelativeDiskMoser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

open scoped ContDiff Topology
open Set Function

namespace PlanarDiskEmbedding

def Nested (D E : PlanarDiskEmbedding) : Prop :=
  E.radius < D.radius ∧ E.carrier ⊆ interior D.carrier

end PlanarDiskEmbedding

namespace SupportedSmoothIsotopy

def mono {U W : Set ℂ} (Φ : SupportedSmoothIsotopy U) (hUW : U ⊆ W) :
    SupportedSmoothIsotopy W where
  map := Φ.map
  smooth := Φ.smooth
  inverse_smooth := Φ.inverse_smooth
  zero := Φ.zero
  support := Φ.support
  compact_support := Φ.compact_support
  support_subset := Φ.support_subset.trans hUW
  fixed := Φ.fixed

end SupportedSmoothIsotopy



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_ParametricNestedDisks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory
open Metric
section

variable (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]

variable {P}
namespace ParametricDiskEmbedding
variable {O : Set P}

def NestedOn (Y : Set P) (D E : ParametricDiskEmbedding P O) : Prop :=
  ∀ y ∈ Y, E.carrier y ⊆ interior (D.carrier y)

def pull {W : Set ℂ} (D : ParametricDiskEmbedding P O)
    (Φ : SupportedSmoothIsotopyFamily P ℂ W) : ParametricDiskEmbedding P O where
  radius := D.radius
  radius_pos := D.radius_pos
  map := fun p => (Φ.map p.1 1).symm (D.map p)
  smooth := Φ.endpoint_inverse_smooth.comp (contDiff_fst.prodMk D.smooth)
  domain := D.domain
  open_domain := D.open_domain
  convex_domain := D.convex_domain
  subset_domain := D.subset_domain
  injective := fun y hy => (Φ.map y 1).symm.injective.injOn.comp (D.injective y hy) (mapsTo_univ _ _)
  nonsingular := by
    intro y hy x hx
    have hd : ContDiff ℝ ∞ (fun x : ℂ => D.map (y,x)) :=
      D.smooth.comp (contDiff_const.prodMk contDiff_id)
    have hdi : ContDiff ℝ ∞ (Φ.map y 1).symm := (Φ.eval y).symm_smooth 1
    change (fderiv ℝ ((Φ.map y 1).symm ∘ (fun x => D.map (y,x))) x).IsInvertible
    rw [fderiv_comp x (hdi.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) (hd.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)]
    exact ((Φ.eval y).symm.fderiv_isInvertible 1 (D.map (y,x))).comp (D.nonsingular y hy x hx)
  orientation := by
    intro y hy
    have hd : ContDiff ℝ ∞ (fun x : ℂ => D.map (y,x)) :=
      D.smooth.comp (contDiff_const.prodMk contDiff_id)
    have hdi : ContDiff ℝ ∞ (Φ.map y 1).symm := (Φ.eval y).symm_smooth 1
    change 0 < (fderiv ℝ ((Φ.map y 1).symm ∘ (fun x => D.map (y,x))) 0).det
    rw [fderiv_comp 0 (hdi.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) (hd.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) 0),
      ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,LinearMap.det_comp]
    exact mul_pos ((Φ.eval y).symm.det_fderiv_pos 1 (D.map (y,0))) (D.orientation y hy)

@[simp] theorem pull_radius {W : Set ℂ} (D : ParametricDiskEmbedding P O)
    (Φ : SupportedSmoothIsotopyFamily P ℂ W) : (D.pull Φ).radius = D.radius := rfl

@[simp] theorem pull_carrier {W : Set ℂ} (D : ParametricDiskEmbedding P O)
    (Φ : SupportedSmoothIsotopyFamily P ℂ W) (y : P) :
    (D.pull Φ).carrier y = (Φ.map y 1).symm '' D.carrier y := by
  exact image_comp (Φ.map y 1).symm (fun x => D.map (y,x)) _

end ParametricDiskEmbedding

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

namespace ParametricDiskEmbedding

def restrictParam {O U : Set P} (D : ParametricDiskEmbedding P O) (hU : U ⊆ O) :
    ParametricDiskEmbedding P U where
  radius := D.radius
  radius_pos := D.radius_pos
  map := D.map
  smooth := D.smooth
  domain := D.domain
  open_domain := D.open_domain
  convex_domain := D.convex_domain
  subset_domain := D.subset_domain
  injective := fun y hy => D.injective y (hU hy)
  nonsingular := fun y hy => D.nonsingular y (hU hy)
  orientation := fun y hy => D.orientation y (hU hy)

end ParametricDiskEmbedding

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_BallVolume
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff ENNReal Pointwise Classical

namespace PackingSufficiencySupport

def closedBall (n : ℕ) (R : ℝ) : Set (Ambient n) :=
  {z | capacity z ≤ R}

def openBall (n : ℕ) (R : ℝ) : Set (Ambient n) :=
  {z | capacity z < R}

def standardForm {n : ℕ} (v w : Ambient n) : ℝ :=
  ∑ j, ((v j).re * (w j).im - (v j).im * (w j).re)

def IsBallEmbedding {n : ℕ} (r : ℝ) (f : Ambient n → Ambient n) : Prop :=
  ∃ U : Set (Ambient n), IsOpen U ∧ closedBall n r ⊆ U ∧
    ContDiffOn ℝ ∞ f U ∧
    Topology.IsEmbedding (fun x : U => f x) ∧
    ∀ x ∈ U, ∀ v w : Ambient n,
      standardForm (fderiv ℝ f x v) (fderiv ℝ f x w) = standardForm v w

def HasPacking (n k : ℕ) (R : ℝ) (r : Fin k → ℝ) : Prop :=
  ∃ f : Fin k → Ambient n → Ambient n,
    (∀ i, IsBallEmbedding (r i) (f i)) ∧
    (∀ i, f i '' closedBall n (r i) ⊆ openBall n R) ∧
    (∀ i j, i ≠ j → Disjoint (f i '' closedBall n (r i))
      (f j '' closedBall n (r j)))

open MeasureTheory

end PackingSufficiencySupport
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_ConvexRearrangement
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff ENNReal Pointwise Classical

namespace PackingSufficiencySupport.MomentPolytope
variable {m N : ℕ}

def region (b : Fin N → Moments m) (c : Fin N → ℝ) : Set (Moments m) :=
  {p | (∀ j, 0 ≤ p j) ∧ ∀ ν, ∑ j, b ν j * p j ≤ c ν}

def split (j : Fin m) : Moments m ≃ₜ Base j × ℝ where
  toFun p := (fun i => p i, p j)
  invFun x := assemble j x.1 x.2
  left_inv p := by
    funext i
    by_cases hi : i = j <;> simp [assemble, hi]
  right_inv x := by
    apply Prod.ext
    · funext i; simp
    · simp
  continuous_toFun := (continuous_pi fun i => continuous_apply i.val).prodMk (continuous_apply j)
  continuous_invFun := by
    apply continuous_pi
    intro i
    by_cases hi : i = j
    · simpa [assemble, hi] using (continuous_snd : Continuous (Prod.snd : Base j × ℝ → ℝ))
    · simp only [assemble, dite_eq_right hi]
      exact (continuous_apply (⟨i, hi⟩ : {i : Fin m // i ≠ j})).comp continuous_fst

end PackingSufficiencySupport.MomentPolytope
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_PolytopeSlices
attribute [-instance] _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff ENNReal Pointwise Classical
namespace PackingSufficiencySupport.MomentPolytope
variable {m N : ℕ}
theorem weighted_assemble (j : Fin m) (B : Moments m) (y : Base j) (h : ℝ) :
    ∑ i, B i * assemble j y h i = B j * h + ∑ i : {i : Fin m // i ≠ j}, B i.val * y i := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j]
  simp only [assemble_at, assemble_off]

theorem convex_region (b : Fin N → Moments m) (c : Fin N → ℝ) : Convex ℝ (region b c) := by
  intro y hy z hz a d ha hd had
  constructor
  · intro j; exact add_nonneg (mul_nonneg ha (hy.1 j)) (mul_nonneg hd (hz.1 j))
  · intro ν
    change ∑ i, b ν i * (a * y i + d * z i) ≤ c ν
    rw [weighted_affine]
    have h := add_le_add (mul_le_mul_of_nonneg_left (hy.2 ν) ha)
      (mul_le_mul_of_nonneg_left (hz.2 ν) hd)
    exact h.trans_eq (by rw [← add_mul, had, one_mul])

def baseRegion (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m) : Set (Base j) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∀ ν, ∑ i : {i : Fin m // i ≠ j}, b ν i.val * y i ≤ c ν}

theorem convex_baseRegion (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m) :
    Convex ℝ (baseRegion b c j) := by
  intro y hy z hz a d ha hd had
  constructor
  · intro i; exact add_nonneg (mul_nonneg ha (hy.1 i)) (mul_nonneg hd (hz.1 i))
  · intro ν
    change ∑ i : {i : Fin m // i ≠ j}, b ν i.val * (a * y i + d * z i) ≤ c ν
    rw [weighted_affine]
    have h := add_le_add (mul_le_mul_of_nonneg_left (hy.2 ν) ha)
      (mul_le_mul_of_nonneg_left (hz.2 ν) hd)
    exact h.trans_eq (by rw [← add_mul, had, one_mul])

theorem active_nonempty (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hb : ∀ ν j, 0 ≤ b ν j) (hc : ∀ ν, 0 < c ν) (hcomp : IsCompact (region b c))
    (j : Fin m) : Nonempty (Active b j) := by
  by_contra hn
  have hzero : ∀ ν, b ν j = 0 := by
    intro ν
    apply le_antisymm _ (hb ν j)
    by_contra h
    exact hn ⟨⟨ν, lt_of_not_ge h⟩⟩
  obtain ⟨M, hM⟩ := (hcomp.image (continuous_apply j)).bddAbove
  let t := max 0 M + 1
  have ht : 0 ≤ t := by dsimp [t] <;> positivity
  have hp : assemble j 0 t ∈ region b c := by
    constructor
    · intro i; by_cases hi : i = j <;> simp [assemble, hi, ht]
    · intro ν; simpa [weighted_assemble, hzero ν] using (hc ν).le
  have h := hM ⟨assemble j 0 t, hp, assemble_at j 0 t⟩
  dsimp [t] at h
  linarith [le_max_right (0 : ℝ) M]

variable (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)

theorem length_le [Nonempty (Active b j)] (ν : Active b j) (y : Base j) :
    length b c j y ≤ endpoint b c j ν y := Finset.inf'_le _ (Finset.mem_univ ν)

theorem le_length_iff [Nonempty (Active b j)] {y : Base j} {h : ℝ} :
    h ≤ length b c j y ↔ ∀ ν : Active b j, h ≤ endpoint b c j ν y := by
  simp [length, Finset.le_inf'_iff]

theorem endpoint_affine (ν : Active b j) (y z : Base j) (a d : ℝ) (had : a+d=1) :
    endpoint b c j ν (a • y + d • z) = a * endpoint b c j ν y + d * endpoint b c j ν z := by
  unfold endpoint
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [weighted_affine]
  calc
    _ = ((a+d) * c ν - (a * ∑ i : {i : Fin m // i ≠ j}, b ν i.val * y i +
        d * ∑ i : {i : Fin m // i ≠ j}, b ν i.val * z i)) / b ν j := by rw [had, one_mul]
    _ = _ := by ring

theorem concave_length [Nonempty (Active b j)] : ConcaveOn ℝ (baseRegion b c j) (length b c j) := by
  refine ⟨convex_baseRegion b c j, ?_⟩
  intro y _ z _ a d ha hd had
  apply (le_length_iff b c j).mpr
  intro ν
  rw [endpoint_affine b c j ν y z a d had]
  exact add_le_add (mul_le_mul_of_nonneg_left (length_le b c j ν y) ha)
    (mul_le_mul_of_nonneg_left (length_le b c j ν z) hd)

theorem assemble_mem_iff [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)
    (y : Base j) (h : ℝ) :
    assemble j y h ∈ region b c ↔ y ∈ baseRegion b c j ∧ 0 ≤ h ∧ h ≤ length b c j y := by
  constructor
  · intro hp
    have hh : 0 ≤ h := by simpa using hp.1 j
    refine ⟨⟨fun i => by simpa using hp.1 i, fun ν => ?_⟩, hh, ?_⟩
    · have h := hp.2 ν
      rw [weighted_assemble] at h
      linarith [mul_nonneg (hb ν j) hh]
    · apply (le_length_iff b c j).mpr
      intro ν
      apply (le_div_iff₀ ν.property).mpr
      have h := hp.2 ν
      rw [weighted_assemble] at h
      dsimp [endpoint]
      nlinarith
  · rintro ⟨hy, hh, hL⟩
    constructor
    · intro i
      by_cases hi : i = j
      · simpa [assemble, hi] using hh
      · simpa [assemble, hi] using hy.1 ⟨i, hi⟩
    · intro ν
      rw [weighted_assemble]
      by_cases hpos : 0 < b ν j
      · have h := (le_length_iff b c j).mp hL ⟨ν, hpos⟩
        have h := (le_div_iff₀ hpos).mp h
        dsimp [endpoint] at h
        nlinarith
      · have hz : b ν j = 0 := le_antisymm (not_lt.mp hpos) (hb ν j)
        simpa [hz] using hy.2 ν

theorem zero_mem (hc : ∀ ν, 0 ≤ c ν) : (0 : Moments m) ∈ region b c := by
  constructor
  · intro i; rfl
  · intro ν; simpa using hc ν

theorem assemble_affine (y z : Base j) (s t a d : ℝ) :
    assemble j (a • y + d • z) (a * s + d * t) =
      a • assemble j y s + d • assemble j z t := by
  funext i
  by_cases hi : i = j <;> simp [assemble, hi]

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.MomentPolytope
open Comparison
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
variable [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)

def sliceEquiv : (region b c) ≃ₜ Slice (baseRegion b c j) (length b c j) :=
  (split j).subtype fun p => by
    have h := assemble_mem_iff b c j hb (fun i => p i) (p j)
    have heq : assemble j (fun i => p i) (p j) = p := (split j).left_inv p
    change p ∈ region b c ↔ (fun i : {i : Fin m // i ≠ j} => p i) ∈ baseRegion b c j ∧
      0 ≤ p j ∧ p j ≤ length b c j (fun i => p i)
    simpa only [heq] using h

def onSlice (F : C(region b c, ℝ)) : C(Slice (baseRegion b c j) (length b c j), ℝ) :=
  F.comp ⟨(sliceEquiv b c j hb).symm, (sliceEquiv b c j hb).symm.continuous⟩

theorem onSlice_convex (F : ConvexMaps (region b c) (convex_region b c)) :
    onSlice b c j hb F.val ∈ convexFunctionSet _
      (convex_sliceDomain _ _ (concave_length b c j)) := by
  intro x y a d ha hd had
  have h := F.property ((sliceEquiv b c j hb).symm x) ((sliceEquiv b c j hb).symm y)
    a d ha hd had
  change F.val ((sliceEquiv b c j hb).symm _) ≤
    a * F.val ((sliceEquiv b c j hb).symm x) + d * F.val ((sliceEquiv b c j hb).symm y)
  have heq : (sliceEquiv b c j hb).symm
      ⟨a • x.val + d • y.val, (convex_sliceDomain _ _ (concave_length b c j))
        x.property y.property ha hd had⟩ =
      (⟨a • ((sliceEquiv b c j hb).symm x).val + d • ((sliceEquiv b c j hb).symm y).val,
        (convex_region b c) ((sliceEquiv b c j hb).symm x).property
          ((sliceEquiv b c j hb).symm y).property ha hd had⟩ : region b c) := by
    apply Subtype.ext
    exact assemble_affine j x.val.1 y.val.1 x.val.2 y.val.2 a d
  rw [heq]
  exact h

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.MomentPolytope
open Comparison
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)

def IncreasingIn (i : Fin m) (F : C(region b c, ℝ)) : Prop :=
  ∀ p q : region b c, p.val i ≤ q.val i → (∀ l, l ≠ i → p.val l = q.val l) → F p ≤ F q

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.MomentPolytope
open Comparison MeasureTheory
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
variable [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)

include hb in
theorem image_split : split j '' region b c = sliceDomain (baseRegion b c j) (length b c j) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (sliceEquiv b c j hb ⟨p,hp⟩).property
  · intro hx
    refine ⟨assemble j x.1 x.2, (assemble_mem_iff b c j hb x.1 x.2).mpr hx, ?_⟩
    exact (split j).apply_symm_apply x

include hb in
theorem isCompact_sliceDomain (hcomp : IsCompact (region b c)) :
    IsCompact (sliceDomain (baseRegion b c j) (length b c j)) := by
  rw [← image_split b c j hb]
  exact hcomp.image (split j).continuous

end PackingSufficiencySupport.MomentPolytope

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RearrangementBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators
open Set Function
open Hamiltonian

variable {m N : ℕ}

@[fun_prop] theorem assemble_zero_smooth (j : Fin m) :
    ContDiff ℝ ∞ (fun y : Base j => assemble j y 0) := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i=j
  · simp only [assemble,hi,dite_eq_left]; exact contDiff_const
  · simp only [assemble,dite_eq_right hi]
    exact contDiff_apply ℝ ℝ (⟨i,hi⟩ : {i : Fin m // i ≠ j})

@[simp] theorem baseProjection_assemble (j : Fin m) (y : Base j) (h : ℝ) :
    baseProjection j (assemble j y h) = y := by funext i; simp [baseProjection]

def fullBase (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m) : Set (Moments m) :=
  {y | y j=0 ∧ baseProjection j y ∈ baseRegion b c j}

variable (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m) [Nonempty (Active b j)]

def fullLength (y : Moments m) : ℝ := length b c j (baseProjection j y)

@[fun_prop] theorem continuous_fullLength : Continuous (fullLength b c j) :=
  (continuous_length b c j).comp (baseProjection_smooth j).continuous

end PackingSufficiencySupport.MomentPolytope

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_BaseHorizontalForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold MeasureTheory
open scoped ContDiff Manifold Topology

def circleClockDensity (b : ℝ) (z : Circle) : ℝ :=
  deriv (intervalClock (-b) b) (shortCircleArgument z)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_CircleHandleBump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Manifold Topology
open Set Function Manifold

instance torus_manifold : IsManifold 𝓘(ℝ,TorusModel) ∞ HandleTorus := by
  rw [show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact IsManifold.prod Circle Circle

instance cylinder_manifold : IsManifold 𝓘(ℝ,CylinderModel) ∞ HandleCylinder := by
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact IsManifold.prod ℝ Circle

def circlePeriodicDescent (F : ℝ → ℝ) (z : Circle) : ℝ :=
  F (shortCircleArgument z)

def localCircleLift (c z : Circle) : ℝ :=
  shortCircleArgument (z/c)+shortCircleArgument c

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def circleFamilyDescent (F : P × ℝ → ℝ) (q : P × Circle) : ℝ :=
  circlePeriodicDescent (fun t => F (q.1,t)) q.2


end

open scoped ContDiff Topology
open Set Function MeasureTheory



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_CylinderAnnularNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

def positiveCircleClock (b : ℝ) (z : Circle) : ℝ :=
  circleClockDensity b (z/circleTurn (1/2))


end


open scoped ContDiff Topology
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularHandleCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def parameterEuclideanPullbackTwoForm (α : P → ManifoldTwoForm E M) (g : F → M)
    (p : P × F) : F →L[ℝ] F →L[ℝ] ℝ :=
  (α p.1 (g p.2)).bilinearComp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)

variable {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def parameterManifoldPullbackTwoForm (α : P → ManifoldTwoForm E M) (g : N → M)
    (p : P) : ManifoldTwoForm F N :=
  manifoldPullbackTwoForm (fun _ => α p) g 0

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_ManifoldFormTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def manifoldPullback (Φ : ℝ × M → M) (Ω : ℝ → ManifoldTwoForm E M)
    (t : ℝ) (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  (Ω t (Φ (t,x))).bilinearComp
    (preferredDifferential (E := E) (fun y => Φ (t,y)) x)
    (preferredDifferential (E := E) (fun y => Φ (t,y)) x)


end

section
open scoped ContDiff Topology NNReal
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def shortFlow {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X) (p : ℝ × E) : E :=
  stepEndpoint X hX p.1 p.2


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_NonautonomousManifoldFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def PreservesTwoFormOn (e : M ≃ₘ⟮𝓘(ℝ,E),𝓘(ℝ,E)⟯ M)
    (Ω₀ Ω₁ : ManifoldTwoForm E M) (D : Set M) : Prop :=
  ∀ x ∈ D, ∀ v w, Ω₁ (e x)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e x v) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e x w) = Ω₀ x v w

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_AnnularFinalPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open scoped BigOperators
open scoped Manifold
open Manifold

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 def baseFiberField (Ω : V →L[ℝ] V →L[ℝ] ℝ) {ι : Type*} (μ : ι → V → ℝ) :
    Option ι → M × V → E × V := fun i => match i with
    | none => fun _ => 0
    | some i => fun z => (0,autonomousField Ω (μ i) z.2)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_SmoothManifoldIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable (E : Type) (M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

variable {E M}
namespace SmoothCircleAction
variable (A : SmoothCircleAction E M)

def differential (s : ℝ) (x : M) : E →L[ℝ] E :=
  manifoldMapDifferential (A.slice s) x

@[simp] theorem differential_zero (x : M) : A.differential 0 x = ContinuousLinearMap.id ℝ E := by
  have he : A.slice 0 = id := funext A.zero
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (A.slice 0) x = _
  rw [he]
  exact mfderiv_id

@[simp] theorem differential_period (s : ℝ) (x : M) :
    A.differential (s+1) x = A.differential s x := by
  have he : A.slice (s+1) = A.slice s := funext (A.period s)
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (A.slice (s+1)) x = _
  rw [he]
  rfl

def average (f : ℝ × M → ℝ) (p : ℝ × M) : ℝ :=
  ∫ s in (0:ℝ)..1, f (p.1,A.slice s p.2)

end SmoothCircleAction

end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_RelativeJets_SymplecticProjectionNaturality
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open Set Function
open scoped ContDiff Topology
open scoped Manifold
open Manifold IsManifold
section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def splitRetraction (L : (F × G) ≃L[ℝ] E) : E →L[ℝ] E :=
  (splitInclusion L).comp ((ContinuousLinearMap.fst ℝ F G).comp L.symm.toContinuousLinearMap)

def localSymplecticPotential (L : (F × G) ≃L[ℝ] E)
    (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (α : ℝ × E → E →L[ℝ] ℝ) (p : ℝ × E) : ℝ :=
  symplecticNormalJet (Ω p) (splitInclusion L) (α p) (p.2-splitRetraction L p.2)

end
section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def relativeLocalPotential (Ω : ℝ → ManifoldTwoForm E M) (α : ℝ → ManifoldOneForm E M)
    (d : OpenPartialHomeomorph M E) (L : (F × G) ≃L[ℝ] E) (p : ℝ × M) : ℝ :=
  localSymplecticPotential L (euclideanPullbackTwoForm Ω d.symm)
    (euclideanPullbackOneForm α d.symm) (p.1,d p.2)

def relativeLocalDomain (Ω : ℝ → ManifoldTwoForm E M)
    (d : OpenPartialHomeomorph M E) (L : (F × G) ≃L[ℝ] E) : Set (ℝ × M) :=
  {p | p.2 ∈ d.source ∧ ((euclideanPullbackTwoForm Ω d.symm (p.1,d p.2)).bilinearComp
      (splitInclusion L) (splitInclusion L)).IsInvertible}

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_CircleAction_CircleRelativeOneForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
section

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

namespace SmoothCircleAction

def generator (A : SmoothCircleAction E M) (x : M) : E :=
  manifoldMapDifferential (F := ℝ) (fun s : ℝ => A.slice s x) (0 : ℝ) (1 : ℝ)

end SmoothCircleAction

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_NonlinearReduction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {D : E →L[ℝ] F} (pkg : D.FredholmPackage)

omit [CompleteSpace E] in
lemma fredholm_original_coords [CompleteSpace E] (x : E) :
    (codCoords pkg) (D x) = (pkg.equiv ((domCoords pkg) x).1,0) := by
  have hz : finitePerturbation pkg (0 : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [_root_.OAI.ContinuousLinearMap.FredholmPackage.finitePerturbation,
      ContinuousLinearMap.comp_apply,zero_apply,map_zero]
  have hh := finitePerturbation_coords pkg (0 : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) x
  simpa only [hz,add_zero,zero_apply] using hh

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_SurjectiveParametricReduction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)

omit [CompleteSpace Y] in
lemma surjective_package_coker_subsingleton [CompleteSpace Y] (hD : Surjective D) : Subsingleton pkg.decCodom.X₀ := by
  have hc (c : pkg.decCodom.X₀) : c=0 := by
    obtain ⟨x,hx⟩ := hD ((codCoords pkg).symm (0,c))
    have hh := congrArg (fun y => ((codCoords pkg) y).2) hx
    rw [fredholm_original_coords,(codCoords pkg).apply_symm_apply] at hh
    exact hh.symm
  exact ⟨fun x y => (hc x).trans (hc y).symm⟩


end
open scoped Topology
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_LiftedCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [CompleteSpace E] [FiniteDimensional ℝ E]

theorem hamiltonian_trajectory_fixed {A : E →L[ℝ] E →L[ℝ] ℝ}
    (hA : A.IsInvertible) (hskew : ∀ v w, A v w = -A w v)
    {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H)
    {u : ℝ → E} (hu : Continuous u)
    (hud : ∀ s, HasDerivAt u (hamiltonianField A H (s,u s)) s)
    (hx : u 0 ∉ Prod.snd '' tsupport H) (t : ℝ) : u t = u 0 := by
  obtain ⟨Φ,_,_,hfix,_,_,hrec⟩ := exists_hamiltonian_endpoint hA hskew hH hHc 0 t
  have he := hrec u hu hud
  rw [zero_add,hfix _ hx] at he
  exact he.symm

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_TailLineCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

 def joinedVeronese (p : (ι → ℂ) × (κ → ℂ)) : VeroneseIndex ι ⊕ κ → ℂ :=
  Sum.elim (veronese p.1) p.2

 def joinedVeroneseDerivative (p : (ι → ℂ) × (κ → ℂ)) :
    ((ι → ℂ) × (κ → ℂ)) →L[ℂ] (VeroneseIndex ι ⊕ κ → ℂ) :=
  ContinuousLinearMap.pi fun i => match i with
  | .inl j => (ContinuousLinearMap.proj j).comp
      ((veroneseDerivative p.1).comp (ContinuousLinearMap.fst ℂ _ _))
  | .inr j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ _ _)

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_SixModelComparisonData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped BigOperators ContDiff ComplexConjugate
open DiagonalQuadrics FiniteMoment.Radial

def complexMonomialDerivative (k : ℕ × ℕ) (z : DiskPair) : DiskPair →L[ℝ] ℂ :=
  ((k.1:ℂ)*z.1^(k.1-1)*z.2^k.2) • (ContinuousLinearMap.fst ℝ ℂ ℂ)+
    (z.1^k.1*(k.2:ℂ)*z.2^(k.2-1)) • (ContinuousLinearMap.snd ℝ ℂ ℂ)

section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def toricLiftDifferential (k : ι → ℕ × ℕ) (G V : ι → κ → ℂ) (z v : DiskPair) : ι × κ → ℂ :=
  fun ij => complexMonomialDerivative (k ij.1) z v * G ij.1 ij.2 +
    complexMonomial (k ij.1) z * V ij.1 ij.2

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end


