-- Prove2me | Definitions.Def_OAIQ240Bp003
-- name    : OAIQ240Bp003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:42:26.755206+00:00
-- url     : https://prove2.me/theorems/b42ff354-b86a-4425-a8c7-c55d3daacecc
-- title:
--   Definitions bundle OAIQ240Bp003 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 536 declarations of OpenAI's Lean: 315 definitions, 8 inductive types or structures, 8 instances and 205 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.blowupCoefficient`, `OAI.HigherDimensionalBallPacking.Rigidity.blowupMoment`, `OAI.HigherDimensionalBallPacking.Rigidity.blowupSize`, `OAI.HigherDimensionalBallPacking.Rigidity.blowupSlope`, `OAI.HigherDimensionalBallPacking.Rigidity.campRadius`, `OAI.HigherDimensionalBallPacking.Rigidity.cappedTime`, `OAI.HigherDimensionalBallPacking.Rigidity.cappedTimeMap`, `OAI.HigherDimensionalBallPacking.Rigidity.extendedTimeTransport`, `OAI.HigherDimensionalBallPacking.Rigidity.freezeTime`, `OAI.HigherDimensionalBallPacking.Rigidity.frozenPath`, `OAI.HigherDimensionalBallPacking.Rigidity.gridDomain`, `OAI.HigherDimensionalBallPacking.Rigidity.initialKernelGraph`, `OAI.HigherDimensionalBallPacking.Rigidity.oneForm`, `OAI.HigherDimensionalBallPacking.Rigidity.outerProfile`, `OAI.HigherDimensionalBallPacking.Rigidity.projectionTimeChain`, `OAI.HigherDimensionalBallPacking.Rigidity.projectionTransport`, `OAI.HigherDimensionalBallPacking.Rigidity.radialCoefficient`, `OAI.HigherDimensionalBallPacking.Rigidity.radialMoment`, `OAI.HigherDimensionalBallPacking.Rigidity.radialOffset`, `OAI.HigherDimensionalBallPacking.Rigidity.radialShift`, `OAI.HigherDimensionalBallPacking.Rigidity.radialSlope`, `OAI.HigherDimensionalBallPacking.Rigidity.radialSwitch`, `OAI.HigherDimensionalBallPacking.Rigidity.splitKernelProjection`, `OAI.PackingSufficiencySupport.Ambient`, `OAI.PackingSufficiencySupport.Chart.conjugate`, `OAI.PackingSufficiencySupport.Chart.conjugateEquiv`, `OAI.PackingSufficiencySupport.Chart.conjugateHomeomorph`, `OAI.PackingSufficiencySupport.Comparison.ConvexMaps`, `OAI.PackingSufficiencySupport.Comparison.IntervalRoom`, `OAI.PackingSufficiencySupport.Comparison.Slice`, `OAI.PackingSufficiencySupport.Comparison.affineStep`, `OAI.PackingSufficiencySupport.Comparison.averageMap`, `OAI.PackingSufficiencySupport.Comparison.clampPoint`, `OAI.PackingSufficiencySupport.Comparison.clampUnit`, `OAI.PackingSufficiencySupport.Comparison.convexFunctionSet`, `OAI.PackingSufficiencySupport.Comparison.fiberFunction`, `OAI.PackingSufficiencySupport.Comparison.integralMap`, `OAI.PackingSufficiencySupport.Comparison.intervalCandidate`, `OAI.PackingSufficiencySupport.Comparison.pointAtHeight`, `OAI.PackingSufficiencySupport.Comparison.scaledUnitFamily` and 283 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `BallPacking_Annuli_BaseHorizontalForms`, `BallPacking_Annuli_CircleHandleBump`, `BallPacking_Annuli_CylinderAnnularNormalization`, `BallPacking_Annuli_QuadricCylinderChart`, `BallPacking_Annuli_SurfacePathPositivity`, `BallPacking_BallMaps_QuadricLargeAmbientPacking`, `BallPacking_BallMaps_SixCubicInnerNormalPacking`, `BallPacking_BallMaps_SphereCartesianDescent`, `BallPacking_Campanato_MeasureEnergy`, `BallPacking_Continuation_ProperPaths`, `BallPacking_DiskMaps_CompactEmbeddingIsotopy`, `BallPacking_DiskMaps_FlatIsotopy`, `BallPacking_DiskMaps_ParameterRelativeDiskMoser`, `BallPacking_Flows_NonautonomousManifoldFlow`, `BallPacking_Flows_TimeSteps`, `BallPacking_Forms_ChartSupportedDensity`, `BallPacking_Forms_CubicFubiniStudy`, `BallPacking_Forms_FixedSpatialIntegral`, `BallPacking_Forms_HorizontalCoupling`, `BallPacking_Forms_ManifoldExteriorAlgebra`, `BallPacking_Forms_ManifoldFormTransport`, `BallPacking_Forms_ManifoldMapDifferential`, `BallPacking_Forms_QuadricInfinityPrimitive`, `BallPacking_Forms_SpatialOneForm`, `BallPacking_Fredholm_NonlinearReduction`, `BallPacking_Fredholm_ProjectionTimeGrid`, `BallPacking_Fredholm_SurjectiveParametricReduction`, `BallPacking_Hamiltonian_LiftedCompact`, `BallPacking_Hamiltonian_ScaledPlanarMotion`, `BallPacking_Hopf_AffineHopfRestriction`, `BallPacking_Hopf_SixLargeQuadricPacking`, `BallPacking_Kahler_PhaseArea`, `BallPacking_Layers_ConstructedSurfaceLayers`, `BallPacking_Layers_LayerAreaForm`, `BallPacking_Layers_ParametricNestedDisks`, `BallPacking_Models_BallVolume`, `BallPacking_Models_DisjointClocks`, `BallPacking_Models_LiouvilleRadialCalculus`, `BallPacking_Moduli_SmoothZeroCharts`, `BallPacking_Moments_AnalyticBoundary`, `BallPacking_Moments_ConvexRearrangement`, `BallPacking_Moments_ConvexWeights`, `BallPacking_Moments_ExponentialMoment`, `BallPacking_Moments_PolytopeSlices`, `BallPacking_Moments_RadialSlopes`, `BallPacking_Moments_RadialSwap`, `BallPacking_Moments_RearrangementBounds`, `BallPacking_Moser_AnnularFinalPacking`, `BallPacking_Moser_BackgroundDensity`, `BallPacking_Moser_CircleCorrection`, `BallPacking_Moser_ManifoldMoserField`, `BallPacking_Moser_ParametricMoser`, `BallPacking_Moser_PlanarCorrection`, `BallPacking_Moser_PlanarCovectorPrimitive`, `BallPacking_Moser_RelativeForms`, `BallPacking_Moser_SymplecticFamily`, `BallPacking_Normal_CompactDegenerationTransfer`, `BallPacking_Normal_CubicToricAmbient`, `BallPacking_Normal_MovingPrimitiveNaturality`, `BallPacking_Projective_AnnularChartHelpers`, `BallPacking_Projective_CubicEndCoordinates`, `BallPacking_Projective_SixLargeCubicPacking`, `BallPacking_RelativeJets_SymplecticProjectionNaturality`, `BallPacking_Residues_AreaPolarChart`, `BallPacking_Rigidity_Adapted`, `BallPacking_Rigidity_Correction`, `BallPacking_Rigidity_CurveArea`, `BallPacking_Rigidity_RadialForm`, `BallPacking_SurfaceArea_CubicRadialEndSmooth`, `BallPacking_SurfaceArea_QuadricEndResidueMass`, `BallPacking_SurfaceArea_QuadricSmoothExhaustion`, `BallPacking_Surfaces_DiagonalQuadric`, `BallPacking_Surfaces_QuadricAnnulusDomain`, `BallPacking_Surfaces_QuadricCurveManifold`, `BallPacking_Surfaces_QuadricInfinityDiffeomorph`, `BallPacking_Surfaces_QuadricOrientation`, `BallPacking_Toric_CubicRadialFamilyExtension`, `BallPacking_Toric_CubicRadialProbability`, `BallPacking_Toric_RestrictedMassIndependence`, `BallPacking_Toric_SixModelComparisonData`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp005`, `OAIQ240Bp006` and `OAIQ240Bp007`; the statements `OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_exact_fibre_embedding`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_exact_fibre_embedding_bp240`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_exact_fibre_embedding_into`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_exact_fibre_embedding_into_bp240`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_uniform_compact_exact_fibre_embedding_central_into`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_uniform_compact_exact_fibre_embedding_central_into_bp240` and `OAI_PackingSufficiencySupport_Hamiltonian_manifold_exact_sublevel_moser`; the proof of `OAI_HigherDimensionalBallPacking_Rigidity_packing_two_line_reduction`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ240_BP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_RelativeForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology NNReal

namespace PackingSufficiencySupport.Hamiltonian

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem smoothOn_contraction_solution {φ : E → F → F} {z : E → F}
    {U : Set E} (hU : IsOpen U)
    (hφ : ContDiff ℝ ∞ (Function.uncurry φ))
    (hc : ∀ x ∈ U, ∃ K : ℝ≥0, ContractingWith K (φ x))
    (hz : ∀ x ∈ U, φ x (z x) = z x) : ContDiffOn ℝ ∞ z U := by
  let G : E × F → F := fun p => p.2 - φ p.1 p.2
  have hG : ContDiff ℝ ∞ G := contDiff_snd.sub hφ
  intro x hx
  obtain ⟨K,hK⟩ := hc x hx
  have hinr : fderiv ℝ G (x,z x) ∘L ContinuousLinearMap.inr ℝ E F =
      1 - fderiv ℝ (φ x) (z x) := by
    have hpx : HasFDerivAt (fun y : F => (x,y)) (ContinuousLinearMap.inr ℝ E F) (z x) :=
      (hasFDerivAt_const x (z x)).prodMk (hasFDerivAt_id (z x))
    have hcomp := (hG.differentiable (by simp) (x,z x)).hasFDerivAt.comp (z x) hpx
    have hφx : ContDiff ℝ ∞ (φ x) := hφ.comp (contDiff_const.prodMk contDiff_id)
    have hsub := (hasFDerivAt_id (z x)).sub ((hφx.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (z x)).hasFDerivAt)
    exact hcomp.unique hsub
  have hnorm : ‖fderiv ℝ (φ x) (z x)‖ < 1 :=
    (norm_fderiv_le_of_lipschitz ℝ hK.2).trans_lt (show (K : ℝ) < 1 from hK.1)
  obtain ⟨u,hu⟩ := isUnit_one_sub_of_norm_lt_one hnorm
  have hinv : (fderiv ℝ G (x,z x) ∘L ContinuousLinearMap.inr ℝ E F).IsInvertible := by
    rw [hinr]
    exact ⟨ContinuousLinearEquiv.ofUnit u,hu⟩
  have hloc := hG.contDiffAt.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv
  have hzero : G (x,z x) = 0 := sub_eq_zero.mpr (hz x hx).symm
  apply ContDiffAt.contDiffWithinAt
  apply hloc.congr_of_eventuallyEq
  filter_upwards [hG.contDiffAt.eventually_apply_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv,
    hU.mem_nhds hx] with y hy hyU
  obtain ⟨L,hL⟩ := hc y hyU
  apply hL.fixedPoint_unique' (hz y hyU)
  change φ y _ = _
  rw [hzero] at hy
  exact (sub_eq_zero.mp hy).symm

end PackingSufficiencySupport.Hamiltonian

open scoped ContDiff Topology
open Set Metric

namespace PackingSufficiencySupport.Hamiltonian

universe u v
variable {K : Type v} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pathLinear (A : C(K, E →L[ℝ] F)) : C(K,E) →L[ℝ] C(K,F) :=
  LinearMap.mkContinuous {
    toFun := fun u => ⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩
    map_add' := by intros; ext t; simp
    map_smul' := by intros; ext t; simp }
    ‖A‖ (by
      intro u
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro t
      exact ((A t).le_opNorm _).trans (mul_le_mul (A.norm_coe_le_norm t)
        (u.norm_coe_le_norm t) (by positivity) (by positivity)))

@[simp] theorem pathLinear_apply (A : C(K, E →L[ℝ] F)) (u : C(K,E)) (t : K) :
    pathLinear A u t = A t (u t) := rfl

def pathLinearOperator : C(K, E →L[ℝ] F) →L[ℝ] C(K,E) →L[ℝ] C(K,F) :=
  LinearMap.mkContinuous {
    toFun := fun A : C(K, E →L[ℝ] F) => pathLinear A
    map_add' := by intros; ext u t; simp
    map_smul' := by intros; ext u t; simp }
    1 (by
      intro A
      rw [one_mul]
      change ‖pathLinear A‖ ≤ ‖A‖
      refine (pathLinear A).opNorm_le_bound (norm_nonneg A) ?_
      intro u
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro t
      exact ((A t).le_opNorm _).trans (mul_le_mul (A.norm_coe_le_norm t)
        (u.norm_coe_le_norm t) (by positivity) (by positivity)))

@[simp] theorem pathLinearOperator_apply (A : C(K, E →L[ℝ] F)) :
    pathLinearOperator A = pathLinear A := rfl

theorem uniform_taylor [FiniteDimensional ℝ E] {f : E → F}
    (hf : ContDiff ℝ 1 f) (S : Set E) (hS : IsCompact S) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ S, ∀ v : E, ‖v‖ < δ →
      ‖f (x+v) - f x - fderiv ℝ f x v‖ ≤ ε * ‖v‖ := by
  have huc : UniformContinuousOn (fderiv ℝ f) (cthickening 1 S) :=
    hS.cthickening.uniformContinuousOn_of_continuous
      (hf.continuous_fderiv (by simp)).continuousOn
  obtain ⟨δ,hδ,hδf⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  let r := min 1 (δ/2)
  have hr : 0 < r := lt_min one_pos (half_pos hδ)
  refine ⟨r,hr,fun x hx v hv => ?_⟩
  have hbound : ∀ y ∈ Metric.closedBall x r,
      ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ ε := by
    intro y hy
    have hy' : dist y x ≤ r := hy
    have hyr : y ∈ cthickening 1 S :=
      mem_cthickening_of_dist_le _ x _ _ hx (hy'.trans (min_le_left _ _))
    have hxr : x ∈ cthickening 1 S := self_subset_cthickening _ hx
    have hyd : dist y x < δ := hy'.trans_lt
      ((min_le_right _ _).trans_lt (half_lt_self hδ))
    simpa only [dist_eq_norm] using (hδf y hyr x hxr hyd).le
  have he := (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => hf.differentiable_one y) hbound (mem_closedBall_self hr.le)
    (show x+v ∈ Metric.closedBall x r by simpa [mem_closedBall, dist_eq_norm] using hv.le)
  simpa only [add_sub_cancel_left] using he

theorem postcomp_hasFDerivAt [FiniteDimensional ℝ E] {f : E → F}
    (hf : ContDiff ℝ 1 f) (u : C(K,E)) :
    HasFDerivAt (ContinuousMap.comp (⟨f,hf.continuous⟩ : C(E,F)))
      (pathLinear ⟨fun t => fderiv ℝ f (u t),
        (hf.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp u.continuous⟩) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hrem⟩ := uniform_taylor hf (range u)
    (isCompact_range u.continuous) hε
  filter_upwards [Metric.ball_mem_nhds (0 : C(K,E)) hδ] with v hv
  have hv' : ‖v‖ < δ := by simpa only [mem_ball, dist_zero_right] using hv
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hvt : ‖v t‖ < δ := (v.norm_coe_le_norm t).trans_lt hv'
  exact (hrem (u t) ⟨t,rfl⟩ (v t) hvt).trans
    (mul_le_mul_of_nonneg_left (v.norm_coe_le_norm t) hε.le)

theorem postcomp_contDiff_nat [FiniteDimensional ℝ E] (q : ℕ) {f : E → F}
    (hf : ContDiff ℝ q f) :
    ContDiff ℝ q (ContinuousMap.comp (⟨f,hf.continuous⟩ : C(E,F)) : C(K,E) → C(K,F)) := by
  induction q generalizing F with
  | zero => exact contDiff_zero.mpr (ContinuousMap.continuous_postcomp _)
  | succ q ih =>
    have hdf : ContDiff ℝ q (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.succ_pos q)
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun u => pathLinear ((⟨fderiv ℝ f,hdf.continuous⟩ : C(E,E →L[ℝ] F)).comp u), ?_, ?_⟩
    · exact (pathLinearOperator (K := K) (E := E) (F := F)).contDiff.comp (ih hdf)
    · intro u
      exact postcomp_hasFDerivAt hf1 u

theorem postcomp_contDiff [FiniteDimensional ℝ E] {f : E → F}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (ContinuousMap.comp (⟨f,hf.continuous⟩ : C(E,F)) : C(K,E) → C(K,F)) := by
  apply contDiff_infty.mpr
  intro q
  exact postcomp_contDiff_nat q ((contDiff_infty.mp hf) q)

end PackingSufficiencySupport.Hamiltonian

open scoped ContDiff Topology
open Set Metric

namespace PackingSufficiencySupport.Hamiltonian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

abbrev Time := Set.Icc (0 : ℝ) 1

def extendPath (u : C(Time,E)) : C(ℝ,E) :=
  u.comp ⟨Set.projIcc 0 1 (by norm_num), continuous_projIcc⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem extendPath_coe (u : C(Time,E)) (t : Time) :
    extendPath u t = u t := by
  simp [extendPath]

def pathIntegral : C(Time,E) →L[ℝ] C(Time,E) :=
  LinearMap.mkContinuous {
    toFun := fun u => ⟨fun t => ∫ s in 0..(t : ℝ), extendPath u s,
      (intervalIntegral.differentiable_integral_of_continuous
        (extendPath u).continuous).continuous.comp continuous_subtype_val⟩
    map_add' := by
      intro u v
      ext t
      exact intervalIntegral.integral_add
        ((extendPath u).continuous.intervalIntegrable _ _)
        ((extendPath v).continuous.intervalIntegrable _ _)
    map_smul' := by
      intro c u
      ext t
      exact intervalIntegral.integral_smul c _ }
    1 (by
      intro u
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
      intro t
      exact (intervalIntegral.norm_integral_le_of_norm_le_const
        (fun s _ => u.norm_coe_le_norm _)).trans (by
          simp only [sub_zero, abs_of_nonneg t.property.1]
          exact mul_le_of_le_one_right (norm_nonneg u) t.property.2))

@[simp] theorem pathIntegral_apply (u : C(Time,E)) (t : Time) :
    pathIntegral u t = ∫ s in 0..(t : ℝ), extendPath u s := rfl

@[simp] theorem pathIntegral_zero (u : C(Time,E)) :
    pathIntegral u ⟨0,by simp⟩ = 0 := by simp

theorem norm_pathIntegral_le (u : C(Time,E)) : ‖pathIntegral u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro t
  exact (intervalIntegral.norm_integral_le_of_norm_le_const
    (fun s _ => u.norm_coe_le_norm _)).trans (by
      simp only [sub_zero, abs_of_nonneg t.property.1]
      exact mul_le_of_le_one_right (norm_nonneg u) t.property.2)


open scoped NNReal

def constantPath : E →L[ℝ] C(Time,E) :=
  LinearMap.mkContinuous {
    toFun := ContinuousMap.const Time
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
    1 (by
      intro x
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
      intro t
      exact le_rfl)

omit [CompleteSpace E] in
@[simp] theorem constantPath_apply (x : E) (t : Time) : constantPath x t = x := rfl

def picard (X : C(E,E)) (p : E × ℝ) (u : C(Time,E)) : C(Time,E) :=
  constantPath p.1 + p.2 • pathIntegral (X.comp u)

@[simp] theorem picard_apply (X : C(E,E)) (p : E × ℝ) (u : C(Time,E)) (s : Time) :
    picard X p u s = p.1 + p.2 • ∫ t in 0..(s : ℝ), extendPath (X.comp u) t := rfl

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem postcomp_lipschitz {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X) :
    LipschitzWith L (X.comp : C(Time,E) → C(Time,E)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  apply (ContinuousMap.dist_le (mul_nonneg L.coe_nonneg dist_nonneg)).mpr
  intro t
  exact (hX.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist t) L.coe_nonneg)

theorem picard_lipschitz {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X) (p : E × ℝ) :
    LipschitzWith (‖p.2‖₊ * L) (picard X p) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [picard, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
    norm_smul, ← map_sub, NNReal.coe_mul, coe_nnnorm]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    ((norm_pathIntegral_le (X.comp u - X.comp v)).trans
      ((postcomp_lipschitz X hX).norm_sub_le u v))
    (norm_nonneg p.2)

theorem picard_contDiff [FiniteDimensional ℝ E] (X : C(E,E)) (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (Function.uncurry (picard X)) := by
  exact ((constantPath (E := E)).contDiff.comp (contDiff_fst.comp contDiff_fst)).add
    ((contDiff_snd.comp contDiff_fst).smul
      ((pathIntegral (E := E)).contDiff.comp
        ((postcomp_contDiff hX).comp contDiff_snd)))

def picardDomain (L : ℝ≥0) : Set (E × ℝ) := {p | ‖p.2‖ * L < 1}

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem picardDomain_open (L : ℝ≥0) : IsOpen (picardDomain (E := E) L) :=
  isOpen_lt (continuous_snd.norm.mul continuous_const) continuous_const

theorem picard_contracts {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {p : E × ℝ} (hp : p ∈ picardDomain L) :
    ContractingWith (‖p.2‖₊ * L) (picard X p) :=
  ⟨by exact_mod_cast hp,picard_lipschitz X hX p⟩

def localPath {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X) (p : E × ℝ) : C(Time,E) := by
  classical
  exact if hp : p ∈ picardDomain L then (picard_contracts X hX hp).fixedPoint (picard X p)
  else constantPath p.1

def fixedStep {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X) (h : ℝ) : E → C(Time,E) :=
  fun x => localPath X hX (x,h)

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_TimeSteps
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


def clockField (X : C(ℝ × E,E)) : C(ℝ × E,ℝ × E) :=
  ⟨fun p => (1,X p), continuous_const.prodMk X.continuous⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem clockField_apply (X : C(ℝ × E,E)) (p : ℝ × E) :
    clockField X p = (1,X p) := rfl

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem clockField_lipschitz {L : ℝ≥0} (X : C(ℝ × E,E)) (hX : LipschitzWith L X) :
    LipschitzWith L (clockField X) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [clockField_apply, Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hX.dist_le_mul p q

omit [CompleteSpace E] in
theorem clockField_smooth (X : C(ℝ × E,E)) (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (clockField X) := contDiff_const.prodMk hX

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_PlanarCorrection
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

abbrev Plane := ℝ × ℝ

def planarArea : Plane →L[ℝ] Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.fst ℝ ℝ ℝ)
    (ContinuousLinearMap.snd ℝ ℝ ℝ) -
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (ContinuousLinearMap.fst ℝ ℝ ℝ)

@[simp] theorem planarArea_apply (v w : Plane) : planarArea v w = v.1*w.2-v.2*w.1 := rfl

@[fun_prop] theorem polar_smooth : ContDiff ℝ ∞ (polarCoord.symm : Plane → Plane) := by
  change ContDiff ℝ ∞ (fun p : Plane => (p.1*Real.cos p.2,p.1*Real.sin p.2))
  fun_prop

def roundDisk (R : ℝ) : Set Plane := {p | p.1^2+p.2^2 < R^2}

def radiusSq (p : Plane) : ℝ := p.1^2+p.2^2
@[fun_prop] theorem radiusSq_smooth : ContDiff ℝ ∞ radiusSq := by unfold radiusSq; fun_prop

@[simp] theorem radiusSq_polar (R t : ℝ) : radiusSq (polarCoord.symm (R,t)) = R^2 := by
  simp only [radiusSq,polarCoord_symm_apply]
  linear_combination R^2 * Real.cos_sq_add_sin_sq t

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_CircleCorrection
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

def coordinateForm (U V : Plane → ℝ) (p : Plane) : Plane →L[ℝ] ℝ :=
  U p • ContinuousLinearMap.fst ℝ ℝ ℝ + V p • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem coordinateForm_apply (U V : Plane → ℝ) (p v : Plane) :
    coordinateForm U V p v = U p*v.1+V p*v.2 := rfl

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_BackgroundDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def euclideanExteriorOneForm (α : E → E →L[ℝ] ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ α x - (fderiv ℝ α x).flip



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_PlanarCovectorPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
open MeasureTheory Set

def planarCovector (U V : ℝ) : Plane →L[ℝ] ℝ :=
  U • ContinuousLinearMap.fst ℝ ℝ ℝ + V • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem planarCovector_apply (U V : ℝ) (v : Plane) :
    planarCovector U V v = U*v.1+V*v.2 := rfl

@[simp] theorem planarCovector_zero : planarCovector 0 0=0 := by
  simp [planarCovector]


end

section
open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def staticPullbackOneForm (α : E → E →L[ℝ] ℝ) (g : F → E) (x : F) : F →L[ℝ] ℝ :=
  (α (g x)).comp (fderiv ℝ g x)


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

abbrev ManifoldTwoForm (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] :=
  M → E →L[ℝ] E →L[ℝ] ℝ

def chartDifferential (c z : M) : E →L[ℝ] E :=
  mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c) z

def chartTwoForm (Ω : ManifoldTwoForm E M) (c : M) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let z := (extChartAt 𝓘(ℝ,E) c).symm y
  let A := (chartDifferential c z).inverse
  (Ω z).bilinearComp A A



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ManifoldMoserField
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

abbrev ManifoldOneForm (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  M → E →L[ℝ] ℝ

def chartOneForm (α : ManifoldOneForm E M) (c : M) (y : E) : E →L[ℝ] ℝ :=
  let z := (extChartAt 𝓘(ℝ,E) c).symm y
  (α z).comp (chartDifferential c z).inverse

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ParametricMoser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Function MeasureTheory

def radialDiskChart (R : ℝ) : OpenPartialHomeomorph Plane Plane :=
  (Complex.equivRealProdCLM.symm.toHomeomorph.toOpenPartialHomeomorph.trans
    (OpenPartialHomeomorph.univBall (0:ℂ) R)).trans
    Complex.equivRealProdCLM.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem radialDiskChart_source (R : ℝ) : (radialDiskChart R).source = univ := by
  simp only [radialDiskChart,OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source,OpenPartialHomeomorph.univBall_source,
    preimage_univ,inter_self]

@[simp] theorem radiusSq_nonneg (p : Plane) : 0 ≤ radiusSq p :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Chart
open scoped ContDiff Topology
open Set Function

variable {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def conjugate (c : OpenPartialHomeomorph E F) (φ : E → E) (x : F) : F := by
  classical
  exact if x ∈ c.target then c (φ (c.symm x)) else x

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem conjugate_of_mem (c : OpenPartialHomeomorph E F) (φ : E → E)
    {x : F} (hx : x ∈ c.target) : conjugate c φ x = c (φ (c.symm x)) := by
  simp [conjugate,hx]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem conjugate_of_notMem (c : OpenPartialHomeomorph E F) (φ : E → E)
    {x : F} (hx : x ∉ c.target) : conjugate c φ x = x := by
  simp [conjugate,hx]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem conjugate_apply (c : OpenPartialHomeomorph E F) (hc : c.source = univ)
    (φ : E → E) (x : E) : conjugate c φ (c x) = c (φ x) := by
  have hx : x ∈ c.source := by rw [hc]; trivial
  rw [conjugate_of_mem c φ (c.map_source hx),c.left_inv hx]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem conjugate_comp (c : OpenPartialHomeomorph E F) (hc : c.source = univ)
    (φ ψ : E → E) (x : F) :
    conjugate c φ (conjugate c ψ x) = conjugate c (φ ∘ ψ) x := by
  by_cases hx : x ∈ c.target
  · rw [conjugate_of_mem c ψ hx,conjugate_apply c hc,
      conjugate_of_mem c (φ ∘ ψ) hx]
    rfl
  · simp only [conjugate_of_notMem c _ hx]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem conjugate_id (c : OpenPartialHomeomorph E F) (x : F) :
    conjugate c id x = x := by
  by_cases hx : x ∈ c.target
  · rw [conjugate_of_mem c id hx]
    exact c.right_inv hx
  · exact conjugate_of_notMem c id hx

def conjugateEquiv (c : OpenPartialHomeomorph E F) (hc : c.source = univ)
    (φ : E ≃ E) : F ≃ F where
  toFun := conjugate c φ
  invFun := conjugate c φ.symm
  left_inv x := by
    rw [conjugate_comp c hc]
    have he : ((φ.symm : E → E) ∘ (φ : E → E)) = id := funext φ.symm_apply_apply
    rw [he,conjugate_id]
  right_inv x := by
    rw [conjugate_comp c hc]
    have he : ((φ : E → E) ∘ (φ.symm : E → E)) = id := funext φ.apply_symm_apply
    rw [he,conjugate_id]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup P] [NormedSpace ℝ P] in

theorem conjugate_eq_of_notMem_image (c : OpenPartialHomeomorph E F)
    (φ : P → E → E) {K : Set (P × E)}
    (hK : ∀ p : P × E, p ∉ K → φ p.1 p.2 = p.2)
    {p : P × F} (hp : p ∉ (fun q : P × E => (q.1,c q.2)) '' K) :
    conjugate c (φ p.1) p.2 = p.2 := by
  by_cases hx : p.2 ∈ c.target
  · rw [conjugate_of_mem c _ hx]
    have hq : (p.1,c.symm p.2) ∉ K := by
      intro h
      apply hp
      exact ⟨(p.1,c.symm p.2),h,by simp only [c.right_inv hx]⟩
    rw [hK _ hq,c.right_inv hx]
  · exact conjugate_of_notMem c _ hx

theorem conjugate_smooth_compact (c : OpenPartialHomeomorph E F)
    (hcs : c.source = univ) (hc : ContDiff ℝ ∞ c)
    (hci : ContDiffOn ℝ ∞ c.symm c.target)
    (φ : P → E → E) (hφ : ContDiff ℝ ∞ (fun p : P × E => φ p.1 p.2))
    (hφc : HasCompactSupport (fun p : P × E => φ p.1 p.2-p.2)) :
    ContDiff ℝ ∞ (fun p : P × F => conjugate c (φ p.1) p.2) ∧
      HasCompactSupport (fun p : P × F => conjugate c (φ p.1) p.2-p.2) ∧
      tsupport (fun p : P × F => conjugate c (φ p.1) p.2-p.2) ⊆
        (fun q : P × E => (q.1,c q.2)) '' tsupport (fun p : P × E => φ p.1 p.2-p.2) := by
  let K : Set (P × F) := (fun q : P × E => (q.1,c q.2)) ''
    tsupport (fun p : P × E => φ p.1 p.2-p.2)
  have hK : IsCompact K := hφc.image (continuous_fst.prodMk (hc.continuous.comp continuous_snd))
  have he (p : P × F) (hp : p ∉ K) : conjugate c (φ p.1) p.2 = p.2 := by
    apply conjugate_eq_of_notMem_image c φ (K := tsupport (fun p : P × E => φ p.1 p.2-p.2)) _ hp
    intro q hq
    exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun p : P × E => φ p.1 p.2-p.2) hq)
  have hsupport : tsupport (fun p : P × F => conjugate c (φ p.1) p.2-p.2) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro p hp
    by_contra h
    exact hp (sub_eq_zero.mpr (he p h))
  refine ⟨?_,hK.of_isClosed_subset (isClosed_tsupport _) hsupport,hsupport⟩
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2 ∈ c.target
  · have hi := (hci p.2 hp).contDiffAt (c.open_target.mem_nhds hp)
    have hd := hc.contDiffAt.comp p (hφ.contDiffAt.comp p
      (contDiffAt_fst.prodMk (hi.comp p contDiffAt_snd)))
    apply hd.congr_of_eventuallyEq
    filter_upwards [(c.open_target.preimage continuous_snd).mem_nhds hp] with q hq
    exact conjugate_of_mem c _ hq
  · have hn : p ∉ K := by
      rintro ⟨q,hq,rfl⟩
      exact hp (c.map_source (by rw [hcs]; trivial))
    apply contDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hn] with q hq
    exact he q hq

omit [NormedSpace ℝ E] [NormedSpace ℝ P] in
theorem inverse_displacement_compact (φ : P → E ≃ₜ E)
    (hφ : HasCompactSupport (fun p : P × E => φ p.1 p.2-p.2)) :
    HasCompactSupport (fun p : P × E => (φ p.1).symm p.2-p.2) := by
  apply HasCompactSupport.intro hφ
  intro p hp
  have he : φ p.1 p.2 = p.2 := sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun p : P × E => φ p.1 p.2-p.2) hp)
  rw [sub_eq_zero]
  apply (φ p.1).injective
  rw [(φ p.1).apply_symm_apply,he]

def conjugateHomeomorph (c : OpenPartialHomeomorph E F)
    (hcs : c.source = univ) (hc : ContDiff ℝ ∞ c)
    (hci : ContDiffOn ℝ ∞ c.symm c.target)
    (φ : E ≃ₜ E) (hφ : ContDiff ℝ ∞ φ) (hφi : ContDiff ℝ ∞ φ.symm)
    (hφc : HasCompactSupport (fun p : E => φ p-p)) : F ≃ₜ F where
  toEquiv := conjugateEquiv c hcs φ.toEquiv
  continuous_toFun := by
    have hj : ContDiff ℝ ∞ (fun p : (Fin 0 → ℝ) × E => φ p.2) := hφ.comp contDiff_snd
    have hk : HasCompactSupport (fun p : (Fin 0 → ℝ) × E => φ p.2-p.2) := by
      apply HasCompactSupport.intro ((isCompact_univ : IsCompact (univ : Set (Fin 0 → ℝ))).prod hφc)
      intro p hp
      exact image_eq_zero_of_notMem_tsupport (f := fun q : E => φ q-q)
        (fun h => hp ⟨mem_univ _,h⟩)
    have hs := (conjugate_smooth_compact c hcs hc hci (fun _ : Fin 0 → ℝ => φ) hj hk).1
    exact (hs.comp ((contDiff_const (c := (0 : Fin 0 → ℝ))).prodMk contDiff_id)).continuous
  continuous_invFun := by
    have hj : ContDiff ℝ ∞ (fun p : (Fin 0 → ℝ) × E => φ.symm p.2) := hφi.comp contDiff_snd
    have hk : HasCompactSupport (fun p : (Fin 0 → ℝ) × E => φ p.2-p.2) := by
      apply HasCompactSupport.intro ((isCompact_univ : IsCompact (univ : Set (Fin 0 → ℝ))).prod hφc)
      intro p hp
      exact image_eq_zero_of_notMem_tsupport (f := fun q : E => φ q-q)
        (fun h => hp ⟨mem_univ _,h⟩)
    have hki := inverse_displacement_compact (fun _ : Fin 0 → ℝ => φ) hk
    have hs := (conjugate_smooth_compact c hcs hc hci (fun _ : Fin 0 → ℝ => φ.symm) hj hki).1
    exact (hs.comp ((contDiff_const (c := (0 : Fin 0 → ℝ))).prodMk contDiff_id)).continuous

end PackingSufficiencySupport.Chart
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_SymplecticFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology NNReal
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def formMoserField (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (α : ℝ × E → E →L[ℝ] ℝ) (p : ℝ × E) : E := -(Ω p).inverse (α p)

theorem formMoserField_smooth {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} (hΩ : ContDiff ℝ ∞ Ω) (hα : ContDiff ℝ ∞ α)
    (hΩinv : ∀ p, (Ω p).IsInvertible) : ContDiff ℝ ∞ (formMoserField Ω α) := by
  have hi : ContDiff ℝ ∞ (fun p => (Ω p).inverse) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact (hΩinv p).contDiffAt_map_inverse.comp p hΩ.contDiffAt
  exact (hi.clm_apply hα).neg

omit [CompleteSpace E] in
theorem formMoserField_solve {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} (hΩinv : ∀ p, (Ω p).IsInvertible) (p : ℝ × E) :
    Ω p (formMoserField Ω α p) = -α p := by
  simp only [formMoserField,map_neg,(hΩinv p).self_apply_inverse]

omit [CompleteSpace E] in
theorem formMoserField_support (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (α : ℝ × E → E →L[ℝ] ℝ) : tsupport (formMoserField Ω α) ⊆ tsupport α := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  apply hp
  simp [formMoserField,image_eq_zero_of_notMem_tsupport (f := α) hn]

theorem formMoserField_contraction_derivative {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} (hΩ : ContDiff ℝ ∞ Ω) (hα : ContDiff ℝ ∞ α)
    (hΩinv : ∀ p, (Ω p).IsInvertible) (p q : ℝ × E) (w : E) :
    fderiv ℝ Ω p q (formMoserField Ω α p) w +
      Ω p (fderiv ℝ (formMoserField Ω α) p q) w = -(fderiv ℝ α p q w) := by
  have hX := formMoserField_smooth hΩ hα hΩinv
  have hleft := ((hΩ.differentiable (by simp) p).hasFDerivAt).clm_apply
    ((hX.differentiable (by simp) p).hasFDerivAt)
  have hright := ((hα.differentiable (by simp) p).hasFDerivAt).neg
  have heq : (fun p => Ω p (formMoserField Ω α p)) = fun p => -α p :=
    funext (formMoserField_solve hΩinv)
  change HasFDerivAt (fun p => -α p) (-fderiv ℝ α p) p at hright
  rw [← heq] at hright
  have hh := congrArg (fun A : (ℝ × E) →L[ℝ] E →L[ℝ] ℝ => A q w) (hleft.unique hright)
  simpa only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    neg_apply,add_comm] using hh

theorem formMoserField_transport_equation {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} (hΩ : ContDiff ℝ ∞ Ω) (hα : ContDiff ℝ ∞ α)
    (hΩinv : ∀ p, (Ω p).IsInvertible)
    (hskew : ∀ p u v, Ω p u v = -Ω p v u)
    (hclosed : ∀ p u v w, fderiv ℝ Ω p (0,u) v w - fderiv ℝ Ω p (0,v) u w +
      fderiv ℝ Ω p (0,w) u v = 0)
    (htime : ∀ p v w, fderiv ℝ Ω p (1,0) v w =
      fderiv ℝ α p (0,v) w - fderiv ℝ α p (0,w) v) (p : ℝ × E) (v w : E) :
    fderiv ℝ Ω p (1,formMoserField Ω α p) v w +
      Ω p (fderiv ℝ (formMoserField Ω α) p (0,v)) w +
      Ω p v (fderiv ℝ (formMoserField Ω α) p (0,w)) = 0 := by
  have h1 := formMoserField_contraction_derivative hΩ hα hΩinv p (0,v) w
  have h2 := formMoserField_contraction_derivative hΩ hα hΩinv p (0,w) v
  have hc := hclosed p (formMoserField Ω α p) v w
  have ht := htime p v w
  rw [show (1,formMoserField Ω α p) = ((1,0) : ℝ × E)+(0,formMoserField Ω α p) by ext <;> simp,
    map_add,add_apply,add_apply,hskew p v]
  linarith


end

open scoped ContDiff Topology NNReal
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def spatialDifferential (H : ℝ × E → ℝ) (p : ℝ × E) : E →L[ℝ] ℝ :=
  (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ E)

@[simp] theorem spatialDifferential_apply (H : ℝ × E → ℝ) (p : ℝ × E) (v : E) :
    spatialDifferential H p v = fderiv ℝ H p (0,v) := rfl

theorem spatialDifferential_smooth {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (spatialDifferential H) :=
  (hH.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp contDiff_const

theorem spatialDifferential_support (H : ℝ × E → ℝ) :
    tsupport (spatialDifferential H) ⊆ tsupport H := by
  apply (tsupport_comp_subset (f := fderiv ℝ H)
    (g := fun A : (ℝ × E) →L[ℝ] ℝ => A.comp (ContinuousLinearMap.inr ℝ ℝ E))
    (by ext; rfl)).trans (tsupport_fderiv_subset ℝ)

theorem spatialDifferential_fderiv {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H)
    (p q : ℝ × E) (w : E) :
    fderiv ℝ (spatialDifferential H) p q w = fderiv ℝ (fderiv ℝ H) p q (0,w) := by
  have hHd : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd := ((hHd.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt).clm_comp
    (hasFDerivAt_const (c := ContinuousLinearMap.inr ℝ ℝ E) p)
  have he := congrArg (fun A : (ℝ × E) →L[ℝ] E →L[ℝ] ℝ => A q w) hd.fderiv
  change fderiv ℝ (fun p => (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ E)) p q w = _
  simpa only [add_apply,ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,
    map_zero,zero_apply,zero_add] using he

theorem spatialDifferential_closed {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H)
    (p : ℝ × E) (v w : E) :
    fderiv ℝ (spatialDifferential H) p (0,v) w =
      fderiv ℝ (spatialDifferential H) p (0,w) v := by
  rw [spatialDifferential_fderiv hH,spatialDifferential_fderiv hH]
  have hs := (hH.contDiffAt (x := p)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  exact hs.eq (0,v) (0,w)

def hamiltonianField (A : E →L[ℝ] E →L[ℝ] ℝ) (H : ℝ × E → ℝ) : ℝ × E → E :=
  formMoserField (fun _ => A) (spatialDifferential H)

variable [CompleteSpace E]

theorem hamiltonianField_smooth {A : E →L[ℝ] E →L[ℝ] ℝ} (hA : A.IsInvertible)
    {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (hamiltonianField A H) :=
  formMoserField_smooth contDiff_const (spatialDifferential_smooth hH) (fun _ => hA)

omit [CompleteSpace E] in
theorem hamiltonianField_support (A : E →L[ℝ] E →L[ℝ] ℝ) (H : ℝ × E → ℝ) :
    tsupport (hamiltonianField A H) ⊆ tsupport H :=
  (formMoserField_support _ _).trans (spatialDifferential_support H)

theorem hamiltonianField_transport_equation {A : E →L[ℝ] E →L[ℝ] ℝ}
    (hA : A.IsInvertible) (hskew : ∀ v w, A v w = -A w v)
    {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) (p : ℝ × E) (v w : E) :
    A (fderiv ℝ (hamiltonianField A H) p (0,v)) w +
      A v (fderiv ℝ (hamiltonianField A H) p (0,w)) = 0 := by
  have he := formMoserField_transport_equation (Ω := fun _ => A)
    contDiff_const (spatialDifferential_smooth hH) (fun _ => hA) (fun _ => hskew)
    (by intro p u v w; simp) (by
      intro p v w
      simp only [fderiv_const_apply,zero_apply]
      exact (sub_eq_zero.mpr (spatialDifferential_closed hH p v w)).symm) p v w
  simpa only [hamiltonianField,fderiv_const_apply,zero_apply,zero_add] using he



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_SpatialOneForm
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def euclideanPullbackTwoForm (Ω : ℝ → ManifoldTwoForm E M) (g : F → M)
    (p : ℝ × F) : F →L[ℝ] F →L[ℝ] ℝ :=
  (Ω p.1 (g p.2)).bilinearComp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)

def euclideanPullbackOneForm (α : ℝ → ManifoldOneForm E M) (g : F → M)
    (p : ℝ × F) : F →L[ℝ] ℝ :=
  (α p.1 (g p.2)).comp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)


end

open scoped ContDiff Manifold Topology
open MeasureTheory Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_FixedSpatialIntegral
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

structure SurfaceCoordinateBox (M : Type*) [TopologicalSpace M] [ChartedSpace Plane M] where
  center : M
  point : Plane
  radius : ℝ
  radius_pos : 0 < radius
  closed_subset : Metric.closedBall point radius ⊆ (extChartAt 𝓘(ℝ,Plane) center).target

namespace SurfaceCoordinateBox

def carrier (B : SurfaceCoordinateBox M) : Set M :=
  (extChartAt 𝓘(ℝ,Plane) B.center).source ∩
    extChartAt 𝓘(ℝ,Plane) B.center ⁻¹' Metric.ball B.point B.radius

end SurfaceCoordinateBox

end

section
open scoped ContDiff Topology
open Set
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def spatialZeroExtension (S : Set E) (f : P × E → F) (q : P × E) : F := by
  classical
  exact if q.2 ∈ S then f q else 0


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

def extendedChartCoefficient (c : M) (Ω : P → ManifoldTwoForm Plane M) : P × Plane → ℝ :=
  spatialZeroExtension (extChartAt 𝓘(ℝ,Plane) c).target
    (fun q => chartTwoForm (Ω q.1) c q.2 (1,0) (0,1))


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def chartMass (c : M) (Ω : ManifoldTwoForm Plane M) : ℝ :=
  ∫ y, extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y)


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

@[simp] theorem chartOneForm_add (α β : ManifoldOneForm E M) (c : M) (y : E) :
    chartOneForm (α+β) c y = chartOneForm α c y + chartOneForm β c y := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

@[simp] theorem chartOneForm_smul (a : ℝ) (α : ManifoldOneForm E M) (c : M) (y : E) :
    chartOneForm (a • α) c y = a • chartOneForm α c y := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

@[simp] theorem chartOneForm_zero (c : M) (y : E) : chartOneForm (0 : ManifoldOneForm E M) c y=0 := rfl

@[simp] theorem chartTwoForm_add (Ω Λ : ManifoldTwoForm E M) (c : M) (y : E) :
    chartTwoForm (Ω+Λ) c y = chartTwoForm Ω c y + chartTwoForm Λ c y := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rfl

@[simp] theorem chartTwoForm_smul (a : ℝ) (Ω : ManifoldTwoForm E M) (c : M) (y : E) :
    chartTwoForm (a • Ω) c y = a • chartTwoForm Ω c y := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rfl

@[simp] theorem chartTwoForm_zero (c : M) (y : E) : chartTwoForm (0 : ManifoldTwoForm E M) c y=0 := rfl



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ChartSupportedDensity
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
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

def SmoothOneFormFamily (α : P → ManifoldOneForm E M) : Prop :=
  ∀ c, ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (α q.1) c q.2)
    (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)




def SmoothTwoForm (Ω : ManifoldTwoForm E M) : Prop :=
  ∀ c, ContDiffOn ℝ ∞ (chartTwoForm Ω c) (extChartAt 𝓘(ℝ,E) c).target


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

structure BoxUnitBump (B : SurfaceCoordinateBox M) where
  form : ManifoldTwoForm Plane M
  smooth : SmoothTwoForm form
  skew : ∀ x u v, form x u v = -form x v u
  supportSet : Set M
  compact_supportSet : IsCompact supportSet
  support_subset : supportSet ⊆ B.carrier
  zero_off : ∀ x, x ∉ supportSet → form x=0
  unit_mass : chartMass B.center form=1



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_DiagonalQuadric
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
abbrev Affine (m : ℕ) := ℂ × (Fin m → ℂ)

def equations (a : Fin m → ℂ) (z : Affine m) : Fin m → ℂ :=
  fun j => z.2 j ^ 2 - z.1 ^ 2 + a j

def locus (a : Fin m → ℂ) : Set (Affine m) := equations a ⁻¹' {0}

def jacobian (z : Affine m) : Affine m →L[ℂ] (Fin m → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    (2*z.2 j) • ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin m → ℂ))) -
    (2*z.1) • ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)

@[simp] theorem jacobian_apply (z v : Affine m) (j : Fin m) :
    jacobian z v j = 2*z.2 j*v.2 j-2*z.1*v.1 := rfl

theorem equations_contDiff (a : Fin m → ℂ) : ContDiff ℂ ∞ (equations a) := by
  apply contDiff_pi.mpr
  intro j
  exact (((contDiff_apply ℂ ℂ j).comp contDiff_snd).pow 2).sub
    (contDiff_fst.pow 2) |>.add contDiff_const

theorem equations_hasFDerivAt (a : Fin m → ℂ) (z : Affine m) :
    HasFDerivAt (equations a) (jacobian z) z := by
  apply hasFDerivAt_pi.mpr
  intro j
  convert! ((((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin m → ℂ))).hasFDerivAt.pow 2).sub
    ((ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)).hasFDerivAt.pow 2)).add_const (a j) using 1
  all_goals try with_reducible_and_instances rfl
  simp

@[simp] theorem mem_locus {a : Fin m → ℂ} {z : Affine m} :
    z∈locus a ↔ ∀ j,z.2 j^2=z.1^2-a j := by
  simp only [locus,mem_preimage,mem_singleton_iff,funext_iff,equations,Pi.zero_apply]
  constructor <;> intro h j <;> have := h j <;> linear_combination this

theorem locus_isClosed (a : Fin m → ℂ) : IsClosed (locus a) :=
  isClosed_singleton.preimage (equations_contDiff a).continuous

theorem at_most_one_zero {a : Fin m → ℂ} (ha : Injective a) {z : Affine m}
    (hz : z∈locus a) {i j : Fin m} (hi : z.2 i=0) (hj : z.2 j=0) : i=j := by
  apply ha
  have hzi := (mem_locus.mp hz) i
  have hzj := (mem_locus.mp hz) j
  rw [hi,zero_pow (by decide)] at hzi
  rw [hj,zero_pow (by decide)] at hzj
  linear_combination hzi-hzj

theorem base_ne_zero_at_branch {a : Fin m → ℂ} (ha : ∀ j,a j≠0) {z : Affine m}
    (hz : z∈locus a) {i : Fin m} (hi : z.2 i=0) : z.1≠0 := by
  intro ht
  have hzi := (mem_locus.mp hz) i
  apply ha i
  simpa only [hi,ht,zero_pow (by decide : (2:ℕ)≠0),zero_sub,eq_neg_iff_add_eq_zero,zero_add] using hzi

theorem ordinary_augmented_bijective {z : Affine m} (hw : ∀ j,z.2 j≠0) :
    Bijective ((ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)).prod (jacobian z)) := by
  constructor
  · intro v w h
    have ht : v.1=w.1 := by
      have ht := congrArg (fun x : Affine m => x.1) h
      exact ht
    apply Prod.ext ht
    funext j
    have he := congrArg (fun x : Affine m => x.2 j) h
    change 2*z.2 j*v.2 j-2*z.1*v.1=2*z.2 j*w.2 j-2*z.1*w.1 at he
    rw [ht] at he
    have hm : (2*z.2 j)*v.2 j=(2*z.2 j)*w.2 j := by linear_combination he
    exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ)≠0) (hw j)) hm
  · rintro ⟨t,y⟩
    refine ⟨(t,fun j => (y j+2*z.1*t)/(2*z.2 j)),?_⟩
    apply Prod.ext
    · rfl
    · funext j
      change 2*z.2 j*((y j+2*z.1*t)/(2*z.2 j))-2*z.1*t=y j
      rw [mul_div_cancel₀ _ (mul_ne_zero (by norm_num) (hw j)),add_sub_cancel_right]

@[simp] theorem sqrt_sq_complex (z : ℂ) : Complex.sqrt z ^ 2=z := by
  exact Complex.cpow_nat_inv_pow z (by decide : (2:ℕ)≠0)

theorem sqrt_of_sq_pos {z : ℂ} (hz : 0<z.re) : Complex.sqrt (z^2)=z :=
  Complex.sq_cpow_two_inv hz

theorem sqrt_re_pos {z : ℂ} (hz : 0<z.re) : 0<(Complex.sqrt z).re := by
  rw [Complex.sqrt,Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  positivity

theorem sqrt_contDiffAt {z : ℂ} (hz : 0<z.re) : ContDiffAt ℂ ∞ Complex.sqrt z :=
  ((Complex.differentiableOn_sqrt.contDiffOn Complex.isOpen_slitPlane) z (Or.inl hz)).contDiffAt
    (Complex.isOpen_slitPlane.mem_nhds (Or.inl hz))

namespace Explicit
variable (m : ℕ)

def parameters (j : Fin (m+2)) : ℂ := (j.val : ℂ)+1

instance parameters_injective : Fact (Injective (parameters m)) := ⟨by
  intro i j h
  apply Fin.ext
  have he : (i.val : ℂ)=(j.val : ℂ) := add_right_cancel h
  exact_mod_cast he⟩

instance parameters_nonzero : Fact (∀ j,parameters m j≠0) := ⟨by
  intro j
  have hp : 0<(j.val : ℝ)+1 := by positivity
  intro h
  have he := congrArg Complex.re h
  simp only [parameters,Complex.add_re,Complex.natCast_re,Complex.one_re,Complex.zero_re] at he
  linarith⟩

@[simp] theorem parameters_zero : parameters m 0=1 := by simp [parameters]
@[simp] theorem parameters_one : parameters m 1=2 := by norm_num [parameters]

def plus (s : ℂ) : ℂ := (s+s⁻¹)/2
def minus (s : ℂ) : ℂ := (s-s⁻¹)/2
def baseSquare (s : ℂ) : ℂ := 1+plus s^2

@[simp] theorem plus_add_minus (s : ℂ) : plus s+minus s=s := by unfold plus minus; ring

theorem plus_sq_sub_minus_sq {s : ℂ} (hs : s≠0) : plus s^2-minus s^2=1 := by
  unfold plus minus
  field_simp
  ring

def annulusPoint (s : ℂ) : Affine (m+2) :=
  (Complex.sqrt (baseSquare s),fun j =>
    if j=0 then plus s else if j=1 then minus s
    else Complex.I*Complex.sqrt (parameters m j-baseSquare s))

@[simp] theorem annulusPoint_zero (s : ℂ) : (annulusPoint m s).2 0=plus s := by simp [annulusPoint]
@[simp] theorem annulusPoint_one (s : ℂ) : (annulusPoint m s).2 1=minus s := by
  have hn : (1 : Fin (m+2))≠0 := by simp
  simp [annulusPoint,hn]

def annulusDomain : Set ℂ := {s | s≠0 ∧ 0<(baseSquare s).re ∧
  ∀ j : Fin (m+2),1<j.val → 0<(parameters m j-baseSquare s).re}

end Explicit

def endSign (b : Bool) : ℂ := if b then -1 else 1
@[simp] theorem endSign_sq (b : Bool) : endSign b^2=1 := by cases b <;> norm_num [endSign]
@[simp] theorem endSign_mul_self (b : Bool) : endSign b*endSign b=1 := by
  simpa only [pow_two] using endSign_sq b
@[simp] theorem endSign_re (b : Bool) : (endSign b).re=if b then -1 else 1 := by
  cases b <;> rfl
@[simp] theorem endSign_im (b : Bool) : (endSign b).im=0 := by cases b <;> simp [endSign]

 def infinityRoot (a : Fin m → ℂ) (ε : Fin m → Bool) (s : ℂ) (j : Fin m) : ℂ :=
  endSign (ε j)*Complex.sqrt (1-a j*s^2)
 def infinityPoint (a : Fin m → ℂ) (ε : Fin m → Bool) (s : ℂ) : Affine m :=
  (s⁻¹,fun j => s⁻¹*infinityRoot a ε s j)
 def infinityRegion (a : Fin m → ℂ) : Set ℂ := {s | ∀ j,0<(1-a j*s^2).re}
 def infinityDomain (a : Fin m → ℂ) : Set ℂ := {s | s≠0 ∧ s∈infinityRegion a}

@[simp] theorem infinityRoot_sq (a : Fin m → ℂ) (ε : Fin m → Bool) (s : ℂ) (j : Fin m) :
    infinityRoot a ε s j^2=1-a j*s^2 := by
  simp only [infinityRoot,mul_pow,endSign_sq,sqrt_sq_complex,one_mul]

 theorem infinityPoint_mem (a : Fin m → ℂ) (ε : Fin m → Bool) {s : ℂ} (hs : s≠0) :
    infinityPoint a ε s∈locus a := by
  apply mem_locus.mpr
  intro j
  change (s⁻¹*infinityRoot a ε s j)^2=(s⁻¹)^2-a j
  rw [mul_pow,infinityRoot_sq]
  field_simp

@[simp] theorem infinityPoint_coordinate (a : Fin m → ℂ) (ε : Fin m → Bool) (s : ℂ) :
    (infinityPoint a ε s).1⁻¹=s := inv_inv s

 theorem infinityRoot_positive (a : Fin m → ℂ) (ε : Fin m → Bool) {s : ℂ}
    (hs : s∈infinityRegion a) (j : Fin m) : 0<(endSign (ε j)*infinityRoot a ε s j).re := by
  rw [infinityRoot,← mul_assoc,endSign_mul_self,one_mul]
  exact sqrt_re_pos (hs j)

 theorem infinityRegion_open (a : Fin m → ℂ) : IsOpen (infinityRegion a) := by
  change IsOpen {s : ℂ | ∀ j,0<(1-a j*s^2).re}
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_lt continuous_const
  fun_prop

 theorem infinityDomain_open (a : Fin m → ℂ) : IsOpen (infinityDomain a) :=
  isOpen_ne_fun continuous_id continuous_const |>.inter (infinityRegion_open a)

@[simp] theorem zero_mem_infinityRegion (a : Fin m → ℂ) : (0 : ℂ)∈infinityRegion a := by
  intro j
  norm_num

 theorem infinityRoot_contDiffAt (a : Fin m → ℂ) (ε : Fin m → Bool) {s : ℂ}
    (hs : s∈infinityRegion a) : ContDiffAt ℂ ∞ (infinityRoot a ε) s := by
  apply contDiffAt_pi.mpr
  intro j
  exact contDiffAt_const.mul ((sqrt_contDiffAt (hs j)).comp s
    (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_id.pow 2))))

 theorem infinityPoint_contDiffAt (a : Fin m → ℂ) (ε : Fin m → Bool) {s : ℂ}
    (hs : s∈infinityDomain a) : ContDiffAt ℂ ∞ (infinityPoint a ε) s := by
  apply (contDiffAt_id.inv hs.1).prodMk
  apply contDiffAt_pi.mpr
  intro j
  exact (contDiffAt_id.inv hs.1).mul (contDiffAt_pi.mp (infinityRoot_contDiffAt a ε hs.2) j)

def curveCoordinate : Option (Fin m) → Affine m →L[ℂ] ℂ
  | none => ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)
  | some i => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ ℂ (Fin m → ℂ))

def regularCoordinate : Option (Fin m) → Set (Affine m)
  | none => {z | ∀ j,z.2 j≠0}
  | some i => {z | z.1≠0 ∧ ∀ j,j≠i → z.2 j≠0}

theorem regularCoordinate_isOpen (c : Option (Fin m)) : IsOpen (regularCoordinate c) := by
  cases c with
  | none =>
    simp only [regularCoordinate,ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_ne_fun (by fun_prop) continuous_const
  | some i =>
    change IsOpen ({z : Affine m | z.1≠0} ∩ {z | ∀ j,j≠i → z.2 j≠0})
    apply IsOpen.inter (isOpen_ne_fun continuous_fst continuous_const)
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
      isOpen_ne_fun (by fun_prop) continuous_const

theorem exists_regularCoordinate {a : Fin m → ℂ} (ha : Injective a) (ha0 : ∀ j,a j≠0)
    {z : Affine m} (hz : z∈locus a) : ∃ c,z∈regularCoordinate c := by
  by_cases hw : ∀ j,z.2 j≠0
  · exact ⟨none,hw⟩
  · push Not at hw
    obtain ⟨i,hi⟩ := hw
    exact ⟨some i,base_ne_zero_at_branch ha0 hz hi,
      fun j hji hj => hji (at_most_one_zero ha hz hj hi)⟩

def normalCoordinates (a : Fin m → ℂ) (c : Option (Fin m)) (z : Affine m) : Affine m :=
  (curveCoordinate c z,equations a z)

theorem normalCoordinates_contDiff (a : Fin m → ℂ) (c : Option (Fin m)) :
    ContDiff ℂ ∞ (normalCoordinates a c) :=
  (curveCoordinate c).contDiff.prodMk (equations_contDiff a)

theorem normalCoordinates_hasFDerivAt (a : Fin m → ℂ) (c : Option (Fin m)) (z : Affine m) :
    HasFDerivAt (normalCoordinates a c) ((curveCoordinate c).prod (jacobian z)) z :=
  (curveCoordinate c).hasFDerivAt.prodMk (equations_hasFDerivAt a z)

structure NormalChart (a : Fin m → ℂ) where
  coordinate : Option (Fin m)
  ambient : OpenPartialHomeomorph (Affine m) (Affine m)
  coe_eq : (ambient : Affine m → Affine m)=normalCoordinates a coordinate
  smooth_inverse : ContDiffOn ℂ ∞ (ambient.symm : Affine m → Affine m) ambient.target

namespace NormalChart
variable {a : Fin m → ℂ} (e : NormalChart a)

@[simp] theorem ambient_apply (x : Affine m) :
    e.ambient x=(curveCoordinate e.coordinate x,equations a x) := by
  rw [e.coe_eq]
  rfl

theorem inverse_on_slice {t : ℂ} (ht : (t,0)∈e.ambient.target) :
    e.ambient.symm (t,0)∈locus a := by
  have h := congrArg Prod.snd (e.ambient.right_inv ht)
  rw [e.ambient_apply] at h
  exact h

def sliceInverse (x : locus a) (t : ℂ) : locus a := by
  classical
  exact if h : (t,0)∈e.ambient.target then ⟨e.ambient.symm (t,0),e.inverse_on_slice h⟩ else x

end NormalChart

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricCurveManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Filter
section
variable {m : ℕ} (a : Fin m → ℂ) [ha : Fact (Injective a)] [ha0 : Fact (∀ j,a j≠0)]

abbrev RealModel := ℝ × ℝ

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
namespace PackingSufficiencySupport.Hamiltonian
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

def partialChartCoefficient
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    (Ω : ManifoldTwoForm Plane M) (y : Plane) : ℝ :=
  euclideanPullbackTwoForm (fun _ => Ω) e (0,y) (1,0) (0,1)

end PackingSufficiencySupport.Hamiltonian


end

noncomputable section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory



namespace PackingSufficiencySupport.Hamiltonian
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
@[simp] theorem partialChartCoefficient_smul
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    (f : M → ℝ) (Ω : ManifoldTwoForm Plane M) (y : Plane) :
    partialChartCoefficient e (fun x => f x • Ω x) y=f (e y)*partialChartCoefficient e Ω y := rfl

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricInfinityDiffeomorph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter Bornology

def inverseComplementCutoff (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  if z=0 then 1 else 1-f z⁻¹

theorem inverseComplementCutoff_compact {f : ℂ → ℝ} (h1 : f=ᶠ[𝓝 0] fun _ => 1) :
    HasCompactSupport (inverseComplementCutoff f) := by
  apply hasCompactSupport_iff_eventuallyEq.mpr
  rw [coclosedCompact_eq_cocompact]
  have hi : Tendsto (Inv.inv : ℂ → ℂ) (cocompact ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hn : ∀ᶠ z : ℂ in cocompact ℂ,z≠0 :=
    isCompact_singleton.compl_mem_cocompact
  filter_upwards [h1.comp_tendsto hi,hn] with z hz hnz
  have hval : f z⁻¹=1 := hz
  simp only [inverseComplementCutoff,hnz,↓reduceIte,hval,sub_self,Pi.zero_apply]

theorem complex_normSq_smooth : ContDiff ℝ ∞ (Complex.normSq : ℂ → ℝ) := by
  change ContDiff ℝ ∞ (fun z : ℂ => z.re*z.re+z.im*z.im)
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Residues_AreaPolarChart
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

def areaPolarDomain : Set Plane := Ioi 0 ×ˢ Ioo 0 1

def planarDot : Plane →L[ℝ] Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.fst ℝ ℝ ℝ)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) +
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem planarDot_apply (z v : Plane) : planarDot z v=z.1*v.1+z.2*v.2 := rfl

def shrinkingCutoff (g : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ := g (((n:ℝ)+1)*t)

theorem shrinkingCutoff_one {g : ℝ → ℝ} {r : ℝ}
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (n : ℕ) :
    ∀ t∈Ioo (-(r/((n:ℝ)+1))) (r/((n:ℝ)+1)),shrinkingCutoff g n t=1 := by
  intro t ht
  apply h1
  have hn : 0<(n:ℝ)+1 := by positivity
  constructor
  · have hh : (-r)/((n:ℝ)+1)<t := by simpa only [neg_div] using ht.1
    have h := (div_lt_iff₀ hn).mp hh
    linarith
  · have h := (lt_div_iff₀ hn).mp ht.2
    nlinarith

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_FlatIsotopy
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

structure SupportedSmoothIsotopy (W : Set E) where
  map : ℝ → E ≃ₜ E
  smooth : ContDiff ℝ ∞ (fun p : ℝ × E => map p.1 p.2)
  inverse_smooth : ContDiff ℝ ∞ (fun p : ℝ × E => (map p.1).symm p.2)
  zero : map 0 = Homeomorph.refl E
  support : Set E
  compact_support : IsCompact support
  support_subset : support ⊆ W
  fixed : ∀ t x, x ∉ support → map t x = x

namespace SupportedSmoothIsotopy

 def refl (W : Set E) : SupportedSmoothIsotopy W where
  map := fun _ => Homeomorph.refl E
  smooth := contDiff_snd
  inverse_smooth := contDiff_snd
  zero := rfl
  support := ∅
  compact_support := isCompact_empty
  support_subset := empty_subset _
  fixed := fun _ _ _ => rfl

 def symm {W : Set E} (Φ : SupportedSmoothIsotopy W) : SupportedSmoothIsotopy W where
  map := fun t => (Φ.map t).symm
  smooth := Φ.inverse_smooth
  inverse_smooth := Φ.smooth
  zero := by rw [Φ.zero]; rfl
  support := Φ.support
  compact_support := Φ.compact_support
  support_subset := Φ.support_subset
  fixed := by
    intro t x hx
    apply (Φ.map t).injective
    rw [(Φ.map t).apply_symm_apply,Φ.fixed t x hx]

end SupportedSmoothIsotopy

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Kahler_PhaseArea
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg
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
abbrev PlanePhase (ι : Type*) := ι → Plane

def phaseArea : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ :=
  ∑ i, planarArea.bilinearComp (ContinuousLinearMap.proj i) (ContinuousLinearMap.proj i)

end
section

variable {ι : Type*} [Fintype ι]

def phaseDot : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ :=
  ∑ i, ((ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.proj i))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.proj i)) +
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.proj i))
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.proj i)))

@[simp] theorem phaseDot_apply (z v : PlanePhase ι) :
    phaseDot z v = ∑ i, ((z i).1*(v i).1+(z i).2*(v i).2) := by
  simp [phaseDot]

def phaseSq (z : PlanePhase ι) : ℝ := phaseDot z z

theorem phaseSq_nonneg (z : PlanePhase ι) : 0 ≤ phaseSq z := by
  rw [phaseSq,phaseDot_apply]
  apply Finset.sum_nonneg
  intro i _
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

@[simp] theorem phaseSq_smul (a : ℝ) (z : PlanePhase ι) :
    phaseSq (a • z) = a^2 * phaseSq z := by
  simp only [phaseSq,map_smul,smul_apply,smul_eq_mul]
  ring

@[fun_prop] theorem phaseSq_smooth : ContDiff ℝ ∞ (phaseSq (ι := ι)) :=
  (phaseDot (ι := ι)).contDiff.clm_apply contDiff_id

end
section

variable {ι : Type*} [Fintype ι]

def fsBallMap (a : ℝ) (z : PlanePhase ι) : PlanePhase ι :=
  (Real.sqrt a / Real.sqrt (1+phaseSq z)) • z

def fsAffineMap (a : ℝ) (z : PlanePhase ι) : PlanePhase ι :=
  (Real.sqrt (a-phaseSq z))⁻¹ • z

def phaseOpenBall (a : ℝ) : Set (PlanePhase ι) := {z | phaseSq z < a}

theorem fs_den_pos (z : PlanePhase ι) : 0 < 1+phaseSq z := by
  linarith [phaseSq_nonneg z]

@[fun_prop] theorem fsBallMap_smooth (a : ℝ) : ContDiff ℝ ∞ (fsBallMap (ι := ι) a) := by
  change ContDiff ℝ ∞ ((fun z : PlanePhase ι => Real.sqrt a / Real.sqrt (1+phaseSq z)) • (id : PlanePhase ι → PlanePhase ι))
  apply ContDiff.smul
  · exact contDiff_const.div ((contDiff_const.add phaseSq_smooth).sqrt
      (fun z => (fs_den_pos z).ne')) (fun z => (Real.sqrt_pos.2 (fs_den_pos z)).ne')
  · exact contDiff_id

theorem fsBallMap_sq {a : ℝ} (ha : 0 ≤ a) (z : PlanePhase ι) :
    phaseSq (fsBallMap a z) = a*phaseSq z/(1+phaseSq z) := by
  simp only [fsBallMap,phaseSq_smul,div_pow,Real.sq_sqrt ha,
    Real.sq_sqrt (fs_den_pos z).le]
  ring

theorem fsBallMap_gap {a : ℝ} (ha : 0 ≤ a) (z : PlanePhase ι) :
    a-phaseSq (fsBallMap a z) = a/(1+phaseSq z) := by
  rw [fsBallMap_sq ha]
  field_simp [(fs_den_pos z).ne']
  ring

@[simp] theorem fsAffineMap_fsBallMap {a : ℝ} (ha : 0 < a) (z : PlanePhase ι) :
    fsAffineMap a (fsBallMap a z) = z := by
  change (Real.sqrt (a-phaseSq (fsBallMap a z)))⁻¹ • fsBallMap a z = z
  rw [fsBallMap_gap ha.le,Real.sqrt_div ha.le]
  simp only [fsBallMap,smul_smul]
  rw [inv_mul_cancel₀ (div_pos (Real.sqrt_pos.2 ha)
    (Real.sqrt_pos.2 (fs_den_pos z))).ne',one_smul]

theorem fsAffineMap_sq {a : ℝ} {z : PlanePhase ι} (hz : z ∈ phaseOpenBall a) :
    phaseSq (fsAffineMap a z) = phaseSq z/(a-phaseSq z) := by
  simp only [fsAffineMap,phaseSq_smul,inv_pow,Real.sq_sqrt (sub_pos.2 hz).le]
  ring

@[simp] theorem fsBallMap_fsAffineMap {a : ℝ} (ha : 0 < a)
    {z : PlanePhase ι} (hz : z ∈ phaseOpenBall a) : fsBallMap a (fsAffineMap a z) = z := by
  have hgap : 0 < a-phaseSq z := sub_pos.2 hz
  have heq : 1+phaseSq (fsAffineMap a z) = a/(a-phaseSq z) := by
    rw [fsAffineMap_sq hz]
    field_simp [hgap.ne']
    ring
  change (Real.sqrt a/Real.sqrt (1+phaseSq (fsAffineMap a z))) • fsAffineMap a z = z
  rw [heq,Real.sqrt_div ha.le]
  simp only [fsAffineMap,smul_smul]
  have hscalar : Real.sqrt a / (Real.sqrt a / Real.sqrt (a-phaseSq z)) *
      (Real.sqrt (a-phaseSq z))⁻¹ = 1 := by
    field_simp [(Real.sqrt_pos.2 ha).ne',(Real.sqrt_pos.2 hgap).ne']
  rw [hscalar,one_smul]

def affineFSForm (a : ℝ) (z : PlanePhase ι) : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ :=
  (a/(1+phaseSq z)) • phaseArea - (a/(1+phaseSq z)^2) •
    ((phaseDot z).smulRight (phaseArea z) - (phaseArea z).smulRight (phaseDot z))

def affineFSPrimitive (a : ℝ) (z : PlanePhase ι) : PlanePhase ι →L[ℝ] ℝ :=
  (a/(2*(1+phaseSq z))) • phaseArea z

def phaseJ : PlanePhase ι →L[ℝ] PlanePhase ι :=
  ContinuousLinearMap.pi fun i =>
    (-((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.proj i))).prod
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.proj i))

omit [Fintype ι] in
@[simp] theorem phaseJ_apply (z : PlanePhase ι) (i : ι) :
    phaseJ z i = (-(z i).2,(z i).1) := rfl

omit [Fintype ι] in
@[simp] theorem phaseJ_sq (z : PlanePhase ι) : phaseJ (phaseJ z) = -z := by
  ext i <;> simp

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def horizontalSystem (Ω : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] F) :
    (E × (F →L[ℝ] ℝ)) →L[ℝ] ((E →L[ℝ] ℝ) × F) :=
  ((Ω.comp (ContinuousLinearMap.fst ℝ E (F →L[ℝ] ℝ))) -
    (((ContinuousLinearMap.compL ℝ E F ℝ).flip A).comp (ContinuousLinearMap.snd ℝ E (F →L[ℝ] ℝ)))).prod
    (A.comp (ContinuousLinearMap.fst ℝ E (F →L[ℝ] ℝ)))

@[simp] theorem horizontalSystem_apply (Ω : E →L[ℝ] E →L[ℝ] ℝ)
    (A : E →L[ℝ] F) (v : E) (l : F →L[ℝ] ℝ) :
    horizontalSystem Ω A (v,l) = (Ω v - l.comp A, A v) := rfl

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldMapDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped Manifold
open scoped ContDiff Topology
open Set Function Manifold
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

def manifoldMapDifferential (g : N → M) (x : N) : F →L[ℝ] E :=
  mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def manifoldPullbackTwoForm (Ω : ℝ → ManifoldTwoForm E M) (e : N → M)
    (t : ℝ) (b : N) : F →L[ℝ] F →L[ℝ] ℝ :=
  (Ω t (e b)).bilinearComp (manifoldMapDifferential (E := E) (F := F) e b)
    (manifoldMapDifferential (E := E) (F := F) e b)

def manifoldPullbackOneForm (α : ℝ → ManifoldOneForm E M) (e : N → M)
    (t : ℝ) (b : N) : F →L[ℝ] ℝ :=
  (α t (e b)).comp (manifoldMapDifferential (E := E) (F := F) e b)

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def manifoldExteriorOneForm (α : ManifoldOneForm E M) : ManifoldTwoForm E M :=
  fun x => (euclideanExteriorOneForm (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)).bilinearComp
    (chartDifferential x x) (chartDifferential x x)

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldFormTransport
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
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def parameterManifoldPullbackOneForm (α : P → ManifoldOneForm E M) (g : N → M)
    (p : P) : ManifoldOneForm F N :=
  manifoldPullbackOneForm (fun _ => α p) g 0

end

section

variable {P E V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

instance (priority := 50) flatProduct_chartedSpace : ChartedSpace (E × V) (M × V) :=
  prodChartedSpace E M V V

def productHorizontalLift (Γ : V → ManifoldOneForm E M) : ManifoldOneForm (E × V) (M × V) :=
  fun z => (Γ z.2 z.1).comp (ContinuousLinearMap.fst ℝ E V)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M] [ChartedSpace E M] in
@[simp] theorem productHorizontalLift_apply (Γ : V → ManifoldOneForm E M)
    (z : M × V) (v : E × V) : productHorizontalLift Γ z v=Γ z.2 z.1 v.1 := rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M] [ChartedSpace E M] in
@[simp] theorem productHorizontalLift_vertical (Γ : V → ManifoldOneForm E M)
    (z : M × V) (v : V) : productHorizontalLift Γ z (0,v)=0 := by
  simp

end

section

variable {F E V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def flatProductMap (g : F → M) : F × V → M × V := Prod.map g id

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricAnnulusDomain
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Topology
open Set Function Filter
open scoped Manifold
open Manifold
variable (m : ℕ)

theorem plus_contDiffAt {s : ℂ} (hs : s≠0) : ContDiffAt ℂ ∞ plus s :=
  (contDiffAt_id.add (contDiffAt_id.inv hs)).div_const 2

theorem minus_contDiffAt {s : ℂ} (hs : s≠0) : ContDiffAt ℂ ∞ minus s :=
  (contDiffAt_id.sub (contDiffAt_id.inv hs)).div_const 2

theorem baseSquare_contDiffAt {s : ℂ} (hs : s≠0) : ContDiffAt ℂ ∞ baseSquare s :=
  contDiffAt_const.add ((plus_contDiffAt hs).pow 2)

theorem annulusDomain_isOpen : IsOpen (annulusDomain m) := by
  rw [isOpen_iff_mem_nhds]
  intro s hs
  have hc := (baseSquare_contDiffAt hs.1).continuousAt
  have hz : ∀ᶠ t in 𝓝 s,t≠0 := isOpen_compl_singleton.mem_nhds hs.1
  have hb : ∀ᶠ t in 𝓝 s,0<(baseSquare t).re :=
    (Complex.continuous_re.continuousAt.comp hc).eventually (Ioi_mem_nhds hs.2.1)
  have hj : ∀ j : Fin (m+2),∀ᶠ t in 𝓝 s,1<j.val → 0<(parameters m j-baseSquare t).re := by
    intro j
    by_cases h : 1<j.val
    · exact ((Complex.continuous_re.continuousAt.comp (continuousAt_const.sub hc)).eventually
        (Ioi_mem_nhds (hs.2.2 j h))).mono (fun _ ht _ => ht)
    · exact Filter.Eventually.of_forall (fun _ ht => (h ht).elim)
  filter_upwards [hz,hb,Filter.eventually_all.mpr hj] with t ht0 htb htj
  exact ⟨ht0,htb,htj⟩

theorem unitCircle_subset_domain {s : ℂ} (hs : ‖s‖=1) : s∈annulusDomain m := by
  have hs0 : s≠0 := by intro h; simp [h] at hs
  have hp : plus s=(s.re : ℂ) := by
    rw [plus,Complex.inv_eq_conj hs,Complex.add_conj]
    push_cast
    ring
  have hb : (baseSquare s).re=1+s.re^2 := by simp [baseSquare,hp,← Complex.ofReal_pow]
  have hn : s.re^2≤1 := by
    have he := Complex.normSq_eq_norm_sq s
    rw [hs,one_pow] at he
    simp only [Complex.normSq_apply] at he
    nlinarith [sq_nonneg s.im]
  refine ⟨hs0,?_,?_⟩
  · rw [hb]; positivity
  · intro j hj
    have hj' : (2 : ℝ)≤j.val := by exact_mod_cast hj
    simp only [parameters,Complex.sub_re,Complex.add_re,Complex.natCast_re,Complex.one_re,hb]
    linarith

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit

abbrev PlaneBase := ℂ × ℂ

 def polynomial (z : PlaneBase) : ℂ := z.1*z.2*(z.1-z.2)+z.2-2*z.1

 def gradV (z : PlaneBase) : ℂ := 2*z.1*z.2-z.2^2-2
 def gradW (z : PlaneBase) : ℂ := z.1^2-2*z.1*z.2+1
 def jacobian (z : PlaneBase) : PlaneBase →L[ℂ] ℂ :=
  gradV z • ContinuousLinearMap.fst ℂ ℂ ℂ+gradW z • ContinuousLinearMap.snd ℂ ℂ ℂ

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_CubicFubiniStudy
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
open Hamiltonian
open scoped BigOperators ComplexConjugate

 def complexArea (z v : ℂ) : ℝ := (conj z*v).im

end PackingSufficiencySupport.DiagonalQuadrics

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

variable {ι : Type*} [Fintype ι]

def complexDiagonal (u : ι → ℂ) : (ι → ℂ) →L[ℝ] (ι → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    (u i) • (ContinuousLinearMap.proj i)

def complexAffineLift (z : ι → ℂ) : Option ι → ℂ
  | none => 1
  | some i => z i

def complexAffineQuotient (y : Option ι → ℂ) : ι → ℂ := fun i => y (some i)/y none

end

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def extendManifoldOneForm (U : Set M) (α : ManifoldOneForm E M) : ManifoldOneForm E M := by
  classical
  exact U.indicator α

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

def pathSpatialExterior (Γ : ℝ × E → E →L[ℝ] ℝ) (p : ℝ × E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (fderiv ℝ Γ p).comp (ContinuousLinearMap.inr ℝ ℝ E) -
    ((fderiv ℝ Γ p).comp (ContinuousLinearMap.inr ℝ ℝ E)).flip

@[simp] theorem pathSpatialExterior_apply (Γ : ℝ × E → E →L[ℝ] ℝ) (p : ℝ × E) (v w : E) :
    pathSpatialExterior Γ p v w = fderiv ℝ Γ p (0,v) w - fderiv ℝ Γ p (0,w) v := rfl


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldExteriorAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian


open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem handle_mfderiv_symm_comp
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞) {x : M} (hx : x∈e.source) :
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e.symm (e x)).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e x) = ContinuousLinearMap.id ℝ E := by
  have he : (e.symm ∘ e) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hd := mfderiv_comp x (e.symm.mdifferentiableAt (by simp) (e.map_source hx))
    (e.mdifferentiableAt (by simp) hx)
  rw [← hd,he.mfderiv_eq,mfderiv_id]
  rfl



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_AnnularChartHelpers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators

section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def linearLiouville (Ω : V →L[ℝ] V →L[ℝ] ℝ) : V → V →L[ℝ] ℝ := fun v => (1/2:ℝ) • Ω v

end

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def primitivePullback (α : F → F →L[ℝ] ℝ) (g : E → F) (x : E) : E →L[ℝ] ℝ :=
  (α (g x)).comp (fderiv ℝ g x)

end

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

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

abbrev AffineIndex := Option (Fin 1)
abbrev EndIndex := Fin 2 → Bool

def zeroEnd : EndIndex := fun _ => false

def endQuotient (ε : EndIndex) (s : ℂ) : AffineIndex → ℂ
  | none => (infinityRoot (parameters 0) ε s 0-1)/s
  | some _ => (infinityRoot (parameters 0) ε s 1-1)/s

def removableCoordinate (s : ℂ) (j : Fin 2) : ℂ :=
  -(parameters 0 j)*s/(infinityRoot (parameters 0) zeroEnd s j+1)

def endRegularRegion : Set ℂ := infinityRegion (parameters 0) ∩
  {s | ∀ j : Fin 2,infinityRoot (parameters 0) zeroEnd s j+1≠0}

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators

variable {ι : Type*} [Fintype ι]
abbrev VeroneseIndex (ι : Type*) := (Bool×ι) ⊕ (ι×ι)

def veronese (z : ι → ℂ) : VeroneseIndex ι → ℂ
  | .inl i => z i.2
  | .inr i => z i.1*z i.2

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian

variable {m : ℕ}

abbrev NormalPolynomialIndex (m : ℕ) := VeroneseIndex (Option (Fin m)) ⊕ Fin m

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

abbrev WeightedAffineIndex := Option (Fin 3)
abbrev WeightedHomogeneousIndex := Option WeightedAffineIndex

 def five (a b c d e : ℂ) : WeightedHomogeneousIndex → ℂ
  | none => a
  | some none => b
  | some (some j) => ![c,d,e] j

 def endCoefficient (s : ℂ) (j : Fin 2) : ℂ :=
  -(parameters 0 j)/(infinityRoot (parameters 0) zeroEnd s j+1)

 def endNumerator (ε : EndIndex) (s : ℂ) (j : Fin 2) : ℂ :=
  infinityRoot (parameters 0) ε s j-1

 def weightedEndOrder (D m : ℕ) (ε : EndIndex) : ℕ :=
  if ε 0 then (if ε 1 then D else D-m) else (if ε 1 then D-m else 0)

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 def weightedEndResidue (D m : ℕ) (ε : EndIndex) (c : ℝ) : ℝ := (weightedEndOrder D m ε:ℝ)*c

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_ExponentialMoment
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators Topology ContDiff
open Set Filter Function
section

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 def partition (w : ι → E) (a : ι → ℝ) (x : E) : ℝ :=
  ∑ i, a i * Real.exp (inner ℝ (w i) x)
 def gradient (w : ι → E) (a : ι → ℝ) (x : E) : E :=
  ∑ i, (a i * Real.exp (inner ℝ (w i) x)) • w i
 def moment (w : ι → E) (a : ι → ℝ) (x : E) : E :=
  (partition w a x)⁻¹ • gradient w a x
 def Surrounds (w : ι → E) (p : E) : Prop :=
  ∃ δ : ℝ, 0<δ ∧ ∀ v : E, ∃ i, δ*‖v‖≤ inner ℝ (w i-p) v

end
section

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 def hessian (w : ι → E) (a : ι → ℝ) (x : E) : E →L[ℝ] E :=
  ∑ i, ((a i*Real.exp (inner ℝ (w i) x)) • innerSL ℝ (w i)).smulRight (w i)

end

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 def inverse (w : ι → E) (a : ι → ℝ) (p : E) : E := invFun (moment w a) p

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

abbrev Plane := ℝ × ℝ
variable {ι : Type*} [Fintype ι]

def monomial (k : ℕ × ℕ) (r : Plane) : ℝ := r.1^k.1 * r.2^k.2

def polynomial (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) : ℝ :=
  ∑ i, a i * monomial (k i) r

def numerator (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) : Plane :=
  (∑ i, ((k i).1:ℝ)*a i*monomial (k i) r,
   ∑ i, ((k i).2:ℝ)*a i*monomial (k i) r)

def moment (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) : Plane :=
  (polynomial k a r)⁻¹ • numerator k a r

def centered (k : ι → ℕ × ℕ) (a : ι → ℝ) (p r : Plane) : Plane :=
  (∑ i, (((k i).1:ℝ)-p.1)*a i*monomial (k i) r,
   ∑ i, (((k i).2:ℝ)-p.2)*a i*monomial (k i) r)

def monomialDerivative (k : ℕ × ℕ) (r : Plane) : Plane →L[ℝ] ℝ :=
  ((k.1:ℝ)*r.1^(k.1-1)*r.2^k.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
  (r.1^k.1*(k.2:ℝ)*r.2^(k.2-1)) • ContinuousLinearMap.snd ℝ ℝ ℝ

def centeredDerivative (k : ι → ℕ × ℕ) (a : ι → ℝ) (p r : Plane) : Plane →L[ℝ] Plane :=
  (∑ i, ((((k i).1:ℝ)-p.1)*a i) • monomialDerivative (k i) r).prod
  (∑ i, ((((k i).2:ℝ)-p.2)*a i) • monomialDerivative (k i) r)

def faceMass (k : ℕ × ℕ) (a t : ℝ) : ℝ := if k.1=0 then a*t^k.2 else 0

def transverse (k : ι → ℕ × ℕ) (a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i,if (k i).1=1 then a i*t^(k i).2 else 0

def active (k : ι → ℕ × ℕ) (a : ι → ℝ) (p t : ℝ) : ℝ :=
  ∑ i,if (k i).1=0 then (((k i).2:ℝ)-p)*a i*((k i).2:ℝ)*t^((k i).2-1) else 0

end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RadialSlopes
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

def slopeNumerator (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) : Plane :=
  (∑ i,((k i).1:ℝ)*a i*r.1^((k i).1-1)*r.2^(k i).2,
   ∑ i,((k i).2:ℝ)*a i*r.1^(k i).1*r.2^((k i).2-1))

def slope (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) : Plane :=
  (polynomial k a r)⁻¹ • slopeNumerator k a r

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators Topology ContDiff
open Set Function

abbrev MomentPlane := EuclideanSpace ℝ (Fin 2)
 def planeVector (x y : ℝ) : MomentPlane := WithLp.toLp 2 ![x,y]
 def trapezoidCorners (A B : ℝ) : Fin 4 → MomentPlane :=
  ![planeVector 0 0,planeVector A 0,planeVector A (B-A),planeVector 0 B]
 def openTrapezoid (A B : ℝ) : Set MomentPlane :=
  {p | 0<p 0 ∧ p 0<A ∧ 0<p 1 ∧ p 0+p 1<B}

 def TrapezoidWeight (A B : ℕ) :=
  {k : Fin (B+1) × Fin (B+1) // k.1.val≤A ∧ k.1.val+k.2.val≤B}
 deriving Fintype, DecidableEq

 def trapezoidWeight (A B : ℕ) (k : TrapezoidWeight A B) : MomentPlane :=
  planeVector k.val.1.val k.val.2.val

 instance trapezoidWeight_nonempty (A B : ℕ) : Nonempty (TrapezoidWeight A B) :=
  ⟨⟨(⟨0,Nat.zero_lt_succ B⟩,⟨0,Nat.zero_lt_succ B⟩),by simp⟩⟩

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

def weight (k : ι → ℕ × ℕ) (i : ι) : MomentPlane := planeVector (k i).1 (k i).2

def logRadius (r : Plane) : MomentPlane := planeVector (Real.log r.1) (Real.log r.2)

def expRadius (x : MomentPlane) : Plane := (Real.exp (x 0),Real.exp (x 1))

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

abbrev Face (k : ι → ℕ × ℕ) := {i : ι // (k i).1=0}

def faceWeight (k : ι → ℕ × ℕ) (i : Face k) : ℝ := (k i.val).2

end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RadialSwap
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.FiniteMoment.Radial

section

open scoped BigOperators Topology ContDiff
open Set Filter Function
variable {ι : Type*} [Fintype ι]




abbrev Quadrant := {r : Plane // 0 ≤ r.1 ∧ 0 ≤ r.2}
instance instInhabitedQuadrant : Inhabited Quadrant := ⟨⟨(0,0),le_rfl,le_rfl⟩⟩

def nonnegativeInverse (k : ι → ℕ × ℕ) (a : ι → ℝ) (p : Plane) : Plane :=
  (invFun (fun r : Quadrant => moment k a r.val) p).val


end

section

open scoped BigOperators Topology ContDiff
open Set Filter Function

def latticeIndex {A B : ℕ} (i : TrapezoidWeight A B) : ℕ × ℕ :=
  (i.val.1.val,i.val.2.val)

def lowerTrapezoid (A B : ℝ) : Set Plane :=
  {p | 0≤p.1 ∧ p.1<A ∧ 0≤p.2 ∧ p.1+p.2<B}


end


open scoped BigOperators Topology ContDiff
open Set Filter Function



end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_AnalyticBoundary
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators Topology ContDiff
open Set Filter Function
section

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 def gibbs (w : ι → E) (a : ι → ℝ) (x : E) (i : ι) : ℝ :=
  a i*Real.exp (inner ℝ (w i) x)/partition w a x

end

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 def selected (w : ι → E) (a : ι → ℝ) (p : E) (i : ι) : ℝ :=
  gibbs w a (inverse w a p) i

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function
section

variable {ι : Type*} [Fintype ι]

def probability (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) (i : ι) : ℝ :=
  a i*monomial (k i) r/polynomial k a r

def selected (k : ι → ℕ × ℕ) (a : ι → ℝ) (p : Plane) (i : ι) : ℝ :=
  probability k a (nonnegativeInverse k a p) i

end

end PackingSufficiencySupport.FiniteMoment.Radial

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_ConvexWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators
open Set

 def closedTrapezoid (A B : ℝ) : Set MomentPlane :=
  {p | 0≤p 0 ∧ p 0≤A ∧ 0≤p 1 ∧ p 0+p 1≤B}

 def markedHeight (S : ℝ) (p : MomentPlane) : ℝ := max (S-p 0-p 1) 0
 def heightGraph (A B S : ℕ) (k : TrapezoidWeight A B) : MomentPlane × ℝ :=
  (trapezoidWeight A B k,markedHeight S (trapezoidWeight A B k))
 def heightHull (A B S : ℕ) : Set (MomentPlane × ℝ) := convexHull ℝ (range (heightGraph A B S))

 def latticeIndex {A B i j : ℕ} (hi : i ≤ A) (hij : i+j ≤ B) : TrapezoidWeight A B :=
  ⟨(⟨i,by omega⟩,⟨j,by omega⟩),hi,hij⟩

end PackingSufficiencySupport.FiniteMoment

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RestrictedMassIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open scoped BigOperators
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [PreconnectedSpace M]
  [NormalSpace M] [SigmaCompactSpace M]

def equalNormalCoefficient (m : ℕ) (b : ℝ) (p : Fin m → ℝ) : ℝ :=
  1-b*∑ j,p j

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicRadialFamilyExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold

 def totalWeight {A B : ℕ} (k : TrapezoidWeight A B) : ℕ := k.val.1.val+k.val.2.val
 def cubicDegree {A B : ℕ} (D : ℕ) (k : TrapezoidWeight A B) : ℕ := D-3*totalWeight k
 def cubicMarkedOrder {A B : ℕ} (S : ℕ) (k : TrapezoidWeight A B) : ℕ := S-totalWeight k

end PackingSufficiencySupport.CubicModel
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

abbrev DiskPlane := ℝ × ℝ

end PackingSufficiencySupport

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicRadialProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators ContDiff Manifold Topology
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

 def limitingEndOrder (D S : ℝ) (p : MomentPlane) (ε : EndIndex) : ℝ :=
  if ε 0 then (if ε 1 then D-3*(p 0+p 1) else D-3*(p 0+p 1)-markedHeight S p)
  else (if ε 1 then D-3*(p 0+p 1)-markedHeight S p else 0)

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_CubicRadialEndSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

def latticeOrigin (A B : ℕ) : TrapezoidWeight A B :=
  ⟨(⟨0,by omega⟩,⟨0,by omega⟩),by simp⟩

end PackingSufficiencySupport.FiniteMoment.Radial

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricSmoothExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
section
variable {m : ℕ} {a : Fin m → ℂ} [Fact (Injective a)] [Fact (∀ j,a j≠0)]

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
def exhaustionRadius (a : Fin m → ℂ) (ℓ : ℕ) : ℝ := 2+∑ j,‖a j‖+ℓ

end

end PackingSufficiencySupport.DiagonalQuadrics

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem homeomorph_fderiv_isInvertible (e : E ≃ₜ E)
    (he : Differentiable ℝ e) (hei : Differentiable ℝ e.symm) (x : E) :
    (fderiv ℝ e x).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := fderiv ℝ e.symm (e x))
  · have hd := ((he (e.symm (e x))).hasFDerivAt.comp (e x) (hei (e x)).hasFDerivAt).fderiv
    simpa only [Function.comp_def,e.apply_symm_apply,e.symm_apply_apply,fderiv_id,fderiv_fun_id] using hd.symm
  · have hd := ((hei (e x)).hasFDerivAt.comp x (he x).hasFDerivAt).fderiv
    simpa only [Function.comp_def,e.symm_apply_apply,fderiv_id,fderiv_fun_id] using hd.symm

namespace SupportedSmoothIsotopy

 theorem map_smooth {W : Set E} (Φ : SupportedSmoothIsotopy W) (t : ℝ) :
    ContDiff ℝ ∞ (Φ.map t) := Φ.smooth.comp (contDiff_const.prodMk contDiff_id)

 theorem symm_smooth {W : Set E} (Φ : SupportedSmoothIsotopy W) (t : ℝ) :
    ContDiff ℝ ∞ (Φ.map t).symm := Φ.inverse_smooth.comp (contDiff_const.prodMk contDiff_id)

 theorem fderiv_isInvertible {W : Set E} (Φ : SupportedSmoothIsotopy W) (t : ℝ) (x : E) :
    (fderiv ℝ (Φ.map t) x).IsInvertible :=
  homeomorph_fderiv_isInvertible (Φ.map t) ((Φ.map_smooth t).differentiable (by simp))
    ((Φ.symm_smooth t).differentiable (by simp)) x

 theorem fderiv_smooth {W : Set E} (Φ : SupportedSmoothIsotopy W) :
    ContDiff ℝ ∞ (fun p : ℝ × E => fderiv ℝ (Φ.map p.1) p.2) := by
  have he (p : ℝ × E) : fderiv ℝ (Φ.map p.1) p.2 =
      (fderiv ℝ (fun p : ℝ × E => Φ.map p.1 p.2) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    have hi : HasFDerivAt (fun x : E => (p.1,x)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 :=
      (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
    exact ((Φ.smooth.differentiable (by simp) p).hasFDerivAt.comp p.2 hi).fderiv
  simp_rw [he]
  exact (Φ.smooth.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp contDiff_const

 theorem det_fderiv_pos {W : Set E} (Φ : SupportedSmoothIsotopy W) (t : ℝ) (x : E) :
    0 < (fderiv ℝ (Φ.map t) x).det := by
  let d : ℝ → ℝ := fun t => (fderiv ℝ (Φ.map t) x).det
  have hd : Continuous d := ContinuousLinearMap.continuous_det.comp
    (Φ.fderiv_smooth.continuous.comp (continuous_id.prodMk continuous_const))
  have hdz (t : ℝ) : d t ≠ 0 := by
    obtain ⟨e,he⟩ := Φ.fderiv_isInvertible t x
    dsimp [d]
    rw [← he]
    exact e.toLinearEquiv.isUnit_det'.ne_zero
  have hd0 : d 0 = 1 := by simp [d,Φ.zero,fderiv_id,ContinuousLinearMap.det]
  by_contra hn
  have ht : d t ≤ 0 := le_of_not_gt hn
  obtain ⟨s,hs⟩ := intermediate_value_univ t 0 hd ⟨ht,by linarith⟩
  exact hdz s hs

end SupportedSmoothIsotopy

end
section

variable (P E : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

structure SupportedSmoothIsotopyFamily (W : Set E) where
  map : P → ℝ → E ≃ₜ E
  smooth : ContDiff ℝ ∞ (fun p : (P × ℝ) × E => map p.1.1 p.1.2 p.2)
  inverse_smooth : ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (map p.1.1 p.1.2).symm p.2)
  zero : ∀ y, map y 0 = Homeomorph.refl E
  support : Set E
  compact_support : IsCompact support
  support_subset : support ⊆ W
  fixed : ∀ y t x, x ∉ support → map y t x = x

variable {P E}
namespace SupportedSmoothIsotopyFamily

theorem endpoint_inverse_smooth {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W) :
    ContDiff ℝ ∞ (fun p : P × E => (Φ.map p.1 1).symm p.2) :=
  Φ.inverse_smooth.comp ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)

end SupportedSmoothIsotopyFamily

end

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

structure PlanarDiskEmbedding where
  radius : ℝ
  radius_pos : 0 < radius
  map : ℂ → ℂ
  smooth : ContDiff ℝ ∞ map
  domain : Set ℂ
  open_domain : IsOpen domain
  convex_domain : Convex ℝ domain
  subset_domain : Metric.closedBall 0 radius ⊆ domain
  injective : InjOn map domain
  nonsingular : ∀ x ∈ domain, (fderiv ℝ map x).IsInvertible
  orientation : 0 < (fderiv ℝ map 0).det

namespace PlanarDiskEmbedding

def carrier (D : PlanarDiskEmbedding) : Set ℂ := D.map '' Metric.closedBall 0 D.radius

def pull {W : Set ℂ} (D : PlanarDiskEmbedding) (Φ : SupportedSmoothIsotopy W) :
    PlanarDiskEmbedding where
  radius := D.radius
  radius_pos := D.radius_pos
  map := (Φ.map 1).symm ∘ D.map
  smooth := (Φ.symm_smooth 1).comp D.smooth
  domain := D.domain
  open_domain := D.open_domain
  convex_domain := D.convex_domain
  subset_domain := D.subset_domain
  injective := (Φ.map 1).symm.injective.injOn.comp D.injective (mapsTo_univ _ _)
  nonsingular := by
    intro x hx
    rw [fderiv_comp x ((Φ.symm_smooth 1).differentiable (by simp) _) (D.smooth.differentiable (by simp) x)]
    exact (Φ.symm.fderiv_isInvertible 1 (D.map x)).comp (D.nonsingular x hx)
  orientation := by
    rw [fderiv_comp 0 ((Φ.symm_smooth 1).differentiable (by simp) _) (D.smooth.differentiable (by simp) 0)]
    rw [ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,LinearMap.det_comp]
    exact mul_pos (Φ.symm.det_fderiv_pos 1 (D.map 0)) D.orientation

@[simp] theorem pull_radius {W : Set ℂ} (D : PlanarDiskEmbedding) (Φ : SupportedSmoothIsotopy W) :
    (D.pull Φ).radius = D.radius := rfl

@[simp] theorem pull_carrier {W : Set ℂ} (D : PlanarDiskEmbedding) (Φ : SupportedSmoothIsotopy W) :
    (D.pull Φ).carrier = (Φ.map 1).symm '' D.carrier := by
  change ((Φ.map 1).symm ∘ D.map) '' Metric.closedBall 0 D.radius =
    (Φ.map 1).symm '' (D.map '' Metric.closedBall 0 D.radius)
  exact image_comp _ _ _

end PlanarDiskEmbedding



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

structure ParametricDiskEmbedding (O : Set P) where
  radius : ℝ
  radius_pos : 0 < radius
  map : P × ℂ → ℂ
  smooth : ContDiff ℝ ∞ map
  domain : Set ℂ
  open_domain : IsOpen domain
  convex_domain : Convex ℝ domain
  subset_domain : Metric.closedBall 0 radius ⊆ domain
  injective : ∀ y ∈ O, InjOn (fun x => map (y,x)) domain
  nonsingular : ∀ y ∈ O, ∀ x ∈ domain,
    (fderiv ℝ (fun x => map (y,x)) x).IsInvertible
  orientation : ∀ y ∈ O, 0 < (fderiv ℝ (fun x => map (y,x)) 0).det

variable {P}
namespace ParametricDiskEmbedding
variable {O : Set P}

def carrier (D : ParametricDiskEmbedding P O) (y : P) : Set ℂ :=
  (fun x => D.map (y,x)) '' Metric.closedBall 0 D.radius

def eval (D : ParametricDiskEmbedding P O) (y : P) (hy : y ∈ O) : PlanarDiskEmbedding where
  radius := D.radius
  radius_pos := D.radius_pos
  map := fun x => D.map (y,x)
  smooth := D.smooth.comp (contDiff_const.prodMk contDiff_id)
  domain := D.domain
  open_domain := D.open_domain
  convex_domain := D.convex_domain
  subset_domain := D.subset_domain
  injective := D.injective y hy
  nonsingular := D.nonsingular y hy
  orientation := D.orientation y hy

@[simp] theorem eval_carrier (D : ParametricDiskEmbedding P O) (y : P) (hy : y ∈ O) :
    (D.eval y hy).carrier = D.carrier y := rfl

end ParametricDiskEmbedding

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_BallVolume
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff ENNReal Pointwise Classical

namespace PackingSufficiencySupport

abbrev Ambient (n : ℕ) := Fin n → ℂ

def capacity {n : ℕ} (z : Ambient n) : ℝ :=
  Real.pi * ∑ j, Complex.normSq (z j)

def realCoordinates (n : ℕ) : Ambient n ≃ₗ[ℝ] ((Fin n ⊕ Fin n) → ℝ) where
  toFun z := Sum.elim (fun j => (z j).re) (fun j => (z j).im)
  invFun v := fun j => ⟨v (Sum.inl j), v (Sum.inr j)⟩
  left_inv z := by rfl
  right_inv v := by funext i; cases i <;> rfl
  map_add' z w := by funext i; cases i <;> rfl
  map_smul' r z := by funext i; cases i <;> simp

def realBasis (n : ℕ) : Module.Basis (Fin n ⊕ Fin n) ℝ (Ambient n) :=
  Module.Basis.ofEquivFun (realCoordinates n)

@[simp]
theorem realBasis_repr {n : ℕ} (v : Ambient n) (i : Fin n ⊕ Fin n) :
    (realBasis n).repr v i = realCoordinates n v i := by
  exact Module.Basis.ofEquivFun_repr_apply _ _ _

@[fun_prop]
theorem continuous_capacity (n : ℕ) : Continuous (capacity : Ambient n → ℝ) := by
  unfold capacity
  fun_prop

open MeasureTheory

@[simp]
theorem capacity_zero (n : ℕ) : capacity (0 : Ambient n) = 0 := by
  simp [capacity]

def dilation (n : ℕ) (t : ℝ) (ht : t ≠ 0) : Ambient n ≃L[ℝ] Ambient n :=
  (LinearEquiv.smulOfNeZero ℝ (Ambient n) t ht).toContinuousLinearEquiv

@[simp] theorem dilation_apply (n : ℕ) (t : ℝ) (ht : t ≠ 0) (z : Ambient n) :
    dilation n t ht z = t • z := rfl

@[simp] theorem dilation_symm_apply (n : ℕ) (t : ℝ) (ht : t ≠ 0) (z : Ambient n) :
    (dilation n t ht).symm z = t⁻¹ • z := rfl

namespace Comparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def convexFunctionSet (S : Set E) (hS : Convex ℝ S) : Set C(S, ℝ) :=
  {f | ∀ (x y : S) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
    f ⟨a • (x : E) + b • (y : E), hS x.property y.property ha hb hab⟩ ≤
      a * f x + b * f y}

abbrev ConvexMaps (S : Set E) (hS : Convex ℝ S) := ↥(convexFunctionSet S hS)

instance convexMaps_nonempty (S : Set E) (hS : Convex ℝ S) : Nonempty (ConvexMaps S hS) :=
  ⟨⟨0, by simp [convexFunctionSet]⟩⟩

def affineStep {S : Set E} {hS : Convex ℝ S} (lam : ℝ) (hlam : 0 ≤ lam)
    (Q F : ConvexMaps S hS) : ConvexMaps S hS :=
  ⟨lam • (F : C(S, ℝ)) + (Q : C(S, ℝ)), by
    intro x y a b ha hb hab
    have hF := mul_le_mul_of_nonneg_left (F.property x y a b ha hb hab) hlam
    have hQ := Q.property x y a b ha hb hab
    change lam * F.val _ + Q.val _ ≤ a * (lam * F.val x + Q.val x) +
      b * (lam * F.val y + Q.val y)
    nlinarith⟩

end Comparison
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
namespace PackingSufficiencySupport
open MeasureTheory
namespace Comparison
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def translate {S : Set E} {hS : Convex ℝ S} (F : ConvexMaps S hS)
    (c : ℝ) : ConvexMaps S hS :=
  ⟨F.val + ContinuousMap.const S c, by
    intro x y a b ha hb hab
    have hf := F.property x y a b ha hb hab
    change F.val _ + c ≤ a * (F.val x + c) + b * (F.val y + c)
    nlinarith [congrArg (fun t : ℝ => t * c) hab]⟩

section SlicedDomain
variable (Y : Set E) (L : E → ℝ)

def sliceDomain : Set (E × ℝ) := {x | x.1 ∈ Y ∧ x.2 ∈ Set.Icc 0 (L x.1)}

abbrev Slice := ↥(sliceDomain Y L)

def sliceBase : C(Slice Y L, Y) :=
  ⟨fun x => ⟨x.val.1, x.property.1⟩,
    (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩

def sliceHeight : C(Slice Y L, ℝ) :=
  ⟨fun x => x.val.2, continuous_snd.comp continuous_subtype_val⟩

def sliceLength (hL : ContinuousOn L Y) : C(Slice Y L, ℝ) :=
  (⟨fun y : Y => L y, hL.domRestrict⟩ : C(Y, ℝ)).comp (sliceBase Y L)

def pointAtHeight (x : Slice Y L) (a : ℝ) (ha : a ∈ Set.Icc 0 (L x.val.1)) :
    Slice Y L := ⟨(x.val.1, a), x.property.1, ha⟩

def intervalCandidate (F : C(Slice Y L, ℝ)) (x : Slice Y L) (a : ℝ)
    (ha : 0 ≤ a) (hax : a + x.val.2 ≤ L x.val.1) : ℝ :=
  max (F (pointAtHeight Y L x a ⟨ha, by linarith [x.property.2.1]⟩))
    (F (pointAtHeight Y L x (a + x.val.2) ⟨by linarith [x.property.2.1], hax⟩))

theorem convex_sliceDomain (hc : ConcaveOn ℝ Y L) : Convex ℝ (sliceDomain Y L) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hc.1 hx.1 hy.1 ha hb hab, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1)
  · exact (add_le_add (mul_le_mul_of_nonneg_left hx.2.2 ha)
      (mul_le_mul_of_nonneg_left hy.2.2 hb)).trans (hc.2 hx.1 hy.1 ha hb hab)

end SlicedDomain

variable (Y : Set E) (L : E → ℝ)

def clampPoint (x : Slice Y L) : C(ℝ, Slice Y L) := by
  refine ⟨fun h => pointAtHeight Y L x (max 0 (min (L x.val.1) h))
    ⟨le_max_left _ _, max_le (x.property.2.1.trans x.property.2.2) (min_le_left _ _)⟩, ?_⟩
  apply Continuous.subtype_mk
  exact continuous_const.prodMk (continuous_const.max (continuous_const.min continuous_id))

def sliceFunction (F : C(Slice Y L, ℝ)) (x : Slice Y L) : C(ℝ, ℝ) :=
  F.comp (clampPoint Y L x)

end Comparison
end PackingSufficiencySupport

namespace PackingSufficiencySupport.MomentPolytope
variable {m N : ℕ}
abbrev Moments (m : ℕ) := Fin m → ℝ
abbrev Base (j : Fin m) := {i : Fin m // i ≠ j} → ℝ

def assemble (j : Fin m) (y : Base j) (h : ℝ) : Moments m :=
  fun i => if hi : i = j then h else y ⟨i, hi⟩

@[simp] theorem assemble_at (j : Fin m) (y : Base j) (h : ℝ) : assemble j y h j = h := by
  simp [assemble]
@[simp] theorem assemble_off (j : Fin m) (y : Base j) (h : ℝ) (i : {i : Fin m // i ≠ j}) :
    assemble j y h i = y i := by simp [assemble, i.property]

end PackingSufficiencySupport.MomentPolytope
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_PolytopeSlices
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

abbrev Active (b : Fin N → Moments m) (j : Fin m) := {ν : Fin N // 0 < b ν j}

variable (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)

def endpoint (ν : Active b j) (y : Base j) : ℝ :=
  (c ν - ∑ i : {i : Fin m // i ≠ j}, b ν i.val * y i) / b ν j

def length [Nonempty (Active b j)] (y : Base j) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun ν => endpoint b c j ν y)

theorem continuous_endpoint (ν : Active b j) : Continuous (endpoint b c j ν) := by
  unfold endpoint
  fun_prop

theorem continuous_length [Nonempty (Active b j)] : Continuous (length b c j) := by
  apply Continuous.finset_inf'_apply
  intro ν _
  exact continuous_endpoint b c j ν

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Comparison
open MeasureTheory
variable {E : Type*} [TopologicalSpace E] [T2Space E]
variable [MeasurableSpace E] [BorelSpace E]

def zeroExtend (S : Set E) (F : C(S, ℝ)) (x : E) : ℝ :=
  if hx : x ∈ S then F ⟨x, hx⟩ else 0

omit [T2Space E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem zeroExtend_coe (S : Set E) (F : C(S, ℝ)) (x : S) :
    zeroExtend S F x = F x := by simp [zeroExtend, x.property]

omit [T2Space E] [MeasurableSpace E] [BorelSpace E] in
theorem zeroExtend_continuousOn (S : Set E) (F : C(S, ℝ)) :
    ContinuousOn (zeroExtend S F) S := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h : S.domRestrict (zeroExtend S F) = F := by ext x; exact zeroExtend_coe S F x
  rw [h]
  exact F.continuous

omit [T2Space E] [MeasurableSpace E] [BorelSpace E] in
theorem indicator_zeroExtend (S : Set E) (F : C(S, ℝ)) :
    S.indicator (zeroExtend S F) = zeroExtend S F := by
  ext x
  by_cases hx : x ∈ S <;> simp [Set.indicator, zeroExtend, hx]

theorem zeroExtend_integrable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (S : Set E) (hS : IsCompact S) (F : C(S, ℝ)) : Integrable (zeroExtend S F) μ := by
  have h := (zeroExtend_continuousOn S F).integrableOn_compact hS (μ := μ)
  have h' := (integrable_indicator_iff hS.measurableSet).mpr h
  rwa [indicator_zeroExtend] at h'

def integralMap (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (S : Set E) (hS : IsCompact S) : C(S, ℝ) →ₗ[ℝ] ℝ where
  toFun F := ∫ x, zeroExtend S F x ∂μ
  map_add' F G := by
    have heq : zeroExtend S (F+G) = fun x => zeroExtend S F x + zeroExtend S G x := by
      ext x; by_cases hx : x ∈ S <;> simp [zeroExtend, hx]
    rw [heq, integral_add (zeroExtend_integrable μ S hS F) (zeroExtend_integrable μ S hS G)]
  map_smul' a F := by
    have heq : zeroExtend S (a • F) = fun x => a • zeroExtend S F x := by
      ext x; by_cases hx : x ∈ S <;> simp [zeroExtend, hx]
    simp only [heq, integral_smul, RingHom.id_apply]

end PackingSufficiencySupport.Comparison

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

namespace PackingSufficiencySupport.Comparison
open scoped ContDiff ENNReal Pointwise Classical
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E]
variable [MeasureSpace E] [BorelSpace E]
variable [IsFiniteMeasureOnCompacts (volume : Measure E)]

def averageMap (S : Set E) (hS : IsCompact S) : C(S, ℝ) →ₗ[ℝ] ℝ :=
  (volume S).toReal⁻¹ • integralMap volume S hS

end PackingSufficiencySupport.Comparison

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators
open Set Function
open Hamiltonian

variable {m N : ℕ}

def baseProjection (j : Fin m) (y : Moments m) : Base j := fun i => y i

def baseProjectionL (j : Fin m) : Moments m →ₗ[ℝ] Base j where
  toFun := baseProjection j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[fun_prop] theorem baseProjection_smooth (j : Fin m) : ContDiff ℝ ∞ (baseProjection j) :=
  (baseProjectionL j).toContinuousLinearMap.contDiff

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

abbrev CircleModel := EuclideanSpace ℝ (Fin 1)

def circleInclusion (z : Circle) : ℂ := z

def ambientAngular (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (1/(2*Real.pi)) • (Complex.imCLM.comp (ContinuousLinearMap.mul ℝ ℂ (starRingEnd ℂ z)))

@[simp] theorem ambientAngular_apply (z w : ℂ) :
    ambientAngular z w = (1/(2*Real.pi))*((starRingEnd ℂ z)*w).im := rfl

theorem circle_coe_smooth : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℂ) ∞
    circleInclusion := by
  let := finrank_real_complex_fact'
  exact contMDiff_coe_sphere (E := ℂ) (n := 1)

def circleTurn (t : ℝ) : Circle := Circle.exp (2*Real.pi*t)

theorem circleTurn_smooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) ∞ circleTurn :=
  contMDiff_circleExp.comp ((contDiff_const.mul contDiff_id).contMDiff)

theorem circleTurn_deriv (t : ℝ) :
    HasDerivAt (fun s : ℝ => (circleTurn s : ℂ))
      ((circleTurn t : ℂ)*((2*Real.pi : ℝ):ℂ)*Complex.I) t := by
  have h := ((((hasDerivAt_id t).const_mul (2*Real.pi)).ofReal_comp).mul_const Complex.I).cexp
  simpa only [circleTurn,Circle.coe_exp,one_mul,mul_one,mul_assoc,id_eq] using h

def shortCircleArgument (z : Circle) : ℝ := Complex.arg z/(2*Real.pi)

theorem circleTurn_isOpenMap : IsOpenMap circleTurn := by
  exact isLocalHomeomorph_circleExp.isOpenMap.comp
    (Homeomorph.mulLeft₀ (2*Real.pi) (by positivity)).isOpenMap

theorem shortCircleArgument_turn {s : ℝ} (hs : s ∈ Ioo (-(1/2):ℝ) (1/2)) :
    shortCircleArgument (circleTurn s)=s := by
  have h1 : -Real.pi<2*Real.pi*s := by
    have ht := mul_lt_mul_of_pos_left hs.1 (show 0<2*Real.pi by positivity)
    nlinarith
  have h2 : 2*Real.pi*s<Real.pi := by
    have ht := mul_lt_mul_of_pos_left hs.2 (show 0<2*Real.pi by positivity)
    nlinarith
  unfold shortCircleArgument circleTurn
  rw [Circle.arg_exp h1 h2.le]
  field_simp

theorem real_contDiffAt_argument {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ Complex.arg z := by
  have hlog : ContDiffAt ℝ ∞ Complex.log z :=
    (Complex.contDiffAt_log hz).restrict_scalars ℝ
  have ht := Complex.imCLM.contDiff.contDiffAt.comp z hlog
  change ContDiffAt ℝ ∞ (fun x => (Complex.log x).im) z at ht
  simpa only [Complex.log_im] using ht

theorem shortCircleArgument_smooth_at {z : Circle} (hz : (z : ℂ) ∈ Complex.slitPlane) :
    ContMDiffAt 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ shortCircleArgument z := by
  have ha : ContMDiffAt 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞
      (fun w : Circle => Complex.arg (circleInclusion w)) z :=
    (real_contDiffAt_argument hz).contMDiffAt.comp z circle_coe_smooth.contMDiffAt
  exact ha.div_const (2*Real.pi)

theorem circleTurn_short_slit {s : ℝ} (hs : s ∈ Ioo (-(1/2):ℝ) (1/2)) :
    (circleTurn s : ℂ) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff_arg.mpr
  refine ⟨?_,Circle.coe_ne_zero _⟩
  have h1 : -Real.pi<2*Real.pi*s := by
    have ht := mul_lt_mul_of_pos_left hs.1 (show 0<2*Real.pi by positivity)
    nlinarith
  have h2 : 2*Real.pi*s<Real.pi := by
    have ht := mul_lt_mul_of_pos_left hs.2 (show 0<2*Real.pi by positivity)
    nlinarith
  simpa only [circleTurn,Circle.arg_exp h1 h2.le] using h2.ne

def circleBandCoordinate : PartialDiffeomorph 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) ℝ Circle ∞ where
  toFun := circleTurn
  invFun := shortCircleArgument
  source := Ioo (-(1/2):ℝ) (1/2)
  target := circleTurn '' Ioo (-(1/2):ℝ) (1/2)
  map_source' s hs := ⟨s,hs,rfl⟩
  map_target' := by
    rintro z ⟨s,hs,rfl⟩
    rwa [shortCircleArgument_turn hs]
  left_inv' := fun _ hs => shortCircleArgument_turn hs
  right_inv' := by
    rintro z ⟨s,hs,rfl⟩
    rw [shortCircleArgument_turn hs]
  open_source := isOpen_Ioo
  open_target := circleTurn_isOpenMap _ isOpen_Ioo
  contMDiffOn_toFun := circleTurn_smooth.contMDiffOn
  contMDiffOn_invFun := by
    rintro z ⟨s,hs,rfl⟩
    exact (shortCircleArgument_smooth_at (circleTurn_short_slit hs)).contMDiffWithinAt

@[simp] theorem circleBandCoordinate_apply (s : ℝ) : circleBandCoordinate s=circleTurn s := rfl

@[simp] theorem circleBandCoordinate_source :
    circleBandCoordinate.source=Ioo (-(1/2):ℝ) (1/2) := rfl

def intervalClock (a b s : ℝ) : ℝ := Real.smoothTransition ((s-a)/(b-a))

@[fun_prop] theorem intervalClock_smooth (a b : ℝ) : ContDiff ℝ ∞ (intervalClock a b) := by
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem circleTurn_shortCircleArgument (z : Circle) :
    circleTurn (shortCircleArgument z)=z := by
  unfold circleTurn shortCircleArgument
  rw [mul_div_cancel₀ _ (show 2*Real.pi≠0 by positivity)]
  exact Circle.exp_arg z

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

abbrev TorusModel := CircleModel × CircleModel
abbrev HandleTorus := Circle × Circle

instance torus_chartedSpace : ChartedSpace TorusModel HandleTorus :=
  prodChartedSpace CircleModel Circle CircleModel Circle

theorem torus_snd_smooth : ContMDiff 𝓘(ℝ,TorusModel) 𝓘(ℝ,CircleModel) ∞
    (Prod.snd : HandleTorus → Circle) := by
  rw [show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact contMDiff_snd





abbrev CylinderModel := ℝ × CircleModel
abbrev HandleCylinder := ℝ × Circle

instance cylinder_chartedSpace : ChartedSpace CylinderModel HandleCylinder :=
  prodChartedSpace ℝ ℝ CircleModel Circle

def torusAnnulusMap (z : HandleCylinder) : HandleTorus := (circleTurn z.1,z.2)
def torusAnnulusInverse (z : HandleTorus) : HandleCylinder := (shortCircleArgument z.1,z.2)

theorem torusAnnulusMap_smooth : ContMDiff 𝓘(ℝ,CylinderModel) 𝓘(ℝ,TorusModel) ∞
    torusAnnulusMap := by
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod,
    show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact (circleTurn_smooth.comp contMDiff_fst).prodMk contMDiff_snd

theorem torusAnnulusInverse_smooth {z : HandleTorus}
    (hz : z.1 ∈ circleBandCoordinate.target) :
    ContMDiffAt 𝓘(ℝ,TorusModel) 𝓘(ℝ,CylinderModel) ∞ torusAnnulusInverse z := by
  have h := circleBandCoordinate.contMDiffOn_invFun.contMDiffAt
    (circleBandCoordinate.open_target.mem_nhds hz)
  rw [show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod,
    show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact (h.comp z contMDiffAt_fst).prodMk contMDiffAt_snd

def torusAnnulus : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,TorusModel)
    HandleCylinder HandleTorus ∞ where
  toFun := torusAnnulusMap
  invFun := torusAnnulusInverse
  source := circleBandCoordinate.source ×ˢ univ
  target := circleBandCoordinate.target ×ˢ univ
  map_source' z hz := ⟨circleBandCoordinate.map_source hz.1,mem_univ _⟩
  map_target' z hz := ⟨circleBandCoordinate.map_target hz.1,mem_univ _⟩
  left_inv' z hz := by
    apply Prod.ext
    · exact circleBandCoordinate.left_inv hz.1
    · rfl
  right_inv' z hz := by
    apply Prod.ext
    · exact circleBandCoordinate.right_inv hz.1
    · rfl
  open_source := circleBandCoordinate.open_source.prod isOpen_univ
  open_target := circleBandCoordinate.open_target.prod isOpen_univ
  contMDiffOn_toFun := torusAnnulusMap_smooth.contMDiffOn
  contMDiffOn_invFun := fun _ hz => (torusAnnulusInverse_smooth hz.1).contMDiffWithinAt





theorem cylinder_snd_smooth : ContMDiff 𝓘(ℝ,CylinderModel) 𝓘(ℝ,CircleModel) ∞
    (Prod.snd : HandleCylinder → Circle) := by
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact contMDiff_snd

theorem circleTurn_add (s t : ℝ) : circleTurn (s+t)=circleTurn s*circleTurn t := by
  simp only [circleTurn,mul_add,Circle.exp_add]


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
open Set Function Manifold

section Restriction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

def restrictHandleDiffeomorph
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    (U : Set M) (hU : IsOpen U) : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞ where
  __ := e.toOpenPartialHomeomorph.restrOpen U hU
  contMDiffOn_toFun := e.contMDiffOn.mono inter_subset_left
  contMDiffOn_invFun := e.symm.contMDiffOn.mono inter_subset_left
end Restriction

end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold

theorem circleTurn_sub (s t : ℝ) : circleTurn (s-t)=circleTurn s/circleTurn t := by
  simp only [circleTurn,mul_sub,Circle.exp_sub]

def positiveCircleArgument (z : Circle) : ℝ :=
  shortCircleArgument (z/circleTurn (1/2))+1/2

theorem positiveCircleArgument_turn {s : ℝ} (hs : s∈Ioo (0:ℝ) 1) :
    positiveCircleArgument (circleTurn s)=s := by
  unfold positiveCircleArgument
  rw [← circleTurn_sub,shortCircleArgument_turn (show s-1/2∈Ioo (-(1/2):ℝ) (1/2) by
    constructor <;> linarith [hs.1,hs.2])]
  ring

theorem circleTurn_positiveCircleArgument (z : Circle) :
    circleTurn (positiveCircleArgument z)=z := by
  rw [positiveCircleArgument,circleTurn_add,circleTurn_shortCircleArgument,div_mul_cancel]


end


open scoped ContDiff Topology
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_LayerAreaForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def surfaceRemainder (K H : E → ℝ) (h : ι → E → ℝ) (ψ : E → E) (v : E) : ℝ :=
  K (ψ v)-K v+H v-∑ i, h i v

@[fun_prop] theorem surfaceRemainder_smooth {K H : E → ℝ} {h : ι → E → ℝ} {ψ : E → E}
    (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H) (hh : ∀ i, ContDiff ℝ ∞ (h i))
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (surfaceRemainder K H h ψ) := by
  exact ((hK.comp hψ).sub hK |>.add hH).sub (ContDiff.sum (fun i _ => hh i))

def surfaceFirstLayer (S : ℝ → ℝ) (H : E → ℝ) (ψ : E → E) (p : ℝ × E) : ℝ :=
  S p.1*H (ψ p.2)

def surfaceFinalLayer (J : E → ℝ) (h : ι → E → ℝ) (R : E → ℝ)
    (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ) (p : ℝ × E) : ℝ :=
  J p.2+(∑ i, ρ i p.1*h i p.2)+ρ₀ p.1*R p.2

@[fun_prop] theorem surfaceFirstLayer_smooth {S : ℝ → ℝ} {H : E → ℝ} {ψ : E → E}
    (hS : ContDiff ℝ ∞ S) (hH : ContDiff ℝ ∞ H) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (surfaceFirstLayer S H ψ) :=
  (hS.comp contDiff_fst).mul ((hH.comp hψ).comp contDiff_snd)

@[fun_prop] theorem surfaceFinalLayer_smooth {J R : E → ℝ} {h : ι → E → ℝ}
    {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ} (hJ : ContDiff ℝ ∞ J) (hR : ContDiff ℝ ∞ R)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (hρ₀ : ContDiff ℝ ∞ ρ₀) : ContDiff ℝ ∞ (surfaceFinalLayer J h R ρ ρ₀) :=
  ((hJ.comp contDiff_snd).add (ContDiff.sum (fun i _ =>
    (hρ i |>.comp contDiff_fst).mul (hh i |>.comp contDiff_snd)))).add
    ((hρ₀.comp contDiff_fst).mul (hR.comp contDiff_snd))


end

open scoped ContDiff
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_ConstructedSurfaceLayers
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure CompactHamiltonianIsotopy (A : E →L[ℝ] E →L[ℝ] ℝ) where
  map : ℝ → E ≃ₜ E
  smooth : ContDiff ℝ ∞ (fun p : ℝ × E => map p.1 p.2)
  inverse_smooth : ContDiff ℝ ∞ (fun p : ℝ × E => (map p.1).symm p.2)
  zero : map 0 = Homeomorph.refl E
  hamiltonian : ℝ × E → ℝ
  hamiltonian_smooth : ContDiff ℝ ∞ hamiltonian
  compact : HasCompactSupport hamiltonian
  flow : ∀ t x, HasDerivAt (fun s => map s x)
    (hamiltonianField A hamiltonian (t,map t x)) t
  symplectic : ∀ t x v w, A (fderiv ℝ (map t) x v) (fderiv ℝ (map t) x w) = A v w
  fixed : ∀ t x, x ∉ Prod.snd '' tsupport hamiltonian → map t x = x

namespace CompactHamiltonianIsotopy
variable {A : E →L[ℝ] E →L[ℝ] ℝ}

@[fun_prop] theorem map_smooth (Φ : CompactHamiltonianIsotopy A) (t : ℝ) :
    ContDiff ℝ ∞ (Φ.map t) := Φ.smooth.comp (contDiff_const.prodMk contDiff_id)

@[fun_prop] theorem map_inverse_smooth (Φ : CompactHamiltonianIsotopy A) (t : ℝ) :
    ContDiff ℝ ∞ (Φ.map t).symm := Φ.inverse_smooth.comp (contDiff_const.prodMk contDiff_id)

end CompactHamiltonianIsotopy

end

open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : E →L[ℝ] E →L[ℝ] ℝ}

variable {ι : Type*} [Fintype ι]

def surfaceInterpolatedLayer (S : ℝ → ℝ) (K H : E → ℝ) (h : ι → E → ℝ)
    (ψ : E → E) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ) (τ : ℝ) (p : ℝ × E) : ℝ :=
  (1-τ)*surfaceFirstLayer S H ψ p +
    τ*surfaceFinalLayer (K-H) h (surfaceRemainder K H h ψ) ρ ρ₀ p



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_SurfacePathPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped Manifold Topology
open Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : E →L[ℝ] E →L[ℝ] ℝ}

variable {ι : Type*} [Fintype ι]
@[fun_prop] theorem surfaceInterpolatedLayer_smooth {S : ℝ → ℝ} {K H : E → ℝ}
    {h : ι → E → ℝ} {ψ : E → E} {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ}
    (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hψ : ContDiff ℝ ∞ ψ)
    (hρ : ∀ i, ContDiff ℝ ∞ (ρ i)) (hρ₀ : ContDiff ℝ ∞ ρ₀) (τ : ℝ) :
    ContDiff ℝ ∞ (surfaceInterpolatedLayer S K H h ψ ρ ρ₀ τ) :=
  (contDiff_const.mul (surfaceFirstLayer_smooth hS hH hψ)).add
    (contDiff_const.mul (surfaceFinalLayer_smooth (hK.sub hH) (surfaceRemainder_smooth hK hH hh hψ) hh hρ hρ₀))

end

def complexUnitDirection (z : ℂ) : Circle := by
  classical
  exact if hz : z=0 then 1 else ⟨((‖z‖⁻¹:ℝ):ℂ)*z,by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩

theorem complexUnitDirection_coe {z : ℂ} (hz : z≠0) :
    (complexUnitDirection z : ℂ)=((‖z‖⁻¹:ℝ):ℂ)*z := by
  simp only [complexUnitDirection]
  erw [dite_eq_right hz]

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_QuadricCylinderChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped Topology
open Set Function

def complexClosedAnnulus (ε : ℝ) : Set ℂ := {z | 1-ε≤‖z‖ ∧ ‖z‖≤1+ε}

end PackingSufficiencySupport

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

abbrev RadialPlane := ℝ × ℝ

def planeRadiusSq (x : RadialPlane) : ℝ := x.1^2+x.2^2

def planeRadialStep (ε : ℝ) (x : RadialPlane) : ℝ :=
  Real.smoothTransition ((planeRadiusSq x-(1-ε)^2)/((1+ε)^2-(1-ε)^2))

def planeClosedAnnulus (ε : ℝ) : Set RadialPlane :=
  Complex.equivRealProdCLM.symm ⁻¹' complexClosedAnnulus ε

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable (m : ℕ)

def transverseRadius (θ : ℝ) : ℝ := Real.sin θ+Real.sqrt (1+Real.sin θ^2)

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

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

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

def FormNeighborhoodEmbedding (K : Set N) (σ : ManifoldTwoForm F N)
    (Ω : ManifoldTwoForm E M) (f : N → M) : Prop :=
  ∃ U : Set N, IsOpen U ∧ K ⊆ U ∧ ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ f U ∧
    Topology.IsEmbedding (fun x : U => f x) ∧
    ∀ x ∈ U, ∀ v w, Ω (f x)
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) f x v) (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) f x w) = σ x v w

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
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : E →L[ℝ] E →L[ℝ] ℝ}

def autonomousField (A : E →L[ℝ] E →L[ℝ] ℝ) (f : E → ℝ) (x : E) : E :=
  hamiltonianField A (fun p => f p.2) (0,x)

end
section

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {μ : V → ℝ} {a : ℝ}

def CollarInvariant (Ω : V →L[ℝ] V →L[ℝ] ℝ) (μ : V → ℝ) (a : ℝ) (f : V → W) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ v,a<μ v→fderiv ℝ f v (autonomousField Ω μ v)=0

end

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

def splitInclusion (L : (F × G) ≃L[ℝ] E) : F →L[ℝ] E :=
  L.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ F G)

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_MovingPrimitiveNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.NormalLift
open scoped ContDiff InnerProduct Topology
open Set Function
section

variable {E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup P] [NormedSpace ℝ P]

def adjointCLM : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) where
  toFun := ContinuousLinearMap.adjoint
  map_add' := map_add ContinuousLinearMap.adjoint
  map_smul' := by intro c A; simp
  cont := ContinuousLinearMap.adjoint.continuous

def gram (A : E →L[ℝ] F) : F →L[ℝ] F := A.comp (adjointCLM A)

def rightLift (A : E →L[ℝ] F) : F →L[ℝ] E :=
  (adjointCLM A).comp (gram A).inverse

end

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

abbrev HilbertModel (E : Type*) [AddCommGroup E] [Module ℝ E] :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def hilbertEquiv : E ≃L[ℝ] HilbertModel E :=
  (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.trans
    (EuclideanSpace.equiv _ ℝ).symm

def hilbertArrow : (E →L[ℝ] F) ≃L[ℝ] (HilbertModel E →L[ℝ] HilbertModel F) :=
  (hilbertEquiv E).arrowCongr (hilbertEquiv F)

def finiteRightLift (A : E →L[ℝ] F) : F →L[ℝ] E :=
  (((hilbertEquiv F).symm).arrowCongr (hilbertEquiv E).symm)
    (rightLift (hilbertArrow E F A))

end PackingSufficiencySupport.NormalLift
end

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open NormalLift Hamiltonian DiagonalQuadrics DiagonalQuadrics.Explicit

def regularLocus : Set PlaneBase := {z | gradV z≠0 ∨ gradW z≠0}

def realJacobian (z : PlaneBase) : PlaneBase →L[ℝ] ℂ :=
  (jacobian z).restrictScalars ℝ

def normalLift (z : PlaneBase) : ℂ →L[ℝ] PlaneBase :=
  finiteRightLift _ _ (realJacobian z)

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_ScaledPlanarMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Comparison
open scoped Topology
open Set Function Filter
section

variable {P : Type*} [TopologicalSpace P] {m : ℕ}

def IntervalRoom (V : P → Fin m → Set ℝ) (L : Fin m → ℝ) (y : P) : Prop :=
  ∀ i, ∃ a b : ℝ, a ∈ V y i ∧ b ∈ V y i ∧ L i < b-a

def clampUnit (h : ℝ) : ℝ := max 0 (min 1 h)

theorem continuous_clampUnit : Continuous clampUnit :=
  continuous_const.max (continuous_const.min continuous_id)

end

variable {P : Type*} [TopologicalSpace P]

def scaledUnitFamily (F : C(P × ℝ,ℝ)) (l : C(P,ℝ)) : C(P × ℝ,ℝ) :=
  F.comp ⟨fun p => (p.1,l p.1*p.2), continuous_fst.prodMk
    ((l.continuous.comp continuous_fst).mul continuous_snd)⟩

def fiberFunction (F : C(P × ℝ,ℝ)) (y : P) : C(ℝ,ℝ) :=
  F.comp ⟨fun t => (y,t),continuous_const.prodMk continuous_id⟩

end PackingSufficiencySupport.Comparison
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

theorem hamiltonianField_add (A : E →L[ℝ] E →L[ℝ] ℝ)
    {H G : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G) (p : ℝ × E) :
    hamiltonianField A (H+G) p = hamiltonianField A H p+hamiltonianField A G p := by
  simp only [hamiltonianField,formMoserField,spatialDifferential]
  rw [fderiv_add (hH.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p) (hG.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)]
  simp only [ContinuousLinearMap.add_comp,map_add,neg_add]

def reparamHamiltonian (H : ℝ × E → ℝ) (a : ℝ → ℝ) (p : ℝ × E) : ℝ :=
  deriv a p.1 * H (a p.1,p.2)

theorem reparamHamiltonian_smooth {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H)
    {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (reparamHamiltonian H a) :=
  (((contDiff_infty_iff_deriv.mp ha).2).comp contDiff_fst).mul
    (hH.comp ((ha.comp contDiff_fst).prodMk contDiff_snd))

omit [NormedSpace ℝ E] in
theorem reparamHamiltonian_compact {H : ℝ × E → ℝ} (hH : HasCompactSupport H)
    (a : ℝ → ℝ) (ha : HasCompactSupport (deriv a)) : HasCompactSupport (reparamHamiltonian H a) := by
  apply HasCompactSupport.intro (ha.prod (hH.image continuous_snd))
  rintro ⟨t,x⟩ hp
  by_contra hn
  have ht : deriv a t ≠ 0 := by intro hz; apply hn; simp [reparamHamiltonian,hz]
  have hx : H (a t,x) ≠ 0 := by intro hz; apply hn; simp [reparamHamiltonian,hz]
  exact hp ⟨subset_closure ht,⟨(a t,x),subset_closure hx,rfl⟩⟩

theorem hamiltonianField_reparam (A : E →L[ℝ] E →L[ℝ] ℝ)
    {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (t : ℝ) (x : E) :
    hamiltonianField A (reparamHamiltonian H a) (t,x) =
      deriv a t • hamiltonianField A H (a t,x) := by
  have hda := (ha.differentiable (by simp) t).hasFDerivAt.comp (t,x)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (t,x)))
  have hdd := (((contDiff_infty_iff_deriv.mp ha).2).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t).hasFDerivAt.comp (t,x)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (t,x)))
  have hi := hda.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := (t,x)))
  have hd := hdd.mul ((hH.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (a t,x)).hasFDerivAt.comp (t,x) hi)
  change HasFDerivAt (fun p : ℝ × E => deriv a p.1 * H (a p.1,p.2)) _ (t,x) at hd
  have he : spatialDifferential (reparamHamiltonian H a) (t,x) =
      deriv a t • spatialDifferential H (a t,x) := by
    ext v
    unfold spatialDifferential reparamHamiltonian
    rw [hd.fderiv]
    simp
  simp only [hamiltonianField,formMoserField,he,map_smul,smul_neg]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_DisjointClocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function

def firstClock (t : ℝ) : ℝ := Real.smoothTransition (3*t)
def secondClock (t : ℝ) : ℝ := Real.smoothTransition (3*t-2)

@[fun_prop] theorem firstClock_smooth : ContDiff ℝ ∞ firstClock := by
  exact Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)
@[fun_prop] theorem secondClock_smooth : ContDiff ℝ ∞ secondClock := by
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

@[simp] theorem firstClock_zero : firstClock 0 = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (by norm_num)
@[simp] theorem secondClock_zero : secondClock 0 = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (by norm_num)
@[simp] theorem firstClock_one : firstClock 1 = 1 := by
  exact Real.smoothTransition.one_of_one_le (by norm_num)
@[simp] theorem secondClock_one : secondClock 1 = 1 := by
  exact Real.smoothTransition.one_of_one_le (by norm_num)

theorem secondClock_locally_zero {t : ℝ} (ht : t < 2/3) :
    secondClock =ᶠ[𝓝 t] fun _ => 0 := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  change s < 2/3 at hs
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

theorem firstClock_locally_one {t : ℝ} (ht : 1/3 < t) :
    firstClock =ᶠ[𝓝 t] fun _ => 1 := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  change 1/3 < s at hs
  exact Real.smoothTransition.one_of_one_le (by linarith)

theorem secondClock_deriv_zero {t : ℝ} (ht : t < 2/3) : deriv secondClock t = 0 :=
  ((hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq (secondClock_locally_zero ht)).deriv

theorem firstClock_deriv_zero {t : ℝ} (ht : 1/3 < t) : deriv firstClock t = 0 :=
  ((hasDerivAt_const t (1:ℝ)).congr_of_eventuallyEq (firstClock_locally_one ht)).deriv

theorem firstClock_deriv_compact : HasCompactSupport (deriv firstClock) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := 1))
  intro t ht
  have hor : t < 0 ∨ 1 < t := by simpa only [mem_Icc,not_and_or,not_le] using ht
  rcases hor with ht | ht
  · have he : firstClock =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      change s < 0 at hs
      exact Real.smoothTransition.zero_of_nonpos (by linarith)
    exact ((hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq he).deriv
  · exact firstClock_deriv_zero (by linarith)

theorem secondClock_deriv_compact : HasCompactSupport (deriv secondClock) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := 1))
  intro t ht
  have hor : t < 0 ∨ 1 < t := by simpa only [mem_Icc,not_and_or,not_le] using ht
  rcases hor with ht | ht
  · exact secondClock_deriv_zero (by linarith)
  · have he : secondClock =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      change 1 < s at hs
      exact Real.smoothTransition.one_of_one_le (by linarith)
    exact ((hasDerivAt_const t (1:ℝ)).congr_of_eventuallyEq he).deriv

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
open DiagonalQuadrics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def complexBlocks (s : ι → ℂ) (z : ι → κ → ℂ) : ι × κ → ℂ := fun ij => s ij.1*z ij.1 ij.2

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

abbrev DiskPair := ℂ × ℂ

def squaredRadii (z : DiskPair) : Plane := (Complex.normSq z.1,Complex.normSq z.2)

def diskDomain (A B : ℝ) : Set DiskPair :=
  {z | (squaredRadii z).1<A ∧ (squaredRadii z).1+(squaredRadii z).2<B}

def diskForward (k : ι → ℕ × ℕ) (a : ι → ℝ) (z : DiskPair) : DiskPair :=
  (Real.sqrt (slope k a (squaredRadii z)).1 • z.1,
   Real.sqrt (slope k a (squaredRadii z)).2 • z.2)

def diskInverse (k : ι → ℕ × ℕ) (a : ι → ℝ) (z : DiskPair) : DiskPair :=
  ((Real.sqrt (slope k a (nonnegativeInverse k a (squaredRadii z))).1)⁻¹ • z.1,
   (Real.sqrt (slope k a (nonnegativeInverse k a (squaredRadii z))).2)⁻¹ • z.2)

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.Hamiltonian
open scoped BigOperators ContDiff ComplexConjugate
open DiagonalQuadrics FiniteMoment.Radial

def complexMonomial (k : ℕ × ℕ) (z : DiskPair) : ℂ := z.1^k.1*z.2^k.2

section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def toricLift (k : ι → ℕ × ℕ) (G : ι → κ → ℂ) (z : DiskPair) : ι × κ → ℂ :=
  complexBlocks (fun i => complexMonomial (k i) z) G

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_CubicToricAmbient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

abbrev CubicConeTarget := PlaneBase × DiskPair
abbrev CubicAmbient := PlaneBase × ℂ

 def cubicNormalCoordinates (t : ℝ) (p : CubicAmbient) : CubicConeTarget :=
  (p.1,(p.2,t⁻¹ • polynomial p.1))

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_CompactDegenerationTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 def cubicAffineDomain : Set CubicAmbient := {p | p.1.1≠0 ∧ p.1.2≠0}

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_SixLargeCubicPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope
open MvPolynomial
open FiniteMoment.Radial

 def quadricParam (u v w : ℂ) : Fin 4 → ℂ := ![v*w,u^2,u*v,u*w]
 def liftAlpha (n J K : ℕ) := J+K-n
 def liftBeta (n J K : ℕ) := n+liftAlpha n J K-(J+K)
 def liftGamma (n J K : ℕ) := J-liftAlpha n J K
 def liftDelta (n J K : ℕ) := K-liftAlpha n J K

 def quadricLiftMonomial (n J K : ℕ) (x : Fin 4 → ℂ) :=
  x 0^liftAlpha n J K*x 1^liftBeta n J K*x 2^liftGamma n J K*x 3^liftDelta n J K

 def quadricLiftPolynomial (n : ℕ) (q : MvPolynomial (Fin 2) ℂ) (x : Fin 4 → ℂ) : ℂ :=
  ∑ d∈q.support,q.coeff d*quadricLiftMonomial n (d 0) (d 1) x

 def planeCubicPolynomial : MvPolynomial (Fin 2) ℂ :=
  X 0^2*X 1+C (-1)*(X 0*X 1^2)+X 1+C (-2)*X 0

 def coefficientPowers (D m : ℕ) : WeightedHomogeneousIndex → ℕ × ℕ
  | none => (0,0)
  | some none => (D-m,0)
  | some (some j) => ![(0,D-m),(D-m,m),(m,D-m)] j

 def coefficientPolynomial (D m : ℕ) (i : WeightedHomogeneousIndex) : MvPolynomial (Fin 2) ℂ :=
  X 0^(coefficientPowers D m i).1*X 1^(coefficientPowers D m i).2

 def cubicNormalSection (D m k : ℕ) (i : WeightedHomogeneousIndex) : MvPolynomial (Fin 2) ℂ :=
  planeCubicPolynomial^k*coefficientPolynomial D m i

 def firstQuadric (x : Fin 4 → ℂ) : ℂ := x 0*x 1-x 2*x 3

 def liftedSection {A B : ℕ} (L S : ℕ) (k : TrapezoidWeight A B)
    (i : WeightedHomogeneousIndex) (x : Fin 4 → ℂ) : ℂ :=
  firstQuadric x^(latticeIndex k).1 *
    quadricLiftPolynomial (L-2*(latticeIndex k).1)
      (cubicNormalSection (cubicDegree (L+S) k) (cubicMarkedOrder S k) (latticeIndex k).2 i) x

 def firstQuadricChart (p : CubicAmbient) : Fin 4 → ℂ := ![p.2,1,p.1.1,p.1.2]

 def outerTube (δ : ℝ) (p : CubicAmbient) : CubicAmbient :=
  (p.1,p.1.1*p.1.2+(δ:ℂ)*p.2)

 def outerPolynomial {A B : ℕ} (L S : ℕ) (t δ : ℝ) (x : Fin 4 → ℂ) :
    TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ :=
  fun ki => (δ:ℂ)⁻¹^(latticeIndex ki.1).1*(t:ℂ)⁻¹^(latticeIndex ki.1).2 *
    liftedSection L S ki.1 ki.2 x

 def outerConePolynomial {A B : ℕ} (L S : ℕ) (t : ℝ) (p : ℝ × CubicAmbient) :
    TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ :=
  fun ki => p.2.2^(latticeIndex ki.1).1*(t:ℂ)⁻¹^(latticeIndex ki.1).2 *
    quadricLiftPolynomial (L-2*(latticeIndex ki.1).1)
      (cubicNormalSection (cubicDegree (L+S) ki.1) (cubicMarkedOrder S ki.1) (latticeIndex ki.1).2 ki.2)
      (firstQuadricChart (outerTube p.1 p.2))

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_SixLargeQuadricPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped BigOperators

variable {ι : Type} [Fintype ι]

 def homogeneousVeronese (m : ℕ) (z : ι → ℂ) : (Fin m → ι) → ℂ :=
  fun j => ∏ i,z (j i)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_AffineHopfRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators

variable {ι : Type} [Fintype ι]

 def bubbleCoordinates (ε : ℂ) (x : Option ι → ℂ) : Option ι → ℂ
  | none => ε*x none
  | some i => x (some i)

 def homogeneousBubble (L m p : ℕ) (ε : ℂ) (x : Option ι → ℂ) : (Fin m → Option ι) → ℂ :=
  fun j => ε^(p-m)*x none^(L-m)*homogeneousVeronese m (bubbleCoordinates ε x) j

variable {κ : Type} [Fintype κ]
 def bubblePolynomial (L m p N : ℕ) (P : (Option ι → ℂ) → (κ → ℂ))
    (ε : ℂ) (x : Option ι → ℂ) : (κ ⊕ ((Fin m → Option ι) ⊕ (Fin L → Option ι))) → ℂ :=
  Sum.elim (P x) (Sum.elim (homogeneousBubble L m p ε x) (fun j => ε^N*homogeneousVeronese L x j))

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff BigOperators
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 def distinguishedChart (ε : ℂ) (z : Fin 3 → ℂ) : Fin 4 → ℂ :=
  ![1,ε*z 0,ε*z 1,ε*z 2]

 def distinguishedResidualTerm (p n k J K : ℕ) (ε : ℂ) (z : Fin 3 → ℂ) : ℂ :=
  ε^(k+liftBeta n J K+liftGamma n J K+liftDelta n J K-p)*
    (z 0-ε*z 1*z 2)^k*z 0^liftBeta n J K*z 1^liftGamma n J K*z 2^liftDelta n J K

 def distinguishedResidualPolynomial {A B : ℕ} (p L S : ℕ) (t δ : ℝ)
    (ε : ℂ) (z : Fin 3 → ℂ) : TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ :=
  fun ki => (δ:ℂ)⁻¹^(latticeIndex ki.1).1*(t:ℂ)⁻¹^(latticeIndex ki.1).2 *
    ∑ d∈(cubicNormalSection (cubicDegree (L+S) ki.1) (cubicMarkedOrder S ki.1) (latticeIndex ki.1).2 ki.2).support,
      (cubicNormalSection (cubicDegree (L+S) ki.1) (cubicMarkedOrder S ki.1) (latticeIndex ki.1).2 ki.2).coeff d *
        distinguishedResidualTerm p (L-2*(latticeIndex ki.1).1) (latticeIndex ki.1).1 (d 0) (d 1) ε z

 def distinguishedHomogeneousCoordinates (x : Option (Fin 3) → ℂ) : Fin 4 → ℂ :=
   ![x none,x (some 0),x (some 1),x (some 2)]

 def cubicBubblePolynomial {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ) (ε : ℂ) :=
   bubblePolynomial L m p N
     (outerPolynomial (A := A) (B := B) L S t δ ∘ distinguishedHomogeneousCoordinates) ε

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_SphereCartesianDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 def firstBubbleLift (z : CubicAmbient) : Option (Fin 3) → ℂ
   | none => z.2
   | some i => ![1,z.1.1,z.1.2] i

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_SixCubicInnerNormalPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope
open FiniteMoment.Radial

 def firstToDistinguished (z : CubicAmbient) : Fin 3 → ℂ :=
   ![z.2⁻¹,z.1.1/z.2,z.1.2/z.2]

 def distinguishedToFirst (z : Fin 3 → ℂ) : CubicAmbient :=
   ((z 1/z 0,z 2/z 0),(z 0)⁻¹)

 theorem firstToDistinguished_smoothAt {z : CubicAmbient} (hz : z.2≠0) :
     ContDiffAt ℝ ∞ firstToDistinguished z := by
   have hC : ContDiffAt ℂ ∞ firstToDistinguished z := by
     apply contDiffAt_pi.mpr
     intro i
     fin_cases i
     · exact contDiffAt_snd.inv hz
     · exact contDiffAt_fst.fst.div contDiffAt_snd hz
     · exact contDiffAt_fst.snd.div contDiffAt_snd hz
   exact hC.restrict_scalars ℝ

 theorem distinguishedToFirst_smoothAt {z : Fin 3 → ℂ} (hz : z 0≠0) :
     ContDiffAt ℝ ∞ distinguishedToFirst z := by
   have h (i : Fin 3) : ContDiffAt ℂ ∞ (fun y : Fin 3 → ℂ => y i) z :=
     (contDiff_apply ℂ ℂ i).contDiffAt
   have hC : ContDiffAt ℂ ∞ distinguishedToFirst z :=
     ((h 1 |>.div (h 0) hz).prodMk (h 2 |>.div (h 0) hz)).prodMk ((h 0).inv hz)
   exact hC.restrict_scalars ℝ

 theorem distinguishedToFirst_first {z : CubicAmbient} (hz : z.2≠0) :
     distinguishedToFirst (firstToDistinguished z)=z := by
   rcases z with ⟨⟨u,v⟩,w⟩
   change ((u/w/w⁻¹,v/w/w⁻¹),w⁻¹⁻¹)=((u,v),w)
   simp [div_inv_eq_mul,hz]

 theorem firstToDistinguished_first {z : Fin 3 → ℂ} (hz : z 0≠0) :
     firstToDistinguished (distinguishedToFirst z)=z := by
   ext i
   fin_cases i <;> simp [firstToDistinguished,distinguishedToFirst,div_inv_eq_mul,hz]

 def firstDistinguishedHomeomorph :
     {z : CubicAmbient // z.2≠0} ≃ₜ {z : Fin 3 → ℂ // z 0≠0} where
   toFun z := ⟨firstToDistinguished z.val,inv_ne_zero z.property⟩
   invFun z := ⟨distinguishedToFirst z.val,inv_ne_zero z.property⟩
   left_inv z := Subtype.ext (distinguishedToFirst_first z.property)
   right_inv z := Subtype.ext (firstToDistinguished_first z.property)
   continuous_toFun := by
     apply Continuous.subtype_mk
     apply continuous_iff_continuousAt.mpr
     intro z
     exact (firstToDistinguished_smoothAt z.property).continuousAt.comp continuous_subtype_val.continuousAt
   continuous_invFun := by
     apply Continuous.subtype_mk
     apply continuous_iff_continuousAt.mpr
     intro z
     exact (distinguishedToFirst_smoothAt z.property).continuousAt.comp continuous_subtype_val.continuousAt

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_LiouvilleRadialCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open Hamiltonian MomentPolytope

 def largeNormalCoefficient (q : ℕ) (p : Fin (q+1) → ℝ) : ℝ :=
  1-p 0-2*∑ j : Fin q,p j.succ

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_QuadricLargeAmbientPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Hamiltonian

variable {m : ℕ}

abbrev HomogeneousInput (m : ℕ) := Option (Option (Fin m)) → ℂ
abbrev HomogeneousOutput (m : ℕ) := Option (NormalPolynomialIndex m) → ℂ

def homogeneousPolynomial (a : Fin m → ℂ) (t : ℝ) (z : HomogeneousInput m) :
    HomogeneousOutput m
  | none => z none^2
  | some (.inl (.inl i)) => z none*z (some i.2)
  | some (.inl (.inr i)) => z (some i.1)*z (some i.2)
  | some (.inr j) => (t:ℂ)⁻¹*(z (some (some j))^2-z (some none)^2+a j*z none^2)

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff BigOperators
open Hamiltonian

variable {m : ℕ}

def homogeneousInfinityOutputSign : Option (NormalPolynomialIndex m) → ℂ
  | some (.inl (.inl _)) => -1
  | _ => 1

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_Adapted
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def radialSwitch (σ τ t : ℝ) : ℝ := Real.smoothTransition ((t-σ)/(τ-σ))

def radialOffset (σ τ t : ℝ) : ℝ := ∫ s in σ..t, radialSwitch σ τ s

def radialShift (σ τ : ℝ) : ℝ := 1 + radialOffset σ τ τ - τ

def radialCoefficient (σ τ t : ℝ) : ℝ := (1 + radialOffset σ τ t)⁻¹

def radialMoment (σ τ t : ℝ) : ℝ := t * radialCoefficient σ τ t

@[simp] theorem radialMoment_zero {σ τ : ℝ} : radialMoment σ τ 0 = 0 := by
  simp [radialMoment]



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_RadialForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def radialSlope (σ τ t : ℝ) : ℝ :=
  -radialSwitch σ τ t / (1 + radialOffset σ τ t)^2

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_CurveArea
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def oneForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : E → E →L[ℝ] ℝ) (x : E) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ 0 (α x)


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def blowupSize (σ τ : ℝ) : ℝ := τ - radialOffset σ τ τ

def blowupMoment (σ τ t : ℝ) : ℝ := blowupSize σ τ + radialOffset σ τ t

def blowupCoefficient (σ τ t : ℝ) : ℝ := blowupMoment σ τ t / t

def blowupSlope (σ τ t : ℝ) : ℝ :=
  (t * radialSwitch σ τ t - blowupMoment σ τ t) / t^2


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_Correction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def outerProfile (A t : ℝ) : ℝ :=
  Real.smoothTransition (t+2) * (1 - Real.smoothTransition ((t-A)/A))



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Campanato_MeasureEnergy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ}


def campRadius (k : ℕ) : ℝ := (1/2)*(1/4)^k



end HigherDimensionalBallPacking.Rigidity
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

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)
local instance pfrK : FiniteDimensional ℝ pkg.decDom.X₀ := pkg.decDom.finite_X₀
local instance pfrX : CompleteSpace pkg.decDom.X₁ := pkg.decDom.isTopCompl.isClosed.completeSpace_coe
local instance pfrY : CompleteSpace pkg.decCodom.X₁ := pkg.decCodom.isTopCompl.isClosed.completeSpace_coe

end

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

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

def splitKernelProjection (A : X →L[ℝ] Y) (R : Y →L[ℝ] X) : X →L[ℝ] X :=
  ContinuousLinearMap.id ℝ X-R.comp A


end
open scoped Topology
open Set Function Filter
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

def projectionTransport (P Q : X →L[ℝ] X) : X →L[ℝ] X :=
  Q*P+(1-Q)*(1-P)



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_ProjectionTimeGrid
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped Topology
open Set Function Filter
variable {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [MetricSpace Z]

def cappedTime (N j : ℕ) (t : ℝ) : ℝ := min t ((j:ℝ)/N)

def projectionTimeChain (P : ℝ × Z → X →L[ℝ] X) (N : ℕ) : ℕ → (ℝ × Z) → X →L[ℝ] X
  | 0,_ => 1
  | j+1,v => projectionTransport (P (cappedTime N j v.1,v.2))
      (P (cappedTime N (j+1) v.1,v.2))*projectionTimeChain P N j v


def cappedTimeMap (N j : ℕ) (v : ℝ × Z) : ℝ × Z := (cappedTime N j v.1,v.2)

def gridDomain (V : Set (ℝ × Z)) (N : ℕ) : Set (ℝ × Z) :=
  V ∩ (fun v : ℝ × Z => (0,v.2)) ⁻¹' V ∩ ⋂ j : Fin (N+1),cappedTimeMap N j.val ⁻¹' V

def extendedTimeTransport (P : ℝ × Z → X →L[ℝ] X) (N : ℕ) (v : ℝ × Z) : X →L[ℝ] X :=
  projectionTransport (P (cappedTimeMap N N v)) (P v)*projectionTimeChain P N N v*
    projectionTransport (P (0,v.2)) (P (cappedTimeMap N 0 v))


end
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

def initialKernelGraph (L : X ≃L[ℝ] Y) (E : Submodule ℝ Y) : E →L[ℝ] (X × E) :=
  (-(L.symm.toContinuousLinearMap.comp E.subtypeL)).prod (ContinuousLinearMap.id ℝ E)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma initialKernelGraph_apply [CompleteSpace X] [CompleteSpace Y]
    (L : X ≃L[ℝ] Y) (E : Submodule ℝ Y) (e : E) :
    initialKernelGraph L E e=(-L.symm (e:Y),e) := rfl

lemma initialKernelGraph_kernel {L : X ≃L[ℝ] Y} {E : Submodule ℝ Y} (v : X × E) :
    L v.1+(v.2:Y)=0 ↔ initialKernelGraph L E v.2=v := by
  constructor
  · intro hv
    rw [initialKernelGraph_apply]
    refine Prod.ext ?_ (rfl : (v.2:E)=v.2)
    change -L.symm (v.2:Y)=v.1
    apply L.injective
    rw [map_neg,L.apply_symm_apply]
    exact (eq_neg_of_add_eq_zero_left hv).symm
  · intro hv
    rw [←hv]
    simp only [initialKernelGraph_apply,map_neg,L.apply_symm_apply,neg_add_cancel]



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moduli_SmoothZeroCharts
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : ℝ × X → Y}

variable [CompleteSpace X] [CompleteSpace Y]
variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)
local instance szcY : CompleteSpace pkg.decCodom.X₁ := pkg.decCodom.isTopCompl.isClosed.completeSpace_coe


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_ProperPaths
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def freezeTime (t : ℝ) : ℝ := Real.smoothTransition (2*t-1/2)
def frozenPath (F : ℝ × X → Y) (v : ℝ × X) : Y := F (freezeTime v.1,v.2)

lemma freezeTime_initial {t : ℝ} (ht : t≤1/4) : freezeTime t=0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end


