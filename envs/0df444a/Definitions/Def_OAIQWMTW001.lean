-- Prove2me | Definitions.Def_OAIQWMTW001
-- name    : OAIQWMTW001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T03:06:18.890687+00:00
-- url     : https://prove2.me/theorems/36d25810-5d14-42c1-a552-2657c8f84ee0
-- title:
--   OpenAI weak MTW split: definitions bundle OAIQWMTW001
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWGlobalSupport.current_main_convexity`. That theorem says that on a compact connected Riemannian manifold of dimension at least two satisfying the weak Ma–Trudinger–Wang condition, every tangent injectivity domain is convex (Villani's conjecture in this setting).
--
--   The bundle holds OpenAI's Lean definitions, structures and predicates from the modules `Analysis_CurveComposition`, `Analysis_IntegralEquation`, `Analysis_SmoothFlow`, `Coordinates_ChartLength`, `Coordinates_ChartMetric`, `Coordinates_CoerciveMetric`, `Coordinates_CoordinateExistence`, `Coordinates_CoordinateGeometry`, `Coordinates_CoordinateLocal`, `Coordinates_EndpointAction`, `Coordinates_IntrinsicNormal`, `Coordinates_LocalDistance`, `Coordinates_NormalAction`, `Coordinates_NormalCoordinates`, `Coordinates_NormalCurve`, `Coordinates_NormalDifferential`, `Coordinates_NormalFlowLength`, `Coordinates_NormalLength`, `Coordinates_NormalMetricSpeed`, `Coordinates_NormalNeighborhood`, `Coordinates_NormalRigidity`, `Coordinates_RadialCoordinates`, `Coordinates_RadialLength`, `Coordinates_RadialRigidity`, `Geodesics_CompactGeodesic`, `Geodesics_GaussLemma`, `Geodesics_IntrinsicExistence`, `Geodesics_IntrinsicGlue`, `Geodesics_IntrinsicOn`, `Geodesics_IntrinsicUniqueness`, `Geodesics_LocalGeodesic`, `Geodesics_UniformNormal`, `Support_CompactHomotopyContinuation`, `Support_FiberHullCompact`, `Support_FirstCutSupport`, `Variations_BrokenActionCalculus`, `Variations_CovariantActionHessian`, `Variations_CurveCalculus`, `Variations_FlowLinearization` of `lean/OAI/Geometry/WeakMTW` (OpenAI, *Global Support and Convex Injectivity Domains under Weak MTW*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0). They are ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas their bodies use. It also imports the bundle `OAIQWMTW000` of this split.
--
--   Among its definitions:
--   - integral operators on paths and the normal flow used for coordinate geodesics (`pointwiseLinear`, `pointwiseOperator`, `integralOperator`, `NormalFlow`, `normalShear`, `normalChart`);
--   - curve states, length and action (`curveState`, `coordinateLength`, `action`, `endpointAction`, `brokenAction`);
--   - intrinsic geodesics, defined metrically (`IsIntrinsicGeodesicOn`, `IsIntrinsicGeodesicAt`);
--   - the index form along a geodesic (`integrand`, `indexForm`) and the action form (`actionForm`);
--   - fibres, fibre hulls, collision exclusion and trial poles of the paper's Sections 3 and 4 (`fiber`, `fiberHull`, `CollisionExclusionAt`, `HasTrialPole`).
--
--   Some lemmas these definitions need use the Gauss lemma. Here the lemma `flow_gauss` is a short bridge from the published standalone statement `OAI.WeakMTWGlobalSupport.GaussLemma.gauss_lemma`, which the bundle imports. So that statement, and its proof, must be live before this bundle is published.
--
--   The theorems the definitions do not need are proved in the solutions of this split. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/WeakMTW at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWMTW000
import Theorems.Thm_OAI_WeakMTWGlobalSupport_GaussLemma_gauss_lemma

section
-- module Solutions.OAIQW_WeakMTW.Analysis_CurveComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff

namespace SmoothCurveComposition

noncomputable section

universe u v
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pointwiseLinear (A : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := fun h => ⟨fun t => A t (h t), A.continuous.clm_apply h.continuous⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
    ‖A‖ (by
      intro h
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg h))).2
      intro t
      exact (A t).le_opNorm (h t) |>.trans
        (mul_le_mul (A.norm_coe_le_norm t) (h.norm_coe_le_norm t)
          (norm_nonneg _) (norm_nonneg _)))

@[simp] theorem pointwiseLinear_apply (A : C(K, E →L[ℝ] F)) (h : C(K, E)) (t : K) :
    pointwiseLinear A h t = A t (h t) := rfl

def pointwiseOperator : C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
  LinearMap.mkContinuous
    { toFun := fun A : C(K, E →L[ℝ] F) => pointwiseLinear A
      map_add' := by intros; ext h t; simp
      map_smul' := by intros; ext h t; simp }
    1 (by
      intro A
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
      intro h
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg h))).2
      intro t
      exact (A t).le_opNorm (h t) |>.trans
        (mul_le_mul (A.norm_coe_le_norm t) (h.norm_coe_le_norm t)
          (norm_nonneg _) (norm_nonneg _)))

@[simp] theorem pointwiseOperator_apply (A : C(K, E →L[ℝ] F)) :
    pointwiseOperator A = pointwiseLinear A := rfl

variable [FiniteDimensional ℝ E]

theorem hasFDerivAt_postcomp {f : E → F} (hf : ContDiff ℝ 1 f) (u : C(K, E)) :
    HasFDerivAt (ContinuousMap.comp ⟨f, hf.continuous⟩)
      (pointwiseLinear (ContinuousMap.comp ⟨fderiv ℝ f,
        hf.continuous_fderiv (by norm_num)⟩ u)) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have huc := (isCompact_closedBall (0 : E) (‖u‖ + 1)).uniformContinuousOn_of_continuous
    (hf.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro h hh
  have hhn : ‖h‖ < min δ 1 := by simpa using hh
  have hhδ : ‖h‖ < δ := lt_of_lt_of_le hhn (min_le_left _ _)
  have hh1 : ‖h‖ < 1 := lt_of_lt_of_le hhn (min_le_right _ _)
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).2
  intro t
  have hut : u t ∈ Metric.closedBall (0 : E) (‖u‖ + 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith [u.norm_coe_le_norm t]
  have huht : u t + h t ∈ Metric.closedBall (0 : E) (‖u‖ + 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖u t + h t‖ ≤ ‖u t‖ + ‖h t‖ := norm_add_le _ _
      _ ≤ ‖u‖ + ‖h‖ := add_le_add (u.norm_coe_le_norm t) (h.norm_coe_le_norm t)
      _ ≤ ‖u‖ + 1 := by linarith
  have hd : ∀ z ∈ segment ℝ (u t) (u t + h t),
      HasFDerivWithinAt (fun z => f z - (fderiv ℝ f (u t)) z)
        (fderiv ℝ f z - fderiv ℝ f (u t)) (segment ℝ (u t) (u t + h t)) z := by
    intro z hz
    exact ((hf.differentiable (by norm_num) z).hasFDerivAt.sub
      (fderiv ℝ f (u t)).hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ z ∈ segment ℝ (u t) (u t + h t),
      ‖fderiv ℝ f z - fderiv ℝ f (u t)‖ ≤ ε := by
    intro z hz
    have hzb := (convex_closedBall (0 : E) (‖u‖ + 1)).segment_subset hut huht hz
    have hzd : dist z (u t) < δ := by
      rw [dist_eq_norm]
      calc
        ‖z - u t‖ ≤ ‖u t + h t - u t‖ := norm_sub_le_of_mem_segment hz
        _ = ‖h t‖ := by simp
        _ ≤ ‖h‖ := h.norm_coe_le_norm t
        _ < δ := hhδ
    simpa only [dist_eq_norm] using (hδf z hzb (u t) hut hzd).le
  have hm := (convex_segment (u t) (u t + h t)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd hb (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  have heq : (f (u t + h t) - (fderiv ℝ f (u t)) (u t + h t)) -
      (f (u t) - (fderiv ℝ f (u t)) (u t)) =
      f (u t + h t) - f (u t) - (fderiv ℝ f (u t)) (h t) := by
    rw [map_add]; abel
  rw [heq, add_sub_cancel_left] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left (h.norm_coe_le_norm t) hε.le)

theorem contDiff_postcomp_nat (n : ℕ) {f : E → F} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (ContinuousMap.comp (α := K) ⟨f, hf.continuous⟩) := by
  induction n generalizing F with
  | zero =>
      exact contDiff_zero.mpr (ContinuousMap.continuous_postcomp _)
  | succ n ih =>
      simp only [Nat.cast_add, Nat.cast_one] at hf ⊢
      refine contDiff_succ_iff_hasFDerivAt.mpr ⟨fun u =>
        pointwiseOperator (ContinuousMap.comp ⟨fderiv ℝ f,
          hf.continuous_fderiv (by positivity)⟩ u), ?_, ?_⟩
      · exact pointwiseOperator.contDiff.comp
          (ih ((contDiff_succ_iff_fderiv.mp hf).2.2))
      · intro u
        exact hasFDerivAt_postcomp (hf.of_le (by exact le_add_of_nonneg_left (by positivity))) u

theorem contDiff_postcomp {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (ContinuousMap.comp (α := K) ⟨f, hf.continuous⟩) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_postcomp_nat n ((contDiff_infty.mp hf) n)

end

end SmoothCurveComposition

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Analysis_IntegralEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
namespace SmoothODE

open Set Filter
open scoped Topology ContDiff unitInterval
noncomputable section

universe v
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

def integralOperator : C(I, E) →L[ℝ] C(I, E) :=
  LinearMap.mkContinuous
    { toFun := fun u =>
        ⟨fun t => ∫ s in (0 : ℝ)..(t : ℝ), u (projIcc 0 1 zero_le_one s),
          (intervalIntegral.continuous_primitive
            (fun a b => (u.continuous.comp continuous_projIcc).intervalIntegrable a b) 0).comp
            continuous_subtype_val⟩
      map_add' := by
        intro u v; ext t
        exact intervalIntegral.integral_add
          ((u.continuous.comp continuous_projIcc).intervalIntegrable _ _)
          ((v.continuous.comp continuous_projIcc).intervalIntegrable _ _)
      map_smul' := by
        intro a u; ext t
        exact intervalIntegral.integral_smul a _ }
    1 (by
      intro u
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg u)).2
      intro t
      calc
        ‖∫ s in (0 : ℝ)..(t : ℝ), u (projIcc 0 1 zero_le_one s)‖ ≤ ‖u‖ * |(t : ℝ) - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => u.norm_coe_le_norm _)
        _ ≤ ‖u‖ * 1 := by
          gcongr
          simpa only [sub_zero, abs_of_nonneg t.2.1] using t.2.2
        _ = ‖u‖ := mul_one _)

@[simp] theorem integralOperator_apply (u : C(I, E)) (t : I) :
    integralOperator u t = ∫ s in (0 : ℝ)..(t : ℝ), u (projIcc 0 1 zero_le_one s) := rfl

@[simp] theorem integralOperator_zero (u : C(I, E)) : integralOperator u 0 = 0 := by
  simp

section Inverse
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace E]

theorem exists_smooth_local_inverse {f : E → F} (hf : ContDiff ℝ ∞ f)
    {a : E} {e : E ≃L[ℝ] F} (he : HasFDerivAt f (e : E →L[ℝ] F) a) :
    ∃ (g : F → E) (V : Set F), IsOpen V ∧ f a ∈ V ∧
      g (f a) = a ∧ ContDiffOn ℝ ∞ g V ∧ ∀ y ∈ V, f (g y) = y := by
  let P := hf.contDiffAt.toOpenPartialHomeomorph f he (by simp)
  have hP : (P : E → F) = f := rfl
  have ha : a ∈ P.source := hf.contDiffAt.mem_toOpenPartialHomeomorph_source he (by simp)
  let U : Set E := (fderiv ℝ f) ⁻¹' Set.range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F)
  have hU : IsOpen U := ContinuousLinearEquiv.isOpen.preimage (hf.continuous_fderiv (by simp))
  have haU : a ∈ U := ⟨e, he.fderiv.symm⟩
  let V := P.target ∩ P.symm ⁻¹' U
  have hV : IsOpen V := P.isOpen_inter_preimage_symm hU
  have hfa : f a ∈ V := by
    refine ⟨P.map_source ha, ?_⟩
    change P.symm (f a) ∈ U
    rw [← hP, P.left_inv ha]
    exact haU
  refine ⟨P.symm, V, hV, hfa, ?_, ?_, ?_⟩
  · exact P.left_inv ha
  · intro y hy
    obtain ⟨e', he'⟩ := hy.2
    apply ContDiffAt.contDiffWithinAt
    apply P.contDiffAt_symm hy.1 (f₀' := e')
    · rw [hP, he']
      exact (hf.differentiable (by simp) _).hasFDerivAt
    · rw [hP]
      exact hf.contDiffAt
  · intro y hy
    exact P.right_inv hy.1

end Inverse

def subtractShear (b : E) : (ℝ × E) ≃L[ℝ] (ℝ × E) where
  toFun z := (z.1, z.2 - z.1 • b)
  invFun z := (z.1, z.2 + z.1 • b)
  map_add' := by
    intro z w; ext <;> simp [add_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  map_smul' := by
    intro c z; ext <;> simp [smul_sub, mul_smul]
  left_inv := by intro z; ext <;> simp
  right_inv := by intro z; ext <;> simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.sub (continuous_fst.smul continuous_const))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.add (continuous_fst.smul continuous_const))

@[simp] theorem subtractShear_apply (b : E) (z : ℝ × E) :
    subtractShear b z = (z.1, z.2 - z.1 • b) := rfl

variable [FiniteDimensional ℝ E]

theorem exists_smooth_integral_curves {f : E → E} (hf : ContDiff ℝ ∞ f) (x₀ : E) :
    ∃ (U : Set (ℝ × E)) (Ψ : ℝ × E → C(I, E)),
      IsOpen U ∧ (0, x₀) ∈ U ∧ ContDiffOn ℝ ∞ Ψ U ∧
      Ψ (0, x₀) = ContinuousMap.const I x₀ ∧
      ∀ q ∈ U, Ψ q = ContinuousMap.const I q.2 +
        q.1 • integralOperator (ContinuousMap.comp ⟨f, hf.continuous⟩ (Ψ q)) := by
  let B : C(I, E) → C(I, E) := fun u =>
    integralOperator (ContinuousMap.comp ⟨f, hf.continuous⟩ u)
  have hB : ContDiff ℝ ∞ B :=
    integralOperator.contDiff.comp (SmoothCurveComposition.contDiff_postcomp hf)
  let H : ℝ × C(I, E) → ℝ × C(I, E) := fun z => (z.1, z.2 - z.1 • B z.2)
  have hH : ContDiff ℝ ∞ H :=
    contDiff_fst.prodMk (contDiff_snd.sub (contDiff_fst.smul (hB.comp contDiff_snd)))
  let u₀ : C(I, E) := ContinuousMap.const I x₀
  have hHd : HasFDerivAt H (subtractShear (B u₀) : (ℝ × C(I, E)) →L[ℝ] (ℝ × C(I, E)))
      (0, u₀) := by
    have hdB : HasFDerivAt (fun z : ℝ × C(I, E) => B z.2)
        ((fderiv ℝ B u₀).comp (ContinuousLinearMap.snd ℝ ℝ C(I, E))) (0, u₀) :=
      HasFDerivAt.comp (f := Prod.snd) (g := B) (0, u₀)
        (hB.differentiable (by simp) u₀).hasFDerivAt hasFDerivAt_snd
    have hd := hasFDerivAt_fst.prodMk (hasFDerivAt_snd.sub
      (hasFDerivAt_fst.smul hdB))
    convert! hd using 1
    ext z <;> simp [subtractShear]
  obtain ⟨g, V, hVo, hVmem, hg0, hg, hgr⟩ := exists_smooth_local_inverse hH hHd
  have hH0 : H (0, u₀) = (0, u₀) := by simp [H]
  rw [hH0] at hVmem hg0
  let J : ℝ × E → ℝ × C(I, E) := fun q => (q.1, ContinuousMap.const I q.2)
  have hJ : ContDiff ℝ ∞ J :=
    contDiff_fst.prodMk ((ContinuousLinearMap.const ℝ I : E →L[ℝ] C(I, E)).contDiff.comp contDiff_snd)
  refine ⟨J ⁻¹' V, fun q => (g (J q)).2, hVo.preimage hJ.continuous, hVmem, ?_, ?_, ?_⟩
  · exact (hg.comp hJ.contDiffOn (fun q hq => hq)).snd
  · exact congrArg Prod.snd hg0
  · intro q hq
    have he := hgr (J q) hq
    have he1 : (g (J q)).1 = q.1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    change (g (J q)).2 - (g (J q)).1 • B (g (J q)).2 = ContinuousMap.const I q.2 at he2
    rw [he1] at he2
    exact sub_eq_iff_eq_add.mp he2

omit [FiniteDimensional ℝ E] in
theorem integral_curve_initial {f : C(E, E)} {q : ℝ × E} {u : C(I, E)}
    (hu : u = ContinuousMap.const I q.2 + q.1 • integralOperator (f.comp u)) :
    u 0 = q.2 := by
  have h := congrArg (fun v : C(I, E) => v 0) hu
  simpa using h

theorem integral_curve_derivative {f : C(E, E)} {q : ℝ × E} {u : C(I, E)}
    (hu : u = ContinuousMap.const I q.2 + q.1 • integralOperator (f.comp u))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s => u (projIcc 0 1 zero_le_one s))
      (q.1 • f (u ⟨t, ht⟩)) (Icc (0 : ℝ) 1) t := by
  let v : ℝ → E := fun s => f (u (projIcc 0 1 zero_le_one s))
  have hv : Continuous v := f.continuous.comp (u.continuous.comp continuous_projIcc)
  have hd := ((intervalIntegral.integral_hasDerivAt_right
    (hv.intervalIntegrable 0 t) (hv.stronglyMeasurableAtFilter _ _) hv.continuousAt).const_smul q.1).const_add q.2
  have heq : ∀ s ∈ Icc (0 : ℝ) 1, u (projIcc 0 1 zero_le_one s) =
      q.2 + q.1 • ∫ r in (0 : ℝ)..s, v r := by
    intro s hs
    have h := congrArg (fun w : C(I, E) => w ⟨s, hs⟩) hu
    simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply,
      ContinuousMap.smul_apply, integralOperator_apply, ContinuousMap.comp_apply,
      projIcc_of_mem zero_le_one hs] using h
  have hd' := hd.hasDerivWithinAt.congr_of_mem heq ht
  simpa only [v, projIcc_of_mem zero_le_one ht] using hd'

theorem exists_smooth_extension {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S : Set E} (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S)
    {a : E} (ha : a ∈ S) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 a] f := by
  obtain ⟨d, hd, hds⟩ := Euclidean.nhds_basis_closedBall.mem_iff.mp (hS.mem_nhds ha)
  let b : ContDiffBump (toEuclidean a) :=
    { rIn := d / 2, rOut := d, rIn_pos := half_pos hd,
      rIn_lt_rOut := half_lt_self hd }
  let β : E → ℝ := b ∘ toEuclidean
  have hβ : ContDiff ℝ ∞ β := b.contDiff.comp (ContinuousLinearEquiv.contDiff _)
  have hsupp : tsupport β ⊆ S := by
    apply subset_trans _ hds
    rw [tsupport, ← Euclidean.closure_ball _ hd.ne']
    apply closure_mono
    intro y hy
    have hby : toEuclidean y ∈ Function.support b := hy
    rwa [b.support_eq] at hby
  have heq : β =ᶠ[𝓝 a] 1 :=
    b.eventuallyEq_one.comp_tendsto (toEuclidean.continuous.tendsto a)
  refine ⟨fun x => β x • f x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport β
    · exact hβ.contDiffAt.smul ((hf x (hsupp hx)).contDiffAt (hS.mem_nhds (hsupp hx)))
    · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [hy, Pi.zero_apply, zero_smul]
  · filter_upwards [heq] with x hx
    simp only [hx, Pi.one_apply, one_smul]

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_endpoint {U : Set (ℝ × E)} {Ψ : ℝ × E → C(I, E)}
    (hΨ : ContDiffOn ℝ ∞ Ψ U) : ContDiffOn ℝ ∞ (fun q => Ψ q 1) U :=
  (ContinuousMap.evalCLM ℝ (1 : I) : C(I, E) →L[ℝ] E).contDiff.comp_contDiffOn hΨ

end
end SmoothODE

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Analysis_SmoothFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
namespace SmoothFlow

open Set Filter
open scoped Topology ContDiff unitInterval
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem unique_Icc {f : E → E} (hf : ContDiff ℝ 1 f) {u v : ℝ → E} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ t ∈ Icc a b, HasDerivWithinAt u (f (u t)) (Icc a b) t)
    (hdv : ∀ t ∈ Icc a b, HasDerivWithinAt v (f (v t)) (Icc a b) t)
    (h0 : u a = v a) : EqOn u v (Icc a b) := by
  let S := u '' Icc a b ∪ v '' Icc a b
  have hS : IsCompact S := (isCompact_Icc.image_of_continuousOn hu).union
    (isCompact_Icc.image_of_continuousOn hv)
  obtain ⟨K, hK⟩ := hf.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hS
  exact ODE_solution_unique_of_mem_Icc_right (fun _ _ => hK) hu
    (fun t ht => (hdu t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => Or.inl (mem_image_of_mem _ (Ico_subset_Icc_self ht))) hv
    (fun t ht => (hdv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => Or.inr (mem_image_of_mem _ (Ico_subset_Icc_self ht))) h0

omit [FiniteDimensional ℝ E] in
theorem normalized_rescale {f : E → E} (hf : ContDiff ℝ ∞ f)
    {T s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {u v : C(I, E)}
    (hdu : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
      HasDerivWithinAt (fun r => u (projIcc 0 1 zero_le_one r)) (T • f (u ⟨t, ht⟩))
        (Icc (0 : ℝ) 1) t)
    (hdv : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
      HasDerivWithinAt (fun r => v (projIcc 0 1 zero_le_one r)) ((s * T) • f (v ⟨t, ht⟩))
        (Icc (0 : ℝ) 1) t)
    (h0 : u 0 = v 0) : ∀ t : I, u (projIcc 0 1 zero_le_one (s * (t : ℝ))) = v t := by
  have hst : MapsTo (fun t : ℝ => s * t) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ⟨mul_nonneg hs.1 ht.1, (mul_le_of_le_one_left ht.1 hs.2).trans ht.2⟩
  let U : ℝ → E := fun t => u (projIcc 0 1 zero_le_one (s * t))
  let V : ℝ → E := fun t => v (projIcc 0 1 zero_le_one t)
  have hU : Continuous U := u.continuous.comp (continuous_projIcc.comp (continuous_const.mul continuous_id))
  have hV : Continuous V := v.continuous.comp continuous_projIcc
  have hdU : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt U ((s * T) • f (U t)) (Icc (0 : ℝ) 1) t := by
    intro t ht
    have hd := (hdu (s * t) (hst ht)).scomp t ((hasDerivAt_id t).const_mul s).hasDerivWithinAt hst
    simpa [U, Function.comp_def, smul_smul, projIcc_of_mem zero_le_one (hst ht)] using hd
  have hdV : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt V ((s * T) • f (V t)) (Icc (0 : ℝ) 1) t := by
    intro t ht
    simpa [V, projIcc_of_mem zero_le_one ht] using hdv t ht
  have heq := unique_Icc ((hf.of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top)).const_smul (s * T)) hU.continuousOn hV.continuousOn hdU hdV
    (by simpa [U, V] using h0)
  intro t
  simpa [U, V, projIcc_of_mem zero_le_one (hst t.2), projIcc_of_mem zero_le_one t.2] using heq t.2

theorem endpoint_hasDerivAt_ne_zero {f : E → E} (hf : ContDiff ℝ ∞ f)
    {U : Set (ℝ × E)} {Ψ : ℝ × E → C(I, E)} (hU : IsOpen U)
    (hΨ : ContDiffOn ℝ ∞ Ψ U)
    (hsol : ∀ q ∈ U, Ψ q = ContinuousMap.const I q.2 +
      q.1 • SmoothODE.integralOperator (ContinuousMap.comp ⟨f, hf.continuous⟩ (Ψ q)))
    {T : ℝ} {x : E} (hTx : (T, x) ∈ U) (hT : T ≠ 0) :
    HasDerivAt (fun t => Ψ (t, x) 1) (f (Ψ (T, x) 1)) T := by
  let F : ℝ → E := fun t => Ψ (t, x) 1
  have hFc : ContDiffAt ℝ ∞ F T :=
    ((SmoothODE.contDiffOn_endpoint hΨ (T, x) hTx).contDiffAt (hU.mem_nhds hTx)).comp T
      (contDiffAt_id.prodMk contDiffAt_const)
  have hFd : DifferentiableAt ℝ F T := hFc.differentiableAt (by simp)
  have hdu := fun t ht => SmoothODE.integral_curve_derivative (hsol (T, x) hTx) (t := t) ht
  have heq : (fun s : ℝ => F (s * T)) =ᶠ[𝓝[Icc (0 : ℝ) 1] (1 : ℝ)]
      (fun s => Ψ (T, x) (projIcc 0 1 zero_le_one s)) := by
    have hnear : ∀ᶠ s in 𝓝 (1 : ℝ), (s * T, x) ∈ U := by
      have hc : Continuous (fun s : ℝ => (s * T, x)) := by fun_prop
      exact (hc.tendsto 1).eventually (by simpa using hU.mem_nhds hTx)
    filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with s hs hsx
    have hds := fun t ht => SmoothODE.integral_curve_derivative (hsol (s * T, x) hsx) (t := t) ht
    have hz : Ψ (T, x) 0 = Ψ (s * T, x) 0 :=
      (SmoothODE.integral_curve_initial (hsol _ hTx)).trans
        (SmoothODE.integral_curve_initial (hsol _ hsx)).symm
    simpa [F] using (normalized_rescale hf hs hdu hds hz (1 : I)).symm
  have hdcomp : HasDerivWithinAt (fun s : ℝ => F (s * T)) (T • deriv F T)
      (Icc (0 : ℝ) 1) 1 := by
    convert! (hFd.hasDerivAt.scomp_of_eq 1 ((hasDerivAt_id 1).mul_const T) (by simp)).hasDerivWithinAt using 1
    simp
  have hdright : HasDerivWithinAt (fun s => Ψ (T, x) (projIcc 0 1 zero_le_one s))
      (T • f (F T)) (Icc (0 : ℝ) 1) 1 := by
    simpa [F] using hdu 1 (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  have hUD : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) 1 :=
    uniqueDiffOn_Icc zero_lt_one 1 (by constructor <;> norm_num)
  have hsame : T • deriv F T = T • f (F T) :=
    ((hdcomp.congr_of_eventuallyEq heq.symm (by simp [F])).derivWithin hUD).symm.trans
      (hdright.derivWithin hUD)
  have hderiv : deriv F T = f (F T) := (smul_right_injective E hT) hsame
  simpa only [hderiv] using hFd.hasDerivAt

theorem endpoint_hasDerivAt_zero {f : E → E} (hf : ContDiff ℝ ∞ f)
    {U : Set (ℝ × E)} {Ψ : ℝ × E → C(I, E)} (hU : IsOpen U)
    (hΨ : ContDiffOn ℝ ∞ Ψ U)
    (hsol : ∀ q ∈ U, Ψ q = ContinuousMap.const I q.2 +
      q.1 • SmoothODE.integralOperator (ContinuousMap.comp ⟨f, hf.continuous⟩ (Ψ q)))
    {x : E} (hx : (0, x) ∈ U) : HasDerivAt (fun t => Ψ (t, x) 1) (f x) 0 := by
  let B : C(I, E) → E := fun u => SmoothODE.integralOperator
    (ContinuousMap.comp ⟨f, hf.continuous⟩ u) 1
  have hB : ContDiff ℝ ∞ B :=
    (ContinuousMap.evalCLM ℝ (1 : I)).contDiff.comp
      (SmoothODE.integralOperator.contDiff.comp (SmoothCurveComposition.contDiff_postcomp hf))
  have hP : ContDiffAt ℝ ∞ (fun t : ℝ => Ψ (t, x)) 0 :=
    ((hΨ (0, x) hx).contDiffAt (hU.mem_nhds hx)).comp 0
      (contDiffAt_id.prodMk contDiffAt_const)
  have hdB := ((hB.contDiffAt.comp 0 hP).differentiableAt (by simp)).hasDerivAt
  have hzero : Ψ (0, x) = ContinuousMap.const I x := by simpa using hsol (0, x) hx
  have hBzero : B (Ψ (0, x)) = f x := by
    simp [hzero, B, SmoothODE.integralOperator_apply, ContinuousMap.comp_apply]
  have hd : HasDerivAt (fun t : ℝ => x + t • B (Ψ (t, x))) (f x) 0 := by
    convert! (((hasDerivAt_id 0).smul hdB).const_add x) using 1
    simp [hBzero]
  apply hd.congr_of_eventuallyEq
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), (t, x) ∈ U :=
    (continuous_id.prodMk continuous_const).continuousAt (hU.mem_nhds hx)
  filter_upwards [hnear] with t ht
  have he := congrArg (fun u : C(I, E) => u 1) (hsol (t, x) ht)
  simpa [B] using he

theorem exists_smooth_flow {f : E → E} (hf : ContDiff ℝ ∞ f) (x₀ : E) :
    ∃ (U : Set (ℝ × E)) (Φ : ℝ × E → E),
      IsOpen U ∧ (0, x₀) ∈ U ∧ ContDiffOn ℝ ∞ Φ U ∧
      (∀ x, (0, x) ∈ U → Φ (0, x) = x) ∧
      ∀ q ∈ U, HasDerivAt (fun t => Φ (t, q.2)) (f (Φ q)) q.1 := by
  obtain ⟨U, Ψ, hU, hmem, hΨ, _, hsol⟩ := SmoothODE.exists_smooth_integral_curves hf x₀
  refine ⟨U, fun q => Ψ q 1, hU, hmem, SmoothODE.contDiffOn_endpoint hΨ, ?_, ?_⟩
  · intro x hx
    have hz : Ψ (0, x) = ContinuousMap.const I x := by simpa using hsol (0, x) hx
    simp [hz]
  · intro q hq
    rcases q with ⟨T, x⟩
    by_cases hT : T = 0
    · subst T
      have hz : Ψ (0, x) = ContinuousMap.const I x := by simpa using hsol (0, x) hq
      simpa [hz] using endpoint_hasDerivAt_zero hf hU hΨ hsol hq
    · exact endpoint_hasDerivAt_ne_zero hf hU hΨ hsol hq hT

theorem exists_smooth_local_flow {f : E → E} {S : Set E} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) {x₀ : E} (hx₀ : x₀ ∈ S) :
    ∃ (U : Set (ℝ × E)) (Φ : ℝ × E → E),
      IsOpen U ∧ (0, x₀) ∈ U ∧ ContDiffOn ℝ ∞ Φ U ∧
      (∀ x, (0, x) ∈ U → Φ (0, x) = x) ∧
      ∀ q ∈ U, Φ q ∈ S ∧ HasDerivAt (fun t => Φ (t, q.2)) (f (Φ q)) q.1 := by
  obtain ⟨g, hg, hgf⟩ := SmoothODE.exists_smooth_extension hS hf hx₀
  obtain ⟨r, hr, hrg⟩ := Metric.eventually_nhds_iff.mp (hgf.and (hS.mem_nhds hx₀))
  obtain ⟨U, Φ, hU, hmem, hΦ, hzero, hd⟩ := exists_smooth_flow hg x₀
  let W := U ∩ Φ ⁻¹' Metric.ball x₀ r
  have hW : IsOpen W := hΦ.continuousOn.isOpen_inter_preimage hU Metric.isOpen_ball
  have hWmem : (0, x₀) ∈ W := ⟨hmem, by simpa [hzero x₀ hmem] using hr⟩
  refine ⟨W, Φ, hW, hWmem, hΦ.mono inter_subset_left,
    fun x hx => hzero x hx.1, ?_⟩
  intro q hq
  have hnear := hrg hq.2
  exact ⟨hnear.2, hnear.1 ▸ hd q hq.1⟩

end
end SmoothFlow

open Set Filter InnerProductSpace
open scoped Topology ContDiff

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_ChartMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Bundle Manifold Set
open scoped Bundle Manifold ContDiff Topology
namespace ChartMetric
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]

abbrev chartLift (x : M) (y : E) : E →L[ℝ] TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y) :=
  (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symmL ℝ ((chartAt E x).symm y)

def metric (x : M) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ (E := TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y))).bilinearComp
    (chartLift x y) (chartLift x y)

@[simp] theorem metric_apply (x : M) (y v w : E) :
    metric x y v w = inner ℝ (chartLift x y v) (chartLift x y w) := rfl

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)] in
theorem lift_smooth (x : M) (v : E) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨(chartAt E x).symm y, chartLift x y v⟩ : TangentBundle 𝓘(ℝ, E) M))
      (chartAt E x).target := by
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x
  have hb : ∀ y ∈ (chartAt E x).target, (chartAt E x).symm y ∈ e.baseSet := by
    intro y hy
    rw [TangentBundle.trivializationAt_baseSet]
    exact (chartAt E x).map_target hy
  have hc := e.contMDiffOn_symm (IB := 𝓘(ℝ, E)) (n := ∞)
  have hf : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun y => ((chartAt E x).symm y, v)) (chartAt E x).target :=
    contMDiffOn_chart_symm.prodMk contMDiffOn_const
  have hcomp := hc.comp hf (fun y hy => e.mem_target.mpr (hb y hy))
  apply hcomp.congr
  intro y hy
  change (⟨(chartAt E x).symm y, e.symmL ℝ ((chartAt E x).symm y) v⟩ : TangentBundle 𝓘(ℝ, E) M) =
    e.toOpenPartialHomeomorph.symm ((chartAt E x).symm y, v)
  rw [e.symmL_apply (hb y hy), e.mk_symm (hb y hy)]

theorem metric_smooth [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
    (x : M) : ContDiffOn ℝ ∞ (metric x) (chartAt E x).target := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  apply contMDiffOn_iff_contDiffOn.mp
  exact @ContMDiffOn.inner_bundle E _ _ E _ 𝓘(ℝ, E) ∞ M _ _ E _ _
    (fun x : M => TangentSpace 𝓘(ℝ, E) x) _
    (fun x : M => (inferInstance : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x)))
    (fun x : M => (inferInstance : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) x)))
    _ _ E _ _ E _ 𝓘(ℝ, E) E _ _ _ (fun y => (chartAt E x).symm y)
    (fun y => chartLift x y v) (fun y => chartLift x y w) _ (lift_smooth x v) (lift_smooth x w)

theorem metric_symmetric (x : M) (y v w : E) : metric x y v w = metric x y w v := by
  rw [metric_apply, metric_apply]
  exact @real_inner_comm (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y))
    (inferInstance : SeminormedAddCommGroup (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y)))
    (inferInstance : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y))) _ _

theorem metric_positive (x : M) {y : E} (hy : y ∈ (chartAt E x).target)
    {v : E} (hv : v ≠ 0) : 0 < metric x y v v := by
  rw [metric_apply]
  apply (@real_inner_self_pos (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y))
    (inferInstance : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y)))
    (inferInstance : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y))) _).mpr
  intro he
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x
  have hb : (chartAt E x).symm y ∈ e.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact (chartAt E x).map_target hy
  apply hv
  have hh := congrArg (e.continuousLinearMapAt ℝ ((chartAt E x).symm y)) he
  change e.continuousLinearMapAt ℝ ((chartAt E x).symm y) (e.symmL ℝ ((chartAt E x).symm y) v) =
    e.continuousLinearMapAt ℝ ((chartAt E x).symm y) 0 at hh
  simpa only [e.continuousLinearMapAt_symmL hb, map_zero] using hh

end
end ChartMetric
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_CoordinateGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace CoordinateGeometry
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

variable {G : E → MetricTensor E} {S : Set E}

theorem hasFDerivAt_geodesicSpray_zero (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v) {x : E} (hx : x ∈ S) :
    HasFDerivAt (geodesicSpray G)
      ((ContinuousLinearMap.snd ℝ E E).prod (0 : E × E →L[ℝ] E)) (x, 0) := by
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (MetricTensor E) := inferInstance
  let : NormedSpace ℝ (MetricTensor E) := inferInstance
  have hc := (hG x hx).contDiffAt (hS.mem_nhds hx)
  have hD : ContDiffAt ℝ ∞ (fun q : E × E => fderiv ℝ G q.1) (x, 0) :=
    (hc.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])).comp (x, 0) contDiffAt_fst
  have hA : HasFDerivAt (fun q : E × E => fderiv ℝ G q.1 q.2 q.2) (0 : E × E →L[ℝ] E →L[ℝ] ℝ) (x, 0) := by
    have hd := (((hD.differentiableAt (by simp)).hasFDerivAt.clm_apply hasFDerivAt_snd).clm_apply hasFDerivAt_snd)
    convert! hd using 1
    apply ContinuousLinearMap.ext
    intro q
    apply ContinuousLinearMap.ext
    intro z
    simp
  have hDflip : ContDiffAt ℝ ∞ (fun q : E × E => (fderiv ℝ G q.1).flip) (x, 0) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.contDiff.contDiffAt.comp (x, 0) hD
  have hAflip := hDflip.clm_apply contDiffAt_snd
  have hDflip2 : ContDiffAt ℝ ∞ (fun q : E × E => ((fderiv ℝ G q.1).flip q.2).flip) (x, 0) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearMap.contDiff.contDiffAt.comp (x, 0) hAflip
  have hB : HasFDerivAt (fun q : E × E => ((fderiv ℝ G q.1).flip q.2).flip q.2) (0 : E × E →L[ℝ] E →L[ℝ] ℝ) (x, 0) := by
    have hd₁ := (hDflip.differentiableAt (by simp)).hasFDerivAt.clm_apply hasFDerivAt_snd
    have hd₂ := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearMap.hasFDerivAt.comp (x, 0) hd₁
    have hd := hd₂.clm_apply hasFDerivAt_snd
    convert! hd using 1
    apply ContinuousLinearMap.ext
    intro q
    apply ContinuousLinearMap.ext
    intro z
    simp
  have hL : HasFDerivAt (fun q : E × E => lowerChristoffel (fderiv ℝ G q.1) q.2 q.2) (0 : E × E →L[ℝ] E →L[ℝ] ℝ) (x, 0) := by
    convert! ((hA.add hA).sub hB).const_smul (1 / 2 : ℝ) using 1
    simp
  have hI : ContDiffAt ℝ ∞ (fun q : E × E => (G q.1).inverse) (x, 0) :=
    ((contDiffOn_metric_inverse hS hG hpos x hx).contDiffAt (hS.mem_nhds hx)).comp (x, 0) contDiffAt_fst
  have hC : HasFDerivAt (fun q : E × E => christoffel G q.1 q.2 q.2) (0 : E × E →L[ℝ] E) (x, 0) := by
    have hd := (hI.differentiableAt (by simp)).hasFDerivAt.clm_apply hL
    convert! hd using 1
    apply ContinuousLinearMap.ext
    intro q
    simp [lowerChristoffel]
  convert! hasFDerivAt_snd.prodMk hC.neg using 1
  simp

end
end CoordinateGeometry

open Set Filter
open scoped Topology ContDiff

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_CurveCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace VariationCalculus

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem directional_linearization {Φ : P → F} {f : F → F} {U : Set P} {p a b : P}
    (hU : IsOpen U) (hp : p ∈ U) (hΦ : ContDiffOn ℝ 2 Φ U)
    (hf : DifferentiableAt ℝ f (Φ p))
    (hode : ∀ q ∈ U, fderiv ℝ Φ q a = f (Φ q)) :
    fderiv ℝ (fderiv ℝ Φ) p a b = fderiv ℝ f (Φ p) (fderiv ℝ Φ p b) := by
  have hc := (hΦ p hp).contDiffAt (hU.mem_nhds hp)
  have hdΦ := hc.differentiableAt (by norm_num)
  have hdD : DifferentiableAt ℝ (fderiv ℝ Φ) p :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA := hdD.hasFDerivAt.clm_apply (hasFDerivAt_const a p)
  have hB := hf.hasFDerivAt.comp p hdΦ.hasFDerivAt
  have he : (fun q => fderiv ℝ Φ q a) =ᶠ[𝓝 p] (fun q => f (Φ q)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hode q hq
  have hlin := congrArg (fun L : P →L[ℝ] F => L b) (hA.unique (hB.congr_of_eventuallyEq he))
  have hs := hc.isSymmSndFDerivAt (by simp) a b
  simpa [hs] using hlin

theorem variation_hasDerivAt {Φ : ℝ × P → F} {f : F → F} {U : Set (ℝ × P)}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ 2 Φ U)
    (hode : ∀ q ∈ U, HasDerivAt (fun t => Φ (t, q.2)) (f (Φ q)) q.1)
    {T : ℝ} {x w : P} (hTx : (T, x) ∈ U) (hf : DifferentiableAt ℝ f (Φ (T, x))) :
    HasDerivAt (fun t => fderiv ℝ Φ (t, x) (0, w))
      (fderiv ℝ f (Φ (T, x)) (fderiv ℝ Φ (T, x) (0, w))) T := by
  have hc := (hΦ (T, x) hTx).contDiffAt (hU.mem_nhds hTx)
  have hdD : DifferentiableAt ℝ (fderiv ℝ Φ) (T, x) :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have htD := hasDerivAt_time_slice hdD
  have hd := (htD.hasFDerivAt.clm_apply (hasFDerivAt_const (0, w) T)).hasDerivAt
  have he := directional_linearization hU hTx hΦ hf (a := (1, 0)) (b := (0, w)) (by
    intro q hq
    exact (hasDerivAt_time_slice (((hΦ q hq).contDiffAt (hU.mem_nhds hq)).differentiableAt
      (by norm_num))).unique (hode q hq))
  convert! hd using 1
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, map_zero, zero_add]
  exact he.symm

end VariationCalculus

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_FlowLinearization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace FlowLinearization
open Set Filter
open scoped Topology ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem equilibrium {f : E → E} {Φ : ℝ × E → E} {U : Set (ℝ × E)} {S : Set E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ 2 Φ U) (hS : IsOpen S)
    (hf : ContDiffOn ℝ 1 f S)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, Φ q ∈ S ∧ HasDerivAt (fun t => Φ (t, q.2)) (f (Φ q)) q.1)
    {x : E} (hx : x ∈ S) (hfx : f x = 0) {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, x) ∈ U) :
    ∀ t ∈ Icc (0 : ℝ) T, Φ (t, x) = x := by
  let u : ℝ → E := fun t => Φ (t, x)
  have hdu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt u (f (u t)) t :=
    fun t ht => (hode _ (hseg t ht)).2
  have heq := unique_Icc (u := u) (v := fun _ => x)
    (fun time htime => ((hΦ _ (hseg time htime)).contDiffAt
      (hU.mem_nhds (hseg time htime))).continuousAt.comp_continuousWithinAt
        (f := fun time : ℝ => (time, x))
        (continuousWithinAt_id.prodMk continuousWithinAt_const)) continuousOn_const
    (fun z hz => by
      have hzs : z ∈ S := by
        rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
        · exact (hode _ (hseg t ht)).1
        · exact hx
      exact (hf z hzs).contDiffAt (hS.mem_nhds hzs))
    (fun t ht => (hdu t ht).hasDerivWithinAt)
    (fun t ht => by simpa only [hfx] using (hasDerivWithinAt_const t (Icc (0 : ℝ) T) x))
    (hzero x (hseg 0 ⟨le_rfl, hT⟩))
  exact fun t ht => heq ht

theorem initial_variation {Φ : ℝ × E → E} {U : Set (ℝ × E)}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ 1 Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q) {x w : E} (hx : (0, x) ∈ U) :
    fderiv ℝ Φ (0, x) (0, w) = w := by
  have hdΦ := ((hΦ _ hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hd := hdΦ.hasFDerivAt.comp x
    ((hasFDerivAt_const (0 : ℝ) x).prodMk (hasFDerivAt_id x))
  have heq : (fun y => Φ (0, y)) =ᶠ[𝓝 x] id := by
    have hmem : ∀ᶠ y in 𝓝 x, (0, y) ∈ U :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
    filter_upwards [hmem] with y hy
    exact hzero y hy
  have huniq := hd.unique ((hasFDerivAt_id x).congr_of_eventuallyEq heq)
  have hh := congrArg (fun L : E →L[ℝ] E => L w) huniq
  simpa using hh

theorem nilpotent_variation {f : E → E} {Φ : ℝ × E → E} {U : Set (ℝ × E)}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ 2 Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, HasDerivAt (fun t => Φ (t, q.2)) (f (Φ q)) q.1)
    {x : E} {A : E →L[ℝ] E} (hf : HasFDerivAt f A x)
    (hA : ∀ w, A (A w) = 0) {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, x) ∈ U)
    (heq : ∀ t ∈ Icc (0 : ℝ) T, Φ (t, x) = x) (w : E) :
    ∀ t ∈ Icc (0 : ℝ) T, fderiv ℝ Φ (t, x) (0, w) = w + t • A w := by
  let J : ℝ → E := fun t => fderiv ℝ Φ (t, x) (0, w)
  let K : ℝ → E := fun t => w + t • A w
  have hdJ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt J (A (J t)) t := by
    intro t ht
    have hdiff : DifferentiableAt ℝ f (Φ (t, x)) := by rw [heq t ht]; exact hf.differentiableAt
    have hd := VariationCalculus.variation_hasDerivAt hU hΦ hode (hseg t ht) hdiff (w := w)
    simpa only [heq t ht, hf.fderiv] using hd
  have hdK : ∀ t : ℝ, HasDerivAt K (A (K t)) t := by
    intro t
    simpa [K, hA] using ((hasDerivAt_id t).smul_const (A w)).const_add w
  have he := unique_Icc (u := J) (v := K)
    (fun t ht => (hdJ t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hdK t).continuousAt.continuousWithinAt)
    (fun _ _ => A.contDiff.contDiffAt)
    (fun t ht => (hdJ t ht).hasDerivWithinAt)
    (fun t ht => (hdK t).hasDerivWithinAt) (by
      simpa [J, K] using initial_variation hU (hΦ.of_le (by norm_num)) hzero (hseg 0 ⟨le_rfl, hT⟩) (w := w))
  exact fun t ht => he ht

end
end FlowLinearization

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_NormalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace NormalCoordinates
open Set Filter CoordinateGeometry
open scoped Topology ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem hasFDerivAt_flow_zero {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1)
    {x : E} (hx : x ∈ S) {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, (x, 0)) ∈ U) :
    HasFDerivAt (fun q => Φ (T, q))
      (ContinuousLinearMap.id ℝ (E × E) + T •
        (ContinuousLinearMap.snd ℝ E E).prod (0 : E × E →L[ℝ] E)) (x, 0) := by
  have heq := FlowLinearization.equilibrium hU (hΦ.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    (hS.prod isOpen_univ) ((contDiffOn_geodesicSpray hS hG hpos).of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top))
    hzero (fun q hq => ⟨⟨(hode q hq).1, mem_univ _⟩, (hode q hq).2⟩)
    (x := (x, 0)) ⟨hx, mem_univ _⟩ (geodesicSpray_zero G x) hT hseg
  have hd := hasFDerivAt_geodesicSpray_zero hS hG hpos hx
  have hlin := FlowLinearization.nilpotent_variation hU (hΦ.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) hzero
    (fun q hq => (hode q hq).2) hd (by intro w; simp) hT hseg heq
  have hTx := hseg T ⟨hT, le_rfl⟩
  have hder := (((hΦ _ hTx).contDiffAt (hU.mem_nhds hTx)).differentiableAt (by simp)).hasFDerivAt.comp
    (x, 0) ((hasFDerivAt_const T (x, 0)).prodMk (hasFDerivAt_id (x, 0)))
  convert! hder using 1
  apply ContinuousLinearMap.ext
  intro w
  simpa [ContinuousLinearMap.comp_apply] using (hlin w T ⟨hT, le_rfl⟩).symm

def normalShear (T : ℝ) (hT : T ≠ 0) : (E × E) ≃L[ℝ] (E × E) where
  toFun q := (q.1, q.1 + T • q.2)
  invFun q := (q.1, T⁻¹ • (q.2 - q.1))
  map_add' a b := by
    ext <;> simp
    abel
  map_smul' a b := by
    apply Prod.ext
    · rfl
    · change a • b.1 + T • (a • b.2) = a • (b.1 + T • b.2)
      rw [smul_add, smul_comm T a]
  left_inv q := by ext <;> simp [smul_smul, hT]
  right_inv q := by ext <;> simp [smul_smul, hT]
  continuous_toFun := continuous_fst.prodMk (continuous_fst.add (continuous_const.smul continuous_snd))
  continuous_invFun := continuous_fst.prodMk (continuous_const.smul (continuous_snd.sub continuous_fst))

theorem hasFDerivAt_normalMap_zero {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1)
    {x : E} (hx : x ∈ S) {T : ℝ} (hT : 0 < T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, (x, 0)) ∈ U) :
    HasFDerivAt (fun q => (q.1, (Φ (T, q)).1)) ((normalShear (E := E) T (ne_of_gt hT)) : E × E →L[ℝ] E × E) (x, 0) := by
  have hd := hasFDerivAt_flow_zero hS hG hpos hU hΦ hzero hode hx hT.le hseg
  convert! hasFDerivAt_fst.prodMk hd.fst using 1

end
end NormalCoordinates

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_NormalNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff

namespace NormalNeighborhood
noncomputable section
section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_smooth_local_diffeomorph {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S : Set E} (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S)
    {a : E} (ha : a ∈ S) {D : E ≃L[ℝ] F}
    (hd : HasFDerivAt f (D : E →L[ℝ] F) a) :
    ∃ e : OpenPartialHomeomorph E F,
      (e : E → F) = f ∧ a ∈ e.source ∧ e.source ⊆ S ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ z ∈ e.source, ∃ L : E ≃L[ℝ] F, fderiv ℝ f z = (L : E →L[ℝ] F) := by
  let P := ((hf a ha).contDiffAt (hS.mem_nhds ha)).toOpenPartialHomeomorph f hd (by simp)
  have hPa : a ∈ P.source :=
    ((hf a ha).contDiffAt (hS.mem_nhds ha)).mem_toOpenPartialHomeomorph_source hd (by simp)
  let W := S ∩ (fderiv ℝ f) ⁻¹' range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F)
  have hW : IsOpen W :=
    (hf.continuousOn_fderiv_of_isOpen hS (by simp)).isOpen_inter_preimage hS
      ContinuousLinearEquiv.isOpen
  have haW : a ∈ W := ⟨ha, ⟨D, hd.fderiv.symm⟩⟩
  let e := P.restrOpen W hW
  have hcoeff : (e : E → F) = f := rfl
  refine ⟨e, hcoeff, ⟨hPa, haW⟩, fun _ hz => hz.2.1, ?_, ?_⟩
  · intro y hy
    have hz := e.map_target hy
    obtain ⟨D', hD'⟩ := hz.2.2
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm hy (f₀' := D')
    · rw [hcoeff, hD']
      exact (((hf _ hz.2.1).contDiffAt (hS.mem_nhds hz.2.1)).differentiableAt (by simp)).hasFDerivAt
    · rw [hcoeff]
      exact (hf _ hz.2.1).contDiffAt (hS.mem_nhds hz.2.1)
  · intro z hz
    obtain ⟨L, hL⟩ := hz.2.2
    exact ⟨L, hL.symm⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem isOpen_initial_segment {U : Set (ℝ × E)} (hU : IsOpen U) (T : ℝ) :
    IsOpen {q : E | ∀ t ∈ Icc (0 : ℝ) T, (t, q) ∈ U} := by
  rw [isOpen_iff_mem_nhds]
  intro q hq
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro t ht
  exact (continuous_swap.continuousAt (x := (q, t))).preimage_mem_nhds
    (hU.mem_nhds (hq t ht))

end General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry

structure NormalFlow (G : E → MetricTensor E) (S : Set E) (x₀ : E) where
  time : ℝ
  time_pos : 0 < time
  domain : Set (ℝ × (E × E))
  domain_open : IsOpen domain
  flow : ℝ × (E × E) → E × E
  flow_smooth : ContDiffOn ℝ ∞ flow domain
  initial : ∀ q, (0, q) ∈ domain → flow (0, q) = q
  ode : ∀ q ∈ domain, (flow q).1 ∈ S ∧
    HasDerivAt (fun t => flow (t, q.2)) (geodesicSpray G (flow q)) q.1
  normal : OpenPartialHomeomorph (E × E) (E × E)
  normal_apply : ∀ q, normal q = (q.1, (flow (time, q)).1)
  center_mem : (x₀, 0) ∈ normal.source
  source_stays : ∀ q ∈ normal.source, ∀ t ∈ Icc (0 : ℝ) time, (t, q) ∈ domain
  inverse_smooth : ContDiffOn ℝ ∞ normal.symm normal.target
  normal_derivative_invertible : ∀ q ∈ normal.source,
    ∃ L : (E × E) ≃L[ℝ] (E × E), fderiv ℝ normal q = (L : (E × E) →L[ℝ] (E × E))

theorem exists_normalFlow {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {x₀ : E} (hx₀ : x₀ ∈ S) : Nonempty (NormalFlow G S x₀) := by
  obtain ⟨U, Φ, hU, h0, hΦ, hzero, hode'⟩ := SmoothFlow.exists_smooth_local_flow
    (hS.prod isOpen_univ) (contDiffOn_geodesicSpray hS hG hpos)
    (x₀ := (x₀, (0 : E))) ⟨hx₀, mem_univ _⟩
  have hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1 :=
    fun q hq => ⟨(hode' q hq).1.1, (hode' q hq).2⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  let T : ℝ := r / 2
  have hT : 0 < T := half_pos hr
  have hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, (x₀, 0)) ∈ U := by
    intro t ht
    apply hball
    simp only [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq, sub_zero,
      abs_of_nonneg ht.1, max_eq_left ht.1]
    exact lt_of_le_of_lt ht.2 (half_lt_self hr)
  let A : Set (E × E) := {q | ∀ t ∈ Icc (0 : ℝ) T, (t, q) ∈ U}
  have hA : IsOpen A := isOpen_initial_segment hU T
  have ha : (x₀, 0) ∈ A := hseg
  let N : E × E → E × E := fun q => (q.1, (Φ (T, q)).1)
  have hN : ContDiffOn ℝ ∞ N A :=
    contDiffOn_fst.prodMk ((hΦ.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun q (hq : q ∈ A) => hq T ⟨hT.le, le_rfl⟩)).fst)
  have hDN := NormalCoordinates.hasFDerivAt_normalMap_zero hS hG hpos hU hΦ
    hzero hode hx₀ hT hseg
  obtain ⟨e, he, hem, hesub, hesmooth, heinv⟩ :=
    exists_smooth_local_diffeomorph hA hN ha hDN
  exact ⟨{
    time := T
    time_pos := hT
    domain := U
    domain_open := hU
    flow := Φ
    flow_smooth := hΦ
    initial := hzero
    ode := hode
    normal := e
    normal_apply := fun q => congrFun he q
    center_mem := hem
    source_stays := fun q hq => hesub hq
    inverse_smooth := hesmooth
    normal_derivative_invertible := fun q hq => by simpa only [he] using heinv q hq
  }⟩

end
end NormalNeighborhood
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_GaussLemma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace GaussLemma
open Set Filter CoordinateGeometry
open scoped Topology ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem flow_gauss {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1)
    {x v : E} {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, (x, v)) ∈ U) (w : E) :
    G (Φ (T, (x, v))).1
      (fderiv ℝ Φ (T, (x, v)) (0, (0, v))).1
      (fderiv ℝ Φ (T, (x, v)) (0, (0, w))).1 = T ^ 2 * G x v w :=
  gauss_lemma hS hG hsym hpos hU hΦ hzero hode hT hseg w

end
end GaussLemma
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_RadialCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff

namespace RadialCoordinates
noncomputable section

section Fiber
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def fiber (e : OpenPartialHomeomorph (X × Y) (X × Y))
    (he : ∀ q, (e q).1 = q.1) (x : X) : OpenPartialHomeomorph Y Y where
  toFun v := (e (x, v)).2
  invFun y := (e.symm (x, y)).2
  source := {v | (x, v) ∈ e.source}
  target := {y | (x, y) ∈ e.target}
  map_source' := by
    intro v hv
    change (x, (e (x, v)).2) ∈ e.target
    have hp : (x, (e (x, v)).2) = e (x, v) := Prod.ext (he (x, v)).symm rfl
    rw [hp]
    exact e.map_source hv
  map_target' := by
    intro y hy
    have hfst : (e.symm (x, y)).1 = x := by
      rw [← he, e.right_inv hy]
    change (x, (e.symm (x, y)).2) ∈ e.source
    have hp : (x, (e.symm (x, y)).2) = e.symm (x, y) := Prod.ext hfst.symm rfl
    rw [hp]
    exact e.map_target hy
  left_inv' := by
    intro v hv
    have hp : (x, (e (x, v)).2) = e (x, v) := Prod.ext (he (x, v)).symm rfl
    change (e.symm (x, (e (x, v)).2)).2 = v
    rw [hp, e.left_inv hv]
  right_inv' := by
    intro y hy
    have hfst : (e.symm (x, y)).1 = x := by rw [← he, e.right_inv hy]
    have hp : (x, (e.symm (x, y)).2) = e.symm (x, y) := Prod.ext hfst.symm rfl
    change (e (x, (e.symm (x, y)).2)).2 = y
    rw [hp, e.right_inv hy]
  continuousOn_toFun :=
    (e.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => hv)).snd
  continuousOn_invFun :=
    (e.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hy => hy)).snd
  open_source := e.open_source.preimage (continuous_const.prodMk continuous_id)
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
end Fiber
end
end RadialCoordinates

namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry NormalNeighborhood

variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

def normalAt (N : NormalFlow G S x₀) (x : E) : OpenPartialHomeomorph E E :=
  RadialCoordinates.fiber N.normal (fun q => by rw [N.normal_apply]) x

omit [FiniteDimensional ℝ E] in
@[simp] theorem normalAt_apply (N : NormalFlow G S x₀) (x v : E) :
    N.normalAt x v = (N.flow (N.time, (x, v))).1 :=
  congrArg Prod.snd (N.normal_apply (x, v))

omit [FiniteDimensional ℝ E] in
@[simp] theorem normalAt_source (N : NormalFlow G S x₀) (x : E) :
    (N.normalAt x).source = {v | (x, v) ∈ N.normal.source} := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem normalAt_target (N : NormalFlow G S x₀) (x : E) :
    (N.normalAt x).target = {y | (x, y) ∈ N.normal.target} := rfl

omit [FiniteDimensional ℝ E] in
 theorem normalAt_smooth (N : NormalFlow G S x₀) (x : E) :
    ContDiffOn ℝ ∞ (N.normalAt x) (N.normalAt x).source := by
  have hcomp : ContDiffOn ℝ ∞ (fun v => N.flow (N.time, (x, v))) (N.normalAt x).source :=
    N.flow_smooth.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
      (fun v hv => N.source_stays (x, v) hv N.time ⟨N.time_pos.le, le_rfl⟩)
  exact hcomp.fst.congr (fun v _ => N.normalAt_apply x v)

omit [FiniteDimensional ℝ E] in
 theorem normalAt_inverse_smooth (N : NormalFlow G S x₀) (x : E) :
    ContDiffOn ℝ ∞ (N.normalAt x).symm (N.normalAt x).target :=
  (N.inverse_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hy => hy)).snd

 theorem normalAt_gauss (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ z ∈ S, ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x v : E} (hv : v ∈ (N.normalAt x).source) (w : E) :
    G (N.normalAt x v) (fderiv ℝ (N.normalAt x) v v)
      (fderiv ℝ (N.normalAt x) v w) = N.time ^ 2 * G x v w := by
  have htv := N.source_stays (x, v) hv N.time ⟨N.time_pos.le, le_rfl⟩
  have hdΦ := ((N.flow_smooth _ htv).contDiffAt (N.domain_open.mem_nhds htv)).differentiableAt
    (by simp)
  have hpath : HasFDerivAt (fun v' : E => (N.time, (x, v')))
      ((0 : E →L[ℝ] ℝ).prod ((0 : E →L[ℝ] E).prod (.id ℝ E))) v :=
    (hasFDerivAt_const _ _).prodMk ((hasFDerivAt_const _ _).prodMk (hasFDerivAt_id v))
  have hd := hdΦ.hasFDerivAt.comp v hpath
  have hde : HasFDerivAt (N.normalAt x)
      ((ContinuousLinearMap.fst ℝ E E).comp ((fderiv ℝ N.flow (N.time, (x, v))).comp
        ((0 : E →L[ℝ] ℝ).prod ((0 : E →L[ℝ] E).prod (.id ℝ E))))) v := by
    convert! hd.fst using 1
    ext z
    exact N.normalAt_apply x z
  rw [hde.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]
  change G (N.normalAt x v) (fderiv ℝ N.flow (N.time, (x, v)) (0, (0, v))).1
    (fderiv ℝ N.flow (N.time, (x, v)) (0, (0, w))).1 = _
  rw [normalAt_apply]
  exact GaussLemma.flow_gauss hS hG hsym hpos N.domain_open N.flow_smooth N.initial N.ode
      N.time_pos.le (N.source_stays (x, v) hv) w
end
end NormalNeighborhood.NormalFlow

namespace RadialCoordinates
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry

omit [FiniteDimensional ℝ E] in
theorem metric_cauchy_sq {B : MetricTensor E}
    (hs : ∀ v w, B v w = B w v) (hp : ∀ v, 0 ≤ B v v) (v w : E) :
    (B v w) ^ 2 ≤ B v v * B w w := by
  have hquad : ∀ t : ℝ, 0 ≤ B v v * (t * t) + (2 * B v w) * t + B w w := by
    intro t
    have h := hp (t • v + w)
    simp only [map_add, map_smul, add_apply,
      smul_apply, smul_eq_mul] at h
    rw [hs w v] at h
    nlinarith only [h]
  have h := discrim_le_zero hquad
  simp only [discrim] at h
  nlinarith only [h]

end
end RadialCoordinates
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_RadialLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace RadialCoordinates
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open CoordinateGeometry

theorem metric_nonneg {B : MetricTensor E}
    (hp : ∀ v : E, v ≠ 0 → 0 < B v v) (v : E) : 0 ≤ B v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (hp v hv).le

theorem hasDerivAt_regularized_radius {B : MetricTensor E}
    (hs : ∀ v w, B v w = B w v) (hp : ∀ v, 0 ≤ B v v)
    {c : ℝ → E} {w : E} {t ε T : ℝ} (hε : 0 < ε) (hc : HasDerivAt c w t) :
    HasDerivAt (fun s => T * Real.sqrt (B (c s) (c s) + ε))
      (T * B (c t) w / Real.sqrt (B (c t) (c t) + ε)) t := by
  have hpos : 0 < B (c t) (c t) + ε := add_pos_of_nonneg_of_pos (hp _) hε
  have hd := (B.hasFDerivAt.comp_hasDerivAt t hc).clm_apply hc
  have hsqrt := ((hd.add_const ε).sqrt hpos.ne').const_mul T
  convert! hsqrt using 1
  simp only [Function.comp_apply, hs w (c t)]
  field_simp
  ring
end
end RadialCoordinates

namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry RadialCoordinates
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

omit [FiniteDimensional ℝ E] in
 theorem base_mem (N : NormalFlow G S x₀) {x v : E} (hv : v ∈ (N.normalAt x).source) :
    x ∈ S := by
  have h0 := N.source_stays (x, v) hv 0 ⟨le_rfl, N.time_pos.le⟩
  have h := (N.ode _ h0).1
  simpa only [N.initial (x, v) h0] using h

omit [FiniteDimensional ℝ E] in
 theorem normalAt_mem (N : NormalFlow G S x₀) {x v : E}
    (hv : v ∈ (N.normalAt x).source) : N.normalAt x v ∈ S := by
  rw [normalAt_apply]
  exact (N.ode _ (N.source_stays (x, v) hv N.time ⟨N.time_pos.le, le_rfl⟩)).1

 theorem radial_derivative_bound (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ z ∈ S, ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x v : E} (hv : v ∈ (N.normalAt x).source) (w : E) {ε : ℝ} (hε : 0 < ε) :
    |N.time * G x v w / Real.sqrt (G x v v + ε)| ≤
      Real.sqrt (G (N.normalAt x v) (fderiv ℝ (N.normalAt x) v w)
        (fderiv ℝ (N.normalAt x) v w)) := by
  let D := fderiv ℝ (N.normalAt x) v
  let B := G (N.normalAt x v)
  have hB : ∀ u, 0 ≤ B u u := metric_nonneg (hpos _ (N.normalAt_mem hv))
  have hbase : 0 ≤ G x v v := metric_nonneg (hpos _ (N.base_mem hv)) v
  have hc := metric_cauchy_sq (hsym _ (N.normalAt_mem hv)) hB (D v) (D w)
  have hg := N.normalAt_gauss hS hG hsym hpos hv
  change (B (D v) (D w)) ^ 2 ≤ B (D v) (D v) * B (D w) (D w) at hc
  rw [show B (D v) (D w) = N.time ^ 2 * G x v w from hg w,
    show B (D v) (D v) = N.time ^ 2 * G x v v from hg v] at hc
  have hmain : N.time ^ 2 * (G x v w) ^ 2 ≤ G x v v * B (D w) (D w) := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos N.time_pos)).mp
    convert! hc using 1 <;> ring
  have hsum : 0 < G x v v + ε := add_pos_of_nonneg_of_pos hbase hε
  apply Real.abs_le_sqrt
  rw [div_pow, Real.sq_sqrt hsum.le, mul_pow]
  apply (div_le_iff₀ hsum).mpr
  exact hmain.trans (by nlinarith only [hB (D w), hε])

theorem radial_along_curve (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ z ∈ S, ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} {c : ℝ → E} {c' : E} {t ε : ℝ} (hε : 0 < ε)
    (ht : c t ∈ (N.normalAt x).target) (hc : HasDerivAt c c' t) :
    ∃ d : ℝ,
      HasDerivAt (fun s => N.time * Real.sqrt
        (G x ((N.normalAt x).symm (c s)) ((N.normalAt x).symm (c s)) + ε)) d t ∧
      |d| ≤ Real.sqrt (G (c t) c' c') := by
  let e := N.normalAt x
  let v := e.symm (c t)
  have hv : v ∈ e.source := e.map_target ht
  have hdi := ((N.normalAt_inverse_smooth x _ ht).contDiffAt
    (e.open_target.mem_nhds ht)).differentiableAt (by simp)
  have hdv := hdi.hasFDerivAt.comp_hasDerivAt t hc
  let w := fderiv ℝ e.symm (c t) c'
  have hdv' : HasDerivAt (fun s => e.symm (c s)) w t := hdv
  have hdf := ((N.normalAt_smooth x _ hv).contDiffAt
    (e.open_source.mem_nhds hv)).differentiableAt (by simp)
  have hforward := hdf.hasFDerivAt.comp_hasDerivAt t hdv'
  have heq : (fun s => e (e.symm (c s))) =ᶠ[𝓝 t] c := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds ht)] with s hs
    exact e.right_inv hs
  have hD : fderiv ℝ e v w = c' :=
    (hforward.congr_of_eventuallyEq heq.symm).unique hc
  refine ⟨N.time * G x v w / Real.sqrt (G x v v + ε), ?_, ?_⟩
  · exact hasDerivAt_regularized_radius (hsym _ (N.base_mem hv))
      (metric_nonneg (hpos _ (N.base_mem hv))) hε hdv'
  · have hbound := N.radial_derivative_bound hS hG hsym hpos hv w hε
    change |N.time * G x v w / Real.sqrt (G x v v + ε)| ≤
      Real.sqrt (G (e v) (fderiv ℝ e v w) (fderiv ℝ e v w)) at hbound
    rw [hD, e.right_inv ht] at hbound
    exact hbound
end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_NormalLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry RadialCoordinates
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

def coordinateLength (G : E → MetricTensor E) (c : ℝ → E) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (G (c t) (deriv c t) (deriv c t)))

theorem regularized_radius_length (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ z ∈ S, ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} {c : ℝ → E} {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε)
    (hc : ContDiffOn ℝ 1 c (Icc a b))
    (hcN : ∀ t ∈ Icc a b, c t ∈ (N.normalAt x).target) :
    ‖N.time * Real.sqrt (G x ((N.normalAt x).symm (c b)) ((N.normalAt x).symm (c b)) + ε) -
      N.time * Real.sqrt (G x ((N.normalAt x).symm (c a)) ((N.normalAt x).symm (c a)) + ε)‖ₑ ≤
      coordinateLength G c a b := by
  let e := N.normalAt x
  let v : ℝ → E := fun t => e.symm (c t)
  let f : ℝ → ℝ := fun t => N.time * Real.sqrt (G x (v t) (v t) + ε)
  have hv : ContDiffOn ℝ 1 v (Icc a b) :=
    ((N.normalAt_inverse_smooth x).of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top)).comp hc hcN
  have hq : ContDiffOn ℝ 1 (fun t => G x (v t) (v t) + ε) (Icc a b) :=
    (((G x).contDiff.comp_contDiffOn hv).clm_apply hv).add contDiffOn_const
  have hqpos : ∀ t ∈ Icc a b, G x (v t) (v t) + ε ≠ 0 := by
    intro t ht
    have hn : 0 ≤ G x (v t) (v t) := metric_nonneg
      (hpos _ (N.base_mem (e.map_target (hcN t ht)))) _
    exact (add_pos_of_nonneg_of_pos hn hε).ne'
  have hf : ContDiffOn ℝ 1 f (Icc a b) := contDiffOn_const.mul (hq.sqrt hqpos)
  apply (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hf hab).trans
  apply lintegral_mono_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  have hd := ((hc t ⟨ht.1.le, ht.2.le⟩).contDiffAt
    (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero
  obtain ⟨d, hdf, hbound⟩ := N.radial_along_curve hS hG hsym hpos hε
    (hcN t ⟨ht.1.le, ht.2.le⟩) hd.hasDerivAt
  have hdEq : deriv f t = d := hdf.deriv
  rw [hdEq, Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal hbound

theorem radial_length (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ z ∈ S, ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} {c : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hc : ContDiffOn ℝ 1 c (Icc a b))
    (hcN : ∀ t ∈ Icc a b, c t ∈ (N.normalAt x).target) :
    ‖N.time * Real.sqrt (G x ((N.normalAt x).symm (c b)) ((N.normalAt x).symm (c b))) -
      N.time * Real.sqrt (G x ((N.normalAt x).symm (c a)) ((N.normalAt x).symm (c a)))‖ₑ ≤
      coordinateLength G c a b := by
  let v : ℝ → E := fun t => (N.normalAt x).symm (c t)
  let r : ℝ → ℝ≥0∞ := fun ε => ‖N.time * Real.sqrt (G x (v b) (v b) + ε) -
      N.time * Real.sqrt (G x (v a) (v a) + ε)‖ₑ
  have hr : Continuous r := by fun_prop
  have hlim : Tendsto r (𝓝[>] (0 : ℝ)) (𝓝 (r 0)) :=
    hr.continuousWithinAt.tendsto
  have hrle : r 0 ≤ coordinateLength G c a b := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact N.regularized_radius_length hS hG hsym hpos hab hε hc hcN
  simpa only [r, add_zero, v] using hrle

end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_ChartLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter MeasureTheory Manifold Bundle
open scoped Topology ContDiff ENNReal Manifold

namespace ChartMetric
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)] in
theorem chartLift_eq_mfderiv_symm (x : M) {y : E} (hy : y ∈ (chartAt E x).target) :
    chartLift x y = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x).symm y := by
  have h := TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ, E))
    ((chartAt E x).map_target hy)
  simp only [mfld_simps] at h
  dsimp only [chartLift]
  convert! h using 1
  rw [(chartAt E x).right_inv hy]

theorem sqrt_metric_eq_norm (x : M) {y : E} (hy : y ∈ (chartAt E x).target) (v : E) :
    Real.sqrt (metric x y v v) =
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x).symm y v‖ := by
  rw [metric_apply, chartLift_eq_mfderiv_symm x hy]
  exact (@norm_eq_sqrt_real_inner
    (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y))
    (inferInstance : SeminormedAddCommGroup (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y)))
    (inferInstance : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y))) _).symm

 theorem coordinateLength_eq_pathELength (x : M) {c : ℝ → E} {a b : ℝ}
    (hc : ContDiffOn ℝ 1 c (Icc a b))
    (hct : ∀ t ∈ Icc a b, c t ∈ (chartAt E x).target) :
    NormalNeighborhood.NormalFlow.coordinateLength (metric x) c a b =
      pathELength 𝓘(ℝ, E) ((chartAt E x).symm ∘ c) a b := by
  rw [NormalNeighborhood.NormalFlow.coordinateLength, pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hd := ((hc t ht').contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero
  have hmc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t :=
    mdifferentiableAt_iff_differentiableAt.mpr hd
  have hms := mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, E)) (chart_mem_atlas E x) (hct t ht')
  rw [sqrt_metric_eq_norm x (hct t ht'), mfderiv_comp t hms hmc]
  simp only [mfderiv_eq_fderiv, ofReal_norm]
  rfl

end
end ChartMetric
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_CoerciveMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace CoordinateGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 theorem positive_metric_coercive {B : MetricTensor E}
    (hB : ∀ v : E, v ≠ 0 → 0 < B v v) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ v : E, κ * ‖v‖ ^ 2 ≤ B v v := by
  by_cases hs : Subsingleton E
  · let := hs
    refine ⟨1, zero_lt_one, ?_⟩
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  · let : Nontrivial E := not_subsingleton_iff_nontrivial.mp hs
    have hc : Continuous (fun v : E => B v v) :=
      (B.continuous.comp continuous_id).clm_apply continuous_id
    obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr zero_le_one) hc.continuousOn
    have hwn : ‖w‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hw
    have hw0 : w ≠ 0 := by intro h; simp [h] at hwn
    refine ⟨B w w, hB w hw0, ?_⟩
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · let u : E := ‖v‖⁻¹ • v
      have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hun : ‖u‖ = 1 := by
        simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
        exact inv_mul_cancel₀ hvn
      have hu : u ∈ Metric.sphere (0 : E) 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hun
      have hvu : ‖v‖ • u = v := by simp [u, smul_smul, hvn]
      have hminu := hmin hu
      have he : B v v = ‖v‖ ^ 2 * B u u := by
        conv_lhs => rw [← hvu]
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring
      rw [he, mul_comm (B w w)]
      exact mul_le_mul_of_nonneg_left hminu (sq_nonneg _)

 theorem uniform_metric_coercive {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContinuousOn G S) {x : E} (hx : x ∈ S)
    (hpos : ∀ v : E, v ≠ 0 → 0 < G x v v) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ S ∧
      ∀ y ∈ V, ∀ v : E, κ * ‖v‖ ^ 2 ≤ G y v v := by
  obtain ⟨m, hm, hbound⟩ := positive_metric_coercive hpos
  let V := S ∩ G ⁻¹' Metric.ball (G x) (m / 2)
  have hV : IsOpen V := hG.isOpen_inter_preimage hS Metric.isOpen_ball
  have hxV : x ∈ V := ⟨hx, Metric.mem_ball_self (half_pos hm)⟩
  refine ⟨m / 2, half_pos hm, V, hV, hxV, inter_subset_left, ?_⟩
  intro y hy v
  have hdiff : ‖G y - G x‖ < m / 2 := by
    have hh : dist (G y) (G x) < m / 2 := hy.2
    rwa [dist_eq_norm (G y) (G x)] at hh
  have hnorm : ‖(G y - G x) v v‖ ≤ ‖G y - G x‖ * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖(G y - G x) v‖ * ‖v‖ := ((G y - G x) v).le_opNorm v
      _ ≤ (‖G y - G x‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right ((G y - G x).le_opNorm v) (norm_nonneg _)
      _ = _ := by ring
  have hd : |G y v v - G x v v| ≤ m / 2 * ‖v‖ ^ 2 := by
    have h := hnorm.trans (mul_le_mul_of_nonneg_right hdiff.le (sq_nonneg ‖v‖))
    simpa only [sub_apply, Real.norm_eq_abs] using h
  have hlo := (abs_le.mp hd).1
  have hb := hbound v
  linarith

end
end CoordinateGeometry
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_CoordinateExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace CoordinateGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open GeodesicScaling

 theorem uniform_local_geodesics {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ y ∈ S, ∀ v : E, v ≠ 0 → 0 < G y v v)
    {x : E} (hx : x ∈ S) (C : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ S ∧
      ∀ y ∈ V, ∀ v : E, G y v v ≤ C ^ 2 →
        ∃ q : ℝ → E × E, q 0 = (y, v) ∧ ContDiffOn ℝ ∞ q (Metric.ball 0 ε) ∧
          ∀ t ∈ Metric.ball 0 ε, (q t).1 ∈ S ∧
            HasDerivAt q (geodesicSpray G (q t)) t := by
  obtain ⟨κ, hκ, V₀, hV₀, hxV₀, hV₀S, hcoer⟩ :=
    uniform_metric_coercive hS hG.continuousOn hx (hpos x hx)
  obtain ⟨W, Φ, hW, hmem, hΦ, hzero, hode⟩ := SmoothFlow.exists_smooth_local_flow
    (hS.prod isOpen_univ) (contDiffOn_geodesicSpray hS hG hpos)
    (x₀ := (x, (0 : E))) ⟨hx, mem_univ _⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hmem)
  let B : ℝ := 1 + C ^ 2 / κ
  have hB : 1 ≤ B := by
    have h := div_nonneg (sq_nonneg C) hκ.le
    dsimp [B]
    linarith
  let l : ℝ := r / (2 * (B + 1))
  have hl : 0 < l := div_pos hr (by linarith)
  have hleq : l * (2 * (B + 1)) = r := div_mul_cancel₀ _ (by linarith)
  let ε : ℝ := l * (r / 2)
  have hε : 0 < ε := mul_pos hl (half_pos hr)
  let V := V₀ ∩ Metric.ball x (r / 2)
  refine ⟨ε, hε, V, hV₀.inter Metric.isOpen_ball,
    ⟨hxV₀, Metric.mem_ball_self (half_pos hr)⟩, fun y hy => hV₀S hy.1, ?_⟩
  intro y hy v hv
  have hnv : ‖v‖ ^ 2 ≤ C ^ 2 / κ := (le_div_iff₀ hκ).mpr (by
    simpa only [mul_comm] using (hcoer y hy.1 v).trans hv)
  have hvB : ‖v‖ ≤ B := by
    have hb : B = 1 + C ^ 2 / κ := rfl
    nlinarith [sq_nonneg (‖v‖ - 1)]
  have hvl : ‖l • v‖ < r / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl]
    have hm := mul_le_mul_of_nonneg_left hvB hl.le
    nlinarith
  let q₀ : E × E := (y, l • v)
  have hdom : ∀ t ∈ Metric.ball (0 : ℝ) ε, (l⁻¹ * t, q₀) ∈ W := by
    intro t ht
    have hta : |t| < ε := by simpa [Metric.mem_ball, Real.dist_eq] using ht
    have htl : |l⁻¹ * t| < r / 2 := by
      rw [abs_mul, abs_inv, abs_of_pos hl, inv_mul_eq_div]
      exact (div_lt_iff₀ hl).mpr (by simpa only [ε, mul_comm] using hta)
    apply hball
    simp only [Metric.mem_ball, Prod.dist_eq, q₀,
      dist_zero_right, max_lt_iff]
    exact ⟨lt_trans htl (half_lt_self hr),
      lt_trans hy.2 (half_lt_self hr), lt_trans hvl (half_lt_self hr)⟩
  let q : ℝ → E × E := fun t => scalePhase l⁻¹ (Φ (l⁻¹ * t, q₀))
  have hq₀ : q 0 = (y, v) := by
    have hd := hdom 0 (Metric.mem_ball_self hε)
    simp only [mul_zero] at hd
    simp only [q, mul_zero, hzero q₀ hd, scalePhase_apply, q₀, smul_smul,
      inv_mul_cancel₀ hl.ne', one_smul]
  refine ⟨q, hq₀, ?_, ?_⟩
  · exact (scalePhase l⁻¹).contDiff.comp_contDiffOn
      (hΦ.comp ((contDiff_const.mul contDiff_id : ContDiff ℝ ∞ (fun t : ℝ => l⁻¹ * t)).prodMk contDiff_const).contDiffOn hdom)
  · intro t ht
    have hd := (hode _ (hdom t ht)).2.scomp t ((hasDerivAt_id t).const_mul l⁻¹)
    have he := (scalePhase l⁻¹).hasFDerivAt.comp_hasDerivAt t hd
    refine ⟨(hode _ (hdom t ht)).1.1, ?_⟩
    convert! he using 1
    simp only [mul_one, scale_spray, q]

end
end CoordinateGeometry
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_CoordinateLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace CoordinateGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem geodesic_energy_on_connected {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set ℝ} (hU : IsOpen U) (hUc : IsPreconnected U) {q : ℝ → E × E}
    (hq : ∀ t ∈ U, (q t).1 ∈ S ∧ HasDerivAt q (geodesicSpray G (q t)) t)
    {s t : ℝ} (hs : s ∈ U) (ht : t ∈ U) :
    G (q s).1 (q s).2 (q s).2 = G (q t).1 (q t).2 (q t).2 := by
  have hd : ∀ r ∈ U, HasDerivAt (fun z => G (q z).1 (q z).2 (q z).2) 0 r := by
    intro r hr
    exact geodesic_energy_hasDerivAt_zero hS hG hsym hpos
      (hq r hr).1 (hq r hr).2.fst (hq r hr).2.snd
  exact hU.is_const_of_deriv_eq_zero hUc
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) hs ht

omit [FiniteDimensional ℝ E] in
theorem radial_scale_radius (B : MetricTensor E) (v : E) {T : ℝ} (hT : 0 < T) (a : ℝ) :
    T * Real.sqrt (B ((a / T) • v) ((a / T) • v)) = |a| * Real.sqrt (B v v) := by
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [show a / T * (a / T * B v v) = (a / T) ^ 2 * B v v by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, ← mul_assoc,
    abs_div, abs_of_pos hT]
  congr 1
  field_simp

end
end CoordinateGeometry

namespace NormalNeighborhood
open Set
 theorem affine_time_mem_convex {U : Set ℝ} (hU : Convex ℝ U)
    {s r T t : ℝ} (hs : s ∈ U) (hr : r ∈ U) (hT : 0 < T) (ht : t ∈ Icc (0 : ℝ) T) :
    s + (r - s) / T * t ∈ U := by
  have hθ : t / T ≤ 1 := (div_le_one hT).mpr ht.2
  have h := hU hs hr (sub_nonneg.mpr hθ) (div_nonneg ht.1 hT.le)
    (show (1 - t / T) + t / T = 1 by ring)
  convert! h using 1
  simp only [smul_eq_mul]
  ring
end NormalNeighborhood
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_NormalAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter CoordinateGeometry
open scoped Topology ContDiff
namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

 def action (N : NormalFlow G S x₀) (q : E × E) : ℝ := N.time^2/2 * G q.1 q.2 q.2

end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_EndpointAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter CoordinateGeometry
open scoped Topology ContDiff
namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

 def endpointAction (N : NormalFlow G S x₀) (q : E × E) : ℝ := N.action (N.normal.symm q)

end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_NormalFlowLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry RadialCoordinates
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

theorem normalAt_zero (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} (hx : (0 : E) ∈ (N.normalAt x).source) : N.normalAt x 0 = x := by
  have he := FlowLinearization.equilibrium N.domain_open
    (N.flow_smooth.of_le (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top))
    (hS.prod isOpen_univ) ((contDiffOn_geodesicSpray hS hG hpos).of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top))
    N.initial (fun q hq => ⟨⟨(N.ode q hq).1, mem_univ _⟩, (N.ode q hq).2⟩)
    (x := (x, 0)) ⟨N.base_mem hx, mem_univ _⟩ (geodesicSpray_zero G x)
    N.time_pos.le (N.source_stays (x, 0) hx)
  rw [N.normalAt_apply, he N.time ⟨N.time_pos.le, le_rfl⟩]

omit [FiniteDimensional ℝ E] in
theorem flow_curve_smooth (N : NormalFlow G S x₀) {x v : E}
    (hv : v ∈ (N.normalAt x).source) :
    ContDiffOn ℝ ∞ (fun t => (N.flow (t, (x, v))).1) (Icc (0 : ℝ) N.time) :=
  (N.flow_smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn
    (N.source_stays (x, v) hv)).fst

theorem flow_curve_length (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ z ∈ S, ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x v : E} (hv : v ∈ (N.normalAt x).source) :
    coordinateLength G (fun t => (N.flow (t, (x, v))).1) 0 N.time =
      ENNReal.ofReal (N.time * Real.sqrt (G x v v)) := by
  have hseg := N.source_stays (x, v) hv
  have h0 := N.initial (x, v) (hseg 0 ⟨le_rfl, N.time_pos.le⟩)
  have hE := geodesic_energy_constant hS (hG.differentiableOn (by simp)) hsym hpos
    (fun t ht => (N.ode _ (hseg t ht)).1)
    (fun t ht => (N.ode _ (hseg t ht)).2.fst)
    (fun t ht => (N.ode _ (hseg t ht)).2.snd)
  rw [coordinateLength]
  have heq : (∫⁻ t in Icc (0 : ℝ) N.time,
      ENNReal.ofReal (Real.sqrt (G (N.flow (t, (x, v))).1
        (deriv (fun s => (N.flow (s, (x, v))).1) t)
        (deriv (fun s => (N.flow (s, (x, v))).1) t)))) =
      ∫⁻ _t in Icc (0 : ℝ) N.time, ENNReal.ofReal (Real.sqrt (G x v v)) := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    have hd : HasDerivAt (fun s => (N.flow (s, (x, v))).1) (N.flow (t, (x, v))).2 t :=
      (N.ode _ (hseg t ht)).2.fst
    dsimp only
    rw [hd.deriv]
    change ENNReal.ofReal (Real.sqrt (G (N.flow (t, (x, v))).1
      (geodesicSpray G (N.flow (t, (x, v)))).1 (geodesicSpray G (N.flow (t, (x, v)))).1)) = _
    rw [hE t ht, h0]
    rfl
  rw [heq, lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
  simp only [sub_zero]
  rw [mul_comm, ← ENNReal.ofReal_mul N.time_pos.le]

end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_LocalDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter MeasureTheory Manifold Bundle
open scoped Topology ContDiff ENNReal Manifold

namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
open NormalNeighborhood NormalFlow ChartMetric
variable (x z : M) {y₀ : E}
variable (N : NormalFlow (metric x) (chartAt E x).target y₀)

def normalChart : OpenPartialHomeomorph E M :=
  (N.normalAt (chartAt E x z)).trans (chartAt E x).symm

omit [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)] in
@[simp] theorem normalChart_apply (v : E) : normalChart x z N v =
    (chartAt E x).symm (N.normalAt (chartAt E x z) v) := rfl

omit [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)] in
@[simp] theorem normalChart_source : (normalChart x z N).source = (N.normalAt (chartAt E x z)).source := by
  ext v
  constructor
  · exact fun hv => hv.1
  · exact fun hv => ⟨hv, N.normalAt_mem hv⟩

@[simp] theorem normalChart_zero (hz : z ∈ (chartAt E x).source)
    (hzero : (0 : E) ∈ (N.normalAt (chartAt E x z)).source) : normalChart x z N 0 = z := by
  rw [normalChart_apply, N.normalAt_zero (chartAt E x).open_target (metric_smooth x)
    (fun z hz v hv => metric_positive x hz hv) hzero]
  exact (chartAt E x).left_inv hz

theorem normalChart_target_center (hz : z ∈ (chartAt E x).source)
    (hzero : (0 : E) ∈ (N.normalAt (chartAt E x z)).source) :
    z ∈ (normalChart x z N).target := by
  have hm := (normalChart x z N).map_source
    (show (0 : E) ∈ (normalChart x z N).source by rw [normalChart_source]; exact hzero)
  simpa only [normalChart_zero x z N hz hzero] using hm

theorem edist_normalChart_le [IsRiemannianManifold 𝓘(ℝ, E) M]
    (hz : z ∈ (chartAt E x).source) {v : E} (hv : v ∈ (normalChart x z N).source) :
    edist z (normalChart x z N v) ≤
      ENNReal.ofReal (N.time * Real.sqrt (metric x (chartAt E x z) v v)) := by
  rw [normalChart_source] at hv
  let c : ℝ → E := fun t => (N.flow (t, (chartAt E x z, v))).1
  have hc : ContDiffOn ℝ 1 c (Icc (0 : ℝ) N.time) :=
    (N.flow_curve_smooth hv).of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top)
  have hct : ∀ t ∈ Icc (0 : ℝ) N.time, c t ∈ (chartAt E x).target :=
    fun t ht => (N.ode _ (N.source_stays (_, v) hv t ht)).1
  have hmc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 ((chartAt E x).symm ∘ c)
      (Icc (0 : ℝ) N.time) :=
    contMDiffOn_chart_symm.comp (contMDiffOn_iff_contDiffOn.mpr hc) hct
  have hfirst : ((chartAt E x).symm ∘ c) 0 = z := by
    simp only [Function.comp_apply, c, N.initial (_, v)
      (N.source_stays (_, v) hv 0 ⟨le_rfl, N.time_pos.le⟩)]
    exact (chartAt E x).left_inv hz
  have hlast : ((chartAt E x).symm ∘ c) N.time = normalChart x z N v := by
    rw [normalChart_apply, N.normalAt_apply]
    rfl
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, E))]
  have h := riemannianEDist_le_pathELength hmc hfirst hlast N.time_pos.le
  rw [← coordinateLength_eq_pathELength x hc hct] at h
  exact h.trans_eq (N.flow_curve_length (chartAt E x).open_target (metric_smooth x)
    (fun z _ => metric_symmetric x z) (fun z hz v hv => metric_positive x hz hv) hv)

theorem radial_path_length {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ (Icc a b))
    (ht : ∀ t ∈ Icc a b, γ t ∈ (normalChart x z N).target) :
    ‖N.time * Real.sqrt (metric x (chartAt E x z)
        ((normalChart x z N).symm (γ b)) ((normalChart x z N).symm (γ b))) -
      N.time * Real.sqrt (metric x (chartAt E x z)
        ((normalChart x z N).symm (γ a)) ((normalChart x z N).symm (γ a)))‖ₑ ≤
      pathELength 𝓘(ℝ, E) γ a b := by
  let c : ℝ → E := (chartAt E x) ∘ γ
  have hct : ∀ t ∈ Icc a b, γ t ∈ (chartAt E x).source := fun t ht' => (ht t ht').1
  have hcn : ∀ t ∈ Icc a b, c t ∈ (N.normalAt (chartAt E x z)).target :=
    fun t ht' => (ht t ht').2
  have hc : ContDiffOn ℝ 1 c (Icc a b) :=
    contMDiffOn_iff_contDiffOn.mp (contMDiffOn_chart.comp hγ hct)
  have h := N.radial_length (chartAt E x).open_target (metric_smooth x)
    (fun z _ => metric_symmetric x z) (fun z hz v hv => metric_positive x hz hv) hab hc hcn
  rw [coordinateLength_eq_pathELength x hc
    (fun t ht' => (chartAt E x).map_source (hct t ht'))] at h
  have heq : pathELength 𝓘(ℝ, E) ((chartAt E x).symm ∘ c) a b =
      pathELength 𝓘(ℝ, E) γ a b :=
    pathELength_congr (fun t ht' => (chartAt E x).left_inv (hct t ht'))
  rw [heq] at h
  exact h

theorem normal_distance_of_ball [IsRiemannianManifold 𝓘(ℝ, E) M]
    (hz : z ∈ (chartAt E x).source)
    (hzero : (0 : E) ∈ (N.normalAt (chartAt E x z)).source)
    {r : ℝ} (hr : 0 < r) (hrs : Metric.ball z r ⊆ (normalChart x z N).target)
    {v : E} (hv : v ∈ (normalChart x z N).source)
    (hvr : N.time * Real.sqrt (metric x (chartAt E x z) v v) < r) :
    dist z (normalChart x z N v) = N.time * Real.sqrt (metric x (chartAt E x z) v v) := by
  let R : ℝ := N.time * Real.sqrt (metric x (chartAt E x z) v v)
  have hR : 0 ≤ R := mul_nonneg N.time_pos.le (Real.sqrt_nonneg _)
  have hu : dist z (normalChart x z N v) ≤ R := by
    have h := edist_normalChart_le x z N hz hv
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hR] at h
    exact h
  apply le_antisymm hu
  by_contra hn
  have hlt : dist z (normalChart x z N v) < R := lt_of_not_ge hn
  have hRpos : 0 < R := lt_of_le_of_lt dist_nonneg hlt
  have he : riemannianEDist 𝓘(ℝ, E) z (normalChart x z N v) < ENNReal.ofReal R := by
    rw [← IsRiemannianManifold.out, edist_dist, ENNReal.ofReal_lt_ofReal_iff hRpos]
    exact hlt
  obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt he zero_lt_one
  have ht : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (normalChart x z N).target := by
    intro t ht'
    apply hrs
    rw [Metric.mem_ball, dist_comm]
    have hp := riemannianEDist_le_pathELength (hγ.contMDiffOn :
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ (Icc (0 : ℝ) t)) h0 rfl ht'.1
    rw [← IsRiemannianManifold.out] at hp
    have hb := hp.trans (pathELength_mono (I := 𝓘(ℝ, E)) (γ := γ) le_rfl ht'.2)
    have hd : edist z (γ t) < ENNReal.ofReal r :=
      (hb.trans_lt hlen).trans_le (ENNReal.ofReal_le_ofReal hvr.le)
    rwa [edist_dist, ENNReal.ofReal_lt_ofReal_iff hr] at hd
  have hl := radial_path_length x z N zero_le_one hγ.contMDiffOn ht
  rw [h0, h1, (normalChart x z N).left_inv hv] at hl
  have hi : (normalChart x z N).symm z = 0 := by
    have hm := (normalChart x z N).left_inv
      (show (0 : E) ∈ (normalChart x z N).source by rw [normalChart_source]; exact hzero)
    simpa only [normalChart_zero x z N hz hzero] using hm
  rw [hi] at hl
  simp only [map_zero, Real.sqrt_zero, mul_zero, sub_zero] at hl
  have hnR : ‖R‖ₑ = ENNReal.ofReal R := by rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hR]
  change ‖R‖ₑ ≤ _ at hl
  rw [hnR] at hl
  exact not_lt_of_ge hl hlen

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_NormalDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff

namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

theorem normalAt_hasFDerivAt_zero (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} (hx : (0 : E) ∈ (N.normalAt x).source) :
    HasFDerivAt (N.normalAt x) (N.time • ContinuousLinearMap.id ℝ E) 0 := by
  have hd := NormalCoordinates.hasFDerivAt_flow_zero hS hG hpos N.domain_open
    N.flow_smooth N.initial N.ode (N.base_mem hx) N.time_pos.le (N.source_stays (x, 0) hx)
  have he := hd.comp (0 : E) ((hasFDerivAt_const x (0 : E)).prodMk (hasFDerivAt_id (0 : E)))
  convert! he.fst using 1
  · ext v
    exact N.normalAt_apply x v
  · ext v
    simp

def timeEquiv (N : NormalFlow G S x₀) : E ≃L[ℝ] E :=
  { LinearEquiv.smulOfNeZero ℝ E N.time N.time_pos.ne' with
    continuous_toFun := continuous_const_smul N.time
    continuous_invFun := continuous_const_smul N.time⁻¹ }

omit [FiniteDimensional ℝ E] in
@[simp] theorem timeEquiv_coe (N : NormalFlow G S x₀) :
    (N.timeEquiv : E →L[ℝ] E) = N.time • ContinuousLinearMap.id ℝ E := by
  ext v
  rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem timeEquiv_symm_coe (N : NormalFlow G S x₀) :
    (N.timeEquiv.symm : E →L[ℝ] E) = N.time⁻¹ • ContinuousLinearMap.id ℝ E := by
  ext v
  rfl

 theorem normalAt_inverse_hasFDerivAt_center (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} (hx : (0 : E) ∈ (N.normalAt x).source) :
    HasFDerivAt (N.normalAt x).symm (N.time⁻¹ • ContinuousLinearMap.id ℝ E) x := by
  have he := N.normalAt_zero hS hG hpos hx
  have hmem : x ∈ (N.normalAt x).target := by
    simpa only [he] using (N.normalAt x).map_source hx
  have hi : (N.normalAt x).symm x = 0 := by
    simpa only [he] using (N.normalAt x).left_inv hx
  have hd : HasFDerivAt (N.normalAt x) (N.timeEquiv : E →L[ℝ] E) ((N.normalAt x).symm x) := by
    rw [hi, timeEquiv_coe]
    exact N.normalAt_hasFDerivAt_zero hS hG hpos hx
  simpa only [timeEquiv_symm_coe] using (N.normalAt x).hasFDerivAt_symm hmem hd

end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_NormalMetricSpeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold

namespace CoordinateGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem quadratic_speed_eq {B : MetricTensor E} {v : ℝ → E} {w : E} {a K : ℝ}
    (hd : HasDerivAt v w a) (hzero : v a = 0)
    (he : ∀ᶠ t in 𝓝 a, B (v t) (v t) = K * (t - a) ^ 2) : B w w = K := by
  have hc : Continuous (fun z : E => B z z) := B.continuous.clm_apply continuous_id
  have hl := hc.continuousAt.tendsto.comp hd.tendsto_slope
  have he' : (fun t => B (slope v a t) (slope v a t)) =ᶠ[𝓝[≠] a] (fun _ => K) := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hta
    have hne : t - a ≠ 0 := sub_ne_zero.mpr hta
    simp only [slope, hzero, vsub_eq_sub, sub_zero, map_smul, smul_apply, smul_eq_mul]
    rw [ht]
    field_simp
  exact tendsto_nhds_unique hl (tendsto_const_nhds.congr' he'.symm)
end
end CoordinateGeometry

namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry

 theorem eventually_dist_normal (x z : M) {y₀ : E}
    (N : NormalFlow (metric x) (chartAt E x).target y₀)
    (hz : z ∈ (chartAt E x).source)
    (hzero : (0 : E) ∈ (N.normalAt (chartAt E x z)).source) :
    ∀ᶠ y in 𝓝 z, dist z y = N.time * Real.sqrt (metric x (chartAt E x z)
      ((normalChart x z N).symm y) ((normalChart x z N).symm y)) := by
  let e := normalChart x z N
  have hz' : z ∈ e.target := normalChart_target_center x z N hz hzero
  have hi : e.symm z = 0 := by
    have h := e.left_inv (show (0 : E) ∈ e.source by rw [normalChart_source]; exact hzero)
    change (normalChart x z N).symm (normalChart x z N 0) = 0 at h
    rwa [normalChart_zero x z N hz hzero] at h
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hz')
  have hc : ContinuousAt (fun y => N.time * Real.sqrt (metric x (chartAt E x z)
      (e.symm y) (e.symm y))) z :=
    continuousAt_const.mul ((continuousAt_const.clm_apply
      (e.symm.continuousAt hz')).clm_apply (e.symm.continuousAt hz')).sqrt
  have hsmall : ∀ᶠ y in 𝓝 z, N.time * Real.sqrt (metric x (chartAt E x z)
      (e.symm y) (e.symm y)) < r := by
    apply hc.eventually_lt_const
    simpa [hi] using hr
  filter_upwards [e.open_target.mem_nhds hz', hsmall] with y hy hys
  have he := normal_distance_of_ball x z N hz hzero hr hrs (e.map_target hy) hys
  change dist z (e (e.symm y)) = _ at he
  rw [e.right_inv hy] at he
  exact he

 theorem coordinate_speed_of_local_distance (x : M) {c : ℝ → E} {a C : ℝ} {w : E}
    (hc : HasDerivAt c w a) (hct : c a ∈ (chartAt E x).target)
    (hC : 0 ≤ C)
    (he : ∀ᶠ t in 𝓝 a,
      dist ((chartAt E x).symm (c a)) ((chartAt E x).symm (c t)) = C * |t - a|) :
    metric x (c a) w w = C ^ 2 := by
  let z := (chartAt E x).symm (c a)
  have hz : z ∈ (chartAt E x).source := (chartAt E x).map_target hct
  have hcz : chartAt E x z = c a := (chartAt E x).right_inv hct
  obtain ⟨N⟩ := exists_normalFlow (chartAt E x).open_target (metric_smooth x)
    (fun z hz v hv => metric_positive x hz hv) hct
  have hzero : (0 : E) ∈ (N.normalAt (c a)).source := N.center_mem
  let ν : ℝ → E := fun t => (N.normalAt (c a)).symm (c t)
  have hνd : HasDerivAt ν (N.time⁻¹ • w) a := by
    simpa only [ν, Function.comp_def, smul_apply, ContinuousLinearMap.id_apply] using
      (N.normalAt_inverse_hasFDerivAt_center (chartAt E x).open_target (metric_smooth x)
        (fun z hz v hv => metric_positive x hz hv) hzero).comp_hasDerivAt a hc
  have hν₀ : ν a = 0 := by
    have h := (N.normalAt (c a)).left_inv hzero
    simpa only [N.normalAt_zero (chartAt E x).open_target (metric_smooth x)
      (fun z hz v hv => metric_positive x hz hv) hzero] using h
  have hγc : ContinuousAt (fun t => (chartAt E x).symm (c t)) a :=
    ((chartAt E x).symm.continuousAt hct).comp hc.continuousAt
  have hn := hγc (eventually_dist_normal x z N hz (by simpa only [hcz] using hzero))
  have heq : ∀ᶠ t in 𝓝 a, metric x (c a) (ν t) (ν t) =
      (C / N.time) ^ 2 * (t - a) ^ 2 := by
    filter_upwards [he, hn, hc.continuousAt.preimage_mem_nhds
      ((chartAt E x).open_target.mem_nhds hct)] with t het hnt ht
    have hpos : 0 ≤ metric x (c a) (ν t) (ν t) := by
      by_cases hv : ν t = 0
      · simp [hv]
      · exact (metric_positive x hct hv).le
    change dist z ((chartAt E x).symm (c t)) = _ at het
    change dist z ((chartAt E x).symm (c t)) = N.time *
      Real.sqrt (metric x (chartAt E x z)
        ((N.normalAt (chartAt E x z)).symm (chartAt E x ((chartAt E x).symm (c t))))
        ((N.normalAt (chartAt E x z)).symm (chartAt E x ((chartAt E x).symm (c t))))) at hnt
    rw [hcz, (chartAt E x).right_inv ht] at hnt
    have hh : Real.sqrt (metric x (c a) (ν t) (ν t)) = C * |t - a| / N.time := by
      apply (eq_div_iff N.time_pos.ne').mpr
      nlinarith [het, hnt]
    have hs := (Real.sqrt_eq_iff_eq_sq hpos
      (div_nonneg (mul_nonneg hC (abs_nonneg _)) N.time_pos.le)).mp hh
    rw [hs]
    simp only [div_pow, mul_pow, sq_abs]
    ring
  have hq := quadratic_speed_eq hνd hν₀ heq
  simp only [map_smul, smul_apply, smul_eq_mul] at hq
  have hT := N.time_pos.ne'
  field_simp at hq
  nlinarith
end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_RadialRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace RadialRigidity
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry

omit [FiniteDimensional ℝ E] in
 theorem eq_endpoints_of_deriv_zero {f : ℝ → E} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ t ∈ Ioo a b, HasDerivAt f 0 t) : f a = f b := by
  obtain ⟨k, hk⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv)
  have hkc : EqOn f (fun _ => k) (Icc a b) :=
    (show EqOn f (fun _ => k) (Ioo a b) from hk).of_subset_closure hc continuousOn_const
      Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])
  exact (hkc ⟨le_rfl, hab.le⟩).trans (hkc ⟨hab.le, le_rfl⟩).symm

omit [FiniteDimensional ℝ E] in
 theorem radial_linear {U : Set ℝ} (hU : IsOpen U) (hUc : Convex ℝ U)
    {ν ν' : ℝ → E} {a : ℝ} (ha : a ∈ U) (hzero : ν a = 0)
    (hd : ∀ t ∈ U, HasDerivAt ν (ν' t) t)
    (hr : ∀ t ∈ U, (t - a) • ν' t = ν t) :
    ∀ t ∈ U, ν t = (t - a) • ν' a := by
  let f := dslope ν a
  have hfc : ContinuousOn f U := (continuousOn_dslope (hU.mem_nhds ha)).mpr
    ⟨fun t ht => (hd t ht).continuousAt.continuousWithinAt, (hd a ha).differentiableAt⟩
  have hfd : ∀ t ∈ U, t ≠ a → HasDerivAt f 0 t := by
    intro t ht hta
    have hne : t - a ≠ 0 := sub_ne_zero.mpr hta
    have hd' := (((hasDerivAt_id t).sub_const a).inv hne).smul ((hd t ht).sub_const (ν a))
    have hh : -(1 / (t - a) ^ 2) • (ν t - ν a) + (t - a)⁻¹ • ν' t = 0 := by
      rw [hzero, sub_zero, ← hr t ht, smul_smul, ← add_smul]
      have he : -(1 / (t - a) ^ 2) * (t - a) + (t - a)⁻¹ = 0 := by field_simp; ring
      rw [he, zero_smul]
    have hg : HasDerivAt (slope ν a) 0 t := by
      convert! hd' using 1
      simpa only [id_eq, Pi.inv_apply, neg_div, add_comm] using hh.symm
    exact hg.congr_of_eventuallyEq (dslope_eventuallyEq_slope_of_ne ν hta)
  intro t ht
  have halte : Icc (min a t) (max a t) ⊆ U := by
    exact hUc.ordConnected.uIcc_subset ha ht
  have hfa : f a = ν' a := (dslope_same ν a).trans (hd a ha).deriv
  have hft : f t = f a := by
    rcases lt_trichotomy a t with hat | hat | hat
    · apply (eq_endpoints_of_deriv_zero hat (hfc.mono (by simpa [min_eq_left hat.le, max_eq_right hat.le] using halte)) ?_).symm
      intro s hs
      exact hfd s (halte (by simpa [min_eq_left hat.le, max_eq_right hat.le] using (show s ∈ Icc _ _ from ⟨hs.1.le, hs.2.le⟩))) (ne_of_gt hs.1)
    · rw [hat]
    · apply eq_endpoints_of_deriv_zero hat (hfc.mono (by simpa [min_eq_right hat.le, max_eq_left hat.le] using halte))
      intro s hs
      exact hfd s (halte (by simpa [min_eq_right hat.le, max_eq_left hat.le] using (show s ∈ Icc _ _ from ⟨hs.1.le, hs.2.le⟩))) (ne_of_lt hs.2)
  rw [← sub_smul_dslope_of_zero hzero t, ← hfa]
  exact congrArg ((t - a) • ·) hft

omit [FiniteDimensional ℝ E] in
 theorem gauss_equality {B₀ B₁ : MetricTensor E} {L : E →L[ℝ] E}
    (hs : ∀ v w, B₁ v w = B₁ w v)
    (hp : ∀ v : E, v ≠ 0 → 0 < B₁ v v)
    (hL : Function.Injective L) {v w : E} {T C θ : ℝ}
    (hg : ∀ u, B₁ (L v) (L u) = T ^ 2 * B₀ v u)
    (hr : T ^ 2 * B₀ v v = C ^ 2 * θ ^ 2)
    (hdr : T ^ 2 * B₀ v w = C ^ 2 * θ)
    (hsp : B₁ (L w) (L w) = C ^ 2) : θ • w = v := by
  have he : B₁ (θ • L w - L v) (θ • L w - L v) = 0 := by
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
    rw [hs (L w) (L v), hg w, hg v, hsp, hdr, hr]
    ring
  have hz : θ • L w - L v = 0 := by
    by_contra hn
    have h := hp _ hn
    rw [he] at h
    exact lt_irrefl _ h
  apply hL
  rw [map_smul]
  exact sub_eq_zero.mp hz
end
end RadialRigidity
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_NormalRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

omit [FiniteDimensional ℝ E] in
 theorem normalAt_fderiv_injective (N : NormalFlow G S x₀) {x v : E}
    (hv : v ∈ (N.normalAt x).source) : Function.Injective (fderiv ℝ (N.normalAt x) v) := by
  let e := N.normalAt x
  have he := ((N.normalAt_smooth x v hv).contDiffAt (e.open_source.mem_nhds hv)).differentiableAt (by simp)
  have hi := ((N.normalAt_inverse_smooth x (e v) (e.map_source hv)).contDiffAt
    (e.open_target.mem_nhds (e.map_source hv))).differentiableAt (by simp)
  have hcomp := hi.hasFDerivAt.comp v he.hasFDerivAt
  have hh : HasFDerivAt (fun w : E => w) ((fderiv ℝ e.symm (e v)).comp (fderiv ℝ e v)) v := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hv] with w hw
    exact (e.left_inv hw).symm
  have hid := hh.unique (hasFDerivAt_id v)
  apply Function.LeftInverse.injective (f := fderiv ℝ e v) (g := fderiv ℝ e.symm (e v))
  intro w
  exact congrArg (fun A : E →L[ℝ] E => A w) hid

 theorem normal_radial_curve (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ z ∈ S, ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} (hzero : (0 : E) ∈ (N.normalAt x).source)
    {U : Set ℝ} (hU : IsOpen U) (hUc : Convex ℝ U)
    {c : ℝ → E} (hc : DifferentiableOn ℝ c U)
    (hct : ∀ t ∈ U, c t ∈ (N.normalAt x).target)
    {a C : ℝ} (ha : a ∈ U) (hca : c a = x)
    (hsp : ∀ t ∈ U, G (c t) (deriv c t) (deriv c t) = C ^ 2)
    (hr : ∀ t ∈ U, N.time ^ 2 * G x ((N.normalAt x).symm (c t))
      ((N.normalAt x).symm (c t)) = C ^ 2 * (t - a) ^ 2) :
    ∀ t ∈ U, c t = N.normalAt x (((t - a) / N.time) • deriv c a) := by
  let e := N.normalAt x
  let ν : ℝ → E := fun t => e.symm (c t)
  have hc' : ∀ t ∈ U, HasDerivAt c (deriv c t) t :=
    fun t ht => ((hc t ht).differentiableAt (hU.mem_nhds ht)).hasDerivAt
  have hνd : ∀ t ∈ U, DifferentiableAt ℝ ν t := by
    intro t ht
    exact (((N.normalAt_inverse_smooth x (c t) (hct t ht)).contDiffAt
      (e.open_target.mem_nhds (hct t ht))).differentiableAt (by simp)).comp t (hc' t ht).differentiableAt
  have hνt : ∀ t ∈ U, ν t ∈ e.source := fun t ht => e.map_target (hct t ht)
  have hν₀ : ν a = 0 := by
    dsimp only [ν]
    rw [hca]
    have hz := N.normalAt_zero hS hG hpos hzero
    have hh := e.left_inv hzero
    change (N.normalAt x).symm (N.normalAt x 0) = 0 at hh
    rwa [hz] at hh
  have hνa : deriv ν a = N.time⁻¹ • deriv c a := by
    have hh := (N.normalAt_inverse_hasFDerivAt_center hS hG hpos hzero)
    have hd := (show HasFDerivAt e.symm (N.time⁻¹ • ContinuousLinearMap.id ℝ E) (c a) by
      rw [hca]; exact hh).comp_hasDerivAt a (hc' a ha)
    exact hd.deriv
  have hrad : ∀ t ∈ U, (t - a) • deriv ν t = ν t := by
    intro t ht
    have hv := hνt t ht
    have hx := N.base_mem hzero
    have heq : e (ν t) = c t := e.right_inv (hct t ht)
    have he := ((N.normalAt_smooth x (ν t) hv).contDiffAt (e.open_source.mem_nhds hv)).differentiableAt (by simp)
    have hcd : deriv c t = fderiv ℝ e (ν t) (deriv ν t) := by
      have hh := he.hasFDerivAt.comp_hasDerivAt t (hνd t ht).hasDerivAt
      have hh' : HasDerivAt c (fderiv ℝ e (ν t) (deriv ν t)) t := by
        apply hh.congr_of_eventuallyEq
        filter_upwards [hU.mem_nhds ht] with s hs
        exact (e.right_inv (hct s hs)).symm
      exact hh'.deriv
    have hq := ((G x).hasFDerivAt.comp_hasDerivAt t (hνd t ht).hasDerivAt).clm_apply
      (hνd t ht).hasDerivAt
    have hq' := hq.const_mul (N.time ^ 2)
    have hp := (((hasDerivAt_id t).sub_const a).pow 2).const_mul (C ^ 2)
    have hh : N.time ^ 2 * (G x (deriv ν t) (ν t) + G x (ν t) (deriv ν t)) =
        C ^ 2 * (2 * (t - a)) := by
      have hq'' : HasDerivAt (fun s => C ^ 2 * (s - a) ^ 2)
          (N.time ^ 2 * (G x (deriv ν t) (ν t) + G x (ν t) (deriv ν t))) t := by
        apply hq'.congr_of_eventuallyEq
        filter_upwards [hU.mem_nhds ht] with s hs
        exact (hr s hs).symm
      simpa using hq''.unique hp
    rw [hsym x hx (deriv ν t) (ν t)] at hh
    have hrd : N.time ^ 2 * G x (ν t) (deriv ν t) = C ^ 2 * (t - a) := by linarith
    apply RadialRigidity.gauss_equality (B₀ := G x) (B₁ := G (e (ν t)))
      (L := fderiv ℝ e (ν t)) (T := N.time) (C := C)
      (hsym _ (N.normalAt_mem hv)) (hpos _ (N.normalAt_mem hv))
      (N.normalAt_fderiv_injective hv)
      (fun w => N.normalAt_gauss hS hG hsym hpos hv w) (hr t ht) hrd
    rw [heq, ← hcd]
    exact hsp t ht
  have hlin := RadialRigidity.radial_linear hU hUc ha hν₀
    (fun t ht => (hνd t ht).hasDerivAt) hrad
  intro t ht
  have hh := e.right_inv (hct t ht)
  change e (ν t) = c t at hh
  rw [hlin t ht, hνa, smul_smul] at hh
  simpa only [div_eq_mul_inv] using hh.symm
end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_IntrinsicNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry

 theorem intrinsic_curve_normal (x : M) {U : Set ℝ} (hU : IsOpen U)
    {c : ℝ → E} (hc : ContDiffOn ℝ ∞ c U)
    (hct : ∀ t ∈ U, c t ∈ (chartAt E x).target)
    {a C : ℝ} (ha : a ∈ U) (hC : 0 ≤ C)
    (hdist : ∀ s ∈ U, ∀ t ∈ U,
      dist ((chartAt E x).symm (c s)) ((chartAt E x).symm (c t)) = C * |s - t|)
    {y₀ : E} (N : NormalFlow (metric x) (chartAt E x).target y₀)
    (hzero : (0 : E) ∈ (N.normalAt (c a)).source) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball a δ ⊆ U ∧
      ∀ t ∈ Metric.ball a δ, c t = N.normalAt (c a) (((t - a) / N.time) • deriv c a) := by
  let e := chartAt E x
  let z := e.symm (c a)
  have hz : z ∈ e.source := e.map_target (hct a ha)
  have hcz : e z = c a := e.right_inv (hct a ha)
  have hca := (hc a ha).contDiffAt (hU.mem_nhds ha)
  have hγc : ContinuousAt (fun t => e.symm (c t)) a :=
    (e.symm.continuousAt (hct a ha)).comp hca.continuousAt
  have hn := hγc (eventually_dist_normal x z N hz (by
    change (0 : E) ∈ (N.normalAt (e z)).source
    rw [hcz]
    exact hzero))
  have hNcenter : c a ∈ (N.normalAt (c a)).target := by
    simpa only [N.normalAt_zero e.open_target (metric_smooth x)
      (fun z hz v hv => metric_positive x hz hv) hzero] using
        (N.normalAt (c a)).map_source hzero
  have hNt := hca.continuousAt.preimage_mem_nhds
    ((N.normalAt (c a)).open_target.mem_nhds hNcenter)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds ha) (inter_mem hNt hn))
  have hsub : Metric.ball a δ ⊆ U := fun t ht => (hδs ht).1
  have hnt : ∀ t ∈ Metric.ball a δ, c t ∈ (N.normalAt (c a)).target :=
    fun t ht => (hδs ht).2.1
  have hsp : ∀ t ∈ Metric.ball a δ,
      metric x (c t) (deriv c t) (deriv c t) = C ^ 2 := by
    intro t ht
    apply coordinate_speed_of_local_distance x
      (((hc t (hsub ht)).contDiffAt (hU.mem_nhds (hsub ht))).differentiableAt (by simp)).hasDerivAt
      (hct t (hsub ht)) hC
    filter_upwards [hU.mem_nhds (hsub ht)] with r hr
    rw [hdist t (hsub ht) r hr, abs_sub_comm t r]
  have hr : ∀ t ∈ Metric.ball a δ, N.time ^ 2 * metric x (c a)
      ((N.normalAt (c a)).symm (c t)) ((N.normalAt (c a)).symm (c t)) =
      C ^ 2 * (t - a) ^ 2 := by
    intro t ht
    have hd := (hδs ht).2.2
    change dist z (e.symm (c t)) = N.time * Real.sqrt (metric x (e z)
      ((N.normalAt (e z)).symm (e (e.symm (c t))))
      ((N.normalAt (e z)).symm (e (e.symm (c t))))) at hd
    rw [hcz, e.right_inv (hct t (hsub ht))] at hd
    have heq := hdist a ha t (hsub ht)
    change dist z (e.symm (c t)) = C * |a - t| at heq
    rw [heq] at hd
    have hh := congrArg (fun r : ℝ => r ^ 2) hd
    rw [mul_pow, mul_pow, Real.sq_sqrt (RadialCoordinates.metric_nonneg
      (fun v hv => metric_positive x (hct a ha) hv) _), sq_abs] at hh
    simpa only [sub_sq_comm a t] using hh.symm
  refine ⟨δ, hδ, hsub, ?_⟩
  exact N.normal_radial_curve e.open_target (metric_smooth x)
    (fun y _ => metric_symmetric x y) (fun y hy v hv => metric_positive x hy hv) hzero
    Metric.isOpen_ball (convex_ball a δ) ((hc.mono hsub).differentiableOn (by simp)) hnt
    (Metric.mem_ball_self hδ) rfl hsp hr
end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_NormalCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff

namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry GeodesicScaling
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

theorem normal_rescaled_curve (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {q : ℝ → E × E} {a b : ℝ}
    (hq : ∀ t ∈ Icc (0 : ℝ) N.time, (q (a + b * t)).1 ∈ S ∧
      HasDerivAt q (geodesicSpray G (q (a + b * t))) (a + b * t))
    (hv : b • (q a).2 ∈ (N.normalAt (q a).1).source) :
    N.normalAt (q a).1 (b • (q a).2) = (q (a + b * N.time)).1 := by
  let u : ℝ → E × E := fun t => N.flow (t, scalePhase b (q a))
  let v : ℝ → E × E := fun t => scalePhase b (q (a + b * t))
  have hseg := N.source_stays ((q a).1, b • (q a).2) hv
  have hdu : ∀ t ∈ Icc (0 : ℝ) N.time, HasDerivAt u (geodesicSpray G (u t)) t :=
    fun t ht => (N.ode _ (hseg t ht)).2
  have hdv : ∀ t ∈ Icc (0 : ℝ) N.time, HasDerivAt v (geodesicSpray G (v t)) t := by
    intro t ht
    have hd := (hq t ht).2.scomp t (((hasDerivAt_id t).const_mul b).const_add a)
    have he := (scalePhase b).hasFDerivAt.comp_hasDerivAt t hd
    simpa only [mul_one, scale_spray, Function.comp_def, id_eq, v] using he
  have hf : ∀ z ∈ u '' Icc (0 : ℝ) N.time ∪ v '' Icc (0 : ℝ) N.time,
      ContDiffAt ℝ 1 (geodesicSpray G) z := by
    intro z hz
    have hzS : z.1 ∈ S := by
      rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · exact (N.ode _ (hseg t ht)).1
      · exact (hq t ht).1
    exact (((contDiffOn_geodesicSpray hS hG hpos) z ⟨hzS, mem_univ _⟩).contDiffAt
      ((hS.prod isOpen_univ).mem_nhds ⟨hzS, mem_univ _⟩)).of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top)
  have hzero : u 0 = v 0 := by
    dsimp [u, v]
    rw [N.initial _ (hseg 0 ⟨le_rfl, N.time_pos.le⟩)]
    simp
  have he := FlowLinearization.unique_Icc
    (fun t ht => (hdu t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hdv t ht).continuousAt.continuousWithinAt) hf
    (fun t ht => (hdu t ht).hasDerivWithinAt)
    (fun t ht => (hdv t ht).hasDerivWithinAt) hzero ⟨N.time_pos.le, le_rfl⟩
  rw [normalAt_apply]
  have he' := congrArg (fun p : E × E => p.1) he
  exact he'

end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_IntrinsicUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry

 theorem coordinate_germ_unique (x : M) {U : Set ℝ} (hU : IsOpen U)
    {c d : ℝ → E} (hc : ContDiffOn ℝ ∞ c U) (hd : ContDiffOn ℝ ∞ d U)
    (hct : ∀ t ∈ U, c t ∈ (chartAt E x).target)
    (hdt : ∀ t ∈ U, d t ∈ (chartAt E x).target)
    {a C D : ℝ} (ha : a ∈ U) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcDist : ∀ s ∈ U, ∀ t ∈ U,
      dist ((chartAt E x).symm (c s)) ((chartAt E x).symm (c t)) = C * |s - t|)
    (hdDist : ∀ s ∈ U, ∀ t ∈ U,
      dist ((chartAt E x).symm (d s)) ((chartAt E x).symm (d t)) = D * |s - t|)
    (he : c a = d a) (he' : deriv c a = deriv d a) : c =ᶠ[𝓝 a] d := by
  obtain ⟨N⟩ := exists_normalFlow (chartAt E x).open_target (metric_smooth x)
    (fun z hz v hv => metric_positive x hz hv) (hct a ha)
  obtain ⟨δ, hδ, _, hδs⟩ := intrinsic_curve_normal x hU hc hct ha hC hcDist N N.center_mem
  obtain ⟨ε, hε, _, hεs⟩ := intrinsic_curve_normal x hU hd hdt ha hD hdDist N
    (by rw [← he]; exact N.center_mem)
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ),
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)] with t htδ htε
  rw [hδs t htδ, hεs t htε, ← he, he']

section
omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

def curveState (γ : ℝ → M) (t : ℝ) : TangentBundle 𝓘(ℝ, E) M :=
  ⟨γ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)⟩

end

end
end RiemannianLocal

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_IntrinsicOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry

section
omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

def IsIntrinsicGeodesicOn (γ : ℝ → M) (C : ℝ) (U : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ U ∧
  ∀ t ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball t ε, ∀ r ∈ Metric.ball t ε,
    dist (γ s) (γ r) = C * |s - r|

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
 theorem IsIntrinsicGeodesicOn.mono {γ : ℝ → M} {C : ℝ} {U V : Set ℝ}
    (h : IsIntrinsicGeodesicOn (E := E) γ C U) (hVU : V ⊆ U) :
    IsIntrinsicGeodesicOn (E := E) γ C V :=
  ⟨h.1.mono hVU, fun t ht => h.2 t (hVU ht)⟩

end

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_UniformNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff ENNReal Manifold

namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
open NormalNeighborhood NormalFlow ChartMetric

 theorem uniform_normal_radius (x z₀ : M) (hz₀ : z₀ ∈ (chartAt E x).source)
    (N : NormalFlow (metric x) (chartAt E x).target (chartAt E x z₀)) :
    ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧ ∀ z ∈ Metric.ball z₀ ε,
      z ∈ (chartAt E x).source ∧
      (0 : E) ∈ (N.normalAt (chartAt E x z)).source ∧
      Metric.ball z r ⊆ (normalChart x z N).target := by
  let c := chartAt E x
  have hx : z₀ ∈ c.source := hz₀
  have hc : ContinuousAt c z₀ := c.continuousAt hx
  have hzero : N.normal (c z₀, 0) = (c z₀, c z₀) := by
    have hh := N.normalAt_zero c.open_target (metric_smooth x)
      (fun z hz v hv => metric_positive x hz hv) N.center_mem
    rw [N.normalAt_apply] at hh
    rw [N.normal_apply, hh]
  have hpair : (c z₀, c z₀) ∈ N.normal.target := by
    rw [← hzero]
    exact N.normal.map_source N.center_mem
  let A : Set M := c.source ∩ {z | (c z, (0 : E)) ∈ N.normal.source}
  have hA : A ∈ 𝓝 z₀ :=
    inter_mem (c.open_source.mem_nhds hx)
      ((hc.prodMk continuousAt_const).preimage_mem_nhds (N.normal.open_source.mem_nhds N.center_mem))
  let B : Set (M × M) := {q | q.1 ∈ c.source ∧ q.2 ∈ c.source ∧
    (c q.1, c q.2) ∈ N.normal.target}
  have hB : B ∈ 𝓝 (z₀, z₀) := by
    have h₁ : {q : M × M | q.1 ∈ c.source} ∈ 𝓝 (z₀, z₀) := continuousAt_fst.preimage_mem_nhds (c.open_source.mem_nhds hx)
    have h₂ : {q : M × M | q.2 ∈ c.source} ∈ 𝓝 (z₀, z₀) := continuousAt_snd.preimage_mem_nhds (c.open_source.mem_nhds hx)
    have hcc : ContinuousAt (fun q : M × M => (c q.1, c q.2)) (z₀, z₀) :=
      (hc.comp continuousAt_fst).prodMk (hc.comp continuousAt_snd)
    have h₃ := hcc.preimage_mem_nhds (N.normal.open_target.mem_nhds hpair)
    exact inter_mem h₁ (inter_mem h₂ h₃)
  obtain ⟨δ₁, hδ₁, hs₁⟩ := Metric.mem_nhds_iff.mp hA
  obtain ⟨δ₂, hδ₂, hs₂⟩ := Metric.mem_nhds_iff.mp hB
  refine ⟨min δ₁ (δ₂ / 3), δ₂ / 3, lt_min hδ₁ (by positivity), by positivity, ?_⟩
  intro z hz
  have hz₁ : dist z z₀ < δ₁ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz₂ : dist z z₀ < δ₂ / 3 := lt_of_lt_of_le hz (min_le_right _ _)
  have ha := hs₁ hz₁
  refine ⟨ha.1, ha.2, ?_⟩
  intro y hy
  have hp : (z, y) ∈ Metric.ball (z₀, z₀) δ₂ := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · change dist z z₀ < δ₂
      linarith
    · change dist y z₀ < δ₂
      have hd := dist_triangle y z z₀
      change dist y z < δ₂ / 3 at hy
      linarith
  have hb := hs₂ hp
  exact ⟨hb.2.1, hb.2.2⟩

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_LocalGeodesic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff ENNReal Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry

 theorem coordinate_geodesic_locally_minimizes (x : M)
    {U : Set ℝ} (hU : IsOpen U) {q : ℝ → E × E}
    (hqsm : ContDiffOn ℝ ∞ q U)
    (hq : ∀ t ∈ U, (q t).1 ∈ (chartAt E x).target ∧
      HasDerivAt q (geodesicSpray (metric x) (q t)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball t₀ δ ⊆ U ∧
      ∀ s ∈ Metric.ball t₀ δ, ∀ r ∈ Metric.ball t₀ δ,
        dist ((chartAt E x).symm (q s).1) ((chartAt E x).symm (q r).1) =
          Real.sqrt (metric x (q t₀).1 (q t₀).2 (q t₀).2) * |s - r| := by
  let c := chartAt E x
  let γ : ℝ → M := fun t => c.symm (q t).1
  let z₀ := γ t₀
  have hz₀ : z₀ ∈ c.source := c.map_target (hq t₀ ht₀).1
  have hcz₀ : c z₀ = (q t₀).1 := c.right_inv (hq t₀ ht₀).1
  obtain ⟨N⟩ := exists_normalFlow c.open_target (metric_smooth x)
    (fun z hz v hv => metric_positive x hz hv) (c.map_source hz₀)
  obtain ⟨ε, R, hε, hR, hballs⟩ := uniform_normal_radius x z₀ hz₀ N
  have hqc : ContinuousAt q t₀ := ((hqsm t₀ ht₀).contDiffAt (hU.mem_nhds ht₀)).continuousAt
  have hγc : ContinuousAt γ t₀ := ContinuousAt.comp
    (g := (c.symm : E → M)) (f := fun t : ℝ => (q t).1)
    (c.symm.continuousAt (hq t₀ ht₀).1) hqc.fst
  obtain ⟨δU, hδU, hδUs⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ht₀)
  obtain ⟨δγ, hδγ, hδγs⟩ := Metric.mem_nhds_iff.mp
    (hγc.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)))
  let F : ℝ × ℝ → E × E := fun p => ((q p.1).1, ((p.2 - p.1) / N.time) • (q p.1).2)
  have hFc : ContinuousAt F (t₀, t₀) := by
    have hq₁ := hqc.comp (continuousAt_fst : ContinuousAt (Prod.fst : ℝ × ℝ → ℝ) (t₀, t₀))
    exact hq₁.fst.prodMk (((continuousAt_snd.sub continuousAt_fst).div_const N.time).smul hq₁.snd)
  have hF₀ : F (t₀, t₀) ∈ N.normal.source := by simpa [F, hcz₀] using N.center_mem
  obtain ⟨δF, hδF, hδFs⟩ := Metric.mem_nhds_iff.mp
    (hFc.preimage_mem_nhds (N.normal.open_source.mem_nhds hF₀))
  let C : ℝ := Real.sqrt (metric x (q t₀).1 (q t₀).2 (q t₀).2)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  let δL : ℝ := R / (4 * (C + 1))
  have hδL : 0 < δL := div_pos hR (by positivity)
  have hδLC : δL * (4 * (C + 1)) = R := div_mul_cancel₀ _ (by positivity : 4 * (C + 1) ≠ 0)
  let δ := min δU (min δγ (min δF δL))
  have hδ : 0 < δ := lt_min hδU (lt_min hδγ (lt_min hδF hδL))
  have hsubU : Metric.ball t₀ δ ⊆ U :=
    (Metric.ball_subset_ball (show δ ≤ δU from min_le_left _ _)).trans hδUs
  refine ⟨δ, hδ, hsubU, ?_⟩
  intro s hs r hr
  have hsU := hsubU hs
  have hsδU : s ∈ Metric.ball t₀ δU :=
    (Metric.ball_subset_ball (show δ ≤ δU from min_le_left _ _)) hs
  have hγs : γ s ∈ Metric.ball z₀ ε :=
    hδγs ((Metric.ball_subset_ball
      (show δ ≤ δγ from (min_le_right _ _).trans (min_le_left _ _))) hs)
  obtain ⟨hcs, hzeros, hballss⟩ := hballs (γ s) hγs
  have hcγs : c (γ s) = (q s).1 := c.right_inv (hq s hsU).1
  have hp : (s, r) ∈ Metric.ball (t₀, t₀) δF := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨lt_of_lt_of_le hs ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))),
      lt_of_lt_of_le hr ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hFsr := hδFs hp
  let v : E := ((r - s) / N.time) • (q s).2
  have hv : v ∈ (N.normalAt (q s).1).source := hFsr
  have hvM : v ∈ (normalChart x (γ s) N).source := by
    rw [normalChart_source, hcγs]
    exact hv
  have hE : metric x (q s).1 (q s).2 (q s).2 = metric x (q t₀).1 (q t₀).2 (q t₀).2 :=
    geodesic_energy_on_connected c.open_target ((metric_smooth x).differentiableOn (by simp))
      (fun z _ => metric_symmetric x z) (fun z hz v hv => metric_positive x hz hv)
      Metric.isOpen_ball (convex_ball t₀ δU).isPreconnected
      (fun t ht => hq t (hδUs ht)) hsδU (Metric.mem_ball_self hδU)
  have hlen : N.time * Real.sqrt (metric x (c (γ s)) v v) = |r - s| * C := by
    rw [hcγs]
    dsimp only [v]
    rw [radial_scale_radius _ _ N.time_pos, hE]
  have hsmall : N.time * Real.sqrt (metric x (c (γ s)) v v) < R := by
    rw [hlen]
    have hsL : dist s t₀ < δL := lt_of_lt_of_le hs
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hrL : dist r t₀ < δL := lt_of_lt_of_le hr
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hd := dist_triangle r t₀ s
    rw [dist_comm t₀ s, Real.dist_eq] at hd
    have hmul : |r - s| * C ≤ (2 * δL) * C :=
      mul_le_mul_of_nonneg_right (by linarith) hC
    nlinarith
  have he := N.normal_rescaled_curve c.open_target (metric_smooth x)
    (fun z hz v hv => metric_positive x hz hv)
    (a := s) (b := (r - s) / N.time)
    (fun t ht => hq _ (hsubU (affine_time_mem_convex (convex_ball t₀ δ) hs hr N.time_pos ht))) hv
  have htend : s + (r - s) / N.time * N.time = r := by
    rw [div_mul_cancel₀ _ N.time_pos.ne']
    ring
  rw [htend] at he
  have hend : normalChart x (γ s) N v = γ r := by
    rw [normalChart_apply, hcγs, he]
  have hd := normal_distance_of_ball x (γ s) N hcs hzeros hR hballss hvM hsmall
  rw [hend, hlen] at hd
  calc
    _ = |r - s| * C := hd
    _ = _ := by rw [abs_sub_comm s r]; exact mul_comm _ _

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_IntrinsicExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open ChartMetric CoordinateGeometry

omit [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M] in
 theorem coordinate_curve_state (x : M) {q : ℝ → E × E} {t : ℝ}
    (ht : (q t).1 ∈ (chartAt E x).target)
    (hq : HasDerivAt q (geodesicSpray (metric x) (q t)) t) :
    curveState (E := E) (fun s => (chartAt E x).symm (q s).1) t =
      ⟨(chartAt E x).symm (q t).1, chartLift x (q t).1 (q t).2⟩ := by
  have hc : HasDerivAt (fun s => (q s).1) (q t).2 t := hq.fst
  have hmc := mdifferentiableAt_iff_differentiableAt.mpr hc.differentiableAt
  have hms := mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, E)) (chart_mem_atlas E x) ht
  refine TotalSpace.ext ?_ ?_
  · rfl
  apply heq_of_eq
  dsimp only [curveState]
  rw [chartLift_eq_mfderiv_symm x ht]
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((chartAt E x).symm ∘ fun s => (q s).1) t 1 = _
  rw [mfderiv_comp t hms hmc]
  simp only [mfderiv_eq_fderiv]
  change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x).symm (q t).1)
    (fderiv ℝ (fun s : ℝ => (q s).1) t 1) = _
  rw [fderiv_apply_one_eq_deriv, hc.deriv]
  rfl

 theorem coordinate_intrinsic (x : M) {U : Set ℝ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {q : ℝ → E × E} (hqs : ContDiffOn ℝ ∞ q U)
    (hq : ∀ t ∈ U, (q t).1 ∈ (chartAt E x).target ∧
      HasDerivAt q (geodesicSpray (metric x) (q t)) t)
    {a : ℝ} (ha : a ∈ U) :
    IsIntrinsicGeodesicOn (E := E) (fun t => (chartAt E x).symm (q t).1)
      (Real.sqrt (metric x (q a).1 (q a).2 (q a).2)) U := by
  refine ⟨contMDiffOn_chart_symm.comp (contMDiffOn_iff_contDiffOn.mpr hqs.fst)
    (fun t ht => (hq t ht).1), ?_⟩
  intro t ht
  obtain ⟨ε, hε, _, hdist⟩ := coordinate_geodesic_locally_minimizes x hU hqs hq ht
  have he := geodesic_energy_on_connected (chartAt E x).open_target
    ((metric_smooth x).differentiableOn (by simp)) (fun z _ => metric_symmetric x z)
    (fun z hz v hv => metric_positive x hz hv) hU hUc hq ht ha
  exact ⟨ε, hε, by simpa only [he] using hdist⟩

 theorem uniformly_local_intrinsic (x : M) {C : ℝ} (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ v : TangentSpace 𝓘(ℝ, E) y, ‖v‖ ≤ C →
        ∃ γ : ℝ → M, curveState (E := E) γ 0 = ⟨y, v⟩ ∧
          IsIntrinsicGeodesicOn (E := E) γ ‖v‖ (Metric.ball 0 ε) := by
  let c := chartAt E x
  let e := trivializationAt E (fun y : M => TangentSpace 𝓘(ℝ, E) y) x
  obtain ⟨ε, hε, W, hW, hxW, hWS, hlocal⟩ := uniform_local_geodesics c.open_target
    (metric_smooth x) (fun z hz v hv => metric_positive x hz hv)
    (c.map_source (mem_chart_source E x)) C
  let V := c.source ∩ c ⁻¹' W
  have hV : IsOpen V := c.continuousOn.isOpen_inter_preimage c.open_source hW
  refine ⟨ε, hε, V, hV, ⟨mem_chart_source E x, hxW⟩, ?_⟩
  intro y hy v hv
  have hyb : y ∈ e.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy.1
  let w : E := e.continuousLinearMapAt ℝ y v
  have hinv : chartLift x (c y) w = v := by
    dsimp only [chartLift]
    rw [c.left_inv hy.1]
    exact e.symmL_continuousLinearMapAt hyb v
  have henergy : metric x (c y) w w = ‖v‖ ^ 2 := by
    rw [metric_apply]
    dsimp only [chartLift]
    rw [c.left_inv hy.1]
    change inner ℝ (e.symmL ℝ y w) (e.symmL ℝ y w) = ‖v‖ ^ 2
    rw [e.symmL_continuousLinearMapAt hyb v]
    exact real_inner_self_eq_norm_sq v
  obtain ⟨q, hq₀, hqs, hq⟩ := hlocal (c y) hy.2 w
    (henergy ▸ (sq_le_sq₀ (norm_nonneg v) hC).mpr hv)
  let γ : ℝ → M := fun t => c.symm (q t).1
  have h0 : (0 : ℝ) ∈ Metric.ball 0 ε := Metric.mem_ball_self hε
  have hstate := coordinate_curve_state x (hq 0 h0).1 (hq 0 h0).2
  rw [hq₀] at hstate
  have hg := coordinate_intrinsic x Metric.isOpen_ball (convex_ball (0 : ℝ) ε).isPreconnected hqs hq h0
  rw [hq₀, henergy, Real.sqrt_sq (norm_nonneg v)] at hg
  refine ⟨γ, ?_, hg⟩
  rw [hstate]
  apply TotalSpace.ext (c.left_inv hy.1)
  exact heq_of_eq hinv

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_IntrinsicGlue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

section
omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

def IsIntrinsicGeodesicAt (γ : ℝ → M) (C t : ℝ) : Prop :=
  ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ t ∧
  ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball t ε, ∀ r ∈ Metric.ball t ε,
    dist (γ s) (γ r) = C * |s - r|

 theorem IsIntrinsicGeodesicOn.at {γ : ℝ → M} {C t : ℝ} {U : Set ℝ}
    (h : IsIntrinsicGeodesicOn (E := E) γ C U) (hU : IsOpen U) (ht : t ∈ U) :
    IsIntrinsicGeodesicAt (E := E) γ C t :=
  ⟨(h.1 t ht).contMDiffAt (hU.mem_nhds ht), h.2 t ht⟩

 theorem intrinsicOn_of_at {γ : ℝ → M} {C : ℝ} {U : Set ℝ}
    (h : ∀ t ∈ U, IsIntrinsicGeodesicAt (E := E) γ C t) :
    IsIntrinsicGeodesicOn (E := E) γ C U :=
  ⟨fun t ht => (h t ht).1.contMDiffWithinAt, fun t ht => (h t ht).2⟩

 theorem IsIntrinsicGeodesicAt.congr {γ η : ℝ → M} {C t : ℝ}
    (h : IsIntrinsicGeodesicAt (E := E) γ C t) (he : η =ᶠ[𝓝 t] γ) :
    IsIntrinsicGeodesicAt (E := E) η C t := by
  refine ⟨h.1.congr_of_eventuallyEq he, ?_⟩
  obtain ⟨ε, hε, hd⟩ := h.2
  obtain ⟨δ, hδ, hδe⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min ε δ, lt_min hε hδ, ?_⟩
  intro s hs r hr
  have hsε := lt_of_lt_of_le hs (min_le_left ε δ)
  have hrε := lt_of_lt_of_le hr (min_le_left ε δ)
  have hsδ := lt_of_lt_of_le hs (min_le_right ε δ)
  have hrδ := lt_of_lt_of_le hr (min_le_right ε δ)
  rw [hδe hsδ, hδe hrδ]
  exact hd s hsε r hrε

end

section
omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

 theorem IsIntrinsicGeodesicOn.comp_sub {γ : ℝ → M} {C a : ℝ} {U : Set ℝ}
    (h : IsIntrinsicGeodesicOn (E := E) γ C U) :
    IsIntrinsicGeodesicOn (E := E) (fun t => γ (t-a)) C ((fun t => t-a) ⁻¹' U) := by
  refine ⟨h.1.comp (contMDiffOn_iff_contDiffOn.mpr
    (contDiff_id.sub contDiff_const).contDiffOn) (fun t ht => ht), ?_⟩
  intro t ht
  obtain ⟨ε, hε, hd⟩ := h.2 (t-a) ht
  refine ⟨ε, hε, ?_⟩
  intro s hs r hr
  have hse : s-a ∈ Metric.ball (t-a) ε := by simpa only [Metric.mem_ball, dist_sub_right] using hs
  have hre : r-a ∈ Metric.ball (t-a) ε := by simpa only [Metric.mem_ball, dist_sub_right] using hr
  simpa only [sub_sub_sub_cancel_right] using hd (s-a) hse (r-a) hre

end
end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_CompactGeodesic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

 theorem compact_uniform_intrinsic [CompactSpace M] {C : ℝ} (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : M, ∀ v : TangentSpace 𝓘(ℝ, E) y, ‖v‖ ≤ C →
      ∃ γ : ℝ → M, curveState (E := E) γ 0 = ⟨y, v⟩ ∧
        IsIntrinsicGeodesicOn (E := E) γ ‖v‖ (Ioo (-ε) ε) := by
  classical
  choose δ hδ V hV hmem hlocal using fun x : M => uniformly_local_intrinsic (E := E) x hC
  have hcover : (univ : Set M) ⊆ ⋃ x, V x := fun x _ => mem_iUnion.mpr ⟨x, hmem x⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover V hV hcover
  have hmin : ∀ F : Finset M, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ F, ε ≤ δ x := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert x _ _ ih =>
      obtain ⟨ε, hε, hb⟩ := ih
      refine ⟨min ε (δ x), lt_min hε (hδ x), ?_⟩
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hb y hy)
  obtain ⟨ε, hε, hεδ⟩ := hmin F
  refine ⟨ε, hε, ?_⟩
  intro y v hv
  obtain ⟨x, hxF, hyV⟩ := mem_iUnion₂.mp (hF (mem_univ y))
  obtain ⟨γ, hγ₀, hγ⟩ := hlocal x y hyV v hv
  refine ⟨γ, hγ₀, hγ.mono ?_⟩
  intro t ht
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  have he := hεδ x hxF
  exact ⟨lt_of_le_of_lt (neg_le_neg he) ht.1, ht.2.trans_le he⟩

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_CompactHomotopyContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology
namespace CompactContinuation
variable {P X Y : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [TopologicalSpace X] [FirstCountableTopology X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y]

 def CollisionExclusionAt (F : P × X → Y) (t : P) : Prop :=
  ∀ x : X, ∀ r : ℕ → P, ∀ p q : ℕ → X,
    Tendsto r atTop (𝓝 t) → Tendsto p atTop (𝓝 x) → Tendsto q atTop (𝓝 x) →
    (∀ j, p j ≠ q j) → (∀ j, F (r j,p j) = F (r j,q j)) → False

end CompactContinuation
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_FiberHullCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set
open scoped BigOperators
namespace ConvexRepresentation
noncomputable section
variable {B E : Type*} [TopologicalSpace B] [T2Space B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

 def fiberHull (K : Set (B × E)) : Set (B × E) :=
    {q | q.2 ∈ convexHull ℝ {v | (q.1,v) ∈ K}}

end
end ConvexRepresentation
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Support_FirstCutSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology

namespace FirstCut

section Segment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def HasTrialPole (A : ℝ → ℝ → LinearMap.BilinForm ℝ E) (ξ : E) : Prop :=
  ∃ C c δ : ℝ, 0 < c ∧ 0 < δ ∧
    ∀ h, 0 < h → h < δ → ∀ s, |s| < δ →
      A h s ξ ξ ≤ C - c / (s ^ 2 + h)

end Segment

end FirstCut

open Set Filter
open scoped Topology

open Set Filter MeasureTheory
open scoped Topology

namespace JacobiIndex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def integrand (R : ℝ → E →L[ℝ] E) (U V : ℝ → E) (t : ℝ) : ℝ :=
  inner ℝ (deriv U t) (deriv V t) - inner ℝ (R t (U t)) (V t)

noncomputable def indexForm (R : ℝ → E →L[ℝ] E) (U V : ℝ → E) : ℝ :=
  ∫ t in (0 : ℝ)..1, integrand R U V t

end JacobiIndex

open Set Filter MeasureTheory
open scoped Topology

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_BrokenActionCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def brokenAction (K : E × E → ℝ) (e : ℝ → ℝ) (a : ℝ → E)
    (τ ε : ℝ) (z : E) (q : ℝ × E) : ℝ :=
  τ / 2 * e q.1 + K (a q.1,q.2) / ε + K (q.2,z) / ε

end
end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_CovariantActionHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Filter Set
open scoped Topology ContDiff
namespace RadialHessianCalculus
open CoordinateGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

 def actionForm (G : E → MetricTensor E) (f : E → ℝ) (a ν : E) : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun v w => fderiv ℝ (fderiv ℝ f) a v w +
    lowerChristoffel (fderiv ℝ G a) v w ν)
    (by intro v v' w; simp only [lowerChristoffel_apply,map_add,add_apply]; ring)
    (by intro c v w; simp only [lowerChristoffel_apply,map_smul,smul_apply,smul_eq_mul]; ring)
    (by intro v w w'; simp only [lowerChristoffel_apply,map_add,add_apply]; ring)
    (by intro c v w; simp only [lowerChristoffel_apply,map_smul,smul_apply,smul_eq_mul]; ring)

end
end RadialHessianCalculus
end

end WeakMTWGlobalSupport

end OAI
end


