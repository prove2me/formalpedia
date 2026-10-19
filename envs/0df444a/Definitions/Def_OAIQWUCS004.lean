-- Prove2me | Definitions.Def_OAIQWUCS004
-- name    : OAIQWUCS004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T00:58:42.484643+00:00
-- url     : https://prove2.me/theorems/f2770b5b-e7a8-4d9a-8b15-5120d4b4c16d
-- title:
--   Kähler forms in charts and the product retracts of the universal cover (OpenAI universal-cover splitting)
-- statement:
--   The last definitions bundle of the split of OpenAI's proof of `OAI.UniversalCoverSplitting.main`. The solution of the goal imports it.
--
--   The bundle holds OpenAI's Lean definitions from `lean/OAI/Geometry/KahlerSplitting` (OpenAI, *Universal-cover splitting for compact Kähler manifolds*, OpenAI Math Release, September 23, 2026, result family 052, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas their bodies use. Among them:
--   - the Kähler form in a chart, its pullbacks, and the Kähler form along a moving family of disks (`kahlerFormInChart`, `pullbackKahler`, `realPullbackKahler`, `movingKahlerForm`). These are used for the area estimate of the paper's Section 4;
--   - the product chart of a splitting chart (`SplittingChart.productChart`);
--   - OpenAI's structure `ProductRetracts`. It holds two idempotent global projections of the universal cover $Z$ at a base point $o$, one for each summand, with charts adapted to them. From it come the fixed-point sets $Y_1$ and $Y_2$ of the two projections as complex manifolds (`fixedManifold`, `Y₁`, `Y₂`), the retractions $q_1 : Z \to Y_1$ and $q_2 : Z \to Y_2$, and the pair map $(q_1, q_2)$ (`q₁`, `q₂`, `pair`). The solution proves that the pair map is the required biholomorphism onto $Y_1 \times Y_2$.
--
--   It imports the bundles `OAIQWUCS002` and `OAIQWUCS003` of this split. The theorems the definitions do not need are proved in the solution of the goal.
-- source:
--   OpenAI, Universal-cover splitting for compact Kähler manifolds, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 052; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Universal-cover-splitting-for-compact-Kahler-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/KahlerSplitting at commit adc7f12

import Mathlib
import Definitions.Def_KahlerSplitting
import Definitions.Def_OAIQWUCS002
import Definitions.Def_OAIQWUCS003

section
-- module Solutions.OAIQW_UniversalCover.MetricBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Manifold ContDiff
open Set
noncomputable section
open Set Topology Filter Metric

namespace UniversalCoverSplitting
section MetricCharts
variable {n : ℕ} {X : ComplexManifold n}

theorem KahlerMetric.exists_projection_bound_on_chartCompact (g : KahlerMetric X)
    (P : ProjectionField X) (hP : HolomorphicProjection P) (c : X.Carrier)
    {K : Set (Model n)} (hK : IsCompact K) (hKt : K ⊆ (extChartAt (model n) c).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ (extChartAt (model n) c).source,
      (extChartAt (model n) c) x ∈ K → ∀ u : Tangent X x,
      g.metric x (P x u) (P x u) ≤ C * g.metric x u u := by
  have hm := (g.continuous_quadraticInChart c).mono (prod_mono hKt Subset.rfl)
  have hp : ContinuousOn (fun z ↦ (projectionInChart P c z).restrictScalars ℝ) K :=
    (ContinuousLinearMap.restrictScalarsL ℂ (Model n) (Model n) ℝ ℝ).continuous.comp_continuousOn
      ((hP c).continuousOn.mono hKt)
  obtain ⟨C,hC,hbound⟩ := exists_quadratic_operator_bound hK
    (fun z u ↦ metricInChart g.metric c z u u)
    (fun z ↦ (projectionInChart P c z).restrictScalars ℝ) hm hp
    (fun z hz u hu ↦ g.positive_quadraticInChart c (hKt hz) hu)
    (fun z _ r u ↦ metricInChart_smul g.metric c z u r)
  refine ⟨C,hC,fun x hx hxK u ↦ ?_⟩
  have hb := hbound ((extChartAt (model n) c) x) hxK
    ((mfderiv (model n) (model n) (extChartAt (model n) c) x) u)
  change metricInChart g.metric c ((extChartAt (model n) c) x)
    (projectionInChart P c ((extChartAt (model n) c) x)
      ((mfderiv (model n) (model n) (extChartAt (model n) c) x) u))
    (projectionInChart P c ((extChartAt (model n) c) x)
      ((mfderiv (model n) (model n) (extChartAt (model n) c) x) u)) ≤
    C * metricInChart g.metric c ((extChartAt (model n) c) x)
      ((mfderiv (model n) (model n) (extChartAt (model n) c) x) u)
      ((mfderiv (model n) (model n) (extChartAt (model n) c) x) u) at hb
  rw [projectionInChart_forward P c hx u,
    metricInChart_forward g.metric c hx, metricInChart_forward g.metric c hx] at hb
  exact hb

theorem KahlerMetric.exists_uniform_projection_quadraticBound [CompactSpace X.Carrier]
    (g : KahlerMetric X) (P : ProjectionField X) (hP : HolomorphicProjection P) :
    ∃ C : ℝ, 0 < C ∧ ∀ x (u : Tangent X x),
      g.metric x (P x u) (P x u) ≤ C * g.metric x u u := by
  classical
  have hlocal : ∀ x : X.Carrier, ∃ (C : ℝ) (U : Set X.Carrier),
      0 < C ∧ U ∈ 𝓝 x ∧ ∀ y ∈ U, ∀ u : Tangent X y,
        g.metric y (P y u) (P y u) ≤ C * g.metric y u u := by
    intro x
    let e := extChartAt (model n) x
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target x)
      (e x) (mem_extChartAt_target x)
    have hr2 : 0 < r / 2 := half_pos hr
    have hK : closedBall (e x) (r / 2) ⊆ e.target :=
      (closedBall_subset_ball (by linarith : r / 2 < r)).trans hball
    obtain ⟨C,hC,hbound⟩ := g.exists_projection_bound_on_chartCompact P hP x
      (isCompact_closedBall (e x) (r / 2)) hK
    refine ⟨C, e.source ∩ e ⁻¹' ball (e x) (r / 2),hC,?_,?_⟩
    · exact inter_mem (extChartAt_source_mem_nhds x)
        ((continuousAt_extChartAt x).preimage_mem_nhds (ball_mem_nhds (e x) hr2))
    · intro y hy u
      exact hbound y hy.1 (ball_subset_closedBall hy.2) u
  choose C U hC hU hbound using hlocal
  obtain ⟨t,_,ht⟩ := isCompact_univ.elim_nhds_subcover U (fun x _ ↦ hU x)
  have hsum : 0 ≤ ∑ x ∈ t, C x := Finset.sum_nonneg (fun x _ ↦ (hC x).le)
  refine ⟨1 + ∑ x ∈ t, C x,by linarith,fun y u ↦ ?_⟩
  obtain ⟨x,hxt,hy⟩ := mem_iUnion₂.mp (ht (mem_univ y))
  have hle : C x ≤ 1 + ∑ z ∈ t, C z := by
    have hcx : C x ≤ ∑ z ∈ t, C z := Finset.single_le_sum (fun z _ ↦ (hC z).le) hxt
    linarith
  exact (hbound x y hy u).trans (mul_le_mul_of_nonneg_right hle (g.nonnegative y u))

theorem KahlerMetric.exists_uniform_projection_normBound [CompactSpace X.Carrier]
    (g : KahlerMetric X) (P : ProjectionField X) (hP : HolomorphicProjection P) :
    ∃ C : ℝ, 0 < C ∧ ∀ x (u : Tangent X x),
      metricNorm g x (P x u) ≤ C * metricNorm g x u := by
  obtain ⟨C,hC,hbound⟩ := g.exists_uniform_projection_quadraticBound P hP
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,fun x u ↦ ?_⟩
  dsimp [metricNorm]
  have hb := Real.sqrt_le_sqrt (hbound x u)
  rwa [Real.sqrt_mul hC.le] at hb

theorem metric_abs_le (g : KahlerMetric X) (x : X.Carrier) (u v : Tangent X x) :
    |g.metric x u v| ≤ metricNorm g x u * metricNorm g x v := by
  let := g.realInnerCore x
  exact InnerProductSpace.Core.norm_inner_le_norm (𝕜 := ℝ) u v

end MetricCharts
end UniversalCoverSplitting
namespace UniversalCoverSplitting
section ComplementProjection
universe u
variable {n r₁ r₂ : ℕ}
variable {X : ComplexManifold.{u} n}

theorem KahlerMetric.exists_uniform_splitting_bound [CompactSpace X.Carrier]
    (g : KahlerMetric X) (S : HolomorphicSplitting X r₁ r₂) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      (∀ x (u : Tangent X x), metricNorm g x (S.projection x u) ≤ C₁ * metricNorm g x u) ∧
      (∀ x (u : Tangent X x),
        metricNorm g x (complementaryProjection S x u) ≤ C₂ * metricNorm g x u) := by
  obtain ⟨C₁,hC₁,h₁⟩ := g.exists_uniform_projection_normBound S.projection S.holomorphic
  obtain ⟨C₂,hC₂,h₂⟩ := g.exists_uniform_projection_normBound
    (complementaryProjection S) S.complement_holomorphic
  exact ⟨C₁,C₂,hC₁,hC₂,h₁,h₂⟩

end ComplementProjection
end UniversalCoverSplitting

noncomputable section
open Set Metric

namespace UniversalCoverSplitting
open Set Metric
variable {n : ℕ} {X : ComplexManifold n}

theorem KahlerMetric.exists_chart_metric_comparison (g : KahlerMetric X) (c : X.Carrier)
    {K : Set (Model n)} (hK : IsCompact K) (he : K ⊆ (extChartAt (model n) c).target) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ z ∈ K, ∀ u : Model n,
      ‖u‖ ^ 2 ≤ C * metricInChart g.metric c z u u ∧
      metricInChart g.metric c z u u ≤ D * ‖u‖ ^ 2 := by
  have hN : ContinuousOn (fun p : Model n × Model n ↦ ‖p.2‖ ^ 2) (K ×ˢ univ) :=
    (continuous_snd.norm.pow 2).continuousOn
  have hQ := (g.continuous_quadraticInChart c).mono (prod_mono_left he)
  have hnormhom (z : Model n) (_ : z ∈ K) (r : ℝ) (u : Model n) :
      ‖r • u‖ ^ 2 = r ^ 2 * ‖u‖ ^ 2 := by rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hnormpos (z : Model n) (_ : z ∈ K) (u : Model n) (hu : u ≠ 0) :
      0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  obtain ⟨C,hC,hCb⟩ := exists_quadratic_comparison hK
    (fun z u ↦ metricInChart g.metric c z u u) (fun _ u ↦ ‖u‖ ^ 2) hQ hN
    (fun z hz u hu ↦ g.positive_quadraticInChart c (he hz) hu)
    (fun z _ r u ↦ metricInChart_smul g.metric c z u r) hnormhom
  obtain ⟨D,hD,hDb⟩ := exists_quadratic_comparison hK
    (fun _ u ↦ ‖u‖ ^ 2) (fun z u ↦ metricInChart g.metric c z u u) hN hQ
    hnormpos hnormhom (fun z _ r u ↦ metricInChart_smul g.metric c z u r)
  exact ⟨C,D,hC,hD,fun z hz u ↦ ⟨hCb z hz u,hDb z hz u⟩⟩

theorem KahlerMetric.exists_chart_speed_comparison (g : KahlerMetric X) (c : X.Carrier)
    {K : Set (Model n)} (hK : IsCompact K) (he : K ⊆ (extChartAt (model n) c).target) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ x ∈ (extChartAt (model n) c).source,
      (extChartAt (model n) c) x ∈ K → ∀ v : Tangent X x,
      (@norm (Model n) _ (mfderiv (model n) (model n) (extChartAt (model n) c) x v)) ≤ C * metricNorm g x v ∧
      metricNorm g x v ≤ D * (@norm (Model n) _ (mfderiv (model n) (model n) (extChartAt (model n) c) x v)) := by
  obtain ⟨C,D,hC,hD,hb⟩ := g.exists_chart_metric_comparison c hK he
  refine ⟨Real.sqrt C,Real.sqrt D,Real.sqrt_pos.mpr hC,Real.sqrt_pos.mpr hD,?_⟩
  intro x hx hxK v
  obtain ⟨hCv,hDv⟩ := hb _ hxK (mfderiv (model n) (model n) (extChartAt (model n) c) x v)
  rw [metricInChart_forward g.metric c hx] at hCv hDv
  have hsq : Real.sqrt ((@norm (Model n) _ (mfderiv (model n) (model n) (extChartAt (model n) c) x v)) ^ 2) =
      @norm (Model n) _ (mfderiv (model n) (model n) (extChartAt (model n) c) x v) :=
    Real.sqrt_sq (norm_nonneg (show Model n from mfderiv (model n) (model n) (extChartAt (model n) c) x v))
  constructor
  · have hh := Real.sqrt_le_sqrt hCv
    rw [hsq, Real.sqrt_mul hC.le] at hh
    exact hh
  · have hh := Real.sqrt_le_sqrt hDv
    rw [Real.sqrt_mul hD.le, hsq] at hh
    exact hh

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Filter Topology Metric MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ} {X : ComplexManifold n}

theorem curveSpeed_nonneg (g : KahlerMetric X) (f : ℂ → X.Carrier) (z : ℂ) :
    0 ≤ curveSpeed g f z := Real.sqrt_nonneg _

theorem chart_deriv_curve {f : ℂ → X.Carrier} {z : ℂ}
    (hf : MDifferentiableAt 𝓘(ℂ, ℂ) (model n) f z)
    (c : X.Carrier) (hc : f z ∈ (extChartAt (model n) c).source) :
    deriv ((extChartAt (model n) c) ∘ f) z =
      mfderiv (model n) (model n) (extChartAt (model n) c) (f z)
        (mfderiv 𝓘(ℂ, ℂ) (model n) f z (1 : ℂ)) := by
  have he : MDifferentiableAt (model n) (model n) (extChartAt (model n) c) (f z) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hc)
  rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv, mfderiv_comp z he hf]
  rfl

theorem curveSpeed_eq_chart (g : KahlerMetric X) {f : ℂ → X.Carrier} {z : ℂ}
    (hf : MDifferentiableAt 𝓘(ℂ, ℂ) (model n) f z)
    (c : X.Carrier) (hc : f z ∈ (extChartAt (model n) c).source) :
    curveSpeed g f z = Real.sqrt (metricInChart g.metric c
      ((extChartAt (model n) c) (f z)) (deriv ((extChartAt (model n) c) ∘ f) z)
      (deriv ((extChartAt (model n) c) ∘ f) z)) := by
  rw [chart_deriv_curve hf c hc, metricInChart_forward g.metric c hc]
  rfl

theorem curveSpeed_continuousOn (g : KahlerMetric X) {f : ℂ → X.Carrier}
    {U : Set ℂ} (hU : IsOpen U)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (model n) f U) :
    ContinuousOn (curveSpeed g f) U := by
  intro z hz
  let c := f z
  let e := extChartAt (model n) c
  have hcf : ContinuousAt f z := (hf.mdifferentiableAt (hU.mem_nhds hz)).continuousAt
  have hN : U ∩ f ⁻¹' e.source ∈ 𝓝 z := inter_mem (hU.mem_nhds hz)
    (hcf (extChartAt_source_mem_nhds (I := model n) c))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hN
  have hd : DifferentiableOn ℂ (e ∘ f) (ball z r) := by
    intro w hw
    have he : MDifferentiableAt (model n) (model n) e (f w) :=
      mdifferentiableAt_extChartAt (by simpa only [e, extChartAt_source, mem_preimage] using (hrs hw).2)
    exact (he.comp w (hf.mdifferentiableAt (hU.mem_nhds (hrs hw).1))).differentiableAt.differentiableWithinAt
  have hcchart : ContinuousOn (fun w ↦ ((e (f w)), deriv (e ∘ f) w)) (ball z r) :=
    hd.continuousOn.prodMk (hd.deriv isOpen_ball).continuousOn
  have hQ : ContinuousOn (fun w ↦ Real.sqrt (metricInChart g.metric c
      (e (f w)) (deriv (e ∘ f) w) (deriv (e ∘ f) w))) (ball z r) :=
    (g.continuous_quadraticInChart c |>.comp hcchart
      (fun w hw ↦ ⟨e.map_source (hrs hw).2, mem_univ _⟩)).sqrt
  have hS : ContinuousOn (curveSpeed g f) (ball z r) := hQ.congr (fun w hw ↦
    curveSpeed_eq_chart g (hf.mdifferentiableAt (hU.mem_nhds (hrs hw).1)) c (hrs hw).2)
  exact (hS.continuousAt (ball_mem_nhds z hr)).continuousWithinAt

theorem curveSpeed_affine (g : KahlerMetric X) {f : ℂ → X.Carrier}
    (p b z : ℂ) (hf : MDifferentiableAt 𝓘(ℂ, ℂ) (model n) f (p + b * z)) :
    curveSpeed g (fun w ↦ f (p + b * w)) z = ‖b‖ * curveSpeed g f (p + b * z) := by
  have ha : HasDerivAt (fun w : ℂ ↦ p + b * w) b z := by
    convert! ((hasDerivAt_id z).const_mul b).const_add p using 1; simp
  unfold curveSpeed
  have he : (fun w ↦ f (p + b * w)) = f ∘ (fun w : ℂ ↦ p + b * w) := rfl
  rw [he, mfderiv_comp z hf ha.differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv]
  change metricNorm g (f (p + b * z))
    (mfderiv 𝓘(ℂ, ℂ) (model n) f (p + b * z) (fderiv ℂ (fun w : ℂ ↦ p + b * w) z 1)) = _
  rw [fderiv_apply_one_eq_deriv, ha.deriv]
  let D : ℂ →L[ℂ] Tangent X (f (p + b * z)) := mfderiv 𝓘(ℂ, ℂ) (model n) f (p + b * z)
  change metricNorm g (f (p + b*z)) (D b) = ‖b‖ * metricNorm g (f (p + b*z)) (D (1 : ℂ))
  have hDb : D b = b • D (1 : ℂ) := by
    simpa only [smul_eq_mul, mul_one] using D.map_smul b (1 : ℂ)
  rw [hDb,metricNorm_complex_smul]

end UniversalCoverSplitting
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.AreaBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Manifold ContDiff
open Set
noncomputable section
open Set Topology Filter Metric
noncomputable section
open Set Metric

noncomputable section
open Set Metric Filter Topology

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped Interval
noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped Interval

namespace UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ} {X : ComplexManifold n}

theorem curveArea_mono (g : KahlerMetric X) (f : ℂ → X.Carrier)
    {U V : Set ℂ} (h : U ⊆ V) : curveArea g f U ≤ curveArea g f V :=
  lintegral_mono_set h

theorem curveArea_eq_ofReal_integral (g : KahlerMetric X) (f : ℂ → X.Carrier)
    {U : Set ℂ} (hi : IntegrableOn (fun z ↦ curveSpeed g f z ^ 2) U) :
    curveArea g f U = ENNReal.ofReal (∫ z in U, curveSpeed g f z ^ 2) :=
  (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))).symm

theorem exists_normalized_curveArea_lowerBound (g : KahlerMetric X)
    (c : X.Carrier) {δ : ℝ} (hδ : 0 < δ) :
    ∃ V ∈ 𝓝 c, ∃ κ : ℝ, 0 < κ ∧ ∀ h : ℂ → X.Carrier,
      MDifferentiableOn 𝓘(ℂ, ℂ) (model n) h (ball 0 δ) →
      h 0 ∈ V → curveSpeed g h 0 = 1 →
      (∀ z ∈ ball 0 δ, curveSpeed g h z ≤ 2) →
      ENNReal.ofReal κ ≤ curveArea g h (ball 0 δ) := by
  let e : OpenPartialHomeomorph X.Carrier (Model n) :=
    { extChartAt (model n) c with
      continuousOn_toFun := continuousOn_extChartAt c
      continuousOn_invFun := continuousOn_extChartAt_symm c
      open_source := isOpen_extChartAt_source c
      open_target := isOpen_extChartAt_target c }
  have hc : c ∈ e.source := mem_extChartAt_source c
  obtain ⟨R,hR,he⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (e.open_target.mem_nhds (e.map_source hc))
  obtain ⟨Cforward,Cback,hC,hD,hcomp⟩ := g.exists_chart_speed_comparison c (isCompact_closedBall (e c) R) he
  let V := e.source ∩ e ⁻¹' ball (e c) (R/2)
  have hV : V ∈ 𝓝 c := (e.isOpen_inter_preimage isOpen_ball).mem_nhds
    ⟨hc, by simpa using half_pos hR⟩
  let r := min (δ/2) (R/(8*Cforward))
  have hr : 0 < r := lt_min (half_pos hδ) (div_pos hR (by positivity))
  have hrδ : r < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hrC : 2*Cforward*r ≤ R/4 := by
    have hm := mul_le_mul_of_nonneg_left (min_le_right (δ/2) (R/(8*Cforward))) (show 0 ≤ 2*Cforward by positivity)
    dsimp [r]
    calc
      2*Cforward*min (δ/2) (R/(8*Cforward)) ≤ 2*Cforward*(R/(8*Cforward)) := hm
      _ = R/4 := by field_simp; ring
  let κ := Real.pi * r^2 / (Cforward^2 * Cback ^ 2)
  refine ⟨V,hV,κ,by dsimp [κ]; positivity,?_⟩
  intro h hh hhV hnorm hbound
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 δ := closedBall_subset_ball hrδ
  have hhcont := hh.continuousOn
  have hderchart (z : ℂ) (hz : z ∈ ball 0 δ) (hs : h z ∈ e.source) :
      DifferentiableAt ℂ (e ∘ h) z := by
    have he' : MDifferentiableAt (model n) (model n) e (h z) :=
      mdifferentiableAt_extChartAt (by simpa only [e,extChartAt_source] using hs)
    exact (he'.comp z (hh.mdifferentiableAt (isOpen_ball.mem_nhds hz))).differentiableAt
  have htrap : ∀ z ∈ closedBall (0 : ℂ) r, h z ∈ e.source ∧ e (h z) ∈ ball (e c) R := by
    apply chart_trapping_on_disk e hR (by positivity : 0 ≤ 2*Cforward) hr.le he (hhcont.mono hsub)
    · refine ⟨hhV.1,?_⟩
      have hi : dist (e (h 0)) (e c) < R/2 := hhV.2
      linarith
    · intro z hz hk
      obtain ⟨w,hw,hwz⟩ := hk
      have hs : h z ∈ e.source := hwz ▸ e.map_target (he hw)
      have hw' : e (h z) ∈ closedBall (e c) R := by rw [← hwz,e.right_inv (he hw)]; exact hw
      refine ⟨hderchart z (hsub hz) hs,?_⟩
      rw [← norm_deriv_eq_norm_fderiv]
      change ‖deriv ((extChartAt (model n) c) ∘ h) z‖ ≤ _
      rw [chart_deriv_curve (hh.mdifferentiableAt (isOpen_ball.mem_nhds (hsub hz))) c hs]
      exact ((hcomp (h z) hs hw' (mfderiv 𝓘(ℂ, ℂ) (model n) h z (1 : ℂ))).1).trans
        (by change Cforward * curveSpeed g h z ≤ 2*Cforward; nlinarith [hbound z (hsub hz)])
  let W := ball (0 : ℂ) δ ∩ h ⁻¹' e.source
  have hW : IsOpen W := hhcont.isOpen_inter_preimage isOpen_ball e.open_source
  have hd : DifferentiableOn ℂ (e ∘ h) W :=
    fun z hz ↦ (hderchart z hz.1 hz.2).differentiableWithinAt
  have hrW : closedBall (0 : ℂ) r ⊆ W := fun z hz ↦ ⟨hsub hz,(htrap z hz).1⟩
  have hDhol : DifferentiableOn ℂ (deriv (e ∘ h)) (closedBall 0 r) := (hd.deriv hW).mono hrW
  have hDs (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) :
      ‖deriv (e ∘ h) z‖ ≤ Cforward * curveSpeed g h z ∧
      curveSpeed g h z ≤ Cback * ‖deriv (e ∘ h) z‖ := by
    change ‖deriv ((extChartAt (model n) c) ∘ h) z‖ ≤ _ ∧
      _ ≤ Cback * ‖deriv ((extChartAt (model n) c) ∘ h) z‖
    rw [chart_deriv_curve (hh.mdifferentiableAt (isOpen_ball.mem_nhds (hsub hz))) c (htrap z hz).1]
    exact hcomp (h z) (htrap z hz).1 (ball_subset_closedBall (htrap z hz).2)
      (mfderiv 𝓘(ℂ, ℂ) (model n) h z (1 : ℂ))
  have hzero : (0 : ℂ) ∈ closedBall 0 r := mem_closedBall_self hr.le
  have hone : 1 ≤ Cback ^ 2 * ‖deriv (e ∘ h) 0‖^2 := by
    have h1 : 1 ≤ Cback * ‖deriv (e ∘ h) 0‖ := by simpa only [hnorm] using (hDs 0 hzero).2
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h1 2
    simpa only [one_pow,mul_pow] using hsq
  have hspeedcont := (curveSpeed_continuousOn g isOpen_ball hh).mono hsub
  have hi : IntegrableOn (fun z ↦ curveSpeed g h z ^ 2) (ball (0 : ℂ) r) :=
    ((hspeedcont.pow 2).integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hDi : IntegrableOn (fun z ↦ ‖deriv (e ∘ h) z‖^2) (ball (0 : ℂ) r) :=
    ((hDhol.continuousOn.norm.pow 2).integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hupper : (∫ z in ball (0 : ℂ) r, ‖deriv (e ∘ h) z‖^2) ≤
      Cforward^2 * ∫ z in ball (0 : ℂ) r, curveSpeed g h z ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hDi (hi.const_mul _) measurableSet_ball
    intro z hz
    have hs := pow_le_pow_left₀ (norm_nonneg _) (hDs z (ball_subset_closedBall hz)).1 2
    simpa only [mul_pow] using hs
  have hlower := (norm_sq_mul_diskArea_le_integral hr.le hDhol).trans hupper
  have hκ : κ ≤ ∫ z in ball (0 : ℂ) r, curveSpeed g h z ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < Cforward^2*Cback ^ 2)).mpr
    calc
      Real.pi*r^2 ≤ (Real.pi*r^2*‖deriv (e ∘ h) 0‖^2)*Cback ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hone (show 0 ≤ Real.pi*r^2 by positivity)]
      _ ≤ (Cforward^2 * ∫ z in ball (0 : ℂ) r, curveSpeed g h z ^ 2)*Cback ^ 2 :=
        mul_le_mul_of_nonneg_right hlower (sq_nonneg Cback)
      _ = (∫ z in ball (0 : ℂ) r, curveSpeed g h z ^ 2)*(Cforward^2*Cback ^ 2) := by ring
  exact ((ENNReal.ofReal_le_ofReal hκ).trans_eq (curveArea_eq_ofReal_integral g h hi).symm).trans
    (curveArea_mono g h (ball_subset_ball hrδ.le))

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ} {X : ComplexManifold n}

theorem exists_uniform_normalized_curveArea_lowerBound [CompactSpace X.Carrier]
    (g : KahlerMetric X) {δ : ℝ} (hδ : 0 < δ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ h : ℂ → X.Carrier,
      MDifferentiableOn 𝓘(ℂ, ℂ) (model n) h (ball 0 δ) →
      curveSpeed g h 0 = 1 →
      (∀ z ∈ ball 0 δ, curveSpeed g h z ≤ 2) →
      ENNReal.ofReal κ ≤ curveArea g h (ball 0 δ) := by
  classical
  choose V hV κ hκ hb using fun c : X.Carrier ↦
    exists_normalized_curveArea_lowerBound g c hδ
  obtain ⟨s,hs⟩ := CompactSpace.elim_nhds_subcover V hV
  have covered (x : X.Carrier) : ∃ c ∈ s, x ∈ V c := by
    have hx : x ∈ ⋃ c ∈ s, V c := by rw [hs]; trivial
    simpa only [mem_iUnion,exists_prop] using hx
  by_cases hne : s.Nonempty
  · refine ⟨s.inf' hne κ, (Finset.lt_inf'_iff hne).mpr (fun c _ ↦ hκ c),?_⟩
    intro h hh hnorm hbound
    obtain ⟨c,hcs,hc⟩ := covered (h 0)
    exact (ENNReal.ofReal_le_ofReal (s.inf'_le κ hcs)).trans (hb c h hh hc hnorm hbound)
  · refine ⟨1,by norm_num,?_⟩
    intro h
    obtain ⟨c,hcs,_⟩ := covered (h 0)
    exact (hne ⟨c,hcs⟩).elim

end UniversalCoverSplitting

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace UniversalCoverSplitting
open Set Metric MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ} {X : ComplexManifold n}

theorem curveArea_positive_affine (g : KahlerMetric X) {f : ℂ → X.Carrier}
    (U : Set ℂ) (hU : MeasurableSet U) (p : ℂ) {a : ℝ} (ha : 0 < a)
    (hf : ∀ z ∈ (fun z : ℂ ↦ p + a • z) '' U,
      MDifferentiableAt 𝓘(ℂ, ℂ) (model n) f z) :
    curveArea g (fun z ↦ f (p + a • z)) U =
      curveArea g f ((fun z : ℂ ↦ p + a • z) '' U) := by
  have hs (z : ℂ) (hz : z ∈ U) :
      curveSpeed g (fun z ↦ f (p + a • z)) z = a * curveSpeed g f (p + a • z) := by
    simpa only [Complex.real_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] using
      curveSpeed_affine g p (a : ℂ) z (hf _ ⟨z,hz,rfl⟩)
  unfold curveArea
  calc
    (∫⁻ z in U, ENNReal.ofReal (curveSpeed g (fun z ↦ f (p + a • z)) z ^ 2)) =
        ∫⁻ z in U, ENNReal.ofReal (a^2) * ENNReal.ofReal (curveSpeed g f (p + a • z) ^ 2) := by
      apply setLIntegral_congr_fun hU
      intro z hz
      dsimp only
      rw [hs z hz,mul_pow,ENNReal.ofReal_mul (sq_nonneg a)]
    _ = ENNReal.ofReal (a^2) * ∫⁻ z in U, ENNReal.ofReal (curveSpeed g f (p + a • z) ^ 2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (a^2) * ((ENNReal.ofReal (a^2))⁻¹ *
        ∫⁻ w in (fun z : ℂ ↦ p + a • z) '' U, ENNReal.ofReal (curveSpeed g f w ^ 2)) := by
      rw [lintegral_comp_positive_affine (fun w ↦ ENNReal.ofReal (curveSpeed g f w ^ 2)) U p ha]
    _ = _ := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top,one_mul]

end UniversalCoverSplitting
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.SmallArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set
open Set Topology Filter Metric
open Set Metric Filter Topology
open Set MeasureTheory Metric Filter Topology
open scoped Interval
open Set MeasureTheory
open scoped ENNReal
open Set Metric

namespace UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ} {X : ComplexManifold n}

theorem small_area_weighted_speed [CompactSpace X.Carrier] (g : KahlerMetric X)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (f : ℂ → X.Carrier) (Ω : Set ℂ), IsOpen Ω →
      MDifferentiableOn 𝓘(ℂ, ℂ) (model n) f Ω →
      ∀ (c : ℂ) (R : ℝ), 0 < R → closedBall c R ⊆ Ω →
      curveArea g f (ball c R) < ENNReal.ofReal η →
      ∀ z ∈ ball c R, (R - dist z c) * curveSpeed g f z < ε := by
  obtain ⟨η,hη,hlower⟩ := exists_uniform_normalized_curveArea_lowerBound g
    (by positivity : 0 < ε/4)
  refine ⟨η,hη,?_⟩
  intro f Ω hΩ hf c R hR hsub harea z hz
  by_contra hsmall
  obtain ⟨p,hp,hap,_,hbr⟩ := exists_brody_rescaling hR hε
    ((curveSpeed_continuousOn g hΩ hf).mono hsub)
    (fun z _ ↦ curveSpeed_nonneg g f z) ⟨z,hz,le_of_not_gt hsmall⟩
  let a := (curveSpeed g f p)⁻¹
  have ha : 0 < a := inv_pos.mpr hap
  let φ : ℂ → ℂ := fun ζ ↦ p + a • ζ
  have hφ (ζ : ℂ) : φ ζ = p + ζ / (curveSpeed g f p : ℂ) := by
    simp only [φ,a,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm]
  have hφmem (ζ : ℂ) (hζ : ζ ∈ ball (0 : ℂ) (ε/4)) : φ ζ ∈ ball c R := by
    rw [hφ]; exact (hbr ζ hζ).1
  let k : ℂ → X.Carrier := f ∘ φ
  have hφdiff (ζ : ℂ) : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) φ ζ := by
    apply DifferentiableAt.mdifferentiableAt
    simpa only [φ,Complex.real_smul,id_eq] using
      (((differentiableAt_id (𝕜 := ℂ) (x := ζ)).const_mul (a : ℂ)).const_add p)
  have hkdiff : MDifferentiableOn 𝓘(ℂ, ℂ) (model n) k (ball 0 (ε/4)) := by
    intro ζ hζ
    exact ((hf.mdifferentiableAt (hΩ.mem_nhds (hsub (ball_subset_closedBall (hφmem ζ hζ))))).comp ζ
      (hφdiff ζ)).mdifferentiableWithinAt
  have hkSpeed (ζ : ℂ) (hζ : ζ ∈ ball (0 : ℂ) (ε/4)) :
      curveSpeed g k ζ = a * curveSpeed g f (φ ζ) := by
    simpa only [k,Function.comp_def,φ,Complex.real_smul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos ha] using
      curveSpeed_affine g p (a : ℂ) ζ
        (hf.mdifferentiableAt (hΩ.mem_nhds (hsub (ball_subset_closedBall (hφmem ζ hζ)))))
  have hk0 : curveSpeed g k 0 = 1 := by
    rw [hkSpeed 0 (mem_ball_self (by positivity))]
    simp [φ,a,inv_mul_cancel₀ hap.ne']
  have hk2 (ζ : ℂ) (hζ : ζ ∈ ball (0 : ℂ) (ε/4)) : curveSpeed g k ζ ≤ 2 := by
    rw [hkSpeed ζ hζ,hφ]
    simpa only [a,div_eq_mul_inv,mul_comm] using (hbr ζ hζ).2
  have hsubarea : curveArea g k (ball 0 (ε/4)) ≤ curveArea g f (ball c R) := by
    change curveArea g (fun ζ ↦ f (p + a • ζ)) (ball 0 (ε/4)) ≤ _
    rw [curveArea_positive_affine g _ measurableSet_ball p ha]
    · exact curveArea_mono g f (by rintro _ ⟨ζ,hζ,rfl⟩; exact hφmem ζ hζ)
    · rintro _ ⟨ζ,hζ,rfl⟩
      exact hf.mdifferentiableAt (hΩ.mem_nhds (hsub (ball_subset_closedBall (hφmem ζ hζ))))
  exact (not_lt_of_ge ((hlower k hkdiff hk0 hk2).trans hsubarea)) harea

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ} {X : ComplexManifold n}

theorem exists_small_area_speed_bound [CompactSpace X.Carrier] (g : KahlerMetric X)
    {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ f : ℂ → X.Carrier,
      MDifferentiableOn 𝓘(ℂ, ℂ) (model n) f Ω →
      curveArea g f Ω < ENNReal.ofReal η → ∀ z ∈ K, curveSpeed g f z < ε := by
  obtain ⟨R,hR,hball⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨η,hη,hb⟩ := small_area_weighted_speed g (mul_pos hε hR)
  refine ⟨η,hη,?_⟩
  intro f hf harea z hz
  have hc : closedBall z R ⊆ Ω := (closedBall_subset_cthickening hz R).trans hball
  have he := hb f Ω hΩ hf z R hR hc ((curveArea_mono g f
    (ball_subset_closedBall.trans hc)).trans_lt harea) z (mem_ball_self hR)
  simp only [dist_self,sub_zero] at he
  nlinarith

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

theorem bounded_curveSpeed_local_trapping (g : KahlerMetric X) (c : X.Carrier)
    {V : Set X.Carrier} (hV : V ∈ 𝓝 c) {L : ℝ} (hL : 0 ≤ L) :
    ∃ W ∈ 𝓝 c, ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ r →
      ∀ (f : ℂ → X.Carrier) (Ω : Set ℂ),
      IsOpen Ω → MDifferentiableOn 𝓘(ℂ, ℂ) (model n) f Ω →
      closedBall (0 : ℂ) ρ ⊆ Ω → f 0 ∈ W →
      (∀ z ∈ closedBall (0 : ℂ) ρ, curveSpeed g f z ≤ L) →
      MapsTo f (closedBall (0 : ℂ) ρ) V := by
  let e : OpenPartialHomeomorph X.Carrier (Model n) :=
    { extChartAt (model n) c with
      continuousOn_toFun := continuousOn_extChartAt c
      continuousOn_invFun := continuousOn_extChartAt_symm c
      open_source := isOpen_extChartAt_source c
      open_target := isOpen_extChartAt_target c }
  have hc : c ∈ e.source := mem_extChartAt_source c
  have het : e c ∈ e.target := e.map_source hc
  have hnear : e.target ∩ e.symm ⁻¹' V ∈ 𝓝 (e c) :=
    inter_mem (e.open_target.mem_nhds het)
      ((e.continuousOn_symm.continuousAt (e.open_target.mem_nhds het))
        (by simpa only [e.left_inv hc] using hV))
  obtain ⟨R,hR,hRsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  have he : closedBall (e c) R ⊆ e.target := fun z hz ↦ (hRsub hz).1
  obtain ⟨C,D,hC,_,hcomp⟩ := g.exists_chart_speed_comparison c
    (isCompact_closedBall (e c) R) he
  let W := e.source ∩ e ⁻¹' ball (e c) (R/2)
  have hW : W ∈ 𝓝 c := (e.isOpen_inter_preimage isOpen_ball).mem_nhds
    ⟨hc,by simpa using half_pos hR⟩
  let r := R / (4 * (C * L + 1))
  have hCL : 0 ≤ C * L := mul_nonneg hC.le hL
  have hr : 0 < r := div_pos hR (by positivity)
  have hrCL : C * L * r ≤ R / 4 := by
    dsimp [r]
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
    have hd : 0 < 4 * (C * L + 1) := by positivity
    field_simp
    nlinarith
  refine ⟨W,hW,r,hr,?_⟩
  intro ρ hρ hρr f Ω hΩ hf hsub hzero hspeed z hz
  have hρCL : C * L * ρ ≤ R / 4 :=
    (mul_le_mul_of_nonneg_left hρr hCL).trans hrCL
  have htrap : ∀ z ∈ closedBall (0 : ℂ) ρ,
      f z ∈ e.source ∧ e (f z) ∈ ball (e c) R := by
    apply chart_trapping_on_disk e hR hCL hρ he (hf.continuousOn.mono hsub)
    · refine ⟨hzero.1,?_⟩
      have hh : dist (e (f 0)) (e c) < R/2 := hzero.2
      linarith
    · intro w hw hk
      obtain ⟨v,hv,hvf⟩ := hk
      have hs : f w ∈ e.source := hvf ▸ e.map_target (he hv)
      have hv' : e (f w) ∈ closedBall (e c) R := by
        rw [← hvf,e.right_inv (he hv)]; exact hv
      have hfd := hf.mdifferentiableAt (hΩ.mem_nhds (hsub hw))
      have hed : MDifferentiableAt (model n) (model n) e (f w) :=
        mdifferentiableAt_extChartAt (by simpa only [e,extChartAt_source] using hs)
      refine ⟨(hed.comp w hfd).differentiableAt,?_⟩
      rw [← norm_deriv_eq_norm_fderiv]
      change ‖deriv ((extChartAt (model n) c) ∘ f) w‖ ≤ C * L
      rw [chart_deriv_curve hfd c hs]
      exact ((hcomp (f w) hs hv' (mfderiv 𝓘(ℂ, ℂ) (model n) f w (1:ℂ))).1).trans
        (mul_le_mul_of_nonneg_left (hspeed w hw) hC.le)
  have ht := htrap z hz
  have hv := (hRsub (ball_subset_closedBall ht.2)).2
  simpa only [mem_preimage,e.left_inv ht.1] using hv

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

attribute [local instance] OAI.UniversalCoverSplitting.instMetricSpaceCarrierOfCompactSpace
theorem bounded_curveSpeed_uniform_trapping [CompactSpace X.Carrier]
    (g : KahlerMetric X) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ r →
      ∀ (f : ℂ → X.Carrier) (Ω : Set ℂ),
      IsOpen Ω → MDifferentiableOn 𝓘(ℂ, ℂ) (model n) f Ω →
      closedBall (0 : ℂ) ρ ⊆ Ω →
      (∀ z ∈ closedBall (0 : ℂ) ρ, curveSpeed g f z ≤ L) →
      ∀ z ∈ closedBall (0 : ℂ) ρ, dist (f 0) (f z) < ε := by
  classical
  choose W hW r hr hb using fun c : X.Carrier ↦
    bounded_curveSpeed_local_trapping g c (ball_mem_nhds c (half_pos hε)) hL
  let V (c : X.Carrier) := W c ∩ ball c (ε/2)
  have hV (c : X.Carrier) : V c ∈ 𝓝 c := inter_mem (hW c) (ball_mem_nhds c (half_pos hε))
  obtain ⟨s,hs⟩ := CompactSpace.elim_nhds_subcover V hV
  have covered (x : X.Carrier) : ∃ c ∈ s, x ∈ V c := by
    have hx : x ∈ ⋃ c ∈ s, V c := by rw [hs]; trivial
    simpa only [mem_iUnion,exists_prop] using hx
  by_cases hne : s.Nonempty
  · refine ⟨s.inf' hne r, (Finset.lt_inf'_iff hne).mpr (fun c _ ↦ hr c),?_⟩
    intro ρ hρ hρr f Ω hΩ hf hsub hspeed z hz
    obtain ⟨c,hcs,hc⟩ := covered (f 0)
    have ht := hb c ρ hρ (hρr.trans (s.inf'_le r hcs)) f Ω hΩ hf hsub hc.1 hspeed hz
    calc
      dist (f 0) (f z) ≤ dist (f 0) c + dist c (f z) := dist_triangle _ _ _
      _ < ε/2 + ε/2 := add_lt_add hc.2 (by simpa only [mem_ball,dist_comm] using ht)
      _ = ε := by ring
  · refine ⟨1,by norm_num,?_⟩
    intro ρ hρ hρr f
    obtain ⟨c,hcs,_⟩ := covered (f 0)
    exact (hne ⟨c,hcs⟩).elim

theorem bounded_curveSpeed_equicontinuousOn [CompactSpace X.Carrier]
    (g : KahlerMetric X) {ι : Type*} (f : ι → ℂ → X.Carrier)
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : ∀ i, MDifferentiableOn 𝓘(ℂ, ℂ) (model n) (f i) Ω)
    (hb : ∀ p ∈ Ω, ∃ R L : ℝ, 0 < R ∧ 0 ≤ L ∧ closedBall p R ⊆ Ω ∧
      ∀ i z, z ∈ closedBall p R → curveSpeed g (f i) z ≤ L) :
    EquicontinuousOn f Ω := by
  intro p hp
  apply EquicontinuousAt.equicontinuousWithinAt
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨R,L,hR,hL,hRΩ,hbound⟩ := hb p hp
  obtain ⟨r,hr,htrap⟩ := bounded_curveSpeed_uniform_trapping g hL hε
  let ρ := min r R
  have hρ : 0 < ρ := lt_min hr hR
  refine ⟨ρ,hρ,?_⟩
  intro z hz i
  let φ : ℂ → ℂ := fun w ↦ p + w
  have hφdiff : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) φ :=
    (differentiable_id.const_add p).mdifferentiable
  have hφmem {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) ρ) : φ w ∈ closedBall p R := by
    simpa [φ,mem_closedBall,dist_eq_norm] using
      (hw.trans (min_le_right r R))
  have hk : MDifferentiableOn 𝓘(ℂ, ℂ) (model n) (f i ∘ φ) (φ ⁻¹' Ω) :=
    (hf i).comp hφdiff.mdifferentiableOn (fun _ hw ↦ hw)
  have hspeed (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) ρ) :
      curveSpeed g (f i ∘ φ) w ≤ L := by
    have ha := curveSpeed_affine g p (1:ℂ) w
      (by simpa only [one_mul,φ] using
        (hf i).mdifferentiableAt (hΩ.mem_nhds (hRΩ (hφmem hw))))
    have hs : curveSpeed g (f i ∘ φ) w = curveSpeed g (f i) (φ w) := by
      simpa only [φ,Function.comp_def,one_mul,norm_one] using ha
    exact hs.trans_le (hbound i (φ w) (hφmem hw))
  have hw : z-p ∈ closedBall (0 : ℂ) ρ := by
    simpa only [mem_closedBall,dist_zero_right,← dist_eq_norm] using hz.le
  have ht := htrap ρ hρ.le (min_le_left r R) (f i ∘ φ) (φ ⁻¹' Ω)
    (hΩ.preimage hφdiff.continuous) hk (fun w hw ↦ hRΩ (hφmem hw)) hspeed (z-p) hw
  simpa only [Function.comp_def,φ,add_zero,add_sub_cancel] using ht

end UniversalCoverSplitting

open Set Filter Topology

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.CompactCurves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped Interval
open Set MeasureTheory
open scoped ENNReal
open Set Metric
open Set Metric Filter Topology
open scoped Manifold
open Set Filter Topology
open Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

attribute [local instance] OAI.UniversalCoverSplitting.instMetricSpaceCarrierOfCompactSpace_1
theorem manifold_holomorphic_locally_uniform_limit [CompactSpace X.Carrier]
    {f : ℕ → ℂ → X.Carrier} {F : ℂ → X.Carrier} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : ∀ j, MDifferentiableOn 𝓘(ℂ, ℂ) (model n) (f j) Ω)
    (hconv : TendstoLocallyUniformlyOn f F atTop Ω) :
    MDifferentiableOn 𝓘(ℂ, ℂ) (model n) F Ω := by
  have hc : ContinuousOn F Ω := hconv.continuousOn
    (Filter.Eventually.of_forall (fun j ↦ (hf j).continuousOn)).frequently
  intro p hp
  let c := F p
  let e := extChartAt (model n) c
  have hes : IsOpen e.source := isOpen_extChartAt_source c
  have hcs : c ∈ e.source := mem_extChartAt_source c
  obtain ⟨δ,hδ,hδsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hes.mem_nhds hcs)
  have hnear : Ω ∩ F ⁻¹' ball c (δ/3) ∈ 𝓝 p := inter_mem (hΩ.mem_nhds hp)
    ((hc.continuousAt (hΩ.mem_nhds hp)) (ball_mem_nhds c (by positivity)))
  obtain ⟨r,hr,hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  have hKΩ : closedBall p r ⊆ Ω := fun z hz ↦ (hrsub hz).1
  have hFsmall (z : ℂ) (hz : z ∈ closedBall p r) : dist (F z) c < δ/3 := (hrsub hz).2
  have hu : TendstoUniformlyOn f F atTop (closedBall p r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp hconv _ hKΩ (isCompact_closedBall p r)
  have hlate : ∀ᶠ j in atTop, MapsTo (f j) (ball p r) (closedBall c δ) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (δ/3) (by positivity)] with j hj
    intro z hz
    have hzK := ball_subset_closedBall hz
    have hdist : dist (f j z) (F z) < δ/3 := by simpa only [dist_comm] using hj z hzK
    have ht := dist_triangle (f j z) (F z) c
    have hh := hFsmall z hzK
    change dist (f j z) c ≤ δ
    linarith
  have hFmap : MapsTo F (ball p r) (closedBall c δ) := by
    intro z hz
    change dist (F z) c ≤ δ
    exact (hFsmall z (ball_subset_closedBall hz)).le.trans (by linarith)
  have heuc : UniformContinuousOn e (closedBall c δ) :=
    (isCompact_closedBall c δ).uniformContinuousOn_of_continuous ((continuousOn_extChartAt c).mono hδsub)
  have hl : TendstoLocallyUniformlyOn (fun j ↦ e ∘ f j) (e ∘ F) atTop (ball p r) :=
    heuc.comp_tendstoLocallyUniformlyOn (hconv.mono (ball_subset_closedBall.trans hKΩ)) hFmap hlate
  have hhol : ∀ᶠ j in atTop, DifferentiableOn ℂ (e ∘ f j) (ball p r) := by
    filter_upwards [hlate] with j hj
    intro z hz
    have hfj := (hf j).mdifferentiableAt (hΩ.mem_nhds (hKΩ (ball_subset_closedBall hz)))
    have hej : MDifferentiableAt (model n) (model n) e (f j z) :=
      mdifferentiableAt_extChartAt (by simpa only [e,extChartAt_source] using hδsub (hj hz))
    exact (hej.comp z hfj).differentiableAt.differentiableWithinAt
  have hchart := (hl.differentiableOn hhol isOpen_ball).differentiableAt
    (ball_mem_nhds p hr)
  have hfpc : F p ∈ e.source := by exact hcs
  have het : e (F p) ∈ e.target := e.map_source hfpc
  have hei : MDifferentiableAt (model n) (model n) e.symm (e (F p)) :=
    mdifferentiableOn_extChartAt_symm.mdifferentiableAt ((isOpen_extChartAt_target c).mem_nhds het)
  have hd := hei.comp p hchart.mdifferentiableAt
  apply (hd.congr_of_eventuallyEq ?_).mdifferentiableWithinAt
  filter_upwards [ball_mem_nhds p hr] with z hz
  exact (e.left_inv (hδsub (hFmap hz))).symm

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

attribute [local instance] OAI.UniversalCoverSplitting.instMetricSpaceCarrierOfCompactSpace_2
theorem bounded_curveSpeed_holomorphic_subsequence [CompactSpace X.Carrier]
    (g : KahlerMetric X) (f : ℕ → ℂ → X.Carrier) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : ∀ j, MDifferentiableOn 𝓘(ℂ, ℂ) (model n) (f j) Ω)
    (hb : ∀ p ∈ Ω, ∃ R L : ℝ, 0 < R ∧ 0 ≤ L ∧ closedBall p R ⊆ Ω ∧
      ∀ j z, z ∈ closedBall p R → curveSpeed g (f j) z ≤ L) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ F : ℂ → X.Carrier,
      MDifferentiableOn 𝓘(ℂ, ℂ) (model n) F Ω ∧
      TendstoLocallyUniformlyOn (f ∘ σ) F atTop Ω := by
  classical
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let ff (j : ℕ) : C(Ω,X.Carrier) :=
    ⟨fun z ↦ f j z, continuousOn_iff_continuous_domRestrict.mp (hf j).continuousOn⟩
  have he := bounded_curveSpeed_equicontinuousOn g f hΩ hf hb
  have he' : Equicontinuous (fun j z ↦ ff j z) := by
    intro z
    exact (equicontinuousAt_restrict_iff f z).mpr (he z z.property)
  obtain ⟨σ,hσ,G,hG⟩ := equicontinuous_compact_target_subsequence ff he'
  let F : ℂ → X.Carrier := fun z ↦ if hz : z ∈ Ω then G ⟨z,hz⟩ else f 0 z
  have hconv : TendstoLocallyUniformlyOn (f ∘ σ) F atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have ht := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hG
    convert ht using 1 <;> first | rfl | simp [F,Function.comp_def]
  exact ⟨σ,hσ,F,manifold_holomorphic_locally_uniform_limit hΩ (fun j ↦ hf (σ j)) hconv,hconv⟩

theorem eventual_curveSpeed_bound_to_bound (g : KahlerMetric X)
    (f : ℕ → ℂ → X.Carrier) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : ∀ j, MDifferentiableOn 𝓘(ℂ, ℂ) (model n) (f j) Ω)
    {p : ℂ} {R L : ℝ} (hsub : closedBall p R ⊆ Ω) (hL : 0 ≤ L)
    (he : ∀ᶠ j in atTop, ∀ z ∈ closedBall p R, curveSpeed g (f j) z ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j z, z ∈ closedBall p R → curveSpeed g (f j) z ≤ C := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  have hex (j : ℕ) : ∃ C : ℝ, ∀ z ∈ closedBall p R, curveSpeed g (f j) z ≤ C := by
    have h := (isCompact_closedBall p R).bddAbove_image
      ((curveSpeed_continuousOn g hΩ (hf j)).mono hsub)
    obtain ⟨C,hC⟩ := h
    exact ⟨C,fun z hz ↦ hC (mem_image_of_mem _ hz)⟩
  choose C hC using hex
  let B := ∑ j ∈ Finset.range N, max (C j) 0
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ le_max_right _ _)
  refine ⟨max L B,le_max_of_le_left hL,?_⟩
  intro j z hz
  by_cases hj : N ≤ j
  · exact (hN j hj z hz).trans (le_max_left _ _)
  · have hjN : j ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hj)
    have hjB : C j ≤ B := (le_max_left _ _).trans
      (Finset.single_le_sum (fun _ _ ↦ le_max_right _ _) hjN)
    exact (hC j z hz).trans (hjB.trans (le_max_right _ _))

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal NNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

attribute [local instance] OAI.UniversalCoverSplitting.instMetricSpaceCarrierOfCompactSpace_3
theorem bounded_curveArea_holomorphic_subsequence [CompactSpace X.Carrier]
    (g : KahlerMetric X) (f : ℕ → ℂ → X.Carrier) {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKn : K.Nonempty) (hKΩ : K ⊆ Ω)
    (hf : ∀ j, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (f j) Ω)
    (C : ℝ≥0) (hC : ∀ j, curveArea g (f j) K ≤ (C : ℝ≥0∞)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ A : Set ℂ, A.Finite ∧ A ⊆ K ∧
      ∃ F : ℂ → X.Carrier,
        MDifferentiableOn 𝓘(ℂ,ℂ) (model n) F (interior K \ A) ∧
        TendstoLocallyUniformlyOn (f ∘ σ) F atTop (interior K \ A) := by
  obtain ⟨η,hη,hsmall⟩ := small_area_weighted_speed g (by norm_num : (0:ℝ) < 1)
  let ε : ℝ≥0 := ⟨η,hη.le⟩
  have hε : 0 < ε := hη
  obtain ⟨τ,hτ,A,hA,hAK,hconc⟩ := bounded_density_finite_concentration hK hKn
    (fun j z ↦ ENNReal.ofReal (curveSpeed g (f j) z ^ 2)) C hC ε hε
  let U := interior K \ A
  have hU : IsOpen U := isOpen_interior.inter hA.isClosed.isOpen_compl
  have hUΩ : U ⊆ Ω := fun _ hz ↦ hKΩ (interior_subset hz.1)
  have hbound : ∀ p ∈ U, ∃ R L : ℝ, 0 < R ∧ 0 ≤ L ∧ closedBall p R ⊆ U ∧
      ∀ j z, z ∈ closedBall p R → curveSpeed g (f (τ j)) z ≤ L := by
    intro p hp
    obtain ⟨r,hr,hrK,he⟩ := hconc p hp
    obtain ⟨s,hs,hsU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
    let R := min (r/2) s
    have hR : 0 < R := lt_min (by positivity) hs
    have hRU : closedBall p R ⊆ U := (closedBall_subset_closedBall (min_le_right _ _)).trans hsU
    have hlate : ∀ᶠ j in atTop, ∀ z ∈ closedBall p R,
        curveSpeed g (f (τ j)) z ≤ 2/r := by
      filter_upwards [he] with j hj
      have ha : curveArea g (f (τ j)) (ball p r) < ENNReal.ofReal η := by
        have heps : (ε : ℝ≥0∞) = ENNReal.ofReal η :=
          (ENNReal.ofReal_eq_coe_nnreal hη.le).symm
        rw [← heps]
        exact hj
      intro z hz
      have hzr : dist z p ≤ r/2 := hz.trans (min_le_left _ _)
      have hzb : z ∈ ball p r := hzr.trans_lt (by linarith)
      have hw := hsmall (f (τ j)) Ω hΩ (hf (τ j)) p r hr (hrK.trans hKΩ) ha z hzb
      have hn := curveSpeed_nonneg g (f (τ j)) z
      apply (le_div_iff₀ hr).mpr
      nlinarith
    obtain ⟨L,hL,hb⟩ := eventual_curveSpeed_bound_to_bound g (f ∘ τ) hU
      (fun j ↦ (hf (τ j)).mono hUΩ) hRU (by positivity : 0 ≤ 2/r) hlate
    exact ⟨R,L,hR,hL,hRU,hb⟩
  obtain ⟨υ,hυ,F,hF,hconv⟩ := bounded_curveSpeed_holomorphic_subsequence g (f ∘ τ) hU
    (fun j ↦ (hf (τ j)).mono hUΩ) hbound
  exact ⟨τ ∘ υ,hτ.comp hυ,A,hA,hAK,F,hF,hconv⟩

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open Complex

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.Removable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped Interval
open Set MeasureTheory
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology MeasureTheory
open Complex
open Set Filter Topology

open Set Metric Filter Topology Complex

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
namespace UniversalCoverSplitting

variable {n : ℕ} {X : ComplexManifold n}

theorem finite_curveArea_scaled_speed [CompactSpace X.Carrier] (g : KahlerMetric X)
    {f : ℂ → X.Carrier} {R : ℝ} (hR : 0 < R)
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f (ball 0 R \ {0}))
    (ha : curveArea g f (ball 0 R \ {0}) ≠ (⊤ : ℝ≥0∞)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ δ →
      ‖z‖ * curveSpeed g f z < ε := by
  obtain ⟨η,hη,hsmall⟩ := small_area_weighted_speed g (half_pos hε)
  obtain ⟨a,ha',harea⟩ := finite_density_small_ball ha (ENNReal.ofReal_pos.mpr hη)
  let δ := min a R / 4
  have hδ : 0 < δ := div_pos (lt_min ha' hR) (by norm_num)
  have hδR : δ < R := by
    have hd := min_le_right a R
    dsimp [δ]; linarith [lt_min ha' hR]
  refine ⟨δ,hδ,hδR,?_⟩
  intro z hz hzδ
  have hc : closedBall z (‖z‖/2) ⊆ ball 0 R \ {0} := by
    intro w hw
    have hwz : dist w z ≤ ‖z‖/2 := hw
    have htri := dist_triangle w z 0
    simp only [dist_zero_right] at htri
    have htri' := dist_triangle z w 0
    simp only [dist_zero_right] at htri'
    rw [dist_comm z w] at htri'
    have hnorm : ‖w‖ < R := by
      have hzR := hzδ.trans hδR.le
      dsimp [δ] at hzδ
      have hh := min_le_right a R
      linarith
    refine ⟨by simpa using hnorm,?_⟩
    intro hw0
    have he : w = 0 := hw0
    subst w
    simp only [norm_zero,dist_zero_left] at htri' hwz
    linarith
  have hcsmall : ball z (‖z‖/2) ⊆ ball (0:ℂ) a := by
    intro w hw
    have hwz : dist w z < ‖z‖/2 := hw
    have htri := dist_triangle w z 0
    simp only [dist_zero_right] at htri
    have hh := min_le_left a R
    dsimp [δ] at hzδ
    have hn : ‖w‖ < a := by linarith
    simpa using hn
  have he : curveArea g f (ball z (‖z‖/2)) < ENNReal.ofReal η :=
    harea _ hcsmall (ball_subset_closedBall.trans hc)
  have hh := hsmall f (ball 0 R \ {0}) (isOpen_ball.sdiff isClosed_singleton) hf z (‖z‖/2)
    (half_pos hz) hc he z (mem_ball_self (half_pos hz))
  simp only [dist_self,sub_zero] at hh
  nlinarith

end UniversalCoverSplitting

open Set Metric Filter Topology Complex

open Set Metric Filter Topology Complex
open scoped Manifold ENNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}
local instance instMetricSpaceCarrierOfCompactSpace_4 [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

theorem finite_curveArea_compact_chart [CompactSpace X.Carrier] (g : KahlerMetric X)
    {f : ℂ → X.Carrier} {R : ℝ} (hR : 0 < R)
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f (ball 0 R \ {0}))
    (ha : curveArea g f (ball 0 R \ {0}) ≠ (⊤ : ℝ≥0∞)) :
    ∃ c : X.Carrier, ∃ r B : ℝ, 0 < r ∧ r < R ∧ 0 < B ∧
      closedBall ((extChartAt (model n) c) c) B ⊆ (extChartAt (model n) c).target ∧
      ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ r →
        f z ∈ (extChartAt (model n) c).source ∧
        (extChartAt (model n) c) (f z) ∈ closedBall ((extChartAt (model n) c) c) B := by
  let u (j : ℕ) : ℝ := 1 / (j+1)
  have hu (j : ℕ) : 0 < u j := by dsimp [u]; positivity
  have hu0 : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨c,σ,hσ,hlim⟩ := CompactSpace.tendsto_subseq (fun j ↦ f (u j : ℂ))
  let e : OpenPartialHomeomorph X.Carrier (Model n) :=
    { extChartAt (model n) c with
      continuousOn_toFun := continuousOn_extChartAt c
      continuousOn_invFun := continuousOn_extChartAt_symm c
      open_source := isOpen_extChartAt_source c
      open_target := isOpen_extChartAt_target c }
  have hc : c ∈ e.source := mem_extChartAt_source c
  obtain ⟨B,hB,hBt⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (e.open_target.mem_nhds (e.map_source hc))
  obtain ⟨C,D,hC,_,hcomp⟩ := g.exists_chart_speed_comparison c (isCompact_closedBall (e c) B) hBt
  let L := B/100
  have hL : 0 < L := div_pos hB (by norm_num)
  obtain ⟨δ,hδ,hδR,hspeed⟩ := finite_curveArea_scaled_speed g hR hf ha (div_pos hL hC)
  have hnear : e.source ∩ e ⁻¹' ball (e c) (B/4) ∈ 𝓝 c :=
    (e.isOpen_inter_preimage isOpen_ball).mem_nhds ⟨hc, by simpa using div_pos hB (by norm_num : (0:ℝ)<4)⟩
  have hnear' : ∀ᶠ j in atTop, f (u (σ j):ℂ) ∈ e.source ∩ e ⁻¹' ball (e c) (B/4) := hlim hnear
  have he := hnear'.and ((hu0.comp hσ.tendsto_atTop).eventually_lt_const hδ)
  obtain ⟨j,hj,hjr⟩ := he.exists
  let r := u (σ j)
  have hr : 0 < r := hu _
  have hrδ : r < δ := hjr
  have hrR : r < R := hrδ.trans hδR
  have hsource (z : ℂ) (hz : 0 < ‖z‖) (hzr : ‖z‖ ≤ r) : z ∈ ball 0 R \ {0} := by
    refine ⟨by simpa using hzr.trans_lt hrR,?_⟩
    simpa only [mem_singleton_iff] using (norm_pos_iff.mp hz)
  have hK (x : X.Carrier) (hx : x ∈ e.symm '' closedBall (e c) B) :
      x ∈ e.source ∧ e x ∈ closedBall (e c) B := by
    obtain ⟨v,hv,rfl⟩ := hx
    exact ⟨e.map_target (hBt hv), by rwa [e.right_inv (hBt hv)]⟩
  have hdiff (z : ℂ) (hz : 0 < ‖z‖) (hzr : ‖z‖ ≤ r)
      (hk : f z ∈ e.symm '' closedBall (e c) B) : DifferentiableAt ℂ (e ∘ f) z := by
    have hfd := hf.mdifferentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds (hsource z hz hzr))
    have hed : MDifferentiableAt (model n) (model n) e (f z) :=
      mdifferentiableAt_extChartAt (by simpa only [e,extChartAt_source] using (hK _ hk).1)
    exact (hed.comp z hfd).differentiableAt
  have hbound (z : ℂ) (hz : 0 < ‖z‖) (hzr : ‖z‖ ≤ r)
      (hk : f z ∈ e.symm '' closedBall (e c) B) : ‖deriv (e ∘ f) z‖ * ‖z‖ ≤ L := by
    have hfd := hf.mdifferentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds (hsource z hz hzr))
    have hnorm : ‖deriv (e ∘ f) z‖ ≤ C * curveSpeed g f z := by
      change ‖deriv ((extChartAt (model n) c) ∘ f) z‖ ≤ C * curveSpeed g f z
      rw [chart_deriv_curve hfd c (hK _ hk).1]
      exact (hcomp (f z) (hK _ hk).1 (hK _ hk).2 (mfderiv 𝓘(ℂ,ℂ) (model n) f z (1:ℂ))).1
    have hh := hspeed z hz (hzr.trans hrδ.le)
    have hm := mul_lt_mul_of_pos_left hh hC
    rw [mul_div_cancel₀ _ hC.ne'] at hm
    nlinarith
  have hcircle : ∀ z ∈ sphere (0:ℂ) r, f z ∈ e.source ∧ e (f z) ∈ ball (e c) B := by
    apply chart_trapping_on_circle e hB hr hL.le hBt
    · apply hf.continuousOn.mono
      intro z hz
      have hn : ‖z‖ = r := by simpa using hz
      exact hsource z (hn ▸ hr) hn.le
    · refine ⟨hj.1,?_⟩
      have hh : dist (e (f (r:ℂ))) (e c) < B/4 := hj.2
      dsimp [L]; linarith
    · intro z hz hk
      have hn : ‖z‖ = r := by simpa using hz
      exact hdiff z (hn ▸ hr) hn.le hk
    · intro z hz hk
      have hn : ‖z‖ = r := by simpa using hz
      simpa only [hn] using hbound z (hn ▸ hr) hn.le hk
  have htrap := punctured_chart_trapping e hB hr hL.le hBt
    (hf.continuousOn.mono (fun z hz ↦ hsource z hz.1 hz.2))
    (fun z hz ↦ ⟨(hcircle z hz).1,ball_subset_closedBall (hcircle z hz).2⟩)
    (show dist (e (f (r:ℂ))) (e c) + 24*L < B from by
      have hh : dist (e (f (r:ℂ))) (e c) < B/4 := hj.2
      dsimp [L]; linarith) hdiff hbound
  exact ⟨c,r,B,hr,hrR,hB,hBt,htrap⟩

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

theorem compact_chart_removable {f : ℂ → X.Carrier} {R r B : ℝ}
    (_hR : 0 < R) (hr : 0 < r) (hrR : r < R) (c : X.Carrier)
    (hBt : closedBall ((extChartAt (model n) c) c) B ⊆ (extChartAt (model n) c).target)
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f (ball 0 R \ {0}))
    (ht : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ r →
      f z ∈ (extChartAt (model n) c).source ∧
      (extChartAt (model n) c) (f z) ∈ closedBall ((extChartAt (model n) c) c) B) :
    ∃ x : X.Carrier, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (Function.update f 0 x) (ball 0 R) := by
  classical
  let e := extChartAt (model n) c
  let Ω := ball (0:ℂ) r \ {0}
  have hsub : Ω ⊆ ball 0 R \ {0} := sdiff_subset_sdiff_left (ball_subset_ball hrR.le)
  have hmem (z : ℂ) (hz : z ∈ Ω) : f z ∈ e.source ∧ e (f z) ∈ closedBall (e c) B := by
    exact ht z (norm_pos_iff.mpr hz.2) (le_of_lt (by simpa using hz.1))
  have hd : DifferentiableOn ℂ (e ∘ f) Ω := by
    intro z hz
    have hfd := hf.mdifferentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds (hsub hz))
    have he : MDifferentiableAt (model n) (model n) e (f z) :=
      mdifferentiableAt_extChartAt (by simpa only [e,extChartAt_source] using (hmem z hz).1)
    exact (he.comp z hfd).differentiableAt.differentiableWithinAt
  have hb : BddAbove (norm ∘ (e ∘ f) '' Ω) := by
    refine ⟨B + ‖e c‖,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    have ht' := norm_le_insert (e c) (e (f z))
    rw [norm_sub_rev] at ht'
    have hh : ‖e (f z) - e c‖ ≤ B := by simpa only [mem_closedBall,dist_eq_norm] using (hmem z hz).2
    dsimp [Function.comp_def]
    linarith
  let b := limUnder (𝓝[≠] (0:ℂ)) (e ∘ f)
  let q := Function.update (e ∘ f) 0 b
  have hq : DifferentiableOn ℂ q (ball 0 r) :=
    differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 hr) hd hb
  have hq0 := hq.differentiableAt (ball_mem_nhds 0 hr)
  have hlim : Tendsto (e ∘ f) (𝓝[≠] (0:ℂ)) (𝓝 b) :=
    continuousAt_update_same.mp hq0.continuousAt
  have hevent : ∀ᶠ z in 𝓝[≠] (0:ℂ), e (f z) ∈ closedBall (e c) B := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0:ℂ) hr),self_mem_nhdsWithin] with z hz hz0
    exact (hmem z ⟨hz,hz0⟩).2
  have hbK : b ∈ closedBall (e c) B := isClosed_closedBall.mem_of_tendsto hlim hevent
  have hbi : MDifferentiableAt (model n) (model n) e.symm b :=
    mdifferentiableOn_extChartAt_symm.mdifferentiableAt
      ((isOpen_extChartAt_target c).mem_nhds (hBt hbK))
  have hqzero : q 0 = b := Function.update_self _ _ _
  have hcomp : MDifferentiableAt 𝓘(ℂ,ℂ) (model n) (e.symm ∘ q) 0 := by
    apply (hqzero ▸ hbi).comp 0 hq0.mdifferentiableAt
  have hzero : MDifferentiableAt 𝓘(ℂ,ℂ) (model n) (Function.update f 0 (e.symm b)) 0 := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds (0:ℂ) hr] with z hz
    by_cases hz0 : z = 0
    · subst z
      simp only [Function.comp_apply,hqzero,Function.update_self]
    · simp only [Function.update_of_ne hz0,q,Function.comp_apply]
      exact (e.left_inv (hmem z ⟨hz,hz0⟩).1).symm
  refine ⟨e.symm b,?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · subst z; exact hzero.mdifferentiableWithinAt
  · have hd' := hf.mdifferentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz,hz0⟩)
    apply (hd'.congr_of_eventuallyEq ?_).mdifferentiableWithinAt
    filter_upwards [isOpen_compl_singleton.mem_nhds hz0] with w hw
    exact Function.update_of_ne hw _ _

theorem finite_curveArea_removable [CompactSpace X.Carrier] (g : KahlerMetric X)
    {f : ℂ → X.Carrier} {R : ℝ} (hR : 0 < R)
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f (ball 0 R \ {0}))
    (ha : curveArea g f (ball 0 R \ {0}) ≠ (⊤ : ℝ≥0∞)) :
    ∃ x : X.Carrier, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (Function.update f 0 x) (ball 0 R) := by
  obtain ⟨c,r,B,hr,hrR,_,hBt,ht⟩ := finite_curveArea_compact_chart g hR hf ha
  exact compact_chart_removable hR hr hrR c hBt hf ht

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}
local instance instMetricSpaceCarrierOfCompactSpace_5 [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

theorem locally_uniform_curveSpeed_tendsto [CompactSpace X.Carrier] (g : KahlerMetric X)
    {f : ℕ → ℂ → X.Carrier} {F : ℂ → X.Carrier} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : ∀ j, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (f j) Ω)
    (hconv : TendstoLocallyUniformlyOn f F atTop Ω) {p : ℂ} (hp : p ∈ Ω) :
    Tendsto (fun j ↦ curveSpeed g (f j) p) atTop (𝓝 (curveSpeed g F p)) := by
  have hF := manifold_holomorphic_locally_uniform_limit hΩ hf hconv
  have hc : ContinuousOn F Ω := hconv.continuousOn
    (Filter.Eventually.of_forall (fun j ↦ (hf j).continuousOn)).frequently
  let c := F p
  let e := extChartAt (model n) c
  have hes : IsOpen e.source := isOpen_extChartAt_source c
  have hcs : c ∈ e.source := mem_extChartAt_source c
  obtain ⟨δ,hδ,hδsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hes.mem_nhds hcs)
  have hnear : Ω ∩ F ⁻¹' ball c (δ/3) ∈ 𝓝 p := inter_mem (hΩ.mem_nhds hp)
    ((hc.continuousAt (hΩ.mem_nhds hp)) (ball_mem_nhds c (by positivity)))
  obtain ⟨r,hr,hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  have hKΩ : closedBall p r ⊆ Ω := fun z hz ↦ (hrsub hz).1
  have hFsmall (z : ℂ) (hz : z ∈ closedBall p r) : dist (F z) c < δ/3 := (hrsub hz).2
  have hu : TendstoUniformlyOn f F atTop (closedBall p r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp hconv _ hKΩ (isCompact_closedBall p r)
  have hlate : ∀ᶠ j in atTop, MapsTo (f j) (ball p r) (closedBall c δ) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (δ/3) (by positivity)] with j hj
    intro z hz
    have hzK := ball_subset_closedBall hz
    have hdist : dist (f j z) (F z) < δ/3 := by simpa only [dist_comm] using hj z hzK
    have ht := dist_triangle (f j z) (F z) c
    have hh := hFsmall z hzK
    change dist (f j z) c ≤ δ
    linarith
  have hFmap : MapsTo F (ball p r) (closedBall c δ) := by
    intro z hz
    change dist (F z) c ≤ δ
    exact (hFsmall z (ball_subset_closedBall hz)).le.trans (by linarith)
  have heuc : UniformContinuousOn e (closedBall c δ) :=
    (isCompact_closedBall c δ).uniformContinuousOn_of_continuous ((continuousOn_extChartAt c).mono hδsub)
  have hl : TendstoLocallyUniformlyOn (fun j ↦ e ∘ f j) (e ∘ F) atTop (ball p r) :=
    heuc.comp_tendstoLocallyUniformlyOn (hconv.mono (ball_subset_closedBall.trans hKΩ)) hFmap hlate
  have hhol : ∀ᶠ j in atTop, DifferentiableOn ℂ (e ∘ f j) (ball p r) := by
    filter_upwards [hlate] with j hj
    intro z hz
    have hfj := (hf j).mdifferentiableAt (hΩ.mem_nhds (hKΩ (ball_subset_closedBall hz)))
    have hej : MDifferentiableAt (model n) (model n) e (f j z) :=
      mdifferentiableAt_extChartAt (by simpa only [e,extChartAt_source] using hδsub (hj hz))
    exact (hej.comp z hfj).differentiableAt.differentiableWithinAt
  have hpb : p ∈ ball p r := mem_ball_self hr
  have ht := (hl.tendsto_at hpb).prodMk ((hl.deriv hhol isOpen_ball).tendsto_at hpb)
  rw [← nhds_prod_eq] at ht
  have het : e (F p) ∈ (extChartAt (model n) c).target := e.map_source hcs
  have hq := ((g.continuous_quadraticInChart c).continuousAt
    (((isOpen_extChartAt_target c).prod isOpen_univ).mem_nhds ⟨het,mem_univ _⟩)).tendsto.comp ht
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hq
  have hfp := hF.mdifferentiableAt (hΩ.mem_nhds hp)
  dsimp only [Function.comp_def,e] at hs
  have heq := curveSpeed_eq_chart g hfp c hcs
  dsimp only [Function.comp_def] at heq
  rw [← heq] at hs
  apply Filter.Tendsto.congr' _ hs
  filter_upwards [hlate] with j hj
  exact (curveSpeed_eq_chart g ((hf j).mdifferentiableAt (hΩ.mem_nhds hp)) c
    (hδsub (hj hpb))).symm

theorem locally_uniform_curveArea_le [CompactSpace X.Carrier] (g : KahlerMetric X)
    {f : ℕ → ℂ → X.Carrier} {F : ℂ → X.Carrier} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : ∀ j, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (f j) Ω)
    (hconv : TendstoLocallyUniformlyOn f F atTop Ω) {C : ℝ≥0∞}
    (hC : ∀ j, curveArea g (f j) Ω ≤ C) : curveArea g F Ω ≤ C := by
  let w (j : ℕ) (z : ℂ) := ENNReal.ofReal (curveSpeed g (f j) z ^ 2)
  have hm (j : ℕ) : AEMeasurable (w j) (volume.restrict Ω) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn ((curveSpeed_continuousOn g hΩ (hf j)).pow 2))).aemeasurable hΩ.measurableSet
  have hl (z : ℂ) (hz : z ∈ Ω) : liminf (fun j ↦ w j z) atTop =
      ENNReal.ofReal (curveSpeed g F z ^ 2) := by
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((locally_uniform_curveSpeed_tendsto g hΩ hf hconv hz).pow 2)).liminf_eq
  calc
    curveArea g F Ω = ∫⁻ z in Ω, liminf (fun j ↦ w j z) atTop := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
      exact (hl z hz).symm
    _ ≤ liminf (fun j ↦ curveArea g (f j) Ω) atTop := lintegral_liminf_le' hm
    _ ≤ C := by
      exact liminf_le_of_frequently_le (Filter.Eventually.of_forall hC).frequently

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.HolomorphicIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology MeasureTheory
open scoped Interval
open Set Filter Topology Metric Complex
open Set Filter Topology Metric
open Set Metric Filter Topology
open scoped ContDiff
open Set
open scoped Manifold ContDiff
open Set Metric
open Set Filter Topology
open scoped Manifold

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

theorem finite_curveArea_removable_at [CompactSpace X.Carrier] (g : KahlerMetric X)
    {f : ℂ → X.Carrier} {p : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f (ball p R \ {p}))
    (ha : curveArea g f (ball p R \ {p}) ≠ (⊤ : ℝ≥0∞)) :
    ∃ x : X.Carrier, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (Function.update f p x) (ball p R) := by
  have him : (fun z : ℂ ↦ p + (1:ℝ) • z) '' (ball 0 R \ {0}) = ball p R \ {p} := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      simpa [dist_eq_norm, add_sub_cancel_left, add_eq_left] using hw
    · intro hz
      refine ⟨z-p,?_,by simp⟩
      simpa [dist_eq_norm, sub_eq_zero] using hz
  have hmap : MapsTo (fun z : ℂ ↦ p+z) (ball 0 R \ {0}) (ball p R \ {p}) := by
    intro z hz
    rw [← him]
    exact ⟨z,hz,by simp⟩
  have hq : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (fun z ↦ f (p+z)) (ball 0 R \ {0}) :=
    hf.comp (((differentiable_const p).add differentiable_id).mdifferentiable.mdifferentiableOn) hmap
  have haq : curveArea g (fun z ↦ f (p+z)) (ball 0 R \ {0}) ≠ (⊤ : ℝ≥0∞) := by
    have he := curveArea_positive_affine g (ball 0 R \ {0})
      (isOpen_ball.sdiff isClosed_singleton).measurableSet p (by norm_num : (0:ℝ)<1)
      (fun z hz ↦ hf.mdifferentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds (him ▸ hz)))
    rw [him] at he
    simpa only [one_smul] using he.trans_ne ha
  obtain ⟨x,hx⟩ := finite_curveArea_removable g hR hq haq
  have hback : MapsTo (fun z : ℂ ↦ z-p) (ball p R) (ball 0 R) := by
    intro z hz; simpa only [mem_ball,dist_eq_norm,sub_zero] using hz
  have heq : (Function.update (fun z ↦ f (p+z)) 0 x) ∘ (fun z : ℂ ↦ z-p) =
      Function.update f p x := by
    funext z
    by_cases hz : z = p
    · subst z; simp
    · simp only [Function.comp_apply,Function.update_of_ne hz,
        Function.update_of_ne (sub_ne_zero.mpr hz),add_sub_cancel]
  refine ⟨x,?_⟩
  rw [← heq]
  exact hx.comp ((differentiable_id.sub_const p).mdifferentiable.mdifferentiableOn) hback

theorem finite_curveArea_remove_finite [CompactSpace X.Carrier] (g : KahlerMetric X)
    {f : ℂ → X.Carrier} {Ω A : Set ℂ} (hΩ : IsOpen Ω) (hA : A.Finite)
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f (Ω \ A))
    (ha : curveArea g f (Ω \ A) ≠ (⊤ : ℝ≥0∞)) :
    ∃ F : ℂ → X.Carrier, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) F Ω ∧ EqOn F f (Ω \ A) := by
  classical
  have hloc : ∀ p ∈ Ω ∩ A, ∃ x : X.Carrier,
      MDifferentiableAt 𝓘(ℂ,ℂ) (model n) (Function.update f p x) p := by
    intro p hp
    have hN : Ω \ (A \ {p}) ∈ 𝓝 p :=
      (hΩ.sdiff (hA.sdiff : (A \ {p}).Finite).isClosed).mem_nhds ⟨hp.1,by simp⟩
    obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp hN
    have hsub' : ball p R \ {p} ⊆ Ω \ A := by
      intro z hz
      have hh := hsub hz.1
      refine ⟨hh.1,fun hzA ↦ hh.2 ⟨hzA,hz.2⟩⟩
    obtain ⟨x,hx⟩ := finite_curveArea_removable_at g hR (hf.mono hsub')
      (ne_top_of_le_ne_top ha (curveArea_mono g f hsub'))
    exact ⟨x,hx.mdifferentiableAt (ball_mem_nhds p hR)⟩
  choose x hx using hloc
  let F : ℂ → X.Carrier := fun p ↦ if hp : p ∈ Ω ∩ A then x p hp else f p
  have heq : EqOn F f (Ω \ A) := by
    intro p hp
    exact dite_eq_right (fun hh ↦ hp.2 hh.2)
  refine ⟨F,?_,heq⟩
  intro p hp
  by_cases hpA : p ∈ A
  · have hd := hx p ⟨hp,hpA⟩
    apply (hd.congr_of_eventuallyEq ?_).mdifferentiableWithinAt
    filter_upwards [(hA.sdiff : (A \ {p}).Finite).isClosed.isOpen_compl.mem_nhds
      (show p ∉ A \ {p} by simp)] with z hz
    by_cases hzp : z = p
    · subst z; simp [F, hp,hpA]
    · have hzA : z ∉ A := fun hh ↦ hz ⟨hh,hzp⟩
      simp [F,hzA,Function.update_of_ne hzp]
  · have hd := hf.mdifferentiableAt ((hΩ.sdiff hA.isClosed).mem_nhds ⟨hp,hpA⟩)
    apply (hd.congr_of_eventuallyEq ?_).mdifferentiableWithinAt
    filter_upwards [hA.isClosed.isOpen_compl.mem_nhds hpA] with z hz
    change z ∉ A at hz
    simp [F,hz]

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold ENNReal NNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}
local instance instMetricSpaceCarrierOfCompactSpace_6 [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

theorem bounded_curveArea_subsequence_with_removed_limit [CompactSpace X.Carrier]
    (g : KahlerMetric X) (f : ℕ → ℂ → X.Carrier) {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKn : K.Nonempty) (hKΩ : K ⊆ Ω)
    (hf : ∀ j, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (f j) Ω)
    (C : ℝ≥0) (hC : ∀ j, curveArea g (f j) K ≤ (C : ℝ≥0∞)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ A : Set ℂ, A.Finite ∧ A ⊆ K ∧
      ∃ F : ℂ → X.Carrier, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) F (interior K) ∧
        TendstoLocallyUniformlyOn (f ∘ σ) F atTop (interior K \ A) := by
  obtain ⟨σ,hσ,A,hA,hAK,F,hF,hconv⟩ :=
    bounded_curveArea_holomorphic_subsequence g f hΩ hK hKn hKΩ hf C hC
  have hU : IsOpen (interior K \ A) := isOpen_interior.sdiff hA.isClosed
  have hUK : interior K \ A ⊆ K := sdiff_subset.trans interior_subset
  have ha : curveArea g F (interior K \ A) ≤ (C : ℝ≥0∞) :=
    locally_uniform_curveArea_le g hU
      (fun j ↦ (hf (σ j)).mono (hUK.trans hKΩ)) hconv
      (fun j ↦ (curveArea_mono g (f (σ j)) hUK).trans (hC (σ j)))
  obtain ⟨G,hG,hGF⟩ := finite_curveArea_remove_finite g isOpen_interior hA hF
    (ne_top_of_le_ne_top ENNReal.coe_ne_top ha)
  exact ⟨σ,hσ,A,hA,hAK,G,hG,hconv.congr_right hGF.symm⟩

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.BoxGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open scoped Interval
open Set Filter Topology Metric Complex
open Set Filter Topology Metric
open scoped ContDiff
open Set
open scoped Manifold ContDiff
open Set Metric
open Set Filter Topology
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold

namespace UniversalCoverSplitting

variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem box_eqOn_of_diagonal (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {f g : ℂ × ℂ → X.Carrier}
    (hf : IsBox S (U ×ˢ U) f) (hg : IsBox S (U ×ˢ U) g)
    (heq : ∀ z ∈ U, f (z,z) = g (z,z)) : EqOn f g (U ×ˢ U) := by
  intro z hz
  exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq (hU.prod hU) (hUc.prod hUc)
    (x := (z.1,z.1)) hf.1 hg.1 ⟨hz.1,hz.1⟩ (box_diagonal_germ_unique h₁ h₂ hU hf hg heq hz.1) hz

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem holomorphic_curve_box_thickening (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → X.Carrier} (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f D) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ (∀ z ∈ D, (z,z) ∈ U) ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S U F ∧ ∀ z ∈ D, F (z,z) = f z := by
  classical
  have hloc (p : D) : ∃ e : SplittingChart S, ∃ R : ℝ, 0 < R ∧
      ball (p:ℂ) R ⊆ D ∧ MapsTo f (ball (p:ℂ) R) e.chart.source := by
    obtain ⟨e,he,_⟩ := exists_splittingChart S h₁ h₂ (f p)
    have hn := (hf.continuousOn.continuousAt (hD.mem_nhds p.property)) (e.chart.open_source.mem_nhds he)
    obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (hD.mem_nhds p.property) hn)
    exact ⟨e,R,hR,fun z hz ↦ (hsub hz).1,fun z hz ↦ (hsub hz).2⟩
  choose e R hR hRD hRe using hloc
  let V (p : D) : Set ℂ := ball (p:ℂ) (R p)
  let W (p : D) : Set (ℂ × ℂ) := V p ×ˢ V p
  let F (p : D) : ℂ × ℂ → X.Carrier := fun z ↦
    (e p).chart.symm (((e p).chart (f z.1)).1,((e p).chart (f z.2)).2)
  have hbox (p : D) : IsBox S (W p) (F p) :=
    ((e p).diagonal_box isOpen_ball (hf.mono (hRD p)) (hRe p)).1
  have hdiag (p : D) (z : ℂ) (hz : z ∈ V p) : F p (z,z) = f z :=
    ((e p).diagonal_box isOpen_ball (hf.mono (hRD p)) (hRe p)).2 z hz
  have hcompat (p q : D) : EqOn (F p) (F q) (W p ∩ W q) := by
    let B : Set ℂ := V p ∩ V q
    have hB : IsOpen B := isOpen_ball.inter isOpen_ball
    have hBc : IsPreconnected B := ((convex_ball (p:ℂ) (R p)).inter (convex_ball (q:ℂ) (R q))).isPreconnected
    have hp : B ×ˢ B ⊆ W p := prod_mono inter_subset_left inter_subset_left
    have hq : B ×ˢ B ⊆ W q := prod_mono inter_subset_right inter_subset_right
    have he := box_eqOn_of_diagonal h₁ h₂ hB hBc ((hbox p).mono hp) ((hbox q).mono hq)
      (fun z hz ↦ (hdiag p z hz.1).trans (hdiag q z hz.2).symm)
    intro z hz
    exact he ⟨⟨hz.1.1,hz.2.1⟩,⟨hz.1.2,hz.2.2⟩⟩
  obtain ⟨G,hG,hGF⟩ := glue_boxes W (fun _ ↦ isOpen_ball.prod isOpen_ball) F hbox hcompat (f 0)
  refine ⟨⋃ p, W p,isOpen_iUnion (fun _ ↦ isOpen_ball.prod isOpen_ball),?_,G,hG,?_⟩
  · intro z hz
    exact mem_iUnion.mpr ⟨⟨z,hz⟩,mem_ball_self (hR ⟨z,hz⟩),mem_ball_self (hR ⟨z,hz⟩)⟩
  · intro z hz
    have hh : (z,z) ∈ W ⟨z,hz⟩ := ⟨mem_ball_self (hR ⟨z,hz⟩),mem_ball_self (hR ⟨z,hz⟩)⟩
    exact (hGF ⟨z,hz⟩ hh).trans (hdiag ⟨z,hz⟩ z hh.1)

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.ClosedForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open scoped Interval
open Set Filter Topology Metric Complex
open Set Filter Topology Metric
open scoped ContDiff
open Set Metric
open Set Filter Topology
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold
open scoped Manifold ContDiff
open Set

namespace UniversalCoverSplitting

variable {n : ℕ} {X : ComplexManifold n}

theorem KahlerMetric.skew_I (g : KahlerMetric X) (x : X.Carrier) (u v : Tangent X x) :
    g.metric x (Complex.I • u) v = - g.metric x (Complex.I • v) u := by
  have h := g.hermitian x u (Complex.I • v)
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at h
  rw [g.symmetric x u (Complex.I • v)] at h
  linarith

theorem KahlerMetric.skew_fundamentalInChart (g : KahlerMetric X) (c : X.Carrier)
    (z u v : Model n) : fundamentalInChart g.metric c z u v =
      -fundamentalInChart g.metric c z v u := by
  let q : Model n →L[ℂ] Tangent X ((extChartAt (model n) c).symm z) :=
    mfderiv (model n) (model n) (extChartAt (model n) c).symm z
  change g.metric _ (q (Complex.I • u)) (q v) = - g.metric _ (q (Complex.I • v)) (q u)
  rw [q.map_smul, q.map_smul]
  exact g.skew_I _ _ _

def kahlerFormInChart (g : KahlerMetric X) (c : X.Carrier) (z : Model n) :
    (Model n) [⋀^Fin 2]→L[ℝ] ℝ :=
  alternatingBilinear ((continuousMetricInChart g.metric c z).comp
    ((Complex.I • ContinuousLinearMap.id ℂ (Model n)).restrictScalars ℝ))

theorem kahlerFormInChart_apply (g : KahlerMetric X) (c : X.Carrier)
    (z : Model n) (v : Fin 2 → Model n) :
    kahlerFormInChart g c z v = fundamentalInChart g.metric c z (v 0) (v 1) := by
  rw [kahlerFormInChart, alternatingBilinear_apply]
  change (fundamentalInChart g.metric c z (v 0) (v 1) -
    fundamentalInChart g.metric c z (v 1) (v 0)) / 2 = _
  rw [g.skew_fundamentalInChart c z (v 1) (v 0)]
  ring

theorem KahlerMetric.smooth_formInChart (g : KahlerMetric X) (c : X.Carrier) :
    ContDiffOn ℝ ∞ (kahlerFormInChart g c) (extChartAt (model n) c).target := by
  have hB : ContDiffOn ℝ ∞ (continuousMetricInChart g.metric c)
      (extChartAt (model n) c).target := by
    apply contDiffOn_clm_apply.mpr
    intro u
    apply contDiffOn_clm_apply.mpr
    intro v
    exact g.smooth c u v
  exact alternatingBilinear_contDiff (hB.clm_comp contDiffOn_const)

theorem KahlerMetric.closed_formInChart (g : KahlerMetric X) (c : X.Carrier)
    {z : Model n} (hz : z ∈ (extChartAt (model n) c).target) :
    extDeriv (kahlerFormInChart g c) z = 0 := by
  have hd := (g.smooth_formInChart c).differentiableOn (by simp) z hz
  have hda := hd.differentiableAt (isOpen_extChartAt_target c |>.mem_nhds hz)
  ext v
  rw [extDeriv_apply hda]
  norm_num [kahlerFormInChart_apply, Fin.sum_univ_succ, Fin.removeNth, Fin.succAbove]
  have hm : (fun y ↦ fundamentalInChart g.metric c y (v 0) (v 2)) =
      -(fun y ↦ fundamentalInChart g.metric c y (v 2) (v 0)) := by
    funext y
    exact g.skew_fundamentalInChart c y _ _
  rw [hm, fderiv_neg]
  simpa [add_assoc] using g.closed c z hz (v 0) (v 1) (v 2)

end UniversalCoverSplitting

open Set Filter Topology Metric Complex
open scoped Real

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.FormDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open scoped Interval
open Set Filter Topology Metric
open scoped ContDiff
open Set Metric
open Set Filter Topology
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold
open scoped Manifold ContDiff
open Set
open Set Filter Topology Metric Complex
open scoped Real

open scoped ContDiff
open Set

open scoped Manifold ContDiff
open Set Filter Topology
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

def pullbackKahler (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier) (z : ℂ × ℂ) :
    (ℂ × ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
  alternatingBilinear ((pullbackMetric g f z).comp
    ((Complex.I • ContinuousLinearMap.id ℂ (ℂ × ℂ)).restrictScalars ℝ))

theorem pullbackKahler_apply (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    (z : ℂ × ℂ) (v : Fin 2 → ℂ × ℂ) :
    pullbackKahler g f z v = g.metric (f z)
      (Complex.I • mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (v 0))
      (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (v 1)) := by
  rw [pullbackKahler, alternatingBilinear_apply]
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f z) := mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z
  change (g.metric (f z) (D (Complex.I • v 0)) (D (v 1)) -
    g.metric (f z) (D (Complex.I • v 1)) (D (v 0))) / 2 = _
  rw [D.map_smul, D.map_smul, g.skew_I (f z) (D (v 1)) (D (v 0))]
  dsimp only [D]
  ring_nf
  rfl

theorem chart_derivative_twoDim {f : ℂ × ℂ → X.Carrier} {z : ℂ × ℂ}
    (hf : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) (model n) f z)
    (c : X.Carrier) (hc : f z ∈ (extChartAt (model n) c).source) :
    fderiv ℂ ((extChartAt (model n) c) ∘ f) z =
      (mfderiv (model n) (model n) (extChartAt (model n) c) (f z)).comp
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z) := by
  have he : MDifferentiableAt (model n) (model n) (extChartAt (model n) c) (f z) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hc)
  rw [← mfderiv_eq_fderiv, mfderiv_comp z he hf]

theorem pullbackKahler_eq_chart (g : KahlerMetric X) {f : ℂ × ℂ → X.Carrier}
    {z : ℂ × ℂ} (hf : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) (model n) f z)
    (c : X.Carrier) (hc : f z ∈ (extChartAt (model n) c).source) :
    pullbackKahler g f z =
      (kahlerFormInChart g c ((extChartAt (model n) c) (f z))).compContinuousLinearMap
        (fderiv ℝ ((extChartAt (model n) c) ∘ f) z) := by
  have he : MDifferentiableAt (model n) (model n) (extChartAt (model n) c) (f z) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hc)
  have hd := (he.comp z hf).differentiableAt
  rw [hd.fderiv_restrictScalars ℝ, chart_derivative_twoDim hf c hc]
  ext v
  simp only [pullbackKahler_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    kahlerFormInChart_apply, Function.comp_apply]
  unfold fundamentalInChart
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f z) := mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z
  let Q : Tangent X (f z) →L[ℂ] Model n :=
    mfderiv (model n) (model n) (extChartAt (model n) c) (f z)
  change g.metric (f z) (Complex.I • D (v 0)) (D (v 1)) =
    metricInChart g.metric c ((extChartAt (model n) c) (f z))
      (Complex.I • Q (D (v 0))) (Q (D (v 1)))
  rw [← Q.map_smul]
  exact (metricInChart_forward g.metric c hc _ _).symm

theorem pullbackKahler_closed (g : KahlerMetric X) {f : ℂ × ℂ → X.Carrier}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    {z : ℂ × ℂ} (hz : z ∈ U) : extDeriv (pullbackKahler g f) z = 0 := by
  let c := f z
  let e := extChartAt (model n) c
  have hcf : ContinuousAt f z := (hf.mdifferentiableAt (hU.mem_nhds hz)).continuousAt
  have hN : U ∩ f ⁻¹' e.source ∈ 𝓝 z := inter_mem (hU.mem_nhds hz)
    (hcf (extChartAt_source_mem_nhds (I := model n) c))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hN
  have hd : DifferentiableOn ℂ (e ∘ f) (Metric.ball z r) := by
    intro w hw
    have he : MDifferentiableAt (model n) (model n) e (f w) :=
      mdifferentiableAt_extChartAt (by simpa only [e, extChartAt_source, mem_preimage] using (hrs hw).2)
    exact (he.comp w (hf.mdifferentiableAt (hU.mem_nhds (hrs hw).1))).differentiableAt.differentiableWithinAt
  have hs : ContDiffAt ℝ ∞ (e ∘ f) z :=
    ((holomorphic_twoDim_contDiffOn isOpen_ball hd).restrict_scalars ℝ).contDiffAt
      (Metric.ball_mem_nhds z hr)
  have hchart : e (f z) ∈ e.target := e.map_source (hrs (Metric.mem_ball_self hr)).2
  have hω : DifferentiableAt ℝ (kahlerFormInChart g c) (e (f z)) :=
    ((g.smooth_formInChart c).differentiableOn (by simp)).differentiableAt
      ((isOpen_extChartAt_target c).mem_nhds hchart)
  have heq : pullbackKahler g f =ᶠ[𝓝 z]
      (fun w ↦ (kahlerFormInChart g c (e (f w))).compContinuousLinearMap
        (fderiv ℝ (e ∘ f) w)) := by
    filter_upwards [Metric.ball_mem_nhds z hr] with w hw
    exact pullbackKahler_eq_chart g (hf.mdifferentiableAt (hU.mem_nhds (hrs hw).1)) c (hrs hw).2
  have hdeq : extDeriv (pullbackKahler g f) z =
      extDeriv (fun w ↦ (kahlerFormInChart g c (e (f w))).compContinuousLinearMap
        (fderiv ℝ (e ∘ f) w)) z := by
    unfold extDeriv
    rw [heq.fderiv_eq]
  rw [hdeq]
  have hr2 : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    simp <;> exact WithTop.coe_le_coe.mpr le_top
  have hp := extDeriv_pullback (f := e ∘ f) hω hs hr2
  have hc0 : extDeriv (kahlerFormInChart g c) ((e ∘ f) z) = 0 :=
    g.closed_formInChart c hchart
  rw [hc0] at hp
  exact hp.trans (by ext v; rfl)

end UniversalCoverSplitting

open scoped Manifold ContDiff
open Set Filter Topology
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

theorem KahlerMetric.contDiff_metricInChart (g : KahlerMetric X) (c : X.Carrier) :
    ContDiffOn ℝ ∞ (continuousMetricInChart g.metric c) (extChartAt (model n) c).target := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  exact g.smooth c u v

theorem exists_smooth_chart_twoDim {f : ℂ × ℂ → X.Carrier}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    {z : ℂ × ℂ} (hz : z ∈ U) :
    ∃ (c : X.Carrier) (r : ℝ), 0 < r ∧
      Metric.ball z r ⊆ U ∩ f ⁻¹' (extChartAt (model n) c).source ∧
      ContDiffOn ℝ ∞ ((extChartAt (model n) c) ∘ f) (Metric.ball z r) := by
  let c := f z
  let e := extChartAt (model n) c
  have hcf : ContinuousAt f z := (hf.mdifferentiableAt (hU.mem_nhds hz)).continuousAt
  have hN : U ∩ f ⁻¹' e.source ∈ 𝓝 z := inter_mem (hU.mem_nhds hz)
    (hcf (extChartAt_source_mem_nhds (I := model n) c))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨c,r,hr,hrs,?_⟩
  have hd : DifferentiableOn ℂ (e ∘ f) (Metric.ball z r) := by
    intro w hw
    have he : MDifferentiableAt (model n) (model n) e (f w) :=
      mdifferentiableAt_extChartAt (by simpa only [e, extChartAt_source, mem_preimage] using (hrs hw).2)
    exact (he.comp w (hf.mdifferentiableAt (hU.mem_nhds (hrs hw).1))).differentiableAt.differentiableWithinAt
  exact (holomorphic_twoDim_contDiffOn isOpen_ball hd).restrict_scalars ℝ

theorem pullbackMetric_apply_eq_chart (g : KahlerMetric X) {f : ℂ × ℂ → X.Carrier}
    {z : ℂ × ℂ} (hf : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) (model n) f z)
    (c : X.Carrier) (hc : f z ∈ (extChartAt (model n) c).source) (u v : ℂ × ℂ) :
    pullbackMetric g f z u v = metricInChart g.metric c ((extChartAt (model n) c) (f z))
      (fderiv ℝ ((extChartAt (model n) c) ∘ f) z u)
      (fderiv ℝ ((extChartAt (model n) c) ∘ f) z v) := by
  have he : MDifferentiableAt (model n) (model n) (extChartAt (model n) c) (f z) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hc)
  have hd := (he.comp z hf).differentiableAt
  rw [hd.fderiv_restrictScalars ℝ, chart_derivative_twoDim hf c hc]
  exact (metricInChart_forward g.metric c hc _ _).symm

theorem pullbackMetric_smooth (g : KahlerMetric X) {f : ℂ × ℂ → X.Carrier}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U) :
    ContDiffOn ℝ ∞ (pullbackMetric g f) U := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v z hz
  obtain ⟨c,r,hr,hrs,hs⟩ := exists_smooth_chart_twoDim hU hf hz
  let e := extChartAt (model n) c
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (e ∘ f)) (Metric.ball z r) :=
    hs.fderiv_of_isOpen isOpen_ball (by simp)
  have hB : ContDiffOn ℝ ∞ (fun w ↦ continuousMetricInChart g.metric c (e (f w)))
      (Metric.ball z r) := (g.contDiff_metricInChart c).comp hs
        (fun w hw ↦ e.map_source (hrs hw).2)
  have hS := (hB.clm_apply (hD.clm_apply (contDiffOn_const (c := u)))).clm_apply
    (hD.clm_apply (contDiffOn_const (c := v)))
  have hC : ContDiffOn ℝ ∞ (fun w ↦ pullbackMetric g f w u v) (Metric.ball z r) := by
    apply hS.congr
    intro w hw
    exact pullbackMetric_apply_eq_chart g (hf.mdifferentiableAt (hU.mem_nhds (hrs hw).1)) c (hrs hw).2 u v
  exact (hC.contDiffAt (Metric.ball_mem_nhds z hr)).contDiffWithinAt

theorem pullbackKahler_smooth (g : KahlerMetric X) {f : ℂ × ℂ → X.Carrier}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U) :
    ContDiffOn ℝ ∞ (pullbackKahler g f) U := by
  exact alternatingBilinear_contDiff ((pullbackMetric_smooth g hU hf).clm_comp contDiffOn_const)

end UniversalCoverSplitting

open scoped Manifold ContDiff
open Set Filter Topology
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

section RealPullback
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def realPullbackKahler (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    (H : E → ℂ × ℂ) (x : E) : E [⋀^Fin 2]→L[ℝ] ℝ :=
  (pullbackKahler g f (H x)).compContinuousLinearMap (fderiv ℝ H x)

theorem realPullbackKahler_as_bilinear (g : KahlerMetric X)
    (f : ℂ × ℂ → X.Carrier) (H : E → ℂ × ℂ) (x : E) :
    realPullbackKahler g f H x = alternatingBilinear
      (((pullbackMetric g f (H x)).comp
        ((Complex.I • ContinuousLinearMap.id ℂ (ℂ × ℂ)).restrictScalars ℝ)).bilinearComp
        (fderiv ℝ H x) (fderiv ℝ H x)) := by
  ext v
  simp only [realPullbackKahler, pullbackKahler,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, alternatingBilinear_apply,
    ContinuousLinearMap.bilinearComp_apply, Function.comp_apply]

theorem realPullbackKahler_smooth [FiniteDimensional ℝ E] (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {H : E → ℂ × ℂ}
    {U : Set (ℂ × ℂ)} {V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hH : ContDiffOn ℝ ∞ H V) (hmap : MapsTo H V U) :
    ContDiffOn ℝ ∞ (realPullbackKahler g f H) V := by
  change ContDiffOn ℝ ∞ (fun x ↦ realPullbackKahler g f H x) V
  simp_rw [realPullbackKahler_as_bilinear]
  apply alternatingBilinear_contDiff
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ H) V := hH.fderiv_of_isOpen hV (by simp)
  have hB := ((pullbackMetric_smooth g hU hf).comp hH hmap).clm_comp
    (contDiffOn_const (c := (Complex.I • ContinuousLinearMap.id ℂ (ℂ × ℂ)).restrictScalars ℝ))
  exact (hB.clm_apply (hD.clm_apply (contDiffOn_const (c := u)))).clm_apply
    (hD.clm_apply (contDiffOn_const (c := v)))

theorem realPullbackKahler_closed (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {H : E → ℂ × ℂ}
    {U : Set (ℂ × ℂ)} {V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hH : ContDiffOn ℝ ∞ H V) (hmap : MapsTo H V U) {x : E} (hx : x ∈ V) :
    extDeriv (realPullbackKahler g f H) x = 0 := by
  have hd : DifferentiableAt ℝ (pullbackKahler g f) (H x) :=
    ((pullbackKahler_smooth g hU hf).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds (hmap hx))
  have hr2 : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    simp <;> exact WithTop.coe_le_coe.mpr le_top
  have hp := extDeriv_pullback (f := H) hd (hH.contDiffAt (hV.mem_nhds hx)) hr2
  rw [pullbackKahler_closed g hU hf (hmap hx)] at hp
  exact hp.trans (by ext v; rfl)

theorem realPullbackKahler_apply (g : KahlerMetric X)
    (f : ℂ × ℂ → X.Carrier) (H : E → ℂ × ℂ) (x : E) (v : Fin 2 → E) :
    realPullbackKahler g f H x v = g.metric (f (H x))
      (Complex.I • mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (H x) (fderiv ℝ H x (v 0)))
      (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (H x) (fderiv ℝ H x (v 1))) := by
  exact pullbackKahler_apply g f (H x) _

end RealPullback
end UniversalCoverSplitting

namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

theorem KahlerMetric.moving_flux_nonpos (g : KahlerMetric X) (x : X.Carrier)
    (u v : Tangent X x) (R d C : ℝ) (hR : 0 ≤ R) (hd : d ≤ -C)
    (hu : metricNorm g x u ≤ C * metricNorm g x v) :
    g.metric x (Complex.I • (u + d • v)) (R • (Complex.I • v)) ≤ 0 := by
  have hq : metricNorm g x v ^ 2 = g.metric x v v :=
    Real.sq_sqrt (g.nonnegative x v)
  have hq0 : 0 ≤ metricNorm g x v := Real.sqrt_nonneg _
  have huv : g.metric x u v ≤ C * g.metric x v v := by
    calc
      _ ≤ |g.metric x u v| := le_abs_self _
      _ ≤ metricNorm g x u * metricNorm g x v := metric_abs_le g x u v
      _ ≤ (C * metricNorm g x v) * metricNorm g x v := mul_le_mul_of_nonneg_right hu hq0
      _ = C * g.metric x v v := by rw [← hq]; ring
  have hin : g.metric x u v + d * g.metric x v v ≤ 0 := by
    have h := mul_le_mul_of_nonneg_right hd (g.nonnegative x v)
    nlinarith
  have heq : g.metric x (Complex.I • (u + d • v)) (R • (Complex.I • v)) =
      R * (g.metric x u v + d * g.metric x v v) := by
    rw [smul_add, smul_comm Complex.I d]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [g.hermitian x u v, g.hermitian x v v]
  rw [heq]
  exact mul_nonpos_of_nonneg_of_nonpos hR hin

theorem KahlerMetric.radial_angular_density (g : KahlerMetric X) (x : X.Carrier)
    (v : Tangent X x) (R r : ℝ) :
    g.metric x (Complex.I • (R • v)) ((R*r) • (Complex.I • v)) =
      r * R^2 * g.metric x v v := by
  rw [smul_comm Complex.I R]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [g.hermitian x v v]
  ring

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.MovingStokes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Metric
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold
open Set Filter Topology Metric Complex
open scoped Real
open Set
open scoped Manifold ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory

open scoped ContDiff
open Set

open scoped Manifold ContDiff
open Set MeasureTheory
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

def movingKahlerForm (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    (R : ℝ → ℝ) : Real3 → Real3 [⋀^Fin 2]→L[ℝ] ℝ :=
  realPullbackKahler g f (movingPolar R)

theorem movingKahlerForm_zero (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    {R : ℝ → ℝ} {x : Real3} (hR : DifferentiableAt ℝ R (x 0)) :
    stokesCoefficient (movingKahlerForm g f R) 0 x =
      x 1 * R (x 0)^2 * g.metric (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
          (0, Complex.exp ((x 2 : ℂ) * Complex.I)))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
          (0, Complex.exp ((x 2 : ℂ) * Complex.I))) := by
  simp only [stokesCoefficient, Fin.val_zero, pow_zero, one_mul, movingKahlerForm,
    realPullbackKahler_apply]
  have h01 : (0 : Fin 3).removeNth realBasis3 0 = realBasis3 1 := rfl
  have h02 : (0 : Fin 3).removeNth realBasis3 1 = realBasis3 2 := rfl
  rw [h01, h02, movingPolar_deriv_one' hR, movingPolar_deriv_two' hR]
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f (movingPolar R x)) :=
    mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
  change g.metric _ (Complex.I • D (R (x 0) • (0, Complex.exp ((x 2 : ℂ) * Complex.I))))
      (D ((R (x 0) * x 1) • (Complex.I • (0, Complex.exp ((x 2 : ℂ) * Complex.I))))) =
      x 1 * R (x 0)^2 * g.metric _
        (D (0, Complex.exp ((x 2 : ℂ) * Complex.I)))
        (D (0, Complex.exp ((x 2 : ℂ) * Complex.I)))
  simp only [ContinuousLinearMap.map_smul_of_tower, map_smul]
  simpa only [map_smul] using g.radial_angular_density (f (movingPolar R x))
    (D (0, Complex.exp ((x 2 : ℂ) * Complex.I))) (R (x 0)) (x 1)

theorem movingKahlerForm_one (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    {R : ℝ → ℝ} {x : Real3} (hR : DifferentiableAt ℝ R (x 0)) :
    stokesCoefficient (movingKahlerForm g f R) 1 x =
      -g.metric (f (movingPolar R x))
        (Complex.I •
          (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (1, 0) +
            (deriv R (x 0) * x 1) • mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
              (0, Complex.exp ((x 2 : ℂ) * Complex.I))))
        ((R (x 0) * x 1) •
          (Complex.I • mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
            (0, Complex.exp ((x 2 : ℂ) * Complex.I)))) := by
  simp only [stokesCoefficient, Fin.val_one, pow_one, neg_one_mul, movingKahlerForm,
    realPullbackKahler_apply]
  have h10 : (1 : Fin 3).removeNth realBasis3 0 = realBasis3 0 := rfl
  have h12 : (1 : Fin 3).removeNth realBasis3 1 = realBasis3 2 := rfl
  rw [h10, h12, movingPolar_deriv_zero' hR, movingPolar_deriv_two' hR]
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f (movingPolar R x)) :=
    mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
  change -g.metric _
      (Complex.I • D ((1, 0) + (deriv R (x 0) * x 1) •
        (0, Complex.exp ((x 2 : ℂ) * Complex.I))))
      (D ((R (x 0) * x 1) • (Complex.I • (0, Complex.exp ((x 2 : ℂ) * Complex.I))))) =
      -g.metric _ (Complex.I • (D (1, 0) +
        (deriv R (x 0) * x 1) • D (0, Complex.exp ((x 2 : ℂ) * Complex.I))))
        ((R (x 0) * x 1) • (Complex.I • D (0, Complex.exp ((x 2 : ℂ) * Complex.I))))
  simp only [map_add, ContinuousLinearMap.map_smul_of_tower, map_smul]

theorem movingKahlerForm_one_zero_radius (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    {R : ℝ → ℝ} {x : Real3} (hR : DifferentiableAt ℝ R (x 0)) (hx : x 1 = 0) :
    stokesCoefficient (movingKahlerForm g f R) 1 x = 0 := by
  rw [movingKahlerForm_one g f hR, hx]
  simp

theorem movingKahlerForm_one_nonneg (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    {R : ℝ → ℝ} {x : Real3} (hR : DifferentiableAt ℝ R (x 0)) (hx : x 1 = 1)
    (hpos : 0 ≤ R (x 0)) (C : ℝ) (hd : deriv R (x 0) ≤ -C)
    (hs : metricNorm g (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (1, 0)) ≤
      C * metricNorm g (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (0, 1))) :
    0 ≤ stokesCoefficient (movingKahlerForm g f R) 1 x := by
  have hvec : ((0, Complex.exp ((x 2 : ℂ) * Complex.I)) : ℂ × ℂ) =
      Complex.exp ((x 2 : ℂ) * Complex.I) • (0, 1) := by simp
  have hnorm : metricNorm g (f (movingPolar R x))
      (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
        (0, Complex.exp ((x 2 : ℂ) * Complex.I))) =
      metricNorm g (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (0, 1)) := by
    let D : (ℂ × ℂ) →L[ℂ] Tangent X (f (movingPolar R x)) :=
      mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
    change metricNorm g _ (D _) = metricNorm g _ (D _)
    rw [hvec, map_smul, metricNorm_complex_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [movingKahlerForm_one g f hR, hx, mul_one, mul_one, neg_nonneg]
  apply g.moving_flux_nonpos _ _ _ _ _ _ hpos hd
  rwa [hnorm]

end UniversalCoverSplitting

open scoped Manifold ContDiff
open Set MeasureTheory
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

theorem movingKahlerForm_two_eq (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    {R : ℝ → ℝ} {x y : Real3} (hR : DifferentiableAt ℝ R (x 0))
    (h0 : x 0 = y 0) (h1 : x 1 = y 1)
    (he : Complex.exp ((x 2 : ℂ) * Complex.I) =
      Complex.exp ((y 2 : ℂ) * Complex.I)) :
    stokesCoefficient (movingKahlerForm g f R) 2 x =
      stokesCoefficient (movingKahlerForm g f R) 2 y := by
  have hRy : DifferentiableAt ℝ R (y 0) := h0 ▸ hR
  have hp : movingPolar R x = movingPolar R y := by
    ext <;> simp only [movingPolar, h0, h1, he]
  have hv : (fun i : Fin 2 ↦ fderiv ℝ (movingPolar R) x
      ((2 : Fin 3).removeNth realBasis3 i)) =
      (fun i : Fin 2 ↦ fderiv ℝ (movingPolar R) y
      ((2 : Fin 3).removeNth realBasis3 i)) := by
    funext i
    fin_cases i
    · change fderiv ℝ (movingPolar R) x (realBasis3 0) =
        fderiv ℝ (movingPolar R) y (realBasis3 0)
      rw [movingPolar_deriv_zero hR, movingPolar_deriv_zero hRy, h0, h1, he]
    · change fderiv ℝ (movingPolar R) x (realBasis3 1) =
        fderiv ℝ (movingPolar R) y (realBasis3 1)
      rw [movingPolar_deriv_one hR, movingPolar_deriv_one hRy, h0, he]
  simp only [stokesCoefficient, movingKahlerForm, realPullbackKahler,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
  rw [hp, hv]

theorem moving_disk_face_monotone (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {R : ℝ → ℝ}
    {U : Set (ℂ × ℂ)} {V : Set Real3} {J : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hJ : IsOpen J)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hR : ContDiffOn ℝ ∞ R J) (hVJ : MapsTo (fun x : Real3 ↦ x 0) V J)
    (hmap : MapsTo (movingPolar R) V U)
    (a b : Real3) (hab : a ≤ b) (hbox : Icc a b ⊆ V)
    (ha1 : a 1 = 0) (hb1 : b 1 = 1) (ha2 : a 2 = 0) (hb2 : b 2 = 2 * Real.pi)
    (C : ℝ) (hpos : ∀ x ∈ Icc a b, 0 ≤ R (x 0))
    (hd : ∀ x ∈ Icc a b, deriv R (x 0) ≤ -C)
    (hs : ∀ x ∈ Icc a b, metricNorm g (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (1, 0)) ≤
      C * metricNorm g (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (0, 1))) :
    (∫ y in Icc (a ∘ (0 : Fin 3).succAbove) (b ∘ (0 : Fin 3).succAbove),
      stokesCoefficient (movingKahlerForm g f R) 0 ((0 : Fin 3).insertNth (b 0) y)) ≤
    ∫ y in Icc (a ∘ (0 : Fin 3).succAbove) (b ∘ (0 : Fin 3).succAbove),
      stokesCoefficient (movingKahlerForm g f R) 0 ((0 : Fin 3).insertNth (a 0) y) := by
  have hH := movingPolar_contDiffOn hR hVJ
  have hB := realPullbackKahler_smooth g hU hV hf hH hmap
  have hc := fun x hx ↦ realPullbackKahler_closed g hU hV hf hH hmap (x := x) hx
  have hRd (x : Real3) (hx : x ∈ Icc a b) : DifferentiableAt ℝ R (x 0) :=
    (hR.differentiableOn (by simp)).differentiableAt (hJ.mem_nhds (hVJ (hbox hx)))
  have hface (i : Fin 3) (t : ℝ) (ht : t ∈ Icc (a i) (b i))
      (y : Fin 2 → ℝ) (hy : y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      i.insertNth t y ∈ Icc a b := by
    constructor <;> intro j
    · obtain rfl | ⟨k,rfl⟩ := i.eq_self_or_eq_succAbove j
      · simpa using ht.1
      · simpa using hy.1 k
    · obtain rfl | ⟨k,rfl⟩ := i.eq_self_or_eq_succAbove j
      · simpa using ht.2
      · simpa using hy.2 k
  apply first_face_integral_le_of_closed hV (hB.of_le (by simp)) hc a b hab hbox
  · intro y hy
    have hx := hface 1 (a 1) ⟨le_rfl,hab 1⟩ y hy
    exact movingKahlerForm_one_zero_radius g f (hRd _ hx) (by simp [ha1])
  · intro y hy
    have hx := hface 1 (b 1) ⟨hab 1,le_rfl⟩ y hy
    exact movingKahlerForm_one_nonneg g f (hRd _ hx) (by simp [hb1])
      (hpos _ hx) C (hd _ hx) (hs _ hx)
  · intro y hy
    have hx := hface 2 (b 2) ⟨hab 2,le_rfl⟩ y hy
    apply movingKahlerForm_two_eq g f (hRd _ hx)
    · rfl
    · rfl
    · simp [ha2, hb2, Complex.exp_two_pi_mul_I]

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.DiskArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Metric
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open scoped ContDiff
open Set
open scoped Manifold ContDiff
open Set MeasureTheory

namespace UniversalCoverSplitting
open Set MeasureTheory Metric
open scoped Manifold
variable {n : ℕ} {X : ComplexManifold n}

theorem sliceDensity_continuousOn (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {U : Set (ℂ × ℂ)} {s : ℂ} {V : Set ℂ}
    (hU : IsOpen U) (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hV : MapsTo (fun z ↦ (s,z)) V U) :
    ContinuousOn (sliceDensity g f s) V := by
  exact (((pullbackMetric_smooth g hU hf).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hV).clm_apply
      continuousOn_const).clm_apply continuousOn_const

theorem curveArea_slice_eq_ofReal_integral (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {U : Set (ℂ × ℂ)} {s : ℂ} {R : ℝ}
    (hU : IsOpen U) (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hmap : MapsTo (fun z ↦ (s,z)) (closedBall 0 R) U) :
    curveArea g (fun z ↦ f (s,z)) (ball 0 R) =
      ENNReal.ofReal (∫ z in ball (0 : ℂ) R, sliceDensity g f s z) := by
  have hi : IntegrableOn (sliceDensity g f s) (closedBall 0 R) :=
    (sliceDensity_continuousOn g hU hf hmap).integrableOn_compact
      (isCompact_closedBall (0 : ℂ) R)
  have hD : ∀ z ∈ ball (0 : ℂ) R,
      curveSpeed g (fun t ↦ f (s,t)) z ^ 2 = sliceDensity g f s z := by
    intro z hz
    exact curveSpeed_slice_sq g (hf.mdifferentiableAt
      (hU.mem_nhds (hmap (ball_subset_closedBall hz))))
  unfold curveArea
  rw [setLIntegral_congr_fun measurableSet_ball (fun z hz ↦ congrArg ENNReal.ofReal (hD z hz))]
  exact (ofReal_integral_eq_lintegral_ofReal (hi.mono_set ball_subset_closedBall)
    (Filter.Eventually.of_forall (sliceDensity_nonneg g f s))).symm

theorem movingKahlerForm_zero_density (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    {R : ℝ → ℝ} {x : Real3} (hR : DifferentiableAt ℝ R (x 0)) :
    stokesCoefficient (movingKahlerForm g f R) 0 x =
      x 1 * R (x 0)^2 * sliceDensity g f (x 0)
        (((R (x 0) * x 1 : ℝ) : ℂ) * Complex.exp ((x 2 : ℂ) * Complex.I)) := by
  rw [movingKahlerForm_zero g f hR]
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f (movingPolar R x)) :=
    mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x)
  change x 1 * R (x 0)^2 * g.metric _
      (D (0,Complex.exp ((x 2 : ℂ) * Complex.I)))
      (D (0,Complex.exp ((x 2 : ℂ) * Complex.I))) =
    x 1 * R (x 0)^2 * g.metric _ (D (0,1)) (D (0,1))
  have hv : ((0,Complex.exp ((x 2 : ℂ) * Complex.I)) : ℂ × ℂ) =
      Complex.exp ((x 2 : ℂ) * Complex.I) • (0,1) := by simp
  rw [hv, map_smul, g.quadratic_complex_smul, Complex.norm_exp_ofReal_mul_I]
  simp

theorem moving_disk_face_eq_areaIntegral (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {R : ℝ → ℝ} {s : ℝ}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hmap : MapsTo (fun z : ℂ ↦ ((s : ℂ),z)) (closedBall 0 (R s)) U)
    (hR : DifferentiableAt ℝ R s) (hpos : 0 ≤ R s) :
    (∫ y in Icc (![0,0] : Fin 2 → ℝ) ![1,2 * Real.pi],
      stokesCoefficient (movingKahlerForm g f R) 0 ((0 : Fin 3).insertNth s y)) =
    ∫ z in ball (0 : ℂ) (R s), sliceDensity g f s z := by
  have he (y : Fin 2 → ℝ) :
      stokesCoefficient (movingKahlerForm g f R) 0 ((0 : Fin 3).insertNth s y) =
      y 0 * (R s)^2 * sliceDensity g f s
        (((R s * y 0 : ℝ) : ℂ) * Complex.exp ((y 1 : ℂ) * Complex.I)) := by
    exact movingKahlerForm_zero_density g f hR
  simp_rw [he]
  exact normalized_polar_integral_eq_disk hpos (sliceDensity_continuousOn g hU hf hmap)

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set MeasureTheory Metric
open scoped Manifold
variable {n : ℕ} {X : ComplexManifold n}

theorem moving_disk_area_le (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {R : ℝ → ℝ}
    {U : Set (ℂ × ℂ)} {V : Set Real3} {J : Set ℝ} {s t C : ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hJ : IsOpen J)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hR : ContDiffOn ℝ ∞ R J) (hVJ : MapsTo (fun x : Real3 ↦ x 0) V J)
    (hmap : MapsTo (movingPolar R) V U) (hst : s ≤ t)
    (hbox : Icc (![s,0,0] : Real3) ![t,1,2 * Real.pi] ⊆ V)
    (hpos : ∀ x ∈ Icc s t, 0 ≤ R x)
    (hd : ∀ x ∈ Icc s t, deriv R x ≤ -C)
    (hs : ∀ x ∈ Icc (![s,0,0] : Real3) ![t,1,2 * Real.pi],
      metricNorm g (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (1,0)) ≤
      C * metricNorm g (f (movingPolar R x))
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (movingPolar R x) (0,1)))
    (hleft : MapsTo (fun z : ℂ ↦ ((s : ℂ),z)) (closedBall 0 (R s)) U)
    (hright : MapsTo (fun z : ℂ ↦ ((t : ℂ),z)) (closedBall 0 (R t)) U) :
    curveArea g (fun z ↦ f (t,z)) (ball 0 (R t)) ≤
      curveArea g (fun z ↦ f (s,z)) (ball 0 (R s)) := by
  have hlo : (![s,0,0] : Real3) ≤ ![t,1,2 * Real.pi] := by
    intro i
    fin_cases i <;> simp [hst, Real.pi_pos.le]
  have ha : (![s,0,0] : Real3) ∈ Icc ![s,0,0] ![t,1,2 * Real.pi] := ⟨le_rfl,hlo⟩
  have hb : (![t,1,2 * Real.pi] : Real3) ∈ Icc ![s,0,0] ![t,1,2 * Real.pi] := ⟨hlo,le_rfl⟩
  have hds : DifferentiableAt ℝ R s :=
    (hR.differentiableOn (by simp)).differentiableAt (hJ.mem_nhds (hVJ (hbox ha)))
  have hdt : DifferentiableAt ℝ R t :=
    (hR.differentiableOn (by simp)).differentiableAt (hJ.mem_nhds (hVJ (hbox hb)))
  have hmono := moving_disk_face_monotone g hU hV hJ hf hR hVJ hmap
    ![s,0,0] ![t,1,2 * Real.pi] hlo hbox rfl rfl rfl rfl C
    (fun x hx ↦ hpos _ ⟨hx.1 0,hx.2 0⟩)
    (fun x hx ↦ hd _ ⟨hx.1 0,hx.2 0⟩) hs
  have hea : ((![s,0,0] : Real3) ∘ (0 : Fin 3).succAbove) = ![0,0] := by
    funext i; fin_cases i <;> rfl
  have heb : ((![t,1,2 * Real.pi] : Real3) ∘ (0 : Fin 3).succAbove) = ![1,2 * Real.pi] := by
    funext i; fin_cases i <;> rfl
  rw [hea, heb] at hmono
  change (∫ y in Icc (![0,0] : Fin 2 → ℝ) ![1,2 * Real.pi],
      stokesCoefficient (movingKahlerForm g f R) 0 ((0 : Fin 3).insertNth t y)) ≤
    (∫ y in Icc (![0,0] : Fin 2 → ℝ) ![1,2 * Real.pi],
      stokesCoefficient (movingKahlerForm g f R) 0 ((0 : Fin 3).insertNth s y)) at hmono
  rw [moving_disk_face_eq_areaIntegral g hU hf hright hdt (hpos t ⟨hst,le_rfl⟩),
    moving_disk_face_eq_areaIntegral g hU hf hleft hds (hpos s ⟨le_rfl,hst⟩)] at hmono
  rw [curveArea_slice_eq_ofReal_integral g hU hf hright,
    curveArea_slice_eq_ofReal_integral g hU hf hleft]
  exact ENNReal.ofReal_le_ofReal hmono

theorem curveArea_slice_ne_top (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {U : Set (ℂ × ℂ)} {s : ℂ} {R : ℝ}
    (hU : IsOpen U) (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hmap : MapsTo (fun z ↦ (s,z)) (closedBall 0 R) U) :
    curveArea g (fun z ↦ f (s,z)) (ball 0 R) ≠ ⊤ := by
  rw [curveArea_slice_eq_ofReal_integral g hU hf hmap]
  exact ENNReal.ofReal_ne_top

end UniversalCoverSplitting

open Set Metric
open scoped ContDiff

namespace UniversalCoverSplitting
open Set Metric MeasureTheory
open scoped Manifold ContDiff
variable {n : ℕ} {X : ComplexManifold n}

theorem moving_disk_area_le_of_slices (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {R : ℝ → ℝ} {U : Set (ℂ × ℂ)}
    {J : Set ℝ} {s t C : ℝ} (hU : IsOpen U) (hJ : IsOpen J)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hR : ContDiffOn ℝ ∞ R J) (hst : s ≤ t) (hIJ : Icc s t ⊆ J)
    (hpos : ∀ x ∈ Icc s t, 0 ≤ R x)
    (hd : ∀ x ∈ Icc s t, deriv R x ≤ -C)
    (hslices : ∀ x ∈ Icc s t, MapsTo (fun z : ℂ ↦ ((x : ℂ),z))
      (closedBall 0 (R x)) U)
    (hs : ∀ z ∈ U, metricNorm g (f z) (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (1,0)) ≤
      C * metricNorm g (f z) (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (0,1))) :
    curveArea g (fun z ↦ f (t,z)) (ball 0 (R t)) ≤
      curveArea g (fun z ↦ f (s,z)) (ball 0 (R s)) := by
  let W : Set Real3 := (fun x ↦ x 0) ⁻¹' J
  let V : Set Real3 := W ∩ movingPolar R ⁻¹' U
  have hWo : IsOpen W := hJ.preimage (by fun_prop)
  have hpc : ContinuousOn (movingPolar R) W :=
    (movingPolar_contDiffOn hR (fun _ hx ↦ hx)).continuousOn
  have hVo : IsOpen V := hpc.isOpen_inter_preimage hWo hU
  have hbox : Icc (![s,0,0] : Real3) ![t,1,2 * Real.pi] ⊆ V := by
    intro x hx
    have hx0 : x 0 ∈ Icc s t := ⟨hx.1 0,hx.2 0⟩
    have hx1 : 0 ≤ x 1 ∧ x 1 ≤ 1 := ⟨hx.1 1,hx.2 1⟩
    refine ⟨hIJ hx0,hslices _ hx0 ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpos _ hx0) hx1.1)]
    exact mul_le_of_le_one_right (hpos _ hx0) hx1.2
  exact moving_disk_area_le g hU hVo hJ hf hR (fun _ hx ↦ hx.1)
    (fun _ hx ↦ hx.2) hst hbox hpos hd
    (fun x hx ↦ hs _ (hbox hx).2) (hslices _ ⟨le_rfl,hst⟩)
    (hslices _ ⟨hst,le_rfl⟩)

theorem shrinking_disk_area_bound (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {U : Set (ℂ × ℂ)} {a k C : ℝ}
    (hU : IsOpen U) (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (ha : a < 0) (hk : 0 < k)
    (hslices : ∀ x ∈ Ico a 0, MapsTo (fun z : ℂ ↦ ((x : ℂ),z))
      (closedBall 0 (shrinkingRadius k x)) U)
    (hs : ∀ z ∈ U, metricNorm g (f z) (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (1,0)) ≤
      C * metricNorm g (f z) (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (0,1))) :
    ∃ x₀ ∈ Ico a 0,
      curveArea g (fun z ↦ f (x₀,z)) (ball 0 (shrinkingRadius k x₀)) ≠ ⊤ ∧
      ∀ x ∈ Ico x₀ 0,
        curveArea g (fun z ↦ f (x,z)) (ball 0 (shrinkingRadius k x)) ≤
          curveArea g (fun z ↦ f (x₀,z)) (ball 0 (shrinkingRadius k x₀)) := by
  obtain ⟨b,hb,hbd⟩ := exists_shrinkingRadius_deriv_le hk C
  let x₀ := max a b
  have hx₀ : x₀ ∈ Ico a 0 := ⟨le_max_left _ _,max_lt ha hb⟩
  refine ⟨x₀,hx₀,curveArea_slice_ne_top g hU hf (hslices _ hx₀),?_⟩
  intro x hx
  apply moving_disk_area_le_of_slices g hU isOpen_Iio hf
    (shrinkingRadius_contDiffOn k) hx.1
    (fun y hy ↦ lt_of_le_of_lt hy.2 hx.2)
    (fun _ _ ↦ shrinkingRadius_nonneg hk.le)
  · intro y hy
    exact hbd y ⟨(le_max_right a b).trans hy.1,hy.2.trans_lt hx.2⟩
  · intro y hy
    exact hslices y ⟨hx₀.1.trans hy.1,hy.2.trans_lt hx.2⟩
  · exact hs

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.MixedShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold ENNReal NNReal
open scoped Manifold
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open Set
open scoped Manifold ContDiff
open Set MeasureTheory
open Set Metric
open scoped ContDiff
open Set Metric Filter Topology

namespace UniversalCoverSplitting

lemma isPreconnected_complexAnnulus {a b : ℝ} (ha : 0 ≤ a) :
    IsPreconnected (complexAnnulus a b) := by
  let F : ℝ × ℝ → ℂ := fun p ↦ (p.1:ℂ) * Complex.exp ((p.2:ℂ)*Complex.I)
  have hF : Continuous F := by fun_prop
  have he : F '' (Ioo a b ×ˢ (univ : Set ℝ)) = complexAnnulus a b := by
    ext z
    constructor
    · rintro ⟨⟨r,t⟩,⟨hr,_⟩,rfl⟩
      have hp : 0 < r := ha.trans_lt hr.1
      simpa [complexAnnulus,F,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hp,Complex.norm_exp_ofReal_mul_I] using hr
    · intro hz
      refine ⟨(‖z‖,z.arg),⟨hz,mem_univ _⟩,?_⟩
      exact Complex.norm_mul_exp_arg_mul_I z
  rw [← he]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ hF.continuousOn

lemma complexAnnulus_union_ball {a b R : ℝ} (haR : a < R) (hRb : R ≤ b) :
    ball (0:ℂ) R ∪ complexAnnulus a b = ball 0 b := by
  ext z
  simp only [complexAnnulus,mem_union,mem_ofPred_eq,mem_ball,dist_zero_right]
  constructor
  · rintro (h|h)
    · exact h.trans_le hRb
    · exact h.2
  · intro hz
    by_cases h : ‖z‖ < R
    · exact Or.inl h
    · exact Or.inr ⟨haR.trans_le (le_of_not_gt h),hz⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsMixedBox.eqOn_of_slice (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W D : Set ℂ} (hW : IsOpen W) (hD : IsOpen D)
    (hWc : IsPreconnected W) (hDc : IsPreconnected D) {w : ℂ} (hw : w ∈ W)
    {f g : ℂ × ℂ → X.Carrier} (hf : IsMixedBox (S := S) c hc (W ×ˢ D) f)
    (hg : IsMixedBox (S := S) c hc (W ×ˢ D) g)
    (he : ∀ z ∈ D, f (w,z) = g (w,z)) : EqOn f g (W ×ˢ D) := by
  intro z hz
  let M := mixedEquiv c hc
  let p : ℂ × ℂ := (c.1*w,c.2*w)
  have hcalc (v : ℂ) : separatedAffine p (1,1) (v,v) = M (w,v) := by
    ext <;> simp [p,M,separatedAffine,mixedEquiv_apply,add_comm]
  have hmo : IsOpen (M '' (W ×ˢ D)) := M.toHomeomorph.isOpenMap _ (hW.prod hD)
  have hh : (f ∘ M.symm) =ᶠ[𝓝 (M (w,z.2))] (g ∘ M.symm) := by
    rw [← hcalc]
    apply box_shifted_diagonal_germ_unique h₁ h₂ hmo hD hf hg p hz.2
    · intro v hv
      rw [hcalc]
      exact mem_image_of_mem M ⟨hw,hv⟩
    · intro v hv
      change f (M.symm (separatedAffine p (1,1) (v,v))) = g (M.symm (separatedAffine p (1,1) (v,v)))
      rw [hcalc,M.symm_apply_apply]
      exact he v hv
  have hevent : f =ᶠ[𝓝 (w,z.2)] g := by
    simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using hh.comp_tendsto M.continuous.continuousAt
  exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq (hW.prod hD) (hWc.prod hDc)
    hf.holomorphic hg.holomorphic (show (w,z.2) ∈ W ×ˢ D from ⟨hw,hz.2⟩) hevent hz

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem holomorphic_curve_mixed_thickening (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) (c : ℂ × ℂ) (hc : c.1 ≠ c.2)
    {D V K : Set ℂ} (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) (hVK : V ⊆ K)
    {f : ℂ → X.Carrier} (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f D) (w : ℂ) :
    ∃ e : ℝ, 0 < e ∧ ∃ F : ℂ × ℂ → X.Carrier,
      IsMixedBox (S := S) c hc (ball w e ×ˢ V) F ∧ ∀ v ∈ V, F (w,v) = f v := by
  obtain ⟨U,hU,hDU,G,hG,hGdiag⟩ := holomorphic_curve_box_thickening h₁ h₂ hD hf
  obtain ⟨e,he,heU⟩ := diagonal_compact_tube hU hK (fun z hz ↦ hDU z (hKD hz)) c
  let p : ℂ × ℂ := (-c.1*w,-c.2*w)
  let T := separatedAffine p (1,1)
  let M := mixedEquiv c hc
  have hcalc (q : ℂ × ℂ) : T (M q) = (q.2+c.1*(q.1-w),q.2+c.2*(q.1-w)) := by
    ext <;> dsimp [T,p,M,separatedAffine,mixedEquiv_apply] <;> ring
  have hmap : MapsTo T (M '' (ball w e ×ˢ V)) U := by
    rintro z ⟨q,hq,rfl⟩
    rw [hcalc]
    apply heU (q.1-w) _ q.2 (hVK hq.2)
    simpa only [mem_ball,dist_zero_right,dist_eq_norm,sub_zero] using hq.1
  have hGT : IsBox S (M '' (ball w e ×ˢ V)) (G ∘ T) := hG.comp_separatedAffine hU p (1,1) hmap
  refine ⟨e,he,(G ∘ T) ∘ M,isMixedBox_iff.mpr hGT,?_⟩
  intro v hv
  simpa only [Function.comp_apply,hcalc,sub_self,mul_zero,add_zero] using hGdiag v (hKD (hVK hv))

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma glue_mixed_boxes_pair {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {U V : Set (ℂ × ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    {f g : ℂ × ℂ → X.Carrier} (hf : IsMixedBox (S := S) c hc U f)
    (hg : IsMixedBox (S := S) c hc V g) (he : EqOn f g (U ∩ V)) :
    ∃ F : ℂ × ℂ → X.Carrier, IsMixedBox (S := S) c hc (U ∪ V) F ∧
      EqOn F f U ∧ EqOn F g V := by
  let W : Bool → Set (ℂ × ℂ) := fun i ↦ if i then U else V
  let G : Bool → ℂ × ℂ → X.Carrier := fun i ↦ if i then f else g
  have hWo (i : Bool) : IsOpen (W i) := by cases i <;> assumption
  have hG (i : Bool) : IsMixedBox (S := S) c hc (W i) (G i) := by cases i <;> assumption
  have hGG (i j : Bool) : EqOn (G i) (G j) (W i ∩ W j) := by
    cases i <;> cases j
    · exact fun _ _ ↦ rfl
    · exact fun z hz ↦ (he ⟨hz.2,hz.1⟩).symm
    · exact he
    · exact fun _ _ ↦ rfl
  obtain ⟨F,hF,hFG⟩ := glue_mixed_boxes W hWo G hG hGG (f 0)
  have hWW : (⋃ i, W i) = U ∪ V := by ext z; simp [W,or_comm]
  exact ⟨F,hWW ▸ hF,hFG true,hFG false⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem mixed_shell_fill_of_slice (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} (hW : IsOpen W) {w : ℂ} (hw : w ∈ W)
    {a R b : ℝ} (ha : 0 ≤ a) (haR : a < R) (hRb : R ≤ b)
    {Fs : ℂ × ℂ → X.Carrier} (hs : IsMixedBox (S := S) c hc (W ×ˢ complexAnnulus a b) Fs)
    {H : ℂ → X.Carrier} (hH : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) H (ball 0 R))
    (hHs : ∀ v ∈ complexAnnulus a R, H v = Fs (w,v)) :
    ∃ e : ℝ, 0 < e ∧ ball w e ⊆ W ∧ ∃ F : ℂ × ℂ → X.Carrier,
      IsMixedBox (S := S) c hc (ball w e ×ˢ ball 0 b) F ∧
      EqOn F Fs (ball w e ×ˢ complexAnnulus a b) := by
  obtain ⟨q,haq,hqR⟩ := exists_between haR
  have hq : 0 < q := ha.trans_lt haq
  obtain ⟨e₁,he₁,G,hG,hGH⟩ := holomorphic_curve_mixed_thickening h₁ h₂ c hc
    isOpen_ball (isCompact_closedBall (0:ℂ) q) (closedBall_subset_ball hqR)
    (ball_subset_closedBall (x := (0:ℂ)) (ε := q)) hH w
  obtain ⟨e₂,he₂,h₂W⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hw)
  let e := min e₁ e₂
  have he : 0 < e := lt_min he₁ he₂
  have heG : ball w e ⊆ ball w e₁ := ball_subset_ball (min_le_left _ _)
  have heW : ball w e ⊆ W := (ball_subset_ball (min_le_right _ _)).trans h₂W
  have hG' : IsMixedBox (S := S) c hc (ball w e ×ˢ ball 0 q) G := hG.mono (prod_mono heG subset_rfl)
  have hs' : IsMixedBox (S := S) c hc (ball w e ×ˢ complexAnnulus a b) Fs := hs.mono (prod_mono heW subset_rfl)
  have hqa : complexAnnulus a q ⊆ ball 0 q := complexAnnulus_subset_ball _ _
  have hqab : complexAnnulus a q ⊆ complexAnnulus a b := fun _ hz ↦ ⟨hz.1,hz.2.trans_le (hqR.le.trans hRb)⟩
  have hcompat : EqOn G Fs (ball w e ×ˢ complexAnnulus a q) := by
    apply IsMixedBox.eqOn_of_slice h₁ h₂ isOpen_ball (isOpen_complexAnnulus _ _)
      (convex_ball w e).isPreconnected (isPreconnected_complexAnnulus ha) (mem_ball_self he)
      (hG'.mono (prod_mono subset_rfl hqa)) (hs'.mono (prod_mono subset_rfl hqab))
    intro v hv
    exact (hGH v (hqa hv)).trans (hHs v ⟨hv.1,hv.2.trans hqR⟩)
  have hcompat' : EqOn G Fs ((ball w e ×ˢ ball 0 q) ∩ (ball w e ×ˢ complexAnnulus a b)) := by
    intro z hz
    exact hcompat ⟨hz.1.1,hz.2.2.1,by simpa using hz.1.2⟩
  obtain ⟨F,hF,hFG,hFs⟩ := glue_mixed_boxes_pair (isOpen_ball.prod isOpen_ball)
    (isOpen_ball.prod (isOpen_complexAnnulus _ _)) hG' hs' hcompat'
  have hV : (ball w e ×ˢ ball 0 q) ∪ (ball w e ×ˢ complexAnnulus a b) = ball w e ×ˢ ball 0 b := by
    rw [← prod_union,complexAnnulus_union_ball haq (hqR.le.trans hRb)]
  exact ⟨e,he,heW,F,hV ▸ hF,hFs⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold ENNReal NNReal
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

local instance instMetricSpaceCarrierOfCompactSpace_7_rd5576f_1 [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X
theorem mixed_shell_fill_of_bounded_slices [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} (hW : IsOpen W) {w : ℂ} (hw : w ∈ W)
    {a R b : ℝ} (ha : 0 ≤ a) (haR : a < R) (hRb : R < b)
    {Fs : ℂ × ℂ → X.Carrier} (hs : IsMixedBox (S := S) c hc (W ×ˢ complexAnnulus a b) Fs)
    (wj : ℕ → ℂ) (_hwj : ∀ j, wj j ∈ W) (hlim : Tendsto wj atTop (𝓝 w))
    (fj : ℕ → ℂ → X.Carrier)
    (hfj : ∀ j, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (fj j) (ball 0 b))
    (heq : ∀ j v, v ∈ complexAnnulus a b → fj j v = Fs (wj j,v))
    (C : ℝ≥0) (hC : ∀ j, curveArea g (fj j) (closedBall 0 R) ≤ (C : ℝ≥0∞)) :
    ∃ e : ℝ, 0 < e ∧ ball w e ⊆ W ∧ ∃ F : ℂ × ℂ → X.Carrier,
      IsMixedBox (S := S) c hc (ball w e ×ˢ ball 0 b) F ∧
      EqOn F Fs (ball w e ×ˢ complexAnnulus a b) := by
  have hR : 0 < R := ha.trans_lt haR
  obtain ⟨σ,hσ,A,hA,hAK,H,hH,hconv⟩ := bounded_curveArea_subsequence_with_removed_limit
    g fj isOpen_ball (isCompact_closedBall (0:ℂ) R)
    (nonempty_closedBall.mpr hR.le) (closedBall_subset_ball hRb) hfj C hC
  rw [interior_closedBall _ hR.ne'] at hH hconv
  have hsmall : complexAnnulus a R ⊆ complexAnnulus a b := fun _ hv ↦ ⟨hv.1,hv.2.trans hRb⟩
  have hcont : ContinuousOn (fun v ↦ Fs (w,v)) (complexAnnulus a R) :=
    hs.holomorphic.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv ↦ ⟨hw,hsmall hv⟩)
  have heoff : EqOn H (fun v ↦ Fs (w,v)) (complexAnnulus a R \ A) := by
    intro v hv
    have hl := hconv.tendsto_at ⟨complexAnnulus_subset_ball _ _ hv.1,hv.2⟩
    have hscont : ContinuousAt Fs (w,v) := hs.holomorphic.continuousOn.continuousAt
      ((hW.prod (isOpen_complexAnnulus _ _)).mem_nhds ⟨hw,hsmall hv.1⟩)
    have hl' : Tendsto (fun j ↦ Fs (wj (σ j),v)) atTop (𝓝 (Fs (w,v))) :=
      hscont.tendsto.comp ((hlim.comp hσ.tendsto_atTop).prodMk_nhds tendsto_const_nhds)
    have hfun : (fun j ↦ fj (σ j) v) = (fun j ↦ Fs (wj (σ j),v)) :=
      funext fun j ↦ heq (σ j) v (hsmall hv.1)
    change Tendsto (fun j ↦ fj (σ j) v) atTop (𝓝 (H v)) at hl
    rw [hfun] at hl
    exact tendsto_nhds_unique hl hl'
  have heall : EqOn H (fun v ↦ Fs (w,v)) (complexAnnulus a R) :=
    heoff.of_subset_closure (hH.continuousOn.mono (complexAnnulus_subset_ball _ _)) hcont
      sdiff_subset ((hA.countable.dense_compl ℂ).open_subset_closure_inter (isOpen_complexAnnulus _ _))
  exact mixed_shell_fill_of_slice h₁ h₂ hW hw ha haR hRb.le hs hH (fun v hv ↦ heall hv)

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem exists_uniform_mixed_slope [CompactSpace X.Carrier]
    (g : KahlerMetric X) (S : HolomorphicSplitting X r s) (c : ℂ × ℂ) (hc : c.1 ≠ c.2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (ℂ × ℂ)) (f : ℂ × ℂ → X.Carrier),
      IsOpen U → IsMixedBox (S := S) c hc U f → ∀ z ∈ U,
      metricNorm g (f z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z (1,0)) ≤
        C * metricNorm g (f z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z (0,1)) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,h₁,h₂⟩ := g.exists_uniform_splitting_bound S
  refine ⟨‖c.1‖ * C₁ + ‖c.2‖ * C₂,by positivity,?_⟩
  intro U f hU hf z hz
  have hh := IsBox.mixed_slope_bound g ((mixedEquiv c hc).toHomeomorph.isOpenMap _ hU)
    hf c hc C₁ C₂ h₁ h₂ (mem_image_of_mem (mixedEquiv c hc) hz)
  have he : (f ∘ (mixedEquiv c hc).symm) ∘ mixedEquiv c hc = f := by
    funext x
    exact congrArg f ((mixedEquiv c hc).symm_apply_apply x)
  rw [he] at hh
  exact hh

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.ShellFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open Set
open scoped Manifold ContDiff
open Set MeasureTheory
open Set Metric
open scoped ContDiff
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold ContDiff ENNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

lemma first_affine_slope (g : KahlerMetric X) {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {f : ℂ × ℂ → X.Carrier} (hf : MDifferentiableOn 𝓘(ℂ,ℂ × ℂ) (model n) f U)
    (u w : ℂ) (C : ℝ)
    (hs : ∀ z ∈ U, metricNorm g (f z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z (1,0)) ≤
      C * metricNorm g (f z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z (0,1)))
    {z : ℂ × ℂ} (hz : separatedAffine (u,0) (w,1) z ∈ U) :
    metricNorm g ((f ∘ separatedAffine (u,0) (w,1)) z)
      (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) (f ∘ separatedAffine (u,0) (w,1)) z (1,0)) ≤
    (C * ‖w‖) * metricNorm g ((f ∘ separatedAffine (u,0) (w,1)) z)
      (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) (f ∘ separatedAffine (u,0) (w,1)) z (0,1)) := by
  have hm := mfderiv_comp z (hf.mdifferentiableAt (hU.mem_nhds hz))
    (separatedAffine_hasFDerivAt (u,0) (w,1) z).differentiableAt.mdifferentiableAt
  rw [hm,mfderiv_eq_fderiv,(separatedAffine_hasFDerivAt (u,0) (w,1) z).fderiv]
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f (separatedAffine (u,0) (w,1) z)) :=
    mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f (separatedAffine (u,0) (w,1) z)
  change metricNorm g _ (D (separatedLinear (w,1) (1,0))) ≤
    (C * ‖w‖) * metricNorm g _ (D (separatedLinear (w,1) (0,1)))
  have h₁ : separatedLinear (w,1) (1,0) = w • (1,0) := by ext <;> simp [separatedLinear]
  have h₂ : separatedLinear (w,1) (0,1) = (0,1) := by ext <;> simp [separatedLinear]
  rw [h₁,h₂,map_smul,metricNorm_complex_smul]
  calc
    _ ≤ ‖w‖ * (C * metricNorm g _ (D (0,1))) := mul_le_mul_of_nonneg_left (hs _ hz) (norm_nonneg _)
    _ = _ := by ring

theorem radial_disk_area_bound (g : KahlerMetric X)
    {A : Set ℂ} {u : ℂ} (hA : IsOpen A) {f : ℂ × ℂ → X.Carrier} {b ρ C R R₀ : ℝ}
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ × ℂ) (model n) f (A ×ˢ ball 0 b))
    (_hρ : 0 < ρ) (hρA : ball u ρ ⊆ A) (hC : 0 ≤ C)
    (hR : 0 < R) (hRR : R + C * ρ < R₀) (hRb : R₀ < b)
    (hs : ∀ z ∈ A ×ˢ ball 0 b,
      metricNorm g (f z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z (1,0)) ≤
      C * metricNorm g (f z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z (0,1))) :
    ∀ w ∈ ball u ρ, curveArea g (fun v ↦ f (w,v)) (closedBall 0 R) ≤
      curveArea g (fun v ↦ f (u,v)) (ball 0 R₀) := by
  intro w hw
  have hw' : ‖w-u‖ < ρ := by simpa [dist_eq_norm] using hw
  let T := separatedAffine (u,0) (w-u,1)
  let U := T ⁻¹' (A ×ˢ ball 0 b)
  let D := C * ‖w-u‖
  let R' : ℝ → ℝ := fun x ↦ R₀ - D * x
  have hD : 0 ≤ D := mul_nonneg hC (norm_nonneg _)
  have hmargin : R < R₀ - D := by
    have := mul_le_mul_of_nonneg_left hw'.le hC
    dsimp [D]
    linarith
  have hT : Continuous T := continuous_iff_continuousAt.mpr fun z ↦ (separatedAffine_hasFDerivAt (u,0) (w-u,1) z).continuousAt
  have hU : IsOpen U := (hA.prod isOpen_ball).preimage hT
  have hf' : MDifferentiableOn 𝓘(ℂ,ℂ × ℂ) (model n) (f ∘ T) U :=
    hf.comp (fun z _ ↦ (separatedAffine_hasFDerivAt (u,0) (w-u,1) z).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt)
      (fun _ hz ↦ hz)
  have hRp (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : 0 ≤ R' x := by
    have := mul_le_mul_of_nonneg_left hx.2 hD
    dsimp [R']
    linarith
  have hslices : ∀ x ∈ Icc (0:ℝ) 1, MapsTo (fun v : ℂ ↦ ((x:ℂ),v)) (closedBall 0 (R' x)) U := by
    intro x hx v hv
    change separatedAffine (u,0) (w-u,1) ((x:ℂ),v) ∈ A ×ˢ ball 0 b
    simp only [separatedAffine,zero_add,one_mul]
    constructor
    · apply hρA
      simp only [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1]
      exact (mul_le_of_le_one_right (norm_nonneg (w-u)) hx.2).trans_lt hw'
    · have hv' : ‖v‖ ≤ R₀ - D*x := by simpa [R'] using hv
      have := mul_nonneg hD hx.1
      simpa only [mem_ball,dist_zero_right] using (show ‖v‖ < b by linarith)
  have hm := moving_disk_area_le_of_slices g hU isOpen_univ hf'
    (show ContDiffOn ℝ ∞ R' univ from (by fun_prop : ContDiff ℝ ∞ R').contDiffOn)
    (show (0:ℝ) ≤ 1 by norm_num) (subset_univ _) hRp
    (fun x _ ↦ by
      have hd : HasDerivAt R' (-D) x := by simpa [R'] using ((hasDerivAt_id x).const_mul D).const_sub R₀
      exact hd.deriv.le) hslices
    (fun z hz ↦ first_affine_slope g (hA.prod isOpen_ball) hf u (w-u) C hs hz)
  have hfinal : curveArea g (fun v ↦ f (w,v)) (ball 0 (R₀-D)) ≤
      curveArea g (fun v ↦ f (u,v)) (ball 0 R₀) := by
    simpa only [Function.comp_apply,T,separatedAffine,R',mul_one,mul_zero,sub_zero,zero_add,one_mul,Complex.ofReal_one,Complex.ofReal_zero,add_sub_cancel,add_zero] using hm
  exact (curveArea_mono g _ (closedBall_subset_ball hmargin)).trans hfinal

end UniversalCoverSplitting

open Set Metric Filter Topology

open Set Metric Filter Topology
open scoped Manifold ENNReal NNReal
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma mixedFillable_closedBall [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} (hW : IsOpen W) {a b R R₀ ρ C : ℝ} (ha : 0 ≤ a)
    (haR : a < R) (hRR : R + C*ρ < R₀) (hRb : R₀ < b)
    (hρ : 0 < ρ) (hC : 0 ≤ C)
    {Fs : ℂ × ℂ → X.Carrier} (hs : IsMixedBox (S := S) c hc (W ×ˢ complexAnnulus a b) Fs)
    {F : ℂ × ℂ → X.Carrier}
    (hF : IsMixedBox (S := S) c hc (MixedFillable S c hc W Fs a b ×ˢ ball 0 b) F)
    (hFs : EqOn F Fs (MixedFillable S c hc W Fs a b ×ˢ complexAnnulus a b))
    (hslope : ∀ z ∈ MixedFillable S c hc W Fs a b ×ˢ ball 0 b,
      metricNorm g (F z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) F z (1,0)) ≤
      C * metricNorm g (F z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) F z (0,1)))
    {u : ℂ} (hball : ball u ρ ⊆ MixedFillable S c hc W Fs a b)
    (hclosed : closedBall u ρ ⊆ W) :
    closedBall u ρ ⊆ MixedFillable S c hc W Fs a b := by
  have hR : 0 < R := ha.trans_lt haR
  have hRR' : R < R₀ := lt_of_le_of_lt (le_add_of_nonneg_right (mul_nonneg hC hρ.le)) hRR
  have hu : u ∈ MixedFillable S c hc W Fs a b := hball (mem_ball_self hρ)
  have hfin : curveArea g (fun v ↦ F (u,v)) (ball 0 R₀) ≠ (⊤ : ℝ≥0∞) :=
    curveArea_slice_ne_top g (isOpen_mixedFillable.prod isOpen_ball) hF.holomorphic
      (fun v hv ↦ ⟨hu,closedBall_subset_ball hRb hv⟩)
  let B : ℝ≥0 := (curveArea g (fun v ↦ F (u,v)) (ball 0 R₀)).toNNReal
  have hbound := radial_disk_area_bound g isOpen_mixedFillable hF.holomorphic hρ hball hC hR hRR hRb hslope
  intro w hw
  have hw' : w ∈ closure (ball u ρ) := by rwa [closure_ball u hρ.ne']
  obtain ⟨wj,hwj,hlim⟩ := mem_closure_iff_seq_limit.mp hw'
  exact mixed_shell_fill_of_bounded_slices g h₁ h₂ hW (hclosed hw) ha haR (hRR'.trans hRb) hs
    wj (fun j ↦ mixedFillable_subset (hball (hwj j))) hlim
    (fun j v ↦ F (wj j,v)) (fun j ↦ hF.slice_holomorphic (hball (hwj j)))
    (fun j v hv ↦ hFs ⟨hball (hwj j),hv⟩) B
    (fun j ↦ by simpa only [B,ENNReal.coe_toNNReal hfin] using hbound _ (hwj j))

theorem mixedFillable_uniform_local_continuation [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) (c : ℂ × ℂ) (hc : c.1 ≠ c.2)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (W : Set ℂ) (Fs : ℂ × ℂ → X.Carrier),
      IsOpen W → IsMixedBox (S := S) c hc (W ×ˢ complexAnnulus a b) Fs →
      ∀ u ∈ MixedFillable S c hc W Fs a b, ∀ e : ℝ, 0 < e → e ≤ δ →
        ball u e ⊆ W → ball u e ⊆ MixedFillable S c hc W Fs a b := by
  obtain ⟨C,hC,hCs⟩ := exists_uniform_mixed_slope g S c hc
  obtain ⟨R,haR,hRb⟩ := exists_between hab
  obtain ⟨R₀,hRR,hR₀b⟩ := exists_between hRb
  let δ := (R₀-R)/(C+1)
  have hCp : 0 < C+1 := by positivity
  have hδ : 0 < δ := div_pos (sub_pos.mpr hRR) hCp
  refine ⟨δ,hδ,?_⟩
  intro W Fs hW hs u hu e he heδ heW
  obtain ⟨F,hF,hFs⟩ := glue_all_mixed_fillings (S := S) (W := W) (Fs := Fs) ha hab
  apply ball_subset_of_closedBall_continuation isOpen_mixedFillable hu
  intro ρ hρ hρe hρA
  have hρδ : ρ < δ := hρe.trans_le heδ
  have hmargin : R + C*ρ < R₀ := by
    have hh : ρ*(C+1) < R₀-R := (lt_div_iff₀ hCp).mp hρδ
    have hρpos := hρ
    nlinarith
  exact mixedFillable_closedBall g h₁ h₂ hW ha haR hmargin hR₀b hρ hC hs hF hFs
    (hCs _ _ (isOpen_mixedFillable.prod isOpen_ball) hF) hρA
    ((closedBall_subset_ball hρe).trans heW)

end UniversalCoverSplitting

open Set Metric Filter Topology

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem mixed_shell_extension [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} (hW : IsOpen W) (hWc : IsPreconnected W) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Fs : ℂ × ℂ → X.Carrier} (hs : IsMixedBox (S := S) c hc (W ×ˢ complexAnnulus a b) Fs)
    {w : ℂ} (hw : w ∈ W) {H : ℂ → X.Carrier}
    (hH : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) H (ball 0 b))
    (hHs : ∀ v ∈ complexAnnulus a b, H v = Fs (w,v)) :
    ∃ F : ℂ × ℂ → X.Carrier, IsMixedBox (S := S) c hc (W ×ˢ ball 0 b) F ∧
      EqOn F Fs (W ×ˢ complexAnnulus a b) := by
  have hwA : w ∈ MixedFillable S c hc W Fs a b :=
    mixed_shell_fill_of_slice h₁ h₂ hW hw ha hab le_rfl hs hH hHs
  obtain ⟨δ,hδ,hcont⟩ := mixedFillable_uniform_local_continuation g h₁ h₂ c hc ha hab
  have hWA : W ⊆ MixedFillable S c hc W Fs a b :=
    subset_of_uniform_local_continuation hW hWc isOpen_mixedFillable mixedFillable_subset
      ⟨w,hwA⟩ hδ (hcont W Fs hW hs)
  have hAW : MixedFillable S c hc W Fs a b = W := Subset.antisymm mixedFillable_subset hWA
  obtain ⟨F,hF,hFs⟩ := glue_all_mixed_fillings (S := S) (c := c) (hc := hc) (W := W) (Fs := Fs) ha hab
  rw [hAW] at hF hFs
  exact ⟨F,hF,hFs⟩

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.SmallAnnuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open Set
open scoped Manifold ContDiff
open Set MeasureTheory
open Set Metric
open scoped ContDiff
open scoped Manifold ContDiff ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem chart_annulus_mixed_extension [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    (e : SplittingChart S) {l η : ℝ} (hl : 0 < l) (hη : 0 < η)
    (hc₁ : ‖c.1‖*η ≤ 1/8) (hc₂ : ‖c.2‖*η ≤ 1/8)
    {H : ℂ → X.Carrier} (hH : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) H (ball 0 (2*l)))
    (hmap : MapsTo H (complexAnnulus (3*l/4) (3*l/2)) e.chart.source) :
    ∃ F : ℂ × ℂ → X.Carrier,
      IsMixedBox (S := S) c hc (ball 0 (η*l) ×ˢ ball 0 (5*l/4)) F ∧
      ∀ v ∈ ball 0 (5*l/4), F (0,v) = H v := by
  let A := complexAnnulus (3*l/4) (3*l/2)
  have hAH : A ⊆ ball (0:ℂ) (2*l) := by
    intro v hv
    rw [mem_ball_zero_iff]
    linarith [hv.2]
  obtain ⟨hG,hGH⟩ := e.diagonal_box (isOpen_complexAnnulus _ _) (hH.mono hAH) hmap
  let G : ℂ × ℂ → X.Carrier := fun q ↦ e.chart.symm ((e.chart (H q.1)).1,(e.chart (H q.2)).2)
  let Fs := G ∘ mixedEquiv c hc
  have hs : IsMixedBox (S := S) c hc (ball 0 (η*l) ×ˢ complexAnnulus l (5*l/4)) Fs := by
    apply hG.toMixed
    intro q hq
    have hw : ‖q.1‖ < η*l := by simpa using hq.1
    exact ⟨mixed_shift_in_annulus hl hc₁ hw hq.2,mixed_shift_in_annulus hl hc₂ hw hq.2⟩
  have hHs : ∀ v ∈ complexAnnulus l (5*l/4), H v = Fs (0,v) := by
    intro v hv
    have hvA : v ∈ A := by constructor <;> linarith [hv.1,hv.2]
    simpa [Fs,G,mixedEquiv_apply] using (hGH v hvA).symm
  have hsmall : ball (0:ℂ) (5*l/4) ⊆ ball 0 (2*l) := ball_subset_ball (by linarith)
  obtain ⟨F,hF,hFs⟩ := mixed_shell_extension g h₁ h₂ isOpen_ball
    (convex_ball (0:ℂ) (η*l)).isPreconnected hl.le (by linarith : l < 5*l/4) hs
    (mem_ball_self (mul_pos hη hl)) (hH.mono hsmall) hHs
  refine ⟨F,hF,?_⟩
  obtain ⟨v,hv⟩ := complexAnnulus_nonempty hl.le (by linarith : l < 5*l/4)
  have he : (fun v ↦ F (0,v)) =ᶠ[𝓝 v] H := by
    filter_upwards [(isOpen_complexAnnulus l (5*l/4)).mem_nhds hv] with z hz
    exact (hFs ⟨mem_ball_self (mul_pos hη hl),hz⟩).trans (hHs z hz).symm
  exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq isOpen_ball
    (convex_ball (0:ℂ) (5*l/4)).isPreconnected
    (hF.slice_holomorphic (mem_ball_self (mul_pos hη hl))) (hH.mono hsmall)
    (complexAnnulus_subset_ball _ _ hv) he

end UniversalCoverSplitting

open Set Metric

open Set Metric

namespace UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ} {X : ComplexManifold n}

theorem exists_annulus_speed_trapping (g : KahlerMetric X) (c : X.Carrier)
    {U : Set X.Carrier} (hU : IsOpen U) (hcU : c ∈ U) :
    ∃ V ∈ 𝓝 c, ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℂ → X.Carrier,
      MDifferentiableOn 𝓘(ℂ, ℂ) (model n) h openAnnulus → h 1 ∈ V →
      (∀ z ∈ compactAnnulus, curveSpeed g h z < ε) → MapsTo h compactAnnulus U := by
  let e : OpenPartialHomeomorph X.Carrier (Model n) :=
    { extChartAt (model n) c with
      continuousOn_toFun := continuousOn_extChartAt c
      continuousOn_invFun := continuousOn_extChartAt_symm c
      open_source := isOpen_extChartAt_source c
      open_target := isOpen_extChartAt_target c }
  have hc : c ∈ e.source := mem_extChartAt_source c
  have hN : e.target ∩ e.symm ⁻¹' U ∈ 𝓝 (e c) :=
    (e.symm.isOpen_inter_preimage hU).mem_nhds ⟨e.map_source hc, by simpa only [mem_preimage,e.left_inv hc] using hcU⟩
  obtain ⟨R,hR,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hN
  have he : closedBall (e c) R ⊆ e.target := fun z hz ↦ (hball hz).1
  obtain ⟨Cforward,Cback,hC,_,hcomp⟩ := g.exists_chart_speed_comparison c (isCompact_closedBall (e c) R) he
  let V := e.source ∩ e ⁻¹' ball (e c) (R/2)
  have hV : V ∈ 𝓝 c := (e.isOpen_inter_preimage isOpen_ball).mem_nhds
    ⟨hc, by simpa using half_pos hR⟩
  let ε := R / (28 * Cforward)
  have hε : 0 < ε := div_pos hR (by positivity)
  have hL : 7 * (Cforward * ε) = R/4 := by dsimp [ε]; field_simp; ring
  refine ⟨V,hV,ε,hε,?_⟩
  intro h hh hstart hspeed
  have htrap : ∀ z ∈ compactAnnulus, h z ∈ e.source ∧ e (h z) ∈ ball (e c) R := by
    apply chart_trapping_on_annulus e hR (mul_nonneg hC.le hε.le) he
      (hh.continuousOn.mono compactAnnulus_subset_openAnnulus)
    · refine ⟨hstart.1,?_⟩
      rw [hL]
      have hi : dist (e (h 1)) (e c) < R/2 := hstart.2
      linarith
    · intro z hz hk
      obtain ⟨w,hw,hwz⟩ := hk
      have hs : h z ∈ e.source := hwz ▸ e.map_target (he hw)
      have hw' : e (h z) ∈ closedBall (e c) R := by rw [← hwz,e.right_inv (he hw)]; exact hw
      have hhz := hh.mdifferentiableAt
        (isOpen_openAnnulus.mem_nhds (compactAnnulus_subset_openAnnulus hz))
      have he' : MDifferentiableAt (model n) (model n) e (h z) :=
        mdifferentiableAt_extChartAt (by simpa only [e,extChartAt_source] using hs)
      refine ⟨(he'.comp z hhz).differentiableAt,?_⟩
      rw [← norm_deriv_eq_norm_fderiv]
      change ‖deriv ((extChartAt (model n) c) ∘ h) z‖ ≤ _
      rw [chart_deriv_curve hhz c hs]
      exact ((hcomp (h z) hs hw' (mfderiv 𝓘(ℂ, ℂ) (model n) h z (1 : ℂ))).1).trans
        (mul_le_mul_of_nonneg_left (hspeed z hz).le hC.le)
  intro z hz
  have hn := (hball (ball_subset_closedBall (htrap z hz).2)).2
  simpa only [mem_preimage,e.left_inv (htrap z hz).1] using hn

theorem exists_small_area_annulus_image_in_cover [CompactSpace X.Carrier]
    (g : KahlerMetric X) (U : X.Carrier → Set X.Carrier)
    (hU : ∀ c, IsOpen (U c)) (hcU : ∀ c, c ∈ U c) :
    ∃ η : ℝ, 0 < η ∧ ∀ h : ℂ → X.Carrier,
      MDifferentiableOn 𝓘(ℂ, ℂ) (model n) h openAnnulus →
      curveArea g h openAnnulus < ENNReal.ofReal η →
      ∃ c, MapsTo h compactAnnulus (U c) := by
  classical
  choose V hV ε hε hb using fun c ↦ exists_annulus_speed_trapping g c (hU c) (hcU c)
  obtain ⟨s,hs⟩ := CompactSpace.elim_nhds_subcover V hV
  have covered (x : X.Carrier) : ∃ c ∈ s, x ∈ V c := by
    have hx : x ∈ ⋃ c ∈ s, V c := by rw [hs]; trivial
    simpa only [mem_iUnion,exists_prop] using hx
  by_cases hne : s.Nonempty
  · have heps : 0 < s.inf' hne ε := (Finset.lt_inf'_iff hne).mpr (fun c _ ↦ hε c)
    obtain ⟨η,hη,hbη⟩ := exists_small_area_speed_bound g isOpen_openAnnulus
      isCompact_compactAnnulus compactAnnulus_subset_openAnnulus heps
    refine ⟨η,hη,?_⟩
    intro h hh harea
    obtain ⟨c,hcs,hc⟩ := covered (h 1)
    refine ⟨c,hb c h hh hc (fun z hz ↦ (hbη h hh harea z hz).trans_le (s.inf'_le ε hcs))⟩
  · refine ⟨1,by norm_num,?_⟩
    intro h
    obtain ⟨c,hcs,_⟩ := covered (h 1)
    exact (hne ⟨c,hcs⟩).elim

end UniversalCoverSplitting

open Set MeasureTheory Filter Topology
open scoped ENNReal

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

lemma inv_smul_mem_compactAnnulus {l : ℝ} (hl : 0 < l) {v : ℂ}
    (hv : v ∈ complexAnnulus (3*l/4) (3*l/2)) : l⁻¹ • v ∈ compactAnnulus := by
  change 3/4 ≤ ‖l⁻¹ • v‖ ∧ ‖l⁻¹ • v‖ ≤ 3/2
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hl)]
  have he : l⁻¹ * ‖v‖ = ‖v‖ / l := by ring
  rw [he]
  exact ⟨(le_div_iff₀ hl).mpr (by linarith [hv.1]),
    (div_le_iff₀ hl).mpr (by linarith [hv.2])⟩

lemma curveArea_rescale_annulus (g : KahlerMetric X) {H : ℂ → X.Carrier}
    {l : ℝ} (hl : 0 < l) (hH : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) H (scaledAnnulus l)) :
    curveArea g (fun z ↦ H (l • z)) openAnnulus = curveArea g H (scaledAnnulus l) := by
  have he : (fun z : ℂ ↦ (0:ℂ)+l • z) '' openAnnulus = scaledAnnulus l := by
    simpa only [zero_add] using positive_smul_openAnnulus hl
  have hAo : IsOpen (scaledAnnulus l) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have h := curveArea_positive_affine g openAnnulus isOpen_openAnnulus.measurableSet 0 hl
    (fun z hz ↦ hH.mdifferentiableAt (hAo.mem_nhds (he ▸ hz)))
  simpa only [zero_add,positive_smul_openAnnulus hl] using h

lemma scaled_slice_holomorphic {f : ℂ × ℂ → X.Carrier} {U : Set (ℂ × ℂ)}
    (hf : MDifferentiableOn 𝓘(ℂ,ℂ × ℂ) (model n) f U) {x : ℂ} {l : ℝ}
    (hmap : MapsTo (fun z : ℂ ↦ (x,l • z)) openAnnulus U) :
    MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (fun z ↦ f (x,l • z)) openAnnulus := by
  apply hf.comp _ hmap
  intro z _
  exact ((hasFDerivAt_const x z).prodMk ((hasFDerivAt_id z).const_smul l)).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.BoundaryExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open scoped Manifold ContDiff
open Set MeasureTheory
open scoped ContDiff
open scoped Manifold ContDiff ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold
open Set Metric
open Set MeasureTheory Filter Topology
open scoped ENNReal
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem exists_boundary_chart_annulus [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) {f : ℂ × ℂ → X.Carrier}
    (hf : IsMixedBox (S := S) c hc U f) {a k η : ℝ} (ha : a < 0) (hk : 0 < k) (hη : 0 < η)
    (hslices : ∀ x ∈ Ico a 0, MapsTo (fun z : ℂ ↦ ((x:ℂ),z))
      (closedBall 0 (shrinkingRadius k x)) U) :
    ∃ x ∈ Ico a 0, ∃ l : ℝ, 0 < l ∧ -x < η*l ∧ 2*l < shrinkingRadius k x ∧
      ∃ e : SplittingChart S,
        MapsTo (fun v ↦ f ((x:ℂ),v)) (complexAnnulus (3*l/4) (3*l/2)) e.chart.source := by
  classical
  choose e he he0 using exists_splittingChart S h₁ h₂
  obtain ⟨ε,hε,himage⟩ := exists_small_area_annulus_image_in_cover g
    (fun p ↦ (e p).chart.source) (fun p ↦ (e p).chart.open_source) he
  obtain ⟨C,_,hC⟩ := exists_uniform_mixed_slope g S c hc
  obtain ⟨x₀,hx₀,hM,hbound⟩ := shrinking_disk_area_bound g hU hf.holomorphic ha hk hslices (hC U f hU hf)
  let M := curveArea g (fun z ↦ f ((x₀:ℂ),z)) (ball 0 (shrinkingRadius k x₀))
  obtain ⟨N,hN,hNM⟩ := exists_number_of_annuli hM hε
  obtain ⟨t,ht,hxt,htsc⟩ := exists_boundary_scales hx₀.2 hk hη N
  let x : ℝ := -t^4
  have hx : x ∈ Ico a 0 := ⟨hx₀.1.trans hxt.1,hxt.2⟩
  have hR : shrinkingRadius k x = k*t^2 := by
    unfold shrinkingRadius x
    have heq : -(-t^4) = (t^2)^2 := by ring
    rw [heq,Real.sqrt_sq (sq_nonneg t)]
  have hsc (i : ℕ) (hi : i < N) :
      scaledAnnulus ((5:ℝ)^i*t^3) ⊆ ball (0:ℂ) (shrinkingRadius k x) := by
    intro z hz
    rw [mem_ball_zero_iff,hR]
    exact hz.2.trans (htsc i hi.le).2
  obtain ⟨i,hi,harea⟩ := exists_small_energy_annulus
    (fun z ↦ ENNReal.ofReal (curveSpeed g (fun v ↦ f ((x:ℂ),v)) z ^ 2))
    (pow_pos ht 3) hsc (hbound x hxt) hNM
  let l : ℝ := (5:ℝ)^i*t^3
  have hl : 0 < l := mul_pos (pow_pos (by norm_num) _) (pow_pos ht _)
  have hlR : 2*l < shrinkingRadius k x := by rw [hR]; exact (htsc i hi.le).2
  have hslice : MapsTo (fun z : ℂ ↦ ((x:ℂ),z)) (ball 0 (shrinkingRadius k x)) U :=
    (hslices x hx).mono_left ball_subset_closedBall
  have hH := hf.slice_holomorphic_on (x:ℂ) hslice
  have hAhol := hH.mono (hsc i hi)
  have hscale : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (fun z ↦ f ((x:ℂ),l • z)) openAnnulus := by
    apply scaled_slice_holomorphic hf.holomorphic
    intro z hz
    exact hslice (hsc i hi (positive_smul_openAnnulus hl ▸ mem_image_of_mem (fun v : ℂ ↦ l • v) hz))
  have hsmall : curveArea g (fun z ↦ f ((x:ℂ),l • z)) openAnnulus < ENNReal.ofReal ε := by
    rw [curveArea_rescale_annulus g hl hAhol]
    exact harea
  obtain ⟨p,hp⟩ := himage _ hscale hsmall
  refine ⟨x,hx,l,hl,?_,hlR,e p,?_⟩
  · change -(-t^4) < η*((5:ℝ)^i*t^3)
    simpa only [neg_neg] using (htsc i hi.le).1
  · intro v hv
    have hz := hp (inv_smul_mem_compactAnnulus hl hv)
    simpa only [smul_smul,mul_inv_cancel₀ hl.ne',one_smul] using hz

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem mixed_boundary_extension_of_shrinking_slices [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) (hUc : Convex ℝ U) {f : ℂ × ℂ → X.Carrier}
    (hf : IsMixedBox (S := S) c hc U f) {a k : ℝ} (ha : a < 0) (hk : 0 < k)
    (hslices : ∀ x ∈ Ico a 0, MapsTo (fun z : ℂ ↦ ((x:ℂ),z))
      (closedBall 0 (shrinkingRadius k x)) U) :
    ∃ V : Set (ℂ × ℂ), IsOpen V ∧ (0:ℂ × ℂ) ∈ V ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsMixedBox (S := S) c hc V F ∧ EqOn F f (V ∩ U) := by
  let K : ℝ := ‖c.1‖+‖c.2‖+1
  have hK : 0 < K := by dsimp [K]; positivity
  let η : ℝ := 1/(8*K)
  have hη : 0 < η := by dsimp [η]; positivity
  have hc₁ : ‖c.1‖*η ≤ 1/8 := by
    dsimp [η]
    rw [mul_one_div,div_le_iff₀ (by positivity : 0 < 8*K)]
    dsimp [K]
    nlinarith [norm_nonneg c.2]
  have hc₂ : ‖c.2‖*η ≤ 1/8 := by
    dsimp [η]
    rw [mul_one_div,div_le_iff₀ (by positivity : 0 < 8*K)]
    dsimp [K]
    nlinarith [norm_nonneg c.1]
  obtain ⟨x,hx,l,hl,hxl,hlR,e,he⟩ := exists_boundary_chart_annulus g h₁ h₂ hU hf ha hk hη hslices
  have hslice : MapsTo (fun z : ℂ ↦ ((x:ℂ),z)) (ball 0 (2*l)) U :=
    (hslices x hx).mono_left (ball_subset_closedBall.trans (closedBall_subset_closedBall hlR.le))
  obtain ⟨G,hG,hGH⟩ := chart_annulus_mixed_extension g h₁ h₂ e hl hη hc₁ hc₂
    (hf.slice_holomorphic_on (x:ℂ) hslice) he
  let V : Set (ℂ × ℂ) := ball (x:ℂ) (η*l) ×ˢ ball 0 (5*l/4)
  have hVo : IsOpen V := isOpen_ball.prod isOpen_ball
  have hVc : Convex ℝ V := (convex_ball _ _).prod (convex_ball _ _)
  have h0V : (0:ℂ × ℂ) ∈ V := by
    constructor
    · change dist (0:ℂ) (x:ℂ) < η*l
      simpa only [dist_zero_left,Complex.norm_real,Real.norm_eq_abs,abs_of_neg hx.2] using hxl
    · exact mem_ball_self (by positivity : 0 < 5*l/4)
  let p : ℂ × ℂ := (-(x:ℂ),0)
  let F : ℂ × ℂ → X.Carrier := fun q ↦ G (p+q)
  have hp : MapsTo (fun q ↦ p+q) V (ball (0:ℂ) (η*l) ×ˢ ball 0 (5*l/4)) := by
    intro q hq
    constructor
    · rw [mem_ball,dist_eq_norm]
      change ‖-(x:ℂ)+q.1-0‖ < η*l
      simpa only [sub_zero,neg_add_eq_sub,mem_ball,dist_eq_norm] using hq.1
    · simpa only [p,Prod.snd_add,zero_add] using hq.2
  have hF : IsMixedBox (S := S) c hc V F := hG.comp_translation (isOpen_ball.prod isOpen_ball) p hp
  refine ⟨V,hVo,h0V,F,hF,?_⟩
  apply IsMixedBox.eqOn_of_slice_in_domain h₁ h₂ (hVo.inter hU) (hVc.inter hUc).isPreconnected
    isOpen_ball (v := 0) (w := (x:ℂ)) (mem_ball_self (by positivity : 0 < 5*l/4))
    (hF.mono inter_subset_left) (hf.mono inter_subset_right)
  · intro z hz
    exact ⟨⟨mem_ball_self (mul_pos hη hl),hz⟩,hslice ((ball_subset_ball (by linarith : 5*l/4 ≤ 2*l)) hz)⟩
  · intro z hz
    simpa only [F,p,Prod.mk_add_mk,neg_add_cancel,zero_add] using hGH z hz

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting

lemma separatedAffine_convex_preimage {U : Set (ℂ × ℂ)} (hU : Convex ℝ U) (p b : ℂ × ℂ) :
    Convex ℝ (separatedAffine p b ⁻¹' U) :=
  (hU.translate_preimage_right p).linear_preimage ((separatedLinear b).restrictScalars ℝ).toLinearMap

end UniversalCoverSplitting

open Set Metric Filter Topology

open Set Metric Filter Topology

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting

variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem affine_mixed_boundary_extension [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {B : Set (ℂ × ℂ)}
    (hB : IsOpen B) (hBc : Convex ℝ B) {f : ℂ × ℂ → X.Carrier} (hf : IsBox S B f)
    (p b c : ℂ × ℂ) (hb₁ : b.1 ≠ 0) (hb₂ : b.2 ≠ 0) (hc : c.1 ≠ c.2)
    {ρ : ℂ × ℂ → ℝ} (hρ : ContDiffAt ℝ 2 ρ 0) (hρ0 : ρ 0 = 0)
    {d e : ℝ} (hd : 0 < d) (he : 0 < e)
    (hD : ∀ (x : ℝ) (v : ℂ), fderiv ℝ ρ 0 ((x:ℂ),v) = d*x)
    (hdef : ∀ z ∈ ball (0:ℂ × ℂ) e, ρ z < 0 → mixedSource p b c hb₁ hb₂ hc z ∈ B) :
    ∃ V : Set (ℂ × ℂ), IsOpen V ∧ p ∈ V ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S V F ∧ EqOn F f (V ∩ B) := by
  let T := separatedHomeomorph p b hb₁ hb₂
  let M := mixedEquiv c hc
  let U := M ⁻¹' (T ⁻¹' B)
  have hU : IsOpen U := (hB.preimage T.continuous).preimage M.continuous
  have hUc : Convex ℝ U := (separatedAffine_convex_preimage hBc p b).linear_preimage (M.restrictScalars ℝ).toLinearMap
  have hfT : IsBox S (T ⁻¹' B) (f ∘ T) := hf.comp_separatedAffine hB p b (fun _ hz ↦ hz)
  have hfM : IsMixedBox (S := S) c hc U ((f ∘ T) ∘ M) := hfT.toMixed (fun _ hz ↦ hz)
  obtain ⟨a,k,ha,hk,hs⟩ := exists_parabolic_interior_disks hρ hρ0 hd he hD hdef
  have hsU : ∀ x ∈ Ico a 0, MapsTo (fun z : ℂ ↦ ((x:ℂ),z)) (closedBall 0 (shrinkingRadius k x)) U := hs
  obtain ⟨V,hV,h0,G,hG,hGf⟩ := mixed_boundary_extension_of_shrinking_slices g h₁ h₂ hU hUc hfM ha hk hsU
  have hMV : IsOpen (M '' V) := M.toHomeomorph.isOpenMap _ hV
  have hTV : IsOpen (T '' (M '' V)) := T.isOpenMap _ hMV
  have hp : p ∈ T '' (M '' V) := by
    have he0 : T (M 0) = p := mixedSource_zero p b c hb₁ hb₂ hc
    exact he0 ▸ mem_image_of_mem T (mem_image_of_mem M h0)
  have hmap : MapsTo T.symm (T '' (M '' V)) (M '' V) := by
    rintro z ⟨y,hy,rfl⟩
    simpa only [T.symm_apply_apply] using hy
  have hF := IsBox.comp_separatedHomeomorph_symm hMV hG p b hb₁ hb₂ hmap
  refine ⟨T '' (M '' V),hTV,hp,(G ∘ M.symm) ∘ T.symm,hF,?_⟩
  rintro z ⟨⟨y,⟨q,hq,rfl⟩,rfl⟩,hz⟩
  simpa only [Function.comp_apply,T.symm_apply_apply,M.symm_apply_apply] using hGf (show q ∈ V ∩ U from ⟨hq,hz⟩)

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.Superellipsoids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open scoped Manifold ContDiff
open Set MeasureTheory
open scoped ContDiff
open scoped Manifold ContDiff ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric
open Set MeasureTheory Filter Topology
open scoped ENNReal
open Set
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold
open Set Metric Filter Topology

namespace UniversalCoverSplitting

lemma superDomain_mono (m : ℕ) {a b : ℝ} (hab : a ≤ b) : superDomain m a ⊆ superDomain m b :=
  fun _ h ↦ h.trans_le hab

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting

lemma superPotential_fderiv_mul {m : ℕ} (hm : 0 < m) (p w : ℂ × ℂ) :
    fderiv ℝ (superPotential m) p (p.1*w.1,p.2*w.2) =
      2*m*(Complex.normSq p.1^m*w.1.re+Complex.normSq p.2^m*w.2.re) := by
  have h₁ := ((normSq_hasFDerivAt p.1).pow m).comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have h₂ := ((normSq_hasFDerivAt p.2).pow m).comp p (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have hD : HasFDerivAt (superPotential m) _ p := h₁.add h₂
  rw [hD.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply]
  rw [← ((normSq_hasFDerivAt p.1).pow m).fderiv,← ((normSq_hasFDerivAt p.2).pow m).fderiv]
  change (fderiv ℝ (fun z : ℂ ↦ Complex.normSq z^m) p.1) (p.1*w.1) +
    (fderiv ℝ (fun z : ℂ ↦ Complex.normSq z^m) p.2) (p.2*w.2) = _
  rw [normSqPow_fderiv_mul hm,normSqPow_fderiv_mul hm]
  ring

lemma superPotential_superSource_fderiv {m : ℕ} (hm : 0 < m) (p : ℂ × ℂ)
    (x : ℝ) (v : ℂ) :
    fderiv ℝ ((superPotential m) ∘ superSource m p) 0 ((x:ℂ),v) =
      (2*m*superPotential m p)*x := by
  rw [fderiv_comp _ ((superPotential_contDiff m (k := 1)).differentiable (by norm_num) _)
    ((superSource_contDiff m p (k := 1)).differentiable (by norm_num) _)]
  rw [ContinuousLinearMap.comp_apply,superSource_fderiv,superSource_zero]
  rw [superPotential_fderiv_mul hm p (
    (x:ℂ)+(Complex.normSq p.2^m:ℝ)*v,(x:ℂ)-(Complex.normSq p.1^m:ℝ)*v)]
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,superPotential]
  ring

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem superDomain_mixed_boundary [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {m : ℕ} (hm : 0 < m)
    {a : ℝ} (ha : 0 < a) {f : ℂ × ℂ → X.Carrier} (hf : IsBox S (superDomain m a) f)
    {p : ℂ × ℂ} (hp : superPotential m p = a) (hp₁ : p.1 ≠ 0) (hp₂ : p.2 ≠ 0) :
    ∃ V : Set (ℂ × ℂ), IsOpen V ∧ p ∈ V ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S V F ∧ EqOn F f (V ∩ superDomain m a) := by
  let A : ℝ := Complex.normSq p.1^m
  let B : ℝ := Complex.normSq p.2^m
  have hA : 0 < A := pow_pos (Complex.normSq_pos.mpr hp₁) _
  have hB : 0 < B := pow_pos (Complex.normSq_pos.mpr hp₂) _
  have hAc : (A:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hBc : (B:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB.ne'
  let b : ℂ × ℂ := ((B:ℂ)*p.1,-(A:ℂ)*p.2)
  let c : ℂ × ℂ := ((B⁻¹:ℝ),(-A⁻¹:ℝ))
  have hb₁ : b.1 ≠ 0 := mul_ne_zero hBc hp₁
  have hb₂ : b.2 ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hAc) hp₂
  have hc : c.1 ≠ c.2 := by
    intro h
    have hh := congrArg Complex.re h
    change B⁻¹ = -A⁻¹ at hh
    linarith [inv_pos.mpr hA,inv_pos.mpr hB]
  have heq : (mixedSource p b c hb₁ hb₂ hc : ℂ × ℂ → ℂ × ℂ) = superSource m p := by
    funext q
    change (p.1+(B:ℂ)*p.1*(q.2+(B⁻¹:ℝ)*q.1),
      p.2+(-(A:ℂ)*p.2)*(q.2+(-A⁻¹:ℝ)*q.1)) =
      (p.1*(1+q.1+(B:ℂ)*q.2),p.2*(1+q.1-(A:ℂ)*q.2))
    ext <;> push_cast <;> field_simp <;> ring
  let ρ : ℂ × ℂ → ℝ := fun z ↦ superPotential m (superSource m p z)-a
  have hρ : ContDiff ℝ 2 ρ := ((superPotential_contDiff m).comp (superSource_contDiff m p)).sub contDiff_const
  have hρ0 : ρ 0 = 0 := by simp [ρ,superSource_zero,hp]
  have hD : ∀ (x : ℝ) (v : ℂ), fderiv ℝ ρ 0 ((x:ℂ),v) = (2*m*a)*x := by
    intro x v
    have hh : DifferentiableAt ℝ ((superPotential m) ∘ superSource m p) 0 :=
      (((superPotential_contDiff m (k := 1)).comp (superSource_contDiff m p)).differentiable (by norm_num)) 0
    have h : HasFDerivAt ρ (fderiv ℝ ((superPotential m) ∘ superSource m p) 0) 0 := hh.hasFDerivAt.sub_const a
    rw [h.fderiv]
    simpa only [hp] using superPotential_superSource_fderiv hm p x v
  apply affine_mixed_boundary_extension g h₁ h₂ (superDomain_open m a) (superDomain_convex m a) hf
    p b c hb₁ hb₂ hc hρ.contDiffAt hρ0 (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hm)) ha)
    (show (0:ℝ)<1 by norm_num) hD
  intro z _ hz
  rw [heq]
  exact sub_neg.mp hz

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.AxisContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open scoped Manifold ContDiff
open Set MeasureTheory
open scoped ContDiff
open scoped Manifold ContDiff ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric
open Set MeasureTheory Filter Topology
open scoped ENNReal
open Set
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma vertical_axis_boundary_extension (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S))
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) (hUc : Convex ℝ U)
    {f : ℂ × ℂ → X.Carrier} (hf : IsBox S U f)
    {O : Set ℂ} (hO : IsOpen O) {α : ℂ → X.Carrier} (hα : IsVerticalCurve S O α)
    {p : ℂ} (hp : p ∈ O) (hpc : p ∈ closure {z : ℂ | (0,z) ∈ U})
    (haxis : ∀ z ∈ O, (0,z) ∈ U → f (0,z) = α z) :
    ∃ V : Set (ℂ × ℂ), IsOpen V ∧ (0,p) ∈ V ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S V F ∧ EqOn F f (V ∩ U) := by
  obtain ⟨e,hep,_⟩ := exists_splittingChart S h₁ h₂ (α p)
  have hαn := (hα.1.continuousOn.continuousAt (hO.mem_nhds hp)) (e.chart.open_source.mem_nhds hep)
  obtain ⟨d,hd,hdO⟩ := Metric.mem_nhds_iff.mp (inter_mem (hO.mem_nhds hp) hαn)
  have hdsub : ball p d ⊆ O := fun _ hz ↦ (hdO hz).1
  have hdae : MapsTo α (ball p d) e.chart.source := fun _ hz ↦ (hdO hz).2
  obtain ⟨q,hq,hqp⟩ := mem_closure_iff_nhds.mp hpc (ball p d) (ball_mem_nhds p hd)
  have hqe : f (0,q) ∈ e.chart.source := (haxis q (hdsub hq) hqp) ▸ hdae hq
  have hfn := (hf.1.continuousOn.continuousAt (hU.mem_nhds hqp)) (e.chart.open_source.mem_nhds hqe)
  obtain ⟨a,ha,haV⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hqp) hfn)
  have hβmap (z : ℂ) (hz : z ∈ ball (0:ℂ) a) : (z,q) ∈ U ∧ f (z,q) ∈ e.chart.source := by
    apply haV
    rw [← ball_prod_same]
    exact ⟨hz,mem_ball_self ha⟩
  let β : ℂ → X.Carrier := fun z ↦ f (z,q)
  have hβ : IsHorizontalCurve S (ball 0 a) β := hf.horizontal_slice hU q (fun z hz ↦ (hβmap z hz).1)
  let V := ball (0:ℂ) a ×ˢ ball p d
  let F : ℂ × ℂ → X.Carrier := fun z ↦ e.chart.symm ((e.chart (β z.1)).1,(e.chart (α z.2)).2)
  have hF : IsBox S V F := e.mix_curves isOpen_ball isOpen_ball hβ.1 (hα.1.mono hdsub)
    (fun z hz ↦ (hβmap z hz).2) hdae
  have haxes := e.mix_curves_axes isOpen_ball isOpen_ball (convex_ball (0:ℂ) a).isPreconnected
    (convex_ball p d).isPreconnected hβ (hα.mono hdsub) (fun z hz ↦ (hβmap z hz).2) hdae
    (mem_ball_self ha) hq (haxis q (hdsub hq) hqp)
  have hVo : IsOpen V := isOpen_ball.prod isOpen_ball
  have hqc : (0,q) ∈ V ∩ U := ⟨⟨mem_ball_self ha,hq⟩,hqp⟩
  obtain ⟨b,hb,hbV⟩ := Metric.mem_nhds_iff.mp ((hVo.inter hU).mem_nhds hqc)
  have hbsub : ball (0:ℂ) b ×ˢ ball q b ⊆ V ∩ U := by rwa [ball_prod_same]
  have hFg : F =ᶠ[𝓝 (0,q)] f := by
    apply box_axes_germ_unique h₁ h₂ isOpen_ball isOpen_ball
      (hF.mono (hbsub.trans inter_subset_left)) (hf.mono (hbsub.trans inter_subset_right)) 0 q
      (mem_ball_self hb) (mem_ball_self hb)
    · intro z hz
      have hm := hbsub (show (z,q) ∈ ball (0:ℂ) b ×ˢ ball q b from ⟨hz,mem_ball_self hb⟩)
      exact haxes.1 z hm.1.1
    · intro z hz
      have hm := hbsub (show (0,z) ∈ ball (0:ℂ) b ×ˢ ball q b from ⟨mem_ball_self hb,hz⟩)
      exact (haxes.2 z hm.1.2).trans (haxis z (hdsub hm.1.2) hm.2).symm
  refine ⟨V,hVo,⟨mem_ball_self ha,mem_ball_self hd⟩,F,hF,?_⟩
  exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq (hVo.inter hU)
    (((convex_ball (0:ℂ) a).prod (convex_ball p d)).inter hUc).isPreconnected
    (hF.1.mono inter_subset_left) (hf.1.mono inter_subset_right) hqc hFg

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting

lemma superPotential_norm_bound {m : ℕ} (hm : 0 < m) {z : ℂ × ℂ} {a : ℝ}
    (hz : superPotential m z ≤ a) : ‖z‖ ≤ max a 1 + 1 := by
  have hb (w : ℂ) (hw : Complex.normSq w ^ m ≤ a) : ‖w‖ ≤ max a 1 + 1 := by
    by_cases h : ‖w‖ ≤ 1
    · linarith [le_max_right a 1]
    have hh : 1 ≤ Complex.normSq w := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
    have hpow := le_self_pow₀ hh hm.ne'
    rw [Complex.normSq_eq_norm_sq] at hpow hw
    nlinarith [le_max_left a 1,le_max_right a 1,norm_nonneg w]
  exact max_le (hb z.1 (le_trans (le_add_of_nonneg_right
    (pow_nonneg (Complex.normSq_nonneg z.2) m)) hz))
    (hb z.2 (le_trans (le_add_of_nonneg_left
      (pow_nonneg (Complex.normSq_nonneg z.1) m)) hz))

lemma superSublevel_compact {m : ℕ} (hm : 0 < m) (a : ℝ) :
    IsCompact {z | superPotential m z ≤ a} := by
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_le (superPotential_contDiff m (k := 0)).continuous continuous_const,?_⟩
  apply (isBounded_closedBall (x := (0:ℂ × ℂ)) (r := max a 1+1)).subset
  intro z hz
  rw [mem_closedBall,dist_zero_right]
  exact superPotential_norm_bound hm hz

lemma superDomain_vertical_axis_closure {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a)
    {p : ℂ} (hp : superPotential m (0,p) ≤ a) :
    p ∈ closure {z : ℂ | (0,z) ∈ superDomain m a} := by
  have ht : Tendsto (fun t : ℝ ↦ t • p) (𝓝[<] 1) (𝓝 p) := by
    have hc : Continuous (fun t : ℝ ↦ t • (p : ℂ)) := continuous_id.smul continuous_const
    have hh := hc.continuousAt (x := (1:ℝ)) |>.tendsto
    rw [one_smul] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0:ℝ)<1 by norm_num))]
    with t ht ht0
  simpa only [Prod.smul_mk,smul_zero] using superPotential_radial_lt hm ha ht0.le ht hp

lemma superSublevel_subset_bidisk {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : a < 1) :
    {z | superPotential m z ≤ a} ⊆ ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1 := by
  intro z hz
  exact superDomain_subset_bidisk hm (le_refl 1) (lt_of_le_of_lt hz ha)

lemma superSublevel_widen {m : ℕ} (hm : 0 < m) {a : ℝ} {W : Set (ℂ × ℂ)}
    (hW : IsOpen W) (hsub : {z | superPotential m z ≤ a} ⊆ W) :
    ∃ b : ℝ, a < b ∧ superDomain m b ⊆ W := by
  let K := {z | superPotential m z ≤ a+1} \ W
  have hK : IsCompact K := (superSublevel_compact hm (a+1)).diff hW
  by_cases hne : K.Nonempty
  · obtain ⟨p,hp,hmin⟩ := hK.exists_isMinOn hne (superPotential_contDiff m (k := 0)).continuous.continuousOn
    have hap : a < superPotential m p := by
      by_contra h
      exact hp.2 (hsub (le_of_not_gt h))
    refine ⟨min (superPotential m p) (a+1),lt_min hap (by linarith),?_⟩
    intro z hz
    change superPotential m z < _ at hz
    by_contra h
    exact not_lt_of_ge (hmin ⟨le_of_lt (lt_of_lt_of_le hz (min_le_right _ _)),h⟩)
      (lt_of_lt_of_le hz (min_le_left _ _))
  · refine ⟨a+1,by linarith,?_⟩
    intro z hz
    change superPotential m z < _ at hz
    by_contra h
    exact hne ⟨z,hz.le,h⟩

end UniversalCoverSplitting

open Set Metric Filter Topology

open Set Metric Filter Topology
open scoped Manifold

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.DiskAxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open scoped Manifold ContDiff
open Set MeasureTheory
open scoped ContDiff
open scoped Manifold ContDiff ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric
open Set MeasureTheory Filter Topology
open scoped ENNReal
open Set
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set Metric Filter Topology
open scoped Manifold

namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma superDomain_full_boundary [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {m : ℕ} (hm : 0 < m)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {f : ℂ × ℂ → X.Carrier} (hf : IsBox S (superDomain m a) f)
    {α β : ℂ → X.Carrier} (hα : IsHorizontalCurve S (ball (0:ℂ) 1) α)
    (hβ : IsVerticalCurve S (ball (0:ℂ) 1) β)
    (he₁ : ∀ z, (z,0) ∈ superDomain m a → f (z,0)=α z)
    (he₂ : ∀ z, (0,z) ∈ superDomain m a → f (0,z)=β z)
    {p : ℂ × ℂ} (hp : p ∈ frontier (superDomain m a)) :
    ∃ V : Set (ℂ × ℂ), IsOpen V ∧ p ∈ V ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S V F ∧ EqOn F f (V ∩ superDomain m a) := by
  have hpa : superPotential m p = a := by rwa [superDomain_frontier hm ha] at hp
  have hpD := superSublevel_subset_bidisk hm ha1 (show superPotential m p ≤ a from hpa.le)
  rcases p with ⟨u,v⟩
  by_cases hv : v = 0
  · subst v
    exact horizontal_axis_boundary_extension h₁ h₂ (superDomain_open m a) (superDomain_convex m a) hf
      isOpen_ball hα hpD.1 (superDomain_axis_closure hm ha hpa.le) (fun z _ hz ↦ he₁ z hz)
  by_cases hu : u = 0
  · subst u
    exact vertical_axis_boundary_extension h₁ h₂ (superDomain_open m a) (superDomain_convex m a) hf
      isOpen_ball hβ hpD.2 (superDomain_vertical_axis_closure hm ha hpa.le) (fun z _ hz ↦ he₂ z hz)
  exact superDomain_mixed_boundary g h₁ h₂ hm ha hf hpa hu hv

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma super_box_maximal {m : ℕ} (hm : 0 < m) (f₀ : ℂ × ℂ → X.Carrier)
    (hini : ∃ a : ℝ, 0 < a ∧ ∃ f : ℂ × ℂ → X.Carrier,
      IsBox S (superDomain m a) f ∧ f =ᶠ[𝓝 0] f₀)
    (hforward : ∀ a : ℝ, 0 < a → a < 1 → ∀ f : ℂ × ℂ → X.Carrier,
      IsBox S (superDomain m a) f → f =ᶠ[𝓝 0] f₀ →
      ∃ b : ℝ, a < b ∧ ∃ F : ℂ × ℂ → X.Carrier,
        IsBox S (superDomain m b) F ∧ F =ᶠ[𝓝 0] f₀) :
    ∃ f : ℂ × ℂ → X.Carrier, IsBox S (superDomain m 1) f ∧ f =ᶠ[𝓝 0] f₀ := by
  classical
  let T : Set ℝ := {a | 0 < a ∧ a ≤ 1 ∧ ∃ f : ℂ × ℂ → X.Carrier,
    IsBox S (superDomain m a) f ∧ f =ᶠ[𝓝 0] f₀}
  obtain ⟨a₀,ha₀,f,hf,hfg⟩ := hini
  have hTne : T.Nonempty := ⟨min a₀ 1,lt_min ha₀ (by norm_num),min_le_right _ _,f,
    hf.mono (superDomain_mono m (min_le_left _ _)),hfg⟩
  have hTbdd : BddAbove T := ⟨1,fun _ h ↦ h.2.1⟩
  let A := sSup T
  have hA : 0 < A := lt_csSup_of_lt hTbdd hTne.choose_spec hTne.choose_spec.1
  have hA1 : A ≤ 1 := csSup_le hTne (fun _ h ↦ h.2.1)
  have hfchoose (a : T) : ∃ f : ℂ × ℂ → X.Carrier,
      IsBox S (superDomain m a) f ∧ f =ᶠ[𝓝 0] f₀ := a.property.2.2
  choose F hF hF₀ using hfchoose
  have hcompat (a b : T) : EqOn (F a) (F b) (superDomain m a ∩ superDomain m b) := by
    apply holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq
      ((superDomain_open m a).inter (superDomain_open m b))
      (((superDomain_convex m a).inter (superDomain_convex m b)).isPreconnected)
      ((hF a).1.mono inter_subset_left) ((hF b).1.mono inter_subset_right)
      (show (0:ℂ × ℂ) ∈ superDomain m a ∩ superDomain m b from
        ⟨superDomain_zero hm a.property.1,superDomain_zero hm b.property.1⟩)
      ((hF₀ a).trans (hF₀ b).symm)
  obtain ⟨G,hG,hGF⟩ := glue_boxes (fun a : T ↦ superDomain m a)
    (fun a ↦ superDomain_open m a) F hF hcompat (f₀ 0)
  have hUnion : (⋃ a : T, superDomain m a) = superDomain m A := by
    ext z
    constructor
    · intro hz
      obtain ⟨a,ha⟩ := mem_iUnion.mp hz
      exact superDomain_mono m (le_csSup hTbdd a.property) ha
    · intro hz
      obtain ⟨a,ha,haP⟩ := exists_lt_of_lt_csSup hTne hz
      exact mem_iUnion.mpr ⟨⟨a,ha⟩,haP⟩
  have hGb : IsBox S (superDomain m A) G := hUnion ▸ hG
  let a : T := ⟨hTne.choose,hTne.choose_spec⟩
  have hGg : G =ᶠ[𝓝 0] f₀ := by
    apply EventuallyEq.trans _ (hF₀ a)
    exact mem_of_superset ((superDomain_open m a).mem_nhds (superDomain_zero hm a.property.1)) (hGF a)
  have hAeq : A = 1 := by
    by_contra hne
    obtain ⟨b,hb,H,hH,hH₀⟩ := hforward A hA (lt_of_le_of_ne hA1 hne) G hGb hGg
    have hmin : min b 1 ∈ T := ⟨lt_min (hA.trans hb) (by norm_num),min_le_right _ _,H,
      hH.mono (superDomain_mono m (min_le_left _ _)),hH₀⟩
    have hle : min b 1 ≤ A := le_csSup hTbdd hmin
    have hlt : A < min b 1 := lt_min hb (lt_of_le_of_ne hA1 hne)
    exact not_lt_of_ge hle hlt
  exact ⟨G,hAeq ▸ hGb,hGg⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting

lemma superSublevel_zero {m : ℕ} (hm : 0 < m) :
    {z | superPotential m z ≤ 0} = {(0:ℂ × ℂ)} := by
  ext z
  constructor
  · intro hz
    have h₁ : Complex.normSq z.1 ^ m = 0 := by
      have h1 := pow_nonneg (Complex.normSq_nonneg z.1) m
      have h2 := pow_nonneg (Complex.normSq_nonneg z.2) m
      change Complex.normSq z.1 ^ m + Complex.normSq z.2 ^ m ≤ 0 at hz
      linarith
    have h₂ : Complex.normSq z.2 ^ m = 0 := by
      have h1 := pow_nonneg (Complex.normSq_nonneg z.1) m
      have h2 := pow_nonneg (Complex.normSq_nonneg z.2) m
      change Complex.normSq z.1 ^ m + Complex.normSq z.2 ^ m ≤ 0 at hz
      linarith
    exact Prod.ext (Complex.normSq_eq_zero.mp ((pow_eq_zero_iff hm.ne').mp h₁)) (Complex.normSq_eq_zero.mp ((pow_eq_zero_iff hm.ne').mp h₂))
  · intro hz
    change superPotential m z ≤ 0
    rw [mem_singleton_iff.mp hz,superPotential_zero hm]

lemma superDomain_small {m : ℕ} (hm : 0 < m) {U : Set (ℂ × ℂ)} (hU : IsOpen U) (h0 : 0 ∈ U) :
    ∃ a : ℝ, 0 < a ∧ superDomain m a ⊆ U := by
  apply superSublevel_widen hm hU
  rw [superSublevel_zero hm]
  exact singleton_subset_iff.mpr h0

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem disk_axes [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {α β : ℂ → X.Carrier} (hα : IsHorizontalCurve S (ball (0:ℂ) 1) α)
    (hβ : IsVerticalCurve S (ball (0:ℂ) 1) β) (hbase : α 0 = β 0) :
    ∃ F : ℂ × ℂ → X.Carrier, IsBox S (ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1) F ∧
      (∀ z ∈ ball (0:ℂ) 1, F (z,0)=α z) ∧ (∀ z ∈ ball (0:ℂ) 1, F (0,z)=β z) := by
  classical
  obtain ⟨d,hd,_,_,f₀,hf₀,hfα,hfβ⟩ := exists_axis_box_germ h₁ h₂ isOpen_ball isOpen_ball
    (mem_ball_self (show (0:ℝ)<1 by norm_num)) (mem_ball_self (show (0:ℝ)<1 by norm_num)) hα hβ hbase
  have hgα : (fun z : ℂ ↦ f₀ (z,0)) =ᶠ[𝓝 0] α := mem_of_superset (ball_mem_nhds 0 hd) hfα
  have hgβ : (fun z : ℂ ↦ f₀ (0,z)) =ᶠ[𝓝 0] β := mem_of_superset (ball_mem_nhds 0 hd) hfβ
  have hcont₁ : Tendsto (fun z : ℂ ↦ (z,(0:ℂ))) (𝓝 0) (𝓝 0) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hcont₂ : Tendsto (fun z : ℂ ↦ ((0:ℂ),z)) (𝓝 0) (𝓝 0) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hex (m : ℕ) (hm : 0 < m) :
      ∃ f : ℂ × ℂ → X.Carrier, IsBox S (superDomain m 1) f ∧ f =ᶠ[𝓝 0] f₀ := by
    apply super_box_maximal hm f₀
    · obtain ⟨a,ha,haU⟩ := superDomain_small hm (isOpen_ball.prod isOpen_ball)
        (show (0:ℂ × ℂ) ∈ ball (0:ℂ) d ×ˢ ball (0:ℂ) d from ⟨mem_ball_self hd,mem_ball_self hd⟩)
      exact ⟨a,ha,f₀,hf₀.mono haU,EventuallyEq.rfl⟩
    intro a ha ha1 f hf hfg
    have haxes := superDomain_axes_of_eventually hm ha ha1.le hf hα hβ
      ((hfg.comp_tendsto hcont₁).trans hgα) ((hfg.comp_tendsto hcont₂).trans hgβ)
    obtain ⟨W,hW,hWsub,H,hH,hHf⟩ := box_extend_closure (superDomain_open m a) (superDomain_convex m a) hf
      (fun _ hp ↦ superDomain_full_boundary g h₁ h₂ hm ha ha1 hf hα hβ haxes.1 haxes.2 hp)
    obtain ⟨b,hb,hbW⟩ := superSublevel_widen hm hW (by rwa [← superDomain_closure hm ha])
    refine ⟨b,hb,H,hH.mono hbW,?_⟩
    have hHfg : H =ᶠ[𝓝 0] f := mem_of_superset ((superDomain_open m a).mem_nhds (superDomain_zero hm ha)) hHf
    exact hHfg.trans hfg
  choose F hF hFg using (fun m : {m : ℕ // 0 < m} ↦ hex m m.property)
  have hcompat (m k : {m : ℕ // 0 < m}) :
      EqOn (F m) (F k) (superDomain m 1 ∩ superDomain k 1) := by
    exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq
      ((superDomain_open m 1).inter (superDomain_open k 1))
      (((superDomain_convex m 1).inter (superDomain_convex k 1)).isPreconnected)
      ((hF m).1.mono inter_subset_left) ((hF k).1.mono inter_subset_right)
      (show (0:ℂ × ℂ) ∈ superDomain m 1 ∩ superDomain k 1 from
        ⟨superDomain_zero m.property (by norm_num),superDomain_zero k.property (by norm_num)⟩)
      ((hFg m).trans (hFg k).symm)
  obtain ⟨G,hG,hGF⟩ := glue_boxes (fun m : {m : ℕ // 0 < m} ↦ superDomain m 1)
    (fun m ↦ superDomain_open m 1) F hF hcompat (α 0)
  refine ⟨G,superDomain_exhaustion ▸ hG,?_,?_⟩
  · intro z hz
    have hzU : (z,0) ∈ ⋃ m : {m : ℕ // 0 < m}, superDomain m 1 := by
      rw [superDomain_exhaustion]
      exact ⟨hz,mem_ball_self (by norm_num)⟩
    obtain ⟨m,hm⟩ := mem_iUnion.mp hzU
    exact (hGF m hm).trans ((superDomain_axes_of_eventually m.property (by norm_num) (le_refl 1)
      (hF m) hα hβ ((hFg m).comp_tendsto hcont₁ |>.trans hgα)
      ((hFg m).comp_tendsto hcont₂ |>.trans hgβ)).1 z hm)
  · intro z hz
    have hzU : (0,z) ∈ ⋃ m : {m : ℕ // 0 < m}, superDomain m 1 := by
      rw [superDomain_exhaustion]
      exact ⟨mem_ball_self (by norm_num),hz⟩
    obtain ⟨m,hm⟩ := mem_iUnion.mp hzU
    exact (hGF m hm).trans ((superDomain_axes_of_eventually m.property (by norm_num) (le_refl 1)
      (hF m) hα hβ ((hFg m).comp_tendsto hcont₁ |>.trans hgα)
      ((hFg m).comp_tendsto hcont₂ |>.trans hgβ)).2 z hm)

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.PlaqueCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

def SplittingChart.productChart (e : SplittingChart S) :
    ProductBoxTopology.ProductChart (splittingAtlas S) where
  chart := e.chart
  mem_atlas := ⟨e,rfl⟩
  first := ball 0 e.radius
  second := ball 0 e.radius
  product_range := e.product_range
  inverse_box := by
    have h := e.inverse_isBlockBox
    rw [e.product_range] at h
    exact h.plaqueBox isOpen_ball isOpen_ball

lemma splittingProductCharts_cover (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) (x : X.Carrier) :
    ∃ e : ProductBoxTopology.ProductChart (splittingAtlas S), x ∈ e.chart.source := by
  obtain ⟨e,he,_⟩ := exists_splittingChart S h₁ h₂ x
  exact ⟨e.productChart,he⟩

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma norm_unitComplex (t : I) : ‖unitComplex t‖ = (t:ℝ) := by
  simp [unitComplex,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg t.property.1]

theorem exists_radial_plaque_box [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {α : E → X.Carrier} {β : F → X.Carrier}
    (hα : IsHorizontalMap S (ball (0:E) 1) α) (hβ : IsVerticalMap S (ball (0:F) 1) β)
    (hbase : α 0=β 0) {p : E} {q : F} (hp : p ∈ ball (0:E) 1) (hq : q ∈ ball (0:F) 1) :
    ∃ R : I × I → X.Carrier, ProductBoxTopology.IsBox (splittingAtlas S) R ∧
      (∀ t : I, R (t,0)=α (unitComplex t • p)) ∧
      (∀ t : I, R (0,t)=β (unitComplex t • q)) := by
  have hm : max ‖p‖ ‖q‖ < 1 := max_lt (mem_ball_zero_iff.mp hp) (mem_ball_zero_iff.mp hq)
  obtain ⟨a,hma,ha1⟩ := exists_between hm
  have ha : 0 < a := (norm_nonneg p).trans_lt ((le_max_left _ _).trans_lt hma)
  have hap : ‖p‖ < a := (le_max_left _ _).trans_lt hma
  have haq : ‖q‖ < a := (le_max_right _ _).trans_lt hma
  have haC : (a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hαs := hα.comp isOpen_ball isOpen_ball
    (show DifferentiableOn ℂ (fun z : ℂ ↦ (z/(a:ℂ)) • p) (ball 0 1) from by fun_prop)
    (fun z hz ↦ radial_scaled_ball ha hap hz)
  have hβs := hβ.comp isOpen_ball isOpen_ball
    (show DifferentiableOn ℂ (fun z : ℂ ↦ (z/(a:ℂ)) • q) (ball 0 1) from by fun_prop)
    (fun z hz ↦ radial_scaled_ball ha haq hz)
  obtain ⟨H,hH,hHα,hHβ⟩ := disk_axes g h₁ h₂ hαs.curve hβs.curve (by simpa using hbase)
  have ht (t : I) : (a:ℂ)*unitComplex t ∈ ball (0:ℂ) 1 := by
    rw [mem_ball_zero_iff,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,norm_unitComplex]
    exact (mul_le_mul_of_nonneg_left t.property.2 ha.le).trans_lt (by simpa using ha1)
  let i : I → ball (0:ℂ) 1 := fun t ↦ ⟨(a:ℂ)*unitComplex t,ht t⟩
  have hi : Continuous i := (continuous_const.mul continuous_unitComplex).subtype_mk _
  let R : I × I → X.Carrier := fun w ↦ H (i w.1,i w.2)
  refine ⟨R,(hH.isBlockBox.plaqueBox isOpen_ball isOpen_ball).precomp hi hi,?_,?_⟩
  · intro t
    change H ((a:ℂ)*unitComplex t,(a:ℂ)*unitComplex 0)=α (unitComplex t • p)
    simpa [unitComplex,Function.comp_def,haC] using hHα ((a:ℂ)*unitComplex t) (ht t)
  · intro t
    change H ((a:ℂ)*unitComplex 0,(a:ℂ)*unitComplex t)=β (unitComplex t • q)
    simpa [unitComplex,Function.comp_def,haC] using hHβ ((a:ℂ)*unitComplex t) (ht t)

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.ParameterGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem ball_axes_zero [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {α : E → X.Carrier} {β : F → X.Carrier}
    (hα : IsHorizontalMap S (ball (0:E) 1) α) (hβ : IsVerticalMap S (ball (0:F) 1) β)
    (hbase : α 0=β 0) :
    ∃ H : E × F → X.Carrier, IsBlockBox S (ball 0 1 ×ˢ ball 0 1) H ∧
      (∀ p ∈ ball 0 1, H (p,0)=α p) ∧ (∀ q ∈ ball 0 1, H (0,q)=β q) := by
  classical
  let U : Set (E × F) := ball 0 1 ×ˢ ball 0 1
  have hU : IsOpen U := isOpen_ball.prod isOpen_ball
  have h0E : (0:E) ∈ ball (0:E) 1 := by simp
  have h0F : (0:F) ∈ ball (0:F) 1 := by simp
  have hex (p : U) := exists_radial_plaque_box g h₁ h₂ hα hβ hbase p.property.1 p.property.2
  let R : (E × F) → I × I → X.Carrier := fun p ↦
    if hp : p ∈ U then Classical.choose (hex ⟨p,hp⟩) else fun _ ↦ α 0
  have hR (p : E × F) (hp : p ∈ U) := Classical.choose_spec (hex ⟨p,hp⟩)
  have hbox (p : E × F) (hp : p ∈ U) :
      ProductBoxTopology.IsBox (splittingAtlas S) (R p) := by
    simpa only [R,dite_eq_left hp] using (hR p hp).1
  have hbottom (p : E × F) (hp : p ∈ U) (t : I) : R p (t,0)=α (unitComplex t • p.1) := by
    simpa only [R,dite_eq_left hp] using (hR p hp).2.1 t
  have hleft (p : E × F) (hp : p ∈ U) (t : I) : R p (0,t)=β (unitComplex t • p.2) := by
    simpa only [R,dite_eq_left hp] using (hR p hp).2.2 t
  have hsm (t : I) : ‖unitComplex t‖ ≤ 1 := by rw [norm_unitComplex]; exact t.property.2
  have hcB : Continuous (fun z : U × I ↦ R z.1 (z.2,0)) := by
    have hmap : ∀ z : U × I, unitComplex z.2 • z.1.val.1 ∈ ball (0:E) 1 :=
      fun z ↦ smul_unit_ball (hsm z.2) z.1.property.1
    have hc : Continuous (fun z : U × I ↦ unitComplex z.2 • z.1.val.1) :=
      (continuous_unitComplex.comp continuous_snd).smul (continuous_subtype_val.comp continuous_fst).fst
    exact hα.1.continuousOn.comp_continuous hc hmap |>.congr fun z ↦ (hbottom _ z.1.property z.2).symm
  have hcL : Continuous (fun z : U × I ↦ R z.1 (0,z.2)) := by
    have hmap : ∀ z : U × I, unitComplex z.2 • z.1.val.2 ∈ ball (0:F) 1 :=
      fun z ↦ smul_unit_ball (hsm z.2) z.1.property.2
    have hc : Continuous (fun z : U × I ↦ unitComplex z.2 • z.1.val.2) :=
      (continuous_unitComplex.comp continuous_snd).smul (continuous_subtype_val.comp continuous_fst).snd
    exact hβ.1.continuousOn.comp_continuous hc hmap |>.congr fun z ↦ (hleft _ z.1.property z.2).symm
  have hcR := ProductBoxTopology.continuous_family (splittingProductCharts_cover h₁ h₂)
    (fun p : U ↦ hbox p p.property) hcB hcL
  have hc : ContinuousOn (Function.uncurry R) (U ×ˢ univ) := by
    apply ProductBoxTopology.continuousOn_prod_iff.mpr
    exact hcR.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hb (t : I) : IsBlockBox S U (fun p ↦ R p (t,0)) := by
    have ht := hα.comp isOpen_ball isOpen_ball
      (show DifferentiableOn ℂ (fun p : E ↦ unitComplex t • p) (ball 0 1) from by fun_prop)
      (fun p hp ↦ smul_unit_ball (hsm t) hp)
    exact (ht.block (V := ball (0:F) 1) isOpen_ball isOpen_ball).congr hU
      (fun p hp ↦ hbottom p hp t)
  have hl (t : I) : IsBlockBox S U (fun p ↦ R p (0,t)) := by
    have ht := hβ.comp isOpen_ball isOpen_ball
      (show DifferentiableOn ℂ (fun q : F ↦ unitComplex t • q) (ball 0 1) from by fun_prop)
      (fun q hq ↦ smul_unit_ball (hsm t) hq)
    exact (ht.block (U := ball (0:E) 1) isOpen_ball isOpen_ball).congr hU
      (fun p hp ↦ hleft p hp t)
  have hcover : ∀ x : X.Carrier, ∃ e ∈ splittingAtlas S, x ∈ e.source := by
    intro x
    obtain ⟨e,he,_⟩ := exists_splittingChart S h₁ h₂ x
    exact ⟨e.chart,⟨e,rfl⟩,he⟩
  refine ⟨fun p ↦ R p (1,1),block_endpoint_of_family h₁ h₂ hU hbox hc hb hl,?_,?_⟩
  · intro p hp
    have hpu : (p,0) ∈ U := ⟨hp,h0F⟩
    have he := ProductBoxTopology.unique (splittingAtlas S) hcover (hbox (p,0) hpu)
      ((hbox (p,0) hpu).precomp continuous_id (continuous_const : Continuous (fun _ : I ↦ (0:I))))
      (fun _ ↦ rfl) (fun t ↦ by
        change R (p,0) (0,t)=R (p,0) (0,0)
        rw [hleft _ hpu,hleft _ hpu]; simp)
    have h := congrFun he (1,1)
    change R (p,0) (1,1)=R (p,0) (1,0) at h
    rw [hbottom _ hpu] at h
    simpa [unitComplex] using h
  · intro q hq
    have hqu : (0,q) ∈ U := ⟨h0E,hq⟩
    have he := ProductBoxTopology.unique (splittingAtlas S) hcover (hbox (0,q) hqu)
      ((hbox (0,q) hqu).precomp (continuous_const : Continuous (fun _ : I ↦ (0:I))) continuous_id)
      (fun t ↦ by
        change R (0,q) (t,0)=R (0,q) (0,0)
        rw [hbottom _ hqu,hbottom _ hqu]; simp) (fun _ ↦ rfl)
    have h := congrFun he (1,1)
    change R (0,q) (1,1)=R (0,q) (0,1) at h
    rw [hleft _ hqu] at h
    simpa [unitComplex] using h

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.PolydiskAxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s d e : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem polydisk_axes [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {α : Model d → X.Carrier} {β : Model e → X.Carrier}
    (hα : IsHorizontalMap S (ball 0 1) α) (hβ : IsVerticalMap S (ball 0 1) β)
    {p₀ : Model d} {q₀ : Model e} (hp₀ : p₀ ∈ ball 0 1) (hq₀ : q₀ ∈ ball 0 1)
    (hbase : α p₀=β q₀) :
    ∃ H : Model d × Model e → X.Carrier, IsBlockBox S (ball 0 1 ×ˢ ball 0 1) H ∧
      (∀ p ∈ ball 0 1, H (p,q₀)=α p) ∧ (∀ q ∈ ball 0 1, H (p₀,q)=β q) := by
  have hpN : -p₀ ∈ ball (0:Model d) 1 := by simpa using hp₀
  have hqN : -q₀ ∈ ball (0:Model e) 1 := by simpa using hq₀
  have hα' := hα.comp isOpen_ball isOpen_ball (UnitPolydisk.differentiableOn_shift hp₀)
    (fun _ h ↦ UnitPolydisk.shift_mem hp₀ h)
  have hβ' := hβ.comp isOpen_ball isOpen_ball (UnitPolydisk.differentiableOn_shift hq₀)
    (fun _ h ↦ UnitPolydisk.shift_mem hq₀ h)
  obtain ⟨F,hF,hFα,hFβ⟩ := ball_axes_zero g h₁ h₂ hα' hβ'
    (by simpa only [Function.comp_apply,UnitPolydisk.shift_zero] using hbase)
  let a := UnitPolydisk.shift (-p₀)
  let b := UnitPolydisk.shift (-q₀)
  have hap₀ : a p₀=0 := by ext i; exact UnitPolydisk.discShift_neg_self
  have hbq₀ : b q₀=0 := by ext i; exact UnitPolydisk.discShift_neg_self
  refine ⟨F ∘ Prod.map a b,hF.comp_parameters isOpen_ball isOpen_ball isOpen_ball isOpen_ball
    (UnitPolydisk.differentiableOn_shift hpN) (UnitPolydisk.differentiableOn_shift hqN)
    (fun _ h ↦ UnitPolydisk.shift_mem hpN h) (fun _ h ↦ UnitPolydisk.shift_mem hqN h),?_,?_⟩
  · intro p hp
    change F (a p,b q₀)=α p
    rw [hbq₀,hFα (a p) (UnitPolydisk.shift_mem hpN hp)]
    have hh := UnitPolydisk.shift_inverse hpN hp
    simpa only [neg_neg,Function.comp_apply] using congrArg α hh
  · intro q hq
    change F (a p₀,b q)=β q
    rw [hap₀,hFβ (b q) (UnitPolydisk.shift_mem hqN hq)]
    have hh := UnitPolydisk.shift_inverse hqN hq
    simpa only [neg_neg,Function.comp_apply] using congrArg β hh

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s d e : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma disk_fill [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {a : Polydisk d → X.Carrier} {b : Polydisk e → X.Carrier}
    (ha : IsDiskHorizontal S a) (hb : IsDiskVertical S b)
    (p : Polydisk d) (q : Polydisk e) (hc : a p=b q) :
    ∃ f, IsDiskTile S f ∧ (∀ x, f (x,q)=a x) ∧ (∀ y, f (p,y)=b y) := by
  obtain ⟨A,hA,eA⟩ := ha
  obtain ⟨B,hB,eB⟩ := hb
  obtain ⟨F,hF,hFa,hFb⟩ := polydisk_axes g h₁ h₂ hA hB p.property q.property
    (by rw [eA p,eB q]; exact hc)
  refine ⟨fun z ↦ F (z.1,z.2),⟨F,hF,fun _ ↦ rfl⟩,?_,?_⟩
  · intro x; exact (hFa x x.property).trans (eA x)
  · intro y; exact (hFb y y.property).trans (eB y)

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.PathBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
open IntervalChain
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {A : Type*} [TopologicalSpace A]

theorem path_diagonal [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {γ : I → X.Carrier} (hγ : Continuous γ) :
    ∃ R : I × I → X.Carrier, ProductBoxTopology.IsBox (splittingAtlas S) R ∧
      ∀ t, R (t,t)=γ t := by
  obtain ⟨t,ht0,ht,⟨N,hN⟩,D,hD,a,ha,eD⟩ :=
    PathSubdivision.parameterize γ (IsDiskTile (d:=r) (e:=s) S)
      (continuous_local_parameter h₁ h₂ hγ)
  let lo : ℕ → Polydisk r := fun i ↦ (a i ⟨t i,le_rfl,ht (Nat.le_succ i)⟩).1
  let hi : ℕ → Polydisk r := fun i ↦ (a i ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩).1
  let bot : ℕ → Polydisk s := fun i ↦ (a i ⟨t i,le_rfl,ht (Nat.le_succ i)⟩).2
  let top : ℕ → Polydisk s := fun i ↦ (a i ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩).2
  have join (i : ℕ) : D i (hi i,top i)=D (i+1) (lo (i+1),bot (i+1)) :=
    (eD i ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩).trans
      (eD (i+1) ⟨t (i+1),le_rfl,ht (Nat.le_succ (i+1))⟩).symm
  obtain ⟨F,hF,hFD,hFh,hFv⟩ := RectangleGrid.diagonal_grid
    {a | IsDiskHorizontal S a} {b | IsDiskVertical S b} {f | IsDiskTile S f}
    (fun _ h q ↦ h.horizontal q) (fun _ h p ↦ h.vertical p)
    (fun _ hA _ hB p q hc ↦ disk_fill g h₁ h₂ hA hB p q hc)
    D hD lo hi bot top join
  let tile (i j : ℕ) : cell t i × cell t j → X.Carrier :=
    fun p ↦ F i j ((a i p.1).1,(a j p.2).2)
  have htile (i j : ℕ) : ProductBoxTopology.IsBox (splittingAtlas S) (tile i j) :=
    (hF i j).plaqueBox.precomp (ha i).fst (ha j).snd
  obtain ⟨R,hR,hRt⟩ := ProductBoxTopology.grid_glue (splittingAtlas S) t t ht0 ht0 ht ht
    N N (hN N le_rfl) (hN N le_rfl) tile htile
    (fun i j y ↦ hFh i j (a j y).2) (fun i j x ↦ hFv i j (a i x).1)
  refine ⟨R,hR,fun x ↦ ?_⟩
  obtain ⟨i,_,hxi⟩ := covers t ht0 ht N (hN N le_rfl) x
  let xx : cell t i := ⟨x,hxi⟩
  calc R (x,x)=tile i i (xx,xx) := hRt i i xx xx
       _ = D i (a i xx) := congrFun (hFD i) (a i xx)
       _ = γ x := eD i xx

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.EtaleGerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
namespace HolomorphicEtale
variable {m n : ℕ} (M : ComplexManifold m) (X : ComplexManifold n)

def sectionOf (f : M.Carrier → X.Carrier) {U : Set M.Carrier} (hU : IsOpen U)
    (hf : MDifferentiableOn (model m) (model n) f U) : U → Germs M X :=
  fun x ↦ ⟨FunctionEtale.sectionOf f x, U,hU,x.property,f,hf,rfl⟩

end HolomorphicEtale
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.ProjectionImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma GlobalProjection.image_horizontal [CompactSpace X.Carrier] (g : KahlerMetric X)
    (Q : GlobalProjection π o h₁ h₂) (z : Z.Carrier) :
    ∃ α : C(I,Z.Carrier), α 0=o ∧ α 1=Q.toFun z ∧
      ProductBoxTopology.IsHorizontal (splittingAtlas S) (π.projection ∘ α) := by
  let := π.simplyConnected
  let γ := PathConnectedSpace.somePath o z
  obtain ⟨R,hR,hdiag⟩ := path_diagonal g h₁ h₂ (π.covering.continuous.comp γ.continuous)
  have hR0 : π.projection o=R (0,0) := by
    rw [hdiag]
    change π.projection o=π.projection (γ 0)
    rw [γ.source]
  let : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by simp⟩
  obtain ⟨L,⟨hL0,hLb⟩,_⟩ := π.covering.existsUnique_continuousMap_lifts ⟨R,hR.1⟩ (0,0) o hR0
  have hcont : Continuous (fun t : I ↦ L (t,t)) := L.continuous.comp (continuous_id.prodMk continuous_id)
  have hLdiag : (fun t : I ↦ L (t,t))=γ := by
    refine π.covering.isSeparatedMap.eq_of_comp_eq π.covering.isLocalHomeomorph.isLocallyInjective
      hcont γ.continuous ?_ 0 ?_
    · ext t
      exact (congrFun hLb (t,t)).trans (hdiag t)
    · exact hL0.trans γ.source.symm
  let α : C(I,Z.Carrier) := ⟨fun t ↦ L (t,0),L.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hα : ProductBoxTopology.IsHorizontal (splittingAtlas S) (π.projection ∘ α) := by
    have he : π.projection ∘ α=(fun t ↦ R (t,0)) := by ext t; exact congrFun hLb (t,0)
    rw [he]
    exact hR.horizontal 0
  have hα0 : α 0=o := hL0
  have hQα := Q.horizontal_fixed α.continuous hα0 hα 1
  have hv : ProductBoxTopology.IsVertical (splittingAtlas S) (fun t ↦ π.projection (L (1,t))) := by
    have he : (fun t ↦ π.projection (L (1,t)))=(fun t ↦ R (1,t)) := by
      ext t; exact congrFun hLb (1,t)
    rw [he]
    exact hR.vertical 1
  have hQv := Q.vertical_constant (L.continuous.comp (continuous_const.prodMk continuous_id)) hv 1
  have hz : L (1,1)=z := (congrFun hLdiag 1).trans γ.target
  change Q.toFun (L (1,1))=Q.toFun (L (1,0)) at hQv
  rw [hz] at hQv
  exact ⟨α,hα0,(hQv.trans hQα).symm,hα⟩

lemma GlobalProjection.idempotent [CompactSpace X.Carrier] (g : KahlerMetric X)
    (Q : GlobalProjection π o h₁ h₂) (z : Z.Carrier) : Q.toFun (Q.toFun z)=Q.toFun z := by
  obtain ⟨α,hα0,hα1,hα⟩ := Q.image_horizontal g z
  have h := Q.horizontal_fixed α.continuous hα0 hα 1
  rwa [hα1] at h

end FirstGerm
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.FixedManifolds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold ContDiff
namespace UniversalCoverSplitting
namespace RetractChart
variable {n r s : ℕ} {Z : ComplexManifold n} {Q : Z.Carrier → Z.Carrier}

lemma differentiableOn_transition (e d : RetractChart Z Q r s) :
    DifferentiableOn ℂ (e.fixedChart.symm.trans d.fixedChart)
      (e.fixedChart.symm.trans d.fixedChart).source := by
  intro a ha
  have hat : (a,(0 : Model s)) ∈ e.chart.target := by
    rw [e.product_range]; exact ⟨ha.1,mem_ball_self e.radius_pos⟩
  have had : e.chart.symm (a,0) ∈ d.chart.source := by
    have hh := ha.2
    change (e.fixedInv a).val ∈ d.chart.source at hh
    rwa [e.fixedInv_val ha.1] at hh
  have he := (e.inverse_holomorphic _ hat).mdifferentiableAt (e.chart.open_target.mem_nhds hat)
  have hd := (d.holomorphic _ had).mdifferentiableAt (d.chart.open_source.mem_nhds had)
  have hins : MDifferentiableAt (model r) 𝓘(ℂ,Model r × Model s) (fun a : Model r ↦ (a,(0 : Model s))) a :=
    mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
  have hdcomp := (mdifferentiableAt_iff_differentiableAt.mp ((hd.comp _ he).comp a hins)).fst
  apply DifferentiableAt.differentiableWithinAt
  apply hdcomp.congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds ha.1] with b hb
  change (d.chart (e.fixedInv b).val).1=(d.chart (e.chart.symm (b,0))).1
  rw [e.fixedInv_val hb]

lemma contDiffOn_transition (e d : RetractChart Z Q r s) :
    ContDiffOn ℂ ∞ (e.fixedChart.symm.trans d.fixedChart)
      (e.fixedChart.symm.trans d.fixedChart).source :=
  finite_holomorphic_contDiffOn (e.fixedChart.symm.trans d.fixedChart).open_source
    (differentiableOn_transition e d)

variable (c : Fixed Q → RetractChart Z Q r s)
    (hc : ∀ x, x.val ∈ (c x).chart.source)

lemma fixedIsManifold : letI := fixedChartedSpace c hc;
    IsManifold (model r) ∞ (Fixed Q) := by
  let := fixedChartedSpace c hc
  apply isManifold_of_contDiffOn
  intro e d he hd
  obtain ⟨x,rfl⟩ := he
  obtain ⟨y,rfl⟩ := hd
  simpa only [model,modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.comp_id,Function.id_comp,preimage_id,range_id,inter_univ] using
    contDiffOn_transition (c x) (c y)

def fixedManifold : ComplexManifold r where
  Carrier := Fixed Q
  topology := inferInstance
  hausdorff := inferInstance
  secondCountable := @TopologicalSpace.Subtype.secondCountableTopology Z.Carrier Z.topology {z | Q z=z} Z.secondCountable
  charted := fixedChartedSpace c hc
  complexSmooth := fixedIsManifold c hc

end RetractChart
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.SwapSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n}

lemma complementaryProjection_swap (S : HolomorphicSplitting X r s) :
    complementaryProjection S.swap=S.projection := by
  funext x
  change ContinuousLinearMap.id ℂ (Tangent X x)-(ContinuousLinearMap.id ℂ (Tangent X x)-S.projection x)=_
  exact sub_sub_cancel _ _

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.ProductRetracts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma integrable_swap_complement (h₁ : Integrable S.projection) :
    Integrable (complementaryProjection S.swap) := by rwa [complementaryProjection_swap]

structure ProductRetracts (π : OrdinaryUniversalCover X Z) (o : Z.Carrier)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S)) where
  first : FirstGerm.GlobalProjection π o h₁ h₂
  second : FirstGerm.GlobalProjection π o h₂ (integrable_swap_complement h₁)
  firstCharts : RetractChart.Fixed first.toFun → RetractChart Z first.toFun r s
  first_mem : ∀ x, x.val ∈ (firstCharts x).chart.source
  secondCharts : RetractChart.Fixed second.toFun → RetractChart Z second.toFun s r
  second_mem : ∀ x, x.val ∈ (secondCharts x).chart.source

namespace ProductRetracts
variable (P : ProductRetracts π o h₁ h₂)

def Y₁ : ComplexManifold r := RetractChart.fixedManifold P.firstCharts P.first_mem
def Y₂ : ComplexManifold s := RetractChart.fixedManifold P.secondCharts P.second_mem

variable [CompactSpace X.Carrier] (g : KahlerMetric X)

def q₁ : Z.Carrier → P.Y₁.Carrier := fun z ↦ ⟨P.first.toFun z,P.first.idempotent g z⟩
def q₂ : Z.Carrier → P.Y₂.Carrier := fun z ↦ ⟨P.second.toFun z,P.second.idempotent g z⟩
def pair : Z.Carrier → P.Y₁.Carrier × P.Y₂.Carrier := fun z ↦ (P.q₁ g z,P.q₂ g z)

end ProductRetracts
end UniversalCoverSplitting
end
end

end OAI
end


