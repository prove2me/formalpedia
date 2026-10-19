-- Prove2me | Definitions.Def_OAIQWUCS003
-- name    : OAIQWUCS003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T00:49:36.255777+00:00
-- url     : https://prove2.me/theorems/4963351e-a667-4de9-bede-0a8c69771fd5
-- title:
--   Annuli and alternating forms for the area estimate (OpenAI universal-cover splitting)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniversalCoverSplitting.main`. Its definitions serve the paper's Section 4 ("Extension across a mixed boundary"). There, Stokes' theorem for the closed Kähler form bounds the areas of shrinking complex tangent disks, and among many disjoint annuli one has small area.
--
--   The bundle holds OpenAI's Lean definitions from `lean/OAI/Geometry/KahlerSplitting` (OpenAI, *Universal-cover splitting for compact Kähler manifolds*, OpenAI Math Release, September 23, 2026, result family 052, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas their bodies use. Among them:
--   - alternating bilinear forms, their evaluation, and total partial derivatives (`alternatingBilinear`, `alternatingEvalCLM`, `totalPartialDeriv`);
--   - the coefficients of the moving Stokes formula on $\mathbb R^3$ (`Real3`, `realBasis3`, `stokesCoefficient`, `stokesCoefficientDeriv`, `movingPolar`) and the polar energy of a map on a disk, $2\pi\int_0^R r \cdot \operatorname{avg}_{|z-c|=r}\|F\|^2\,dr$ (`polarEnergy`);
--   - open, compact and scaled annuli, their boundary paths, and shrinking radii (`openAnnulus`, `compactAnnulus`, `scaledAnnulus`, `annulusPath`, `shrinkingRadius`);
--   - the source domain of the Hartogs shell (`superSource`).
--
--   It imports the bundles `OAIQWUCS000` and `OAIQWUCS001` of this split. The theorems the definitions do not need are proved in the solutions of this split.
-- source:
--   OpenAI, Universal-cover splitting for compact Kähler manifolds, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 052; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Universal-cover-splitting-for-compact-Kahler-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/KahlerSplitting at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWUCS000
import Definitions.Def_OAIQWUCS001

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

noncomputable section
open Set Metric
namespace UniversalCoverSplitting
variable {B E : Type*} [TopologicalSpace B] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_quadratic_comparison {K : Set B} (hK : IsCompact K)
    (Q T : B → E → ℝ)
    (hQ : ContinuousOn (fun p : B × E ↦ Q p.1 p.2) (K ×ˢ univ))
    (hT : ContinuousOn (fun p : B × E ↦ T p.1 p.2) (K ×ˢ univ))
    (hpos : ∀ x ∈ K, ∀ u, u ≠ 0 → 0 < Q x u)
    (hhom : ∀ x ∈ K, ∀ (r : ℝ) u, Q x (r • u) = r ^ 2 * Q x u)
    (hThom : ∀ x ∈ K, ∀ (r : ℝ) u, T x (r • u) = r ^ 2 * T x u) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ u, T x u ≤ C * Q x u := by
  let L : Set (B × E) := K ×ˢ sphere 0 1
  have hL : IsCompact L := hK.prod (isCompact_sphere 0 1)
  have hQL : ContinuousOn (fun p : B × E ↦ Q p.1 p.2) L :=
    hQ.mono (prod_mono_right (subset_univ _))
  have hnum : ContinuousOn (fun p : B × E ↦ T p.1 p.2) L :=
    hT.mono (prod_mono_right (subset_univ _))
  have hden : ∀ p ∈ L, Q p.1 p.2 ≠ 0 := by
    intro p hp
    apply ne_of_gt (hpos p.1 hp.1 p.2 _)
    intro he
    have hn : ‖p.2‖ = (1:ℝ) := by simpa using hp.2
    simp [he] at hn
  obtain ⟨C,hC⟩ := hL.bddAbove_image (hnum.div hQL hden)
  refine ⟨max C 1, by positivity, fun x hx u ↦ ?_⟩
  have hzero : Q x 0 = 0 := by simpa using hhom x hx 0 (0:E)
  have hTzero : T x 0 = 0 := by simpa using hThom x hx 0 (0:E)
  by_cases hu : u = 0
  · simp [hu,hzero,hTzero]
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let v := ‖u‖⁻¹ • u
  have hvnorm : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  have hv : v ∈ sphere (0:E) 1 := by simpa using hvnorm
  have hb : T x v / Q x v ≤ max C 1 :=
    (hC ⟨(x,v),⟨hx,hv⟩,rfl⟩).trans (le_max_left _ _)
  have hvpos : 0 < Q x v := hpos x hx v (by intro hh; simp [hh] at hvnorm)
  have hquad : T x v ≤ max C 1 * Q x v := (div_le_iff₀ hvpos).mp hb
  have huv : ‖u‖ • v = u := by
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  calc
    T x u = ‖u‖ ^ 2 * T x v := by
      conv_lhs => rw [← huv]
      exact hThom x hx ‖u‖ v
    _ ≤ ‖u‖ ^ 2 * (max C 1 * Q x v) := mul_le_mul_of_nonneg_left hquad (sq_nonneg _)
    _ = max C 1 * Q x u := by
      have hs : Q x u = ‖u‖ ^ 2 * Q x v := by rw [← hhom x hx ‖u‖ v, huv]
      rw [hs]
      ring

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
namespace UniversalCoverSplitting
variable {M E : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem chart_trapping_on_interval (e : OpenPartialHomeomorph M E)
    {c : E} {R L T : ℝ} (_hR : 0 < R) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (he : closedBall c R ⊆ e.target) {γ : ℝ → M}
    (hγ : ContinuousOn γ (Icc 0 T))
    (hzero : γ 0 ∈ e.source ∧ dist (e (γ 0)) c < R - L * T)
    (hder : ∀ t ∈ Icc 0 T, γ t ∈ e.symm '' closedBall c R →
      ∃ D : E, HasDerivWithinAt (e ∘ γ) D (Icc 0 T) t ∧ ‖D‖ ≤ L) :
    ∀ t ∈ Icc 0 T, γ t ∈ e.source ∧ e (γ t) ∈ ball c R := by
  let K := e.symm '' closedBall c R
  have hK : IsCompact K := (isCompact_closedBall c R).image_of_continuousOn
    (e.continuousOn_symm.mono he)
  have hKs : K ⊆ e.source := by
    rintro _ ⟨z,hz,rfl⟩
    exact e.map_target (he hz)
  have hKe : ∀ x ∈ K, e x ∈ closedBall c R := by
    rintro _ ⟨z,hz,rfl⟩
    simpa only [e.right_inv (he hz)] using hz
  have h0 : γ 0 ∈ K := by
    refine ⟨e (γ 0),?_,e.left_inv hzero.1⟩
    exact (hzero.2.trans_le (sub_le_self _ (mul_nonneg hL hT))).le
  have hA : IsClosed ((γ ⁻¹' K) ∩ Icc 0 T) :=
    by simpa [inter_comm] using hγ.preimage_isClosed_of_isClosed isClosed_Icc hK.isClosed
  have control (t : ℝ) (ht : t ∈ Icc 0 T)
      (hst : Icc 0 t ⊆ γ ⁻¹' K) : e (γ t) ∈ ball c R := by
    have hbound : ‖e (γ t) - e (γ 0)‖ ≤ L * t := by
      choose! D hD hDL using fun s (hs : s ∈ Icc 0 t) ↦
        hder s ⟨hs.1,hs.2.trans ht.2⟩ (hst hs)
      have hh := norm_image_sub_le_of_norm_deriv_le_segment'
        (fun s hs ↦ (hD s hs).mono (Icc_subset_Icc_right ht.2))
        (fun s hs ↦ hDL s (Ico_subset_Icc_self hs)) t (by exact ⟨ht.1,le_rfl⟩)
      simpa using hh
    change dist (e (γ t)) c < R
    have hdist : dist (e (γ t)) (e (γ 0)) ≤ L * t := by
      simpa [dist_eq_norm] using hbound
    have hm := mul_le_mul_of_nonneg_left ht.2 hL
    calc
      dist (e (γ t)) c ≤ dist (e (γ t)) (e (γ 0)) + dist (e (γ 0)) c := dist_triangle _ _ _
      _ ≤ L * T + dist (e (γ 0)) c := add_le_add (hdist.trans hm) le_rfl
      _ < R := by linarith [hzero.2]
  have hall : Icc 0 T ⊆ γ ⁻¹' K := by
    apply hA.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset h0
    intro t ht hst
    have hsrc := hKs (hst (right_mem_Icc.mpr ht.1))
    have hball := control t (Ico_subset_Icc_self ht) hst
    have hopen : IsOpen (e.source ∩ e ⁻¹' ball c R) := e.isOpen_inter_preimage isOpen_ball
    have hsub : e.source ∩ e ⁻¹' ball c R ⊆ K := by
      intro x hx
      exact ⟨e x,ball_subset_closedBall hx.2,e.left_inv hx.1⟩
    exact (((hγ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)).mono Ioi_subset_Ici_self)
      (mem_of_superset (hopen.mem_nhds ⟨hsrc,hball⟩) hsub)
  intro t ht
  exact ⟨hKs (hall ht),control t ht (fun s hs ↦ hall ⟨hs.1,hs.2.trans ht.2⟩)⟩

section ComplexDisk
variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem chart_trapping_on_disk (e : OpenPartialHomeomorph M E)
    {c : E} {R L r : ℝ} (hR : 0 < R) (hL : 0 ≤ L) (_hr : 0 ≤ r)
    (he : closedBall c R ⊆ e.target) {h : ℂ → M}
    (hc : ContinuousOn h (closedBall 0 r))
    (hzero : h 0 ∈ e.source ∧ dist (e (h 0)) c < R - L * r)
    (hder : ∀ z ∈ closedBall 0 r, h z ∈ e.symm '' closedBall c R →
      DifferentiableAt ℂ (e ∘ h) z ∧ ‖fderiv ℂ (e ∘ h) z‖ ≤ L) :
    ∀ z ∈ closedBall 0 r, h z ∈ e.source ∧ e (h z) ∈ ball c R := by
  intro z hz
  have hz' : ‖z‖ ≤ r := by simpa using hz
  have hmem (t : ℝ) (ht : t ∈ Icc 0 1) : t • z ∈ closedBall 0 r := by
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans hz'
  have hγ : ContinuousOn (fun t : ℝ ↦ h (t • z)) (Icc 0 1) :=
    hc.comp (continuous_id.smul continuous_const).continuousOn hmem
  have hinit : h ((0 : ℝ) • z) ∈ e.source ∧ dist (e (h ((0 : ℝ) • z))) c < R - (L * ‖z‖) * 1 := by
    simp only [zero_smul,mul_one]
    refine ⟨hzero.1,hzero.2.trans_le ?_⟩
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hz' hL) R
  have htrap := chart_trapping_on_interval e hR (mul_nonneg hL (norm_nonneg z)) zero_le_one
    he hγ hinit (fun t ht hk ↦ ?_) 1 (by norm_num)
  · simpa using htrap
  obtain ⟨hd,hb⟩ := hder (t • z) (hmem t ht) hk
  refine ⟨fderiv ℂ (e ∘ h) (t • z) z,?_,?_⟩
  · simpa only [Function.comp_def,id_eq,one_smul,ContinuousLinearMap.coe_restrictScalars'] using
      ((hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
        ((hasDerivAt_id t).smul_const z)).hasDerivWithinAt (s := Icc 0 1)
  · exact ((fderiv ℂ (e ∘ h) (t • z)).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg z))

end ComplexDisk
end UniversalCoverSplitting

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped Interval
namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem norm_circleAverage_sq_le {F : ℂ → E} {c : ℂ} {R : ℝ}
    (hF : ContinuousOn F (sphere c |R|)) :
    ‖Real.circleAverage F c R‖ ^ 2 ≤ Real.circleAverage (fun z ↦ ‖F z‖ ^ 2) c R := by
  have hc : Continuous (fun θ : ℝ ↦ F (circleMap c R θ)) :=
    hF.comp_continuous (continuous_circleMap c R) (fun θ ↦ circleMap_mem_sphere' c R θ)
  have hg : ConvexOn ℝ (univ : Set E) (fun v ↦ ‖v‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ ↦ norm_nonneg _) 2
  rw [Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]
  apply hg.map_set_average_le (continuous_norm.pow 2).continuousOn isClosed_univ
  · simp [Real.volume_uIoc, Real.pi_pos]
  · rw [Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  · exact Filter.Eventually.of_forall (fun _ ↦ mem_univ _)
  · exact (hc.intervalIntegrable _ _).def'
  · exact ((hc.norm.pow 2).intervalIntegrable _ _).def'

theorem norm_sq_le_circleAverage {F : ℂ → E} {c : ℂ} {R : ℝ}
    (hF : DiffContOnCl ℂ F (ball c |R|)) :
    ‖F c‖ ^ 2 ≤ Real.circleAverage (fun z ↦ ‖F z‖ ^ 2) c R := by
  by_cases hR : R = 0
  · simp [hR]
  rw [← hF.circleAverage]
  exact norm_circleAverage_sq_le (hF.2.mono (by
    rw [closure_ball _ (abs_ne_zero.mpr hR)]
    exact sphere_subset_closedBall))

def polarEnergy (F : ℂ → E) (c : ℂ) (R : ℝ) : ℝ :=
  2 * Real.pi * ∫ r in 0..R, r * Real.circleAverage (fun z ↦ ‖F z‖ ^ 2) c r

theorem norm_sq_mul_diskArea_le_polarEnergy {F : ℂ → E} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hF : DifferentiableOn ℂ F (closedBall c R)) :
    Real.pi * R ^ 2 * ‖F c‖ ^ 2 ≤ polarEnergy F c R := by
  have hc : ContinuousOn (Real.circleAverage (fun z ↦ ‖F z‖ ^ 2) c) (Icc 0 R) := by
    apply Real.ContinuousOn.circleAverage
    · exact (hF.continuousOn.norm.pow 2).mono (fun z hz ↦ by
        simpa only [mem_closedBall, dist_eq_norm] using hz.2)
    · exact fun _ hr ↦ hr.1
  have hi : IntervalIntegrable (fun r ↦ r * Real.circleAverage (fun z ↦ ‖F z‖ ^ 2) c r)
      volume 0 R := (continuousOn_id.mul hc).intervalIntegrable_of_Icc hR
  have hle : (∫ r in 0..R, r * ‖F c‖ ^ 2) ≤
      ∫ r in 0..R, r * Real.circleAverage (fun z ↦ ‖F z‖ ^ 2) c r := by
    apply intervalIntegral.integral_mono_on hR ((continuous_id.mul continuous_const).intervalIntegrable _ _) hi
    intro r hr
    apply mul_le_mul_of_nonneg_left _ hr.1
    apply norm_sq_le_circleAverage
    apply hF.diffContOnCl_ball
    rw [abs_of_nonneg hr.1]
    exact closedBall_subset_closedBall hr.2
  have heq : (∫ r in (0 : ℝ)..R, r * ‖F c‖ ^ 2) = R ^ 2 / 2 * ‖F c‖ ^ 2 := by
    rw [intervalIntegral.integral_mul_const, integral_id]
    ring
  rw [heq] at hle
  have hh := mul_le_mul_of_nonneg_left hle (show 0 ≤ 2 * Real.pi by positivity)
  unfold polarEnergy
  nlinarith

end UniversalCoverSplitting
noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped Interval
namespace UniversalCoverSplitting

lemma polar_symm_circle (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply]
  simp only [circleMap, zero_add, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

theorem disk_integral_eq_polar {f : ℂ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ContinuousOn f (closedBall 0 R)) :
    (∫ z in ball (0 : ℂ) R, f z) =
      2 * Real.pi * ∫ r in 0..R, r * Real.circleAverage f 0 r := by
  let G : ℝ × ℝ → ℝ := fun p ↦ p.1 * f (Complex.polarCoord.symm p)
  have htarget : Complex.polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi :=
    Complex.polarCoord_target
  have heq : (∫ z in ball (0 : ℂ) R, f z) =
      ∫ p in (Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi), G p := by
    rw [← integral_indicator measurableSet_ball,
      ← Complex.integral_comp_polarCoord_symm]
    change (∫ p in Complex.polarCoord.target, p.1 • (ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p)) = _
    have hi : (∫ p in Complex.polarCoord.target,
        p.1 • (ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p)) =
        ∫ p in Complex.polarCoord.target, {p : ℝ × ℝ | p.1 < R}.indicator G p := by
      apply setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
      intro p hp
      rw [htarget] at hp
      have hm : Complex.polarCoord.symm p ∈ ball (0 : ℂ) R ↔ p.1 < R := by
        simp only [mem_ball, dist_zero_right]
        rw [Complex.norm_polarCoord_symm,abs_of_pos (show 0 < p.1 from hp.1)]
      change p.1 • (ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p) = _
      by_cases h : p.1 < R
      · rw [indicator_of_mem (hm.mpr h),indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.1 < R} from h)]
        rfl
      · rw [indicator_of_notMem (mt hm.mp h),indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.1 < R} from h),smul_zero]
    rw [hi,setIntegral_indicator (isOpen_lt continuous_fst continuous_const).measurableSet]
    have hs : Complex.polarCoord.target ∩ {p : ℝ × ℝ | p.1 < R} =
        Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi := by
      rw [htarget]
      ext p
      simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioi, mem_Ioo]
      tauto
    rw [hs]
  have hGc : ContinuousOn G (Icc 0 R ×ˢ Icc (-Real.pi) Real.pi) := by
    apply continuousOn_fst.mul (hf.comp _ _)
    · have hh : Continuous (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p) := by
        simp_rw [Complex.polarCoord_symm_apply]
        fun_prop
      exact hh.continuousOn
    · intro p hp
      simp only [mem_closedBall,dist_zero_right,Complex.norm_polarCoord_symm,
        abs_of_nonneg hp.1.1]
      exact hp.1.2
  have hGi : IntegrableOn G (Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi) :=
    (hGc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [heq,MeasureTheory.Measure.volume_eq_prod]
  rw [setIntegral_prod G (by simpa only [← MeasureTheory.Measure.volume_eq_prod] using hGi)]
  have hi (r : ℝ) : (∫ θ in Ioo (-Real.pi) Real.pi, G (r,θ)) =
      2 * Real.pi * (r * Real.circleAverage f 0 r) := by
    have ha := Real.circleAverage_eq_integral_add (f := f) (c := (0 : ℂ)) (R := r) (-Real.pi)
    have hpi : 2 * Real.pi + -Real.pi = Real.pi := by ring
    change Real.circleAverage f 0 r = (2 * Real.pi)⁻¹ •
      (∫ θ in (0:ℝ)..2*Real.pi, (fun t ↦ f (circleMap 0 r t)) (θ + -Real.pi)) at ha
    rw [intervalIntegral.integral_comp_add_right (fun t ↦ f (circleMap 0 r t)), zero_add, hpi] at ha
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      integral_Ioc_eq_integral_Ioo] at ha
    simp only [smul_eq_mul] at ha
    unfold G
    simp_rw [polar_symm_circle]
    rw [integral_const_mul]
    rw [ha]
    field_simp
  simp_rw [hi]
  rw [integral_const_mul,intervalIntegral.integral_of_le hR,integral_Ioc_eq_integral_Ioo]

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set MeasureTheory Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem norm_sq_mul_diskArea_le_integral {F : ℂ → E} {R : ℝ}
    (hR : 0 ≤ R) (hF : DifferentiableOn ℂ F (closedBall 0 R)) :
    Real.pi * R ^ 2 * ‖F 0‖ ^ 2 ≤ ∫ z in ball (0 : ℂ) R, ‖F z‖ ^ 2 := by
  rw [disk_integral_eq_polar (f := fun z ↦ ‖F z‖ ^ 2) hR (hF.continuousOn.norm.pow 2)]
  exact norm_sq_mul_diskArea_le_polarEnergy hR hF

end UniversalCoverSplitting

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace UniversalCoverSplitting

theorem lintegral_comp_positive_affine (F : ℂ → ℝ≥0∞) (U : Set ℂ)
    (p : ℂ) {a : ℝ} (ha : 0 < a) :
    (∫⁻ z in U, F (p + a • z)) = (ENNReal.ofReal (a^2))⁻¹ *
      ∫⁻ w in (fun z : ℂ ↦ p + a • z) '' U, F w := by
  let e : ℂ ≃ₜ ℂ := (Homeomorph.smulOfNeZero a ha.ne').trans (Homeomorph.addLeft p)
  have hm : Measure.map e (volume : Measure ℂ) = (ENNReal.ofReal (a^2))⁻¹ • volume := by
    change Measure.map ((fun z : ℂ ↦ p + z) ∘ (fun z : ℂ ↦ a • z)) volume = _
    rw [← Measure.map_map (measurable_const_add p) (measurable_const_smul a),
      Measure.map_addHaar_smul volume ha.ne',
      Measure.map_smul,
      map_add_left_eq_self,Complex.finrank_real_complex,abs_of_pos (by positivity : 0 < (a^2)⁻¹),
      ENNReal.ofReal_inv_of_pos (by positivity)]
  have hr := e.toMeasurableEquiv.restrict_map (volume : Measure ℂ) (e '' U)
  change (Measure.map e volume).restrict (e '' U) =
    Measure.map e (volume.restrict (e ⁻¹' (e '' U))) at hr
  rw [e.injective.preimage_image] at hr
  calc
    (∫⁻ z in U, F (p + a • z)) = ∫⁻ z, F z ∂Measure.map e (volume.restrict U) :=
      (lintegral_map_equiv F e.toMeasurableEquiv).symm
    _ = ∫⁻ z in e '' U, F z ∂Measure.map e volume := by rw [← hr]
    _ = (ENNReal.ofReal (a^2))⁻¹ * ∫⁻ z in e '' U, F z := by
      rw [hm,Measure.restrict_smul,lintegral_smul_measure,smul_eq_mul]
    _ = _ := rfl

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

theorem exists_brody_maximum {a : ℂ → ℝ} {c : ℂ} {R ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (ha : ContinuousOn a (closedBall c R))
    (han : ∀ z ∈ closedBall c R, 0 ≤ a z)
    (hw : ∃ z ∈ ball c R, ε ≤ (R - dist z c) * a z) :
    ∃ p ∈ ball c R, 0 < a p ∧ ε ≤ (R - dist p c) * a p ∧
      ∀ z ∈ ball p ((R - dist p c) / 2), z ∈ ball c R ∧ a z ≤ 2 * a p := by
  let w := fun z ↦ (R - dist z c) * a z
  have hc : ContinuousOn w (closedBall c R) :=
    (continuousOn_const.sub (continuous_id.dist continuous_const).continuousOn).mul ha
  obtain ⟨p,hp,hmax⟩ := (isCompact_closedBall c R).exists_isMaxOn
    (nonempty_closedBall.mpr hR.le) hc
  obtain ⟨z,hz,hwz⟩ := hw
  have hep : ε ≤ w p := hwz.trans (hmax (ball_subset_closedBall hz))
  have hap := han p hp
  have hdp : dist p c < R := by
    have hh : dist p c ≤ R := hp
    by_contra hn
    have he : dist p c = R := le_antisymm hh (le_of_not_gt hn)
    dsimp [w] at hep
    rw [he, sub_self, zero_mul] at hep
    linarith
  have hapos : 0 < a p := by
    by_contra hn
    have he : a p = 0 := le_antisymm (le_of_not_gt hn) hap
    dsimp [w] at hep
    rw [he, mul_zero] at hep
    linarith
  refine ⟨p,hdp,hapos,hep,?_⟩
  intro v hv
  have hvp : dist v p < (R - dist p c) / 2 := hv
  have htri := dist_triangle v p c
  have hvd : dist v c < R := by linarith
  refine ⟨hvd,?_⟩
  have ham := han v (ball_subset_closedBall hvd)
  have hvmax := hmax (ball_subset_closedBall hvd)
  dsimp [w] at hvmax
  have hdist : (R - dist p c) / 2 ≤ R - dist v c := by linarith
  have hm := mul_le_mul_of_nonneg_right hdist ham
  have hpdist : 0 < R - dist p c := sub_pos.mpr hdp
  nlinarith

theorem exists_brody_rescaling {a : ℂ → ℝ} {c : ℂ} {R ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (ha : ContinuousOn a (closedBall c R))
    (han : ∀ z ∈ closedBall c R, 0 ≤ a z)
    (hw : ∃ z ∈ ball c R, ε ≤ (R - dist z c) * a z) :
    ∃ p ∈ ball c R, 0 < a p ∧ a p / a p = 1 ∧
      ∀ ζ ∈ ball (0 : ℂ) (ε/4),
        p + ζ / (a p : ℂ) ∈ ball c R ∧ a (p + ζ / (a p : ℂ)) / a p ≤ 2 := by
  obtain ⟨p,hp,hap,hep,hbound⟩ := exists_brody_maximum hR hε ha han hw
  refine ⟨p,hp,hap,div_self hap.ne',?_⟩
  intro ζ hζ
  have hn : ‖ζ‖ < ε/4 := by simpa using hζ
  have hd : dist (p + ζ / (a p : ℂ)) p = ‖ζ‖ / a p := by
    rw [dist_eq_norm]
    simp [Complex.norm_real, abs_of_pos hap]
  have hnear : p + ζ / (a p : ℂ) ∈ ball p ((R-dist p c)/2) := by
    rw [mem_ball, hd, div_lt_iff₀ hap]
    nlinarith
  obtain ⟨hmem,hle⟩ := hbound _ hnear
  exact ⟨hmem,(div_le_iff₀ hap).mpr hle⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold

open Set Filter Topology
namespace UniversalCoverSplitting

theorem equicontinuous_compact_target_subsequence
    {T Y : Type*} [TopologicalSpace T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MetricSpace Y] [CompactSpace Y]
    (f : ℕ → C(T,Y)) (he : Equicontinuous (fun j x ↦ f j x)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ g : C(T,Y),
      Tendsto (f ∘ σ) atTop (𝓝 g) := by
  classical
  have he' : Equicontinuous (fun (i : range f) x ↦ i.val x) := by
    choose a ha using fun i : range f ↦ i.property
    have hh := he.comp a
    simpa only [Function.comp_def,ha] using hh
  have : T2Space (UniformOnFun T Y {K : Set T | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      ext x
      simp only [mem_sUnion, mem_ofPred_eq, mem_univ, iff_true]
      exact ⟨{x},isCompact_singleton,mem_singleton x⟩)
  have hc : IsCompact (closure (range f)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun (h : C(T,Y)) x ↦ h x) (𝔖 := {K : Set T | IsCompact K})
      (fun _ h ↦ h)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · exact fun K _ ↦ he'.equicontinuousOn K
    · exact fun _ _ _ _ ↦ ⟨univ,isCompact_univ,fun _ _ ↦ mem_univ _⟩
  obtain ⟨g,_,σ,hσ,hg⟩ := hc.tendsto_subseq (fun j ↦ subset_closure (mem_range_self j))
  exact ⟨σ,hσ,g,hg⟩

end UniversalCoverSplitting

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

namespace UniversalCoverSplitting

variable {T : Type*} [MetricSpace T] [MeasurableSpace T] [BorelSpace T]

theorem finite_large_atoms (μ : Measure T) [IsFiniteMeasure μ]
    {ε : ℝ≥0∞} (hε : 0 < ε) : Set.Finite {p : T | ε ≤ μ {p}} := by
  apply Measure.finite_const_le_meas_of_disjoint_iUnion μ hε
    (fun p ↦ measurableSet_singleton p)
  · intro p q hpq
    exact disjoint_singleton.mpr hpq
  · exact measure_ne_top μ _

theorem eventually_small_ball_of_small_atom {μ : ProbabilityMeasure T}
    {μs : ℕ → ProbabilityMeasure T} (hμ : Tendsto μs atTop (𝓝 μ))
    {p : T} {ε : ℝ≥0∞} (hp : (μ : Measure T) {p} < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ j in atTop,
      (μs j : Measure T) (closedBall p r) < ε := by
  obtain ⟨U,hU,hUo,hUm⟩ := ({p} : Set T).exists_isOpen_lt_of_lt ε hp
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds (hU (mem_singleton p)))
  refine ⟨r/2,by positivity,?_⟩
  apply eventually_lt_of_limsup_lt (hu := ⟨⊤, Filter.Eventually.of_forall (fun _ ↦ le_top)⟩)
  apply (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_closedBall).trans_lt
  exact (measure_mono ((closedBall_subset_ball (by linarith)).trans hrU)).trans_lt hUm

theorem bounded_measure_finite_concentration [CompactSpace T] [Nonempty T]
    (μs : ℕ → FiniteMeasure T) (C : ℝ≥0) (hC : ∀ j, (μs j).mass ≤ C)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ A : Set T, A.Finite ∧
      ∀ p ∉ A, ∃ r : ℝ, 0 < r ∧ ∀ᶠ j in atTop,
        (μs (σ j) : Measure T) (closedBall p r) < (ε : ℝ≥0∞) := by
  obtain ⟨ν,σ,hσ,hν⟩ := CompactSpace.tendsto_subseq (fun j ↦ (μs j).normalize)
  let δ : ℝ≥0 := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  let A : Set T := {p | (δ : ℝ≥0∞) ≤ (ν : Measure T) {p}}
  have hA : A.Finite := finite_large_atoms (ν : Measure T) (by exact_mod_cast hδ)
  refine ⟨σ,hσ,A,hA,?_⟩
  intro p hp
  have hp' : (ν : Measure T) {p} < (δ : ℝ≥0∞) := lt_of_not_ge hp
  obtain ⟨r,hr,he⟩ := eventually_small_ball_of_small_atom hν hp'
  refine ⟨r,hr,?_⟩
  filter_upwards [he] with j hj
  have hj' : (μs (σ j)).normalize (closedBall p r) < δ := by
    change ((μs (σ j)).normalize : Measure T) (closedBall p r) < (δ : ℝ≥0∞) at hj
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hj
    exact ENNReal.coe_lt_coe.mp hj
  have hb : μs (σ j) (closedBall p r) < ε := by
    rw [(μs (σ j)).self_eq_mass_mul_normalize]
    calc
      (μs (σ j)).mass * (μs (σ j)).normalize (closedBall p r)
          ≤ (C + 1) * (μs (σ j)).normalize (closedBall p r) := by
            gcongr
            exact (hC _).trans (le_add_of_nonneg_right zero_le_one)
      _ < (C + 1) * δ := mul_lt_mul_of_pos_left hj' (by positivity)
      _ = ε := by dsimp [δ]; field_simp
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact ENNReal.coe_lt_coe.mpr hb

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal
namespace UniversalCoverSplitting

theorem bounded_density_finite_concentration
    {K : Set ℂ} (hK : IsCompact K) (hKn : K.Nonempty)
    (w : ℕ → ℂ → ℝ≥0∞) (C : ℝ≥0)
    (hC : ∀ j, (∫⁻ z in K, w j z) ≤ (C : ℝ≥0∞))
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ A : Set ℂ, A.Finite ∧ A ⊆ K ∧
      ∀ p ∈ interior K \ A, ∃ r : ℝ, 0 < r ∧ closedBall p r ⊆ K ∧
        ∀ᶠ j in atTop, (∫⁻ z in ball p r, w (σ j) z) < (ε : ℝ≥0∞) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : Nonempty K := hKn.to_subtype
  let ν (j : ℕ) : Measure ℂ := (volume.withDensity (w j)).restrict K
  have hνall (j : ℕ) : ν j univ = ∫⁻ z in K, w j z := by
    simp only [ν,Measure.restrict_apply_univ,withDensity_apply _ hK.measurableSet]
  have hfinite (j : ℕ) : IsFiniteMeasure (ν j) :=
    ⟨by rw [hνall]; exact (hC j).trans_lt (ENNReal.coe_lt_top)⟩
  let μ (j : ℕ) : FiniteMeasure ℂ := ⟨ν j,hfinite j⟩
  let μK (j : ℕ) : FiniteMeasure K := (μ j).comap Subtype.val
  have hmass (j : ℕ) : (μK j).mass ≤ C := by
    apply ((μ j).mass_comap_le Subtype.val).trans
    change (ν j univ).toNNReal ≤ C
    rw [hνall]
    simpa using ENNReal.toNNReal_mono ENNReal.coe_ne_top (hC j)
  obtain ⟨σ,hσ,B,hB,hsmall⟩ := bounded_measure_finite_concentration μK C hmass ε hε
  refine ⟨σ,hσ,Subtype.val '' B,hB.image _,by rintro _ ⟨z,_,rfl⟩; exact z.property,?_⟩
  intro p hp
  have hpK : p ∈ K := interior_subset hp.1
  let pK : K := ⟨p,hpK⟩
  have hpB : pK ∉ B := fun h ↦ hp.2 ⟨pK,h,rfl⟩
  obtain ⟨r,hr,he⟩ := hsmall pK hpB
  obtain ⟨s,hs,hsK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (mem_interior_iff_mem_nhds.mp hp.1)
  let ρ := min r s
  have hρ : 0 < ρ := lt_min hr hs
  have hρK : closedBall p ρ ⊆ K := (closedBall_subset_closedBall (min_le_right r s)).trans hsK
  refine ⟨ρ,hρ,hρK,?_⟩
  filter_upwards [he] with j hj
  have hcomap : (μK (σ j) : Measure K) (closedBall pK r) =
      ν (σ j) (Subtype.val '' closedBall pK r) := by
    exact Measure.comap_apply Subtype.val Subtype.val_injective
      (fun s hs ↦ (MeasurableEmbedding.subtype_coe hK.measurableSet).measurableSet_image.mpr hs) _ measurableSet_closedBall
  have hball : ball p ρ ⊆ Subtype.val '' closedBall pK r := by
    intro z hz
    have hzK := hρK (ball_subset_closedBall hz)
    refine ⟨⟨z,hzK⟩,?_,rfl⟩
    change dist z p ≤ r
    exact hz.le.trans (min_le_left r s)
  have harea : ν (σ j) (ball p ρ) = ∫⁻ z in ball p ρ, w (σ j) z := by
    change ((volume.withDensity (w (σ j))).restrict K) (ball p ρ) = _
    rw [Measure.restrict_apply measurableSet_ball,
      inter_eq_left.mpr (ball_subset_closedBall.trans hρK),
      withDensity_apply _ measurableSet_ball]
  rw [hcomap] at hj
  exact (harea.symm.trans_le (measure_mono hball)).trans_lt hj

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal NNReal

open Set Metric Filter Topology MeasureTheory
open Complex
namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in

theorem holomorphic_circleAverage_eq {f : ℂ → E} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (hc : ContinuousOn f (closedBall 0 R \ ball 0 r))
    (hd : ∀ z ∈ ball 0 R \ closedBall 0 r, DifferentiableAt ℂ f z) :
    Real.circleAverage f 0 R = Real.circleAverage f 0 r := by
  rw [Real.circleAverage_eq_circleIntegral (ne_of_gt (hr.trans_le hrR)),
    Real.circleAverage_eq_circleIntegral hr.ne']
  congr 1
  exact Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
    hr hrR (s := ∅) countable_empty hc (fun z hz ↦ hd z hz.1)

omit [CompleteSpace E] in

theorem norm_circleAverage_le {f : ℂ → E} {r B : ℝ}
    (h : ∀ z ∈ sphere (0:ℂ) |r|, ‖f z‖ ≤ B) :
    ‖Real.circleAverage f 0 r‖ ≤ B := by
  rw [Real.circleAverage_def,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr Real.two_pi_pos)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 2 * Real.pi) (fun θ _ ↦ h _ (circleMap_mem_sphere' 0 r θ))
  have ht : |2 * Real.pi - 0| = 2 * Real.pi := by rw [sub_zero, abs_of_pos Real.two_pi_pos]
  rw [ht] at hb
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (B * (2 * Real.pi)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = B := by field_simp

theorem norm_sub_circleAverage_le {f : ℂ → E} {r B : ℝ} {v : E}
    (hf : ContinuousOn f (sphere (0:ℂ) |r|))
    (h : ∀ z ∈ sphere (0:ℂ) |r|, ‖f z - v‖ ≤ B) :
    ‖v - Real.circleAverage f 0 r‖ ≤ B := by
  have hb := norm_circleAverage_le h
  rw [Real.circleAverage_fun_sub hf.circleIntegrable' continuousOn_const.circleIntegrable',
    Real.circleAverage_const] at hb
  simpa only [norm_sub_rev] using hb

omit [CompleteSpace E] in

theorem holomorphic_circle_oscillation {f : ℂ → E} {r L : ℝ}
    (hr : 0 < r) (hL : 0 ≤ L)
    (hd : ∀ z ∈ sphere (0:ℂ) r, DifferentiableAt ℂ f z)
    (hb : ∀ z ∈ sphere (0:ℂ) r, ‖deriv f z‖ * r ≤ L) :
    ∀ z ∈ sphere (0:ℂ) r, ‖f z - f (r:ℂ)‖ ≤ 8 * L := by
  have hnorm (θ : ℝ) : ‖circleMap 0 r θ‖ = r := by
    simpa using circleMap_mem_sphere (0:ℂ) hr.le θ
  have hder (θ : ℝ) : HasDerivAt (fun t ↦ f (circleMap 0 r t))
      ((circleMap 0 r θ * Complex.I) • deriv f (circleMap 0 r θ)) θ := by
    exact (hd _ (circleMap_mem_sphere 0 hr.le θ)).hasDerivAt.scomp θ
      (hasDerivAt_circleMap 0 r θ)
  have hbound (θ : ℝ) : ‖(circleMap 0 r θ * Complex.I) • deriv f (circleMap 0 r θ)‖ ≤ L := by
    rw [norm_smul,norm_mul,Complex.norm_I,mul_one,hnorm,mul_comm]
    exact hb _ (circleMap_mem_sphere 0 hr.le θ)
  intro z hz
  have hz' : z ∈ circleMap 0 r '' Ioc 0 (2 * Real.pi) := by
    rw [image_circleMap_Ioc,abs_of_pos hr]
    exact hz
  obtain ⟨θ,hθ,rfl⟩ := hz'
  have hp := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t (_ : t ∈ Icc 0 (2 * Real.pi)) ↦ (hder t).hasDerivWithinAt)
    (fun t _ ↦ hbound t) θ ⟨hθ.1.le,hθ.2⟩
  have ht : L * (θ - 0) ≤ 8 * L := by
    have hh : θ ≤ 8 := hθ.2.trans (by linarith [Real.pi_lt_four])
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hh hL
  simpa [circleMap] using hp.trans ht

theorem holomorphic_annulus_oscillation {f : ℂ → E} {r R L : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hL : 0 ≤ L)
    (hc : ContinuousOn f (closedBall 0 R \ ball 0 r))
    (hd : ∀ z ∈ closedBall 0 R \ ball 0 r, DifferentiableAt ℂ f z)
    (hb : ∀ z ∈ closedBall 0 R \ ball 0 r, ‖deriv f z‖ * ‖z‖ ≤ L) :
    ∀ z ∈ sphere (0:ℂ) r, ‖f z - f (R:ℂ)‖ ≤ 24 * L := by
  have hs (s : ℝ) (hs : s ∈ Icc r R) : sphere (0:ℂ) s ⊆ closedBall 0 R \ ball 0 r := by
    intro z hz
    have hn : ‖z‖ = s := by simpa using hz
    simp only [Set.mem_sdiff,mem_closedBall,mem_ball,dist_zero_right,not_lt]
    exact ⟨hn ▸ hs.2, hn ▸ hs.1⟩
  have ho (s : ℝ) (hs' : s ∈ Icc r R) :
      ∀ z ∈ sphere (0:ℂ) s, ‖f z - f (s:ℂ)‖ ≤ 8 * L := by
    apply holomorphic_circle_oscillation (hr.trans_le hs'.1) hL
    · exact fun z hz ↦ hd z (hs s hs' hz)
    · intro z hz
      have hn : ‖z‖ = s := by simpa using hz
      simpa only [hn] using hb z (hs s hs' hz)
  have hm (s : ℝ) (hs' : s ∈ Icc r R) :
      ‖f (s:ℂ) - Real.circleAverage f 0 s‖ ≤ 8 * L := by
    apply norm_sub_circleAverage_le
    · rw [abs_of_pos (hr.trans_le hs'.1)]
      exact hc.mono (hs s hs')
    · rw [abs_of_pos (hr.trans_le hs'.1)]
      exact ho s hs'
  have havg := holomorphic_circleAverage_eq hr hrR hc
    (fun z hz ↦ hd z ⟨ball_subset_closedBall hz.1, fun hh ↦ hz.2 (ball_subset_closedBall hh)⟩)
  intro z hz
  have h₁ := ho r ⟨le_rfl,hrR⟩ z hz
  have h₂ := hm r ⟨le_rfl,hrR⟩
  have h₃ := hm R ⟨hrR,le_rfl⟩
  rw [havg] at h₃
  have ht₁ := dist_triangle (f z) (f (r:ℂ)) (Real.circleAverage f 0 r)
  have ht₂ := dist_triangle (f z) (Real.circleAverage f 0 r) (f (R:ℂ))
  simp only [dist_eq_norm] at ht₁ ht₂
  rw [norm_sub_rev (Real.circleAverage f 0 r) (f (R:ℂ))] at ht₂
  linarith

end UniversalCoverSplitting

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

namespace UniversalCoverSplitting

theorem compact_family_trapping {M T : Type*}
    [TopologicalSpace M] [TopologicalSpace T] [CompactSpace T]
    (H : ℝ → T → M) (hH : Continuous (Function.uncurry H))
    {K V : Set M} (hK : IsClosed K) (hV : IsOpen V) (hVK : V ⊆ K)
    {b : ℝ} (_hb : 0 ≤ b) (hzero : ∀ u, H 0 u ∈ K)
    (hcontrol : ∀ t ∈ Ico 0 b,
      (∀ s ∈ Icc 0 t, ∀ u, H s u ∈ K) → ∀ u, H t u ∈ V) :
    ∀ t ∈ Icc 0 b, ∀ u, H t u ∈ K := by
  let A : Set ℝ := {t | ∀ u, H t u ∈ K}
  have hA : IsClosed A := by
    have he : A = ⋂ u : T, (fun t ↦ H t u) ⁻¹' K := by ext t; simp [A]
    rw [he]
    exact isClosed_iInter (fun u ↦ hK.preimage (hH.comp (continuous_id.prodMk continuous_const)))
  have hall : Icc 0 b ⊆ A := by
    apply (hA.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hzero
    intro t ht hst
    have hc := hcontrol t ht (fun s hs u ↦ hst hs u)
    have he : ∀ᶠ s in 𝓝 t, ∀ u : T, H s u ∈ V := by
      have hh := isCompact_univ.eventually_forall_of_forall_eventually
        (x₀ := t) (K := (univ : Set T)) (P := fun s u ↦ H s u ∈ V)
        (fun u _ ↦ hH.continuousAt (hV.mem_nhds (hc u)))
      simpa only [mem_univ,forall_const] using hh
    exact nhdsWithin_le_nhds (he.mono (fun s hs u ↦ hVK (hs u)))
  exact fun t ht u ↦ hall ht u

end UniversalCoverSplitting

open Set Metric Filter Topology Complex
namespace UniversalCoverSplitting
variable {M E : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [ProperSpace E]

theorem punctured_chart_trapping (e : OpenPartialHomeomorph M E)
    {f : ℂ → M} {c : E} {R r L : ℝ}
    (_hR : 0 < R) (_hr : 0 < r) (hL : 0 ≤ L)
    (hchart : closedBall c R ⊆ e.target)
    (hc : ContinuousOn f {z | 0 < ‖z‖ ∧ ‖z‖ ≤ r})
    (houter : ∀ z ∈ sphere (0:ℂ) r, f z ∈ e.source ∧ e (f z) ∈ closedBall c R)
    (hmargin : dist (e (f (r:ℂ))) c + 24 * L < R)
    (hd : ∀ z, 0 < ‖z‖ → ‖z‖ ≤ r →
      f z ∈ e.symm '' closedBall c R → DifferentiableAt ℂ (e ∘ f) z)
    (hb : ∀ z, 0 < ‖z‖ → ‖z‖ ≤ r →
      f z ∈ e.symm '' closedBall c R → ‖deriv (e ∘ f) z‖ * ‖z‖ ≤ L) :
    ∀ z, 0 < ‖z‖ → ‖z‖ ≤ r →
      f z ∈ e.source ∧ e (f z) ∈ closedBall c R := by
  let K := e.symm '' closedBall c R
  let V := e.source ∩ e ⁻¹' ball c R
  have hK : IsClosed K :=
    ((isCompact_closedBall c R).image_of_continuousOn (e.continuousOn_symm.mono hchart)).isClosed
  have hV : IsOpen V := e.isOpen_inter_preimage isOpen_ball
  have hVK : V ⊆ K := by
    intro x hx
    exact ⟨e x,ball_subset_closedBall hx.2,e.left_inv hx.1⟩
  have hmem (x : M) (hx : x ∈ K) : x ∈ e.source ∧ e x ∈ closedBall c R := by
    obtain ⟨w,hw,rfl⟩ := hx
    exact ⟨e.map_target (hchart hw), by rwa [e.right_inv (hchart hw)]⟩
  have hring (a : ℝ) (ha : 0 < a) (har : a ≤ r) :
      ∀ z, a ≤ ‖z‖ → ‖z‖ ≤ r → f z ∈ K := by
    let T := sphere (0:ℂ) 1
    let : CompactSpace T := isCompact_iff_compactSpace.mp (isCompact_sphere (0:ℂ) 1)
    let ρ : ℝ → ℝ := fun t ↦ max a (min (r-t) r)
    have hρ : Continuous ρ := continuous_const.max ((continuous_const.sub continuous_id).min continuous_const)
    have hρlo (t : ℝ) : a ≤ ρ t := le_max_left _ _
    have hρhi (t : ℝ) : ρ t ≤ r := max_le har (min_le_right _ _)
    have hρeq (t : ℝ) (ht : t ∈ Icc 0 (r-a)) : ρ t = r-t := by
      dsimp [ρ]
      rw [min_eq_left (by linarith [ht.1]),max_eq_right (by linarith [ht.2])]
    let H : ℝ → T → M := fun t u ↦ f ((ρ t : ℂ) * (u:ℂ))
    have harg (t : ℝ) (u : T) : ‖(ρ t : ℂ) * (u:ℂ)‖ = ρ t := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (ha.trans_le (hρlo t)),
        norm_eq_of_mem_sphere,mul_one]
    have hH : Continuous (Function.uncurry H) := by
      apply hc.comp_continuous
      · exact ((Complex.continuous_ofReal.comp (hρ.comp continuous_fst)).mul
          (continuous_subtype_val.comp continuous_snd))
      · intro p
        exact ⟨by rw [harg]; exact ha.trans_le (hρlo p.1), by rw [harg]; exact hρhi p.1⟩
    have hzero : ∀ u, H 0 u ∈ K := by
      intro u
      have hn : ‖(ρ 0 : ℂ) * (u:ℂ)‖ = r := by rw [harg,hρeq 0 ⟨le_rfl,sub_nonneg.mpr har⟩,sub_zero]
      have ho := houter ((ρ 0:ℂ)*(u:ℂ)) (by simpa only [mem_sphere,dist_zero_right] using hn)
      exact ⟨e _,ho.2,e.left_inv ho.1⟩
    have hcontrol : ∀ t ∈ Ico 0 (r-a),
        (∀ s ∈ Icc 0 t, ∀ u, H s u ∈ K) → ∀ u, H t u ∈ V := by
      intro t ht hprev u
      have ht' : t ∈ Icc 0 (r-a) := ⟨ht.1,ht.2.le⟩
      have hrt : 0 < r-t := by linarith [ht.2]
      have hrtR : r-t ≤ r := by linarith [ht.1]
      have hann : ∀ z ∈ closedBall (0:ℂ) r \ ball 0 (r-t), f z ∈ K := by
        intro w hw
        have hwlo : r-t ≤ ‖w‖ := by simpa using hw.2
        have hwhi : ‖w‖ ≤ r := by simpa using hw.1
        have hwpos : 0 < ‖w‖ := hrt.trans_le hwlo
        let v : T := ⟨(‖w‖⁻¹ : ℂ) * w, by
          simp [T,inv_mul_cancel₀ hwpos.ne']⟩
        have hs : r-‖w‖ ∈ Icc 0 t := ⟨by linarith,by linarith⟩
        have hp := hprev (r-‖w‖) hs v
        have hv : (ρ (r-‖w‖) : ℂ) * (v:ℂ) = w := by
          rw [hρeq _ ⟨hs.1,hs.2.trans ht.2.le⟩]
          dsimp [v]
          simp only [sub_sub_cancel]
          rw [← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hwpos.ne'),one_mul]
        simpa only [H,hv] using hp
      have hfc : ContinuousOn (e ∘ f) (closedBall 0 r \ ball 0 (r-t)) := by
        apply e.continuousOn.comp (hc.mono _) (fun w hw ↦ (hmem _ (hann w hw)).1)
        intro w hw
        have hlo : r-t ≤ ‖w‖ := by simpa using hw.2
        exact ⟨hrt.trans_le hlo,by simpa using hw.1⟩
      have ho := holomorphic_annulus_oscillation hrt hrtR hL hfc
        (fun w hw ↦ hd w (hrt.trans_le (by simpa using hw.2)) (by simpa using hw.1) (hann w hw))
        (fun w hw ↦ hb w (hrt.trans_le (by simpa using hw.2)) (by simpa using hw.1) (hann w hw))
        ((ρ t:ℂ)*(u:ℂ)) (by simp only [mem_sphere,dist_zero_right]; rw [harg,hρeq t ht'])
      have hm := hmem _ (hprev t ⟨ht.1,le_rfl⟩ u)
      refine ⟨hm.1,?_⟩
      change dist (e (H t u)) c < R
      have htri := dist_triangle (e (H t u)) (e (f (r:ℂ))) c
      have hdist : dist (e (H t u)) (e (f (r:ℂ))) ≤ 24*L := by
        simpa only [dist_eq_norm,Function.comp_apply,H] using ho
      linarith
    intro z hzlo hzhi
    let u : T := ⟨(‖z‖⁻¹:ℂ)*z, by
      have hzpos := ha.trans_le hzlo
      simp [T,inv_mul_cancel₀ hzpos.ne']⟩
    have hs : r-‖z‖ ∈ Icc 0 (r-a) := ⟨by linarith,by linarith⟩
    have hg := compact_family_trapping H hH hK hV hVK (sub_nonneg.mpr har) hzero hcontrol _ hs u
    have hv : (ρ (r-‖z‖):ℂ)*(u:ℂ) = z := by
      rw [hρeq _ hs]
      dsimp [u]
      simp only [sub_sub_cancel]
      rw [← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (ha.trans_le hzlo).ne'),one_mul]
    simpa only [H,hv] using hg
  intro z hz hrz
  exact hmem _ (hring ‖z‖ hz hrz z le_rfl hrz)

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
namespace UniversalCoverSplitting

theorem finite_density_small_ball {w : ℂ → ℝ≥0∞} {Ω : Set ℂ}
    (hfin : (∫⁻ z in Ω, w z) ≠ (⊤ : ℝ≥0∞)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ D : Set ℂ, D ⊆ ball 0 δ → D ⊆ Ω →
      (∫⁻ z in D, w z) < ε := by
  obtain ⟨b,hb,hsmall⟩ := exists_pos_setLIntegral_lt_of_measure_lt hfin hε.ne'
  have hv : Tendsto (fun t : ℝ ↦ volume (ball (0:ℂ) t)) (𝓝 0) (𝓝 0) := by
    have hh := ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2)
      (ENNReal.continuous_ofReal.tendsto (0:ℝ))) (Or.inr (ENNReal.coe_ne_top : (NNReal.pi : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)))
    simpa only [Complex.volume_ball,ENNReal.ofReal_zero,zero_pow (by norm_num : 2 ≠ 0),zero_mul] using hh
  obtain ⟨a,ha,haV⟩ := Metric.nhds_basis_ball.mem_iff.mp (hv.eventually_lt_const hb)
  let δ := a/2
  have hδ : 0 < δ := half_pos ha
  have hm : volume (ball (0:ℂ) δ) < b := haV (by simpa [δ,Real.dist_eq,abs_of_pos ha] using (half_lt_self ha))
  refine ⟨δ,hδ,?_⟩
  intro D hD hDΩ
  have hh := hsmall D ((Measure.restrict_le_self _).trans_lt ((measure_mono hD).trans_lt hm))
  rwa [Measure.restrict_restrict_of_subset hDΩ] at hh

end UniversalCoverSplitting

open Set Metric Filter Topology Complex
namespace UniversalCoverSplitting
variable {M E : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [ProperSpace E]

theorem chart_trapping_on_circle (e : OpenPartialHomeomorph M E)
    {f : ℂ → M} {c : E} {R r L : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hL : 0 ≤ L)
    (he : closedBall c R ⊆ e.target)
    (hc : ContinuousOn f (sphere (0:ℂ) r))
    (hzero : f (r:ℂ) ∈ e.source ∧ dist (e (f (r:ℂ))) c < R - 8*L)
    (hd : ∀ z ∈ sphere (0:ℂ) r, f z ∈ e.symm '' closedBall c R →
      DifferentiableAt ℂ (e ∘ f) z)
    (hb : ∀ z ∈ sphere (0:ℂ) r, f z ∈ e.symm '' closedBall c R →
      ‖deriv (e ∘ f) z‖ * r ≤ L) :
    ∀ z ∈ sphere (0:ℂ) r, f z ∈ e.source ∧ e (f z) ∈ ball c R := by
  have hγ : ContinuousOn (fun θ : ℝ ↦ f (circleMap 0 r θ)) (Icc 0 (2*Real.pi)) :=
    hc.comp (continuous_circleMap 0 r).continuousOn (fun θ _ ↦ circleMap_mem_sphere 0 hr.le θ)
  have hinit : f (circleMap 0 r 0) ∈ e.source ∧
      dist (e (f (circleMap 0 r 0))) c < R - L * (2*Real.pi) := by
    simpa [circleMap] using And.intro hzero.1 (hzero.2.trans_le (by
      have ht : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
      nlinarith))
  have ht := chart_trapping_on_interval e hR hL Real.two_pi_pos.le he hγ hinit
    (fun θ _ hk ↦ ?_)
  · intro z hz
    have hz' : z ∈ circleMap 0 r '' Ioc 0 (2*Real.pi) := by
      rw [image_circleMap_Ioc,abs_of_pos hr]
      exact hz
    obtain ⟨θ,hθ,rfl⟩ := hz'
    exact ht θ ⟨hθ.1.le,hθ.2⟩
  have hm := circleMap_mem_sphere (0:ℂ) hr.le θ
  refine ⟨(circleMap 0 r θ * I) • deriv (e ∘ f) (circleMap 0 r θ),?_,?_⟩
  · exact ((hd _ hm hk).hasDerivAt.scomp θ (hasDerivAt_circleMap 0 r θ)).hasDerivWithinAt
  · rw [norm_smul,norm_mul,norm_I,mul_one]
    have hn : ‖circleMap 0 r θ‖ = r := by simpa using hm
    rw [hn,mul_comm]
    exact hb _ hm hk

end UniversalCoverSplitting

open Set Metric Filter Topology Complex
open scoped Manifold ENNReal

open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.PathDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped Interval
open Set MeasureTheory
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set
open scoped Manifold

open Set Metric Filter Topology Asymptotics

open Set Metric Filter Topology Asymptotics

open Set Metric Filter Topology

namespace UniversalCoverSplitting
variable {𝕜 E F T : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace T] [CompactSpace T]

@[simp] theorem pathLinearApplyL_apply (A : C(T,E →L[𝕜] F)) :
    pathLinearApplyL A = pathLinearApply A := rfl

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

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ}

theorem diagonal_compact_tube {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {K : Set ℂ} (hK : IsCompact K) (hKU : ∀ z ∈ K, (z,z) ∈ U) (c : ℂ × ℂ) :
    ∃ e : ℝ, 0 < e ∧ ∀ w ∈ ball (0:ℂ) e, ∀ z ∈ K,
      (z+c.1*w,z+c.2*w) ∈ U := by
  let T : ℂ × ℂ → ℂ × ℂ := fun q ↦ (q.2+c.1*q.1,q.2+c.2*q.1)
  have hT : Continuous T := by fun_prop
  have hsub : ({0} : Set ℂ) ×ˢ K ⊆ T ⁻¹' U := by
    rintro ⟨w,z⟩ ⟨hw,hz⟩
    have hw0 : w = 0 := mem_singleton_iff.mp hw
    subst w
    simpa [T] using hKU z hz
  obtain ⟨V,W,hVo,hWo,h0,hK',hVW⟩ := generalized_tube_lemma isCompact_singleton hK
    (hU.preimage hT) hsub
  obtain ⟨e,he,heV⟩ := Metric.mem_nhds_iff.mp (hVo.mem_nhds (h0 (mem_singleton 0)))
  refine ⟨e,he,?_⟩
  intro w hw z hz
  exact hVW (show (w,z) ∈ V ×ˢ W from ⟨heV hw,hK' hz⟩)

end UniversalCoverSplitting

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

section AlternatingBilinear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def alternatingBilinear (B : E →L[ℝ] E →L[ℝ] ℝ) : E [⋀^Fin 2]→L[ℝ] ℝ :=
  (1/2 : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin
    (((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap).comp B)

theorem alternatingBilinear_apply (B : E →L[ℝ] E →L[ℝ] ℝ) (v : Fin 2 → E) :
    alternatingBilinear B v = (B (v 0) (v 1) - B (v 1) (v 0)) / 2 := by
  simp [alternatingBilinear, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_two, Fin.removeNth, Fin.succAbove, div_eq_mul_inv]
  ring

theorem alternatingBilinear_contDiff {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {B : D → E →L[ℝ] E →L[ℝ] ℝ} {U : Set D} {k : WithTop ℕ∞}
    (hB : ContDiffOn ℝ k B U) : ContDiffOn ℝ k (fun x ↦ alternatingBilinear (B x)) U := by
  exact ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).contDiff.comp_contDiffOn
    (contDiffOn_const.clm_comp hB)).const_smul (1/2 : ℝ)

end AlternatingBilinear

end UniversalCoverSplitting

open Set Filter Topology Metric Complex
open scoped Real

namespace UniversalCoverSplitting

section CauchyParameters
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in

theorem continuousOn_cauchy_partial {T S : Set (ℂ × ℂ)} {f : ℂ × ℂ → F}
    (hf : ContinuousOn f T) {r : ℝ} (hr : 0 < r)
    (hmap : ∀ z ∈ S, ∀ θ : ℝ, (circleMap z.1 r θ, z.2) ∈ T) :
    ContinuousOn (fun z : ℂ × ℂ ↦ cderiv r (fun w ↦ f (w, z.2)) z.1) S := by
  rw [continuousOn_iff_continuous_domRestrict]
  let G : S → ℝ → F := fun z θ ↦
    (circleMap 0 r θ * I) • (((circleMap 0 r θ) ^ 2)⁻¹ •
      f (circleMap z.val.1 r θ, z.val.2))
  have hG : Continuous G.uncurry := by
    have hshift : Continuous (fun p : S × ℝ ↦
        (circleMap p.1.val.1 r p.2, p.1.val.2)) := by
      unfold circleMap
      fun_prop
    have hm : MapsTo (fun p : S × ℝ ↦
        (circleMap p.1.val.1 r p.2, p.1.val.2)) univ T :=
      fun p _ ↦ hmap p.1.val p.1.property p.2
    have hcomp := continuousOn_univ.mp (hf.comp hshift.continuousOn hm)
    have hne (p : S × ℝ) : circleMap 0 r p.2 ≠ 0 := by
      exact circleMap_ne_mem_ball (mem_ball_self hr) p.2
    dsimp [G, Function.uncurry]
    apply Continuous.smul
    · fun_prop
    · exact (((continuous_circleMap 0 r).comp continuous_snd).pow 2).inv₀
        (fun p ↦ pow_ne_zero 2 (hne p)) |>.smul hcomp
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) hG (a₀ := 0) (b₀ := 2 * Real.pi)
  have hc := hi.const_smul ((2 * Real.pi * I : ℂ)⁻¹)
  change Continuous (fun z : S ↦ cderiv r (fun w ↦ f (w, z.val.2)) z.val.1)
  convert! hc using 1
  ext z
  simp only [cderiv, circleIntegral, deriv_circleMap, G, circleMap, zero_add,
    add_sub_cancel_left, Pi.smul_apply]

theorem continuousAt_partial_deriv {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f : ℂ × ℂ → F} (hf : ContinuousOn f (U ×ˢ V))
    (hd : ∀ y ∈ V, DifferentiableOn ℂ (fun x ↦ f (x, y)) U)
    {p : ℂ × ℂ} (hp : p ∈ U ×ˢ V) :
    ContinuousAt (fun z : ℂ × ℂ ↦ deriv (fun w ↦ f (w, z.2)) z.1) p := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp.1)
  let S := Metric.ball p.1 (r / 2) ×ˢ V
  have hS : S ∈ 𝓝 p := prod_mem_nhds (ball_mem_nhds _ (by linarith)) (hV.mem_nhds hp.2)
  have hball (z : ℂ × ℂ) (hz : z ∈ S) : closedBall z.1 (r / 2) ⊆ U := by
    apply Subset.trans (Metric.closedBall_subset_ball' (y := p.1) ?_) hrU
    have : dist z.1 p.1 < r / 2 := hz.1
    linarith
  have hc := continuousOn_cauchy_partial (S := S) hf (by linarith : 0 < r / 2)
    (fun z hz θ ↦ ⟨hball z hz (circleMap_mem_closedBall _ (by linarith) _), hz.2⟩)
  have heq : (fun z : ℂ × ℂ ↦ cderiv (r / 2) (fun w ↦ f (w, z.2)) z.1)
      =ᶠ[𝓝 p] (fun z : ℂ × ℂ ↦ deriv (fun w ↦ f (w, z.2)) z.1) := by
    filter_upwards [hS] with z hz
    exact cderiv_eq_deriv hU (hd z.2 hz.2) (by linarith) (hball z hz)
  exact (hc.continuousAt hS).congr heq

def totalPartialDeriv (f : ℂ × ℂ → F) (p : ℂ × ℂ) : (ℂ × ℂ) →L[ℂ] F :=
  (ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) F (ContinuousLinearMap.fst ℂ ℂ ℂ))
    (deriv (fun w ↦ f (w, p.2)) p.1) +
  (ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) F (ContinuousLinearMap.snd ℂ ℂ ℂ))
    (deriv (fun w ↦ f (p.1, w)) p.2)

theorem hasStrictFDerivAt_of_continuousOn_of_separately
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f : ℂ × ℂ → F} (hf : ContinuousOn f (U ×ˢ V))
    (h₁ : ∀ y ∈ V, DifferentiableOn ℂ (fun x ↦ f (x, y)) U)
    (h₂ : ∀ x ∈ U, DifferentiableOn ℂ (fun y ↦ f (x, y)) V)
    {p : ℂ × ℂ} (hp : p ∈ U ×ˢ V) :
    HasStrictFDerivAt f (totalPartialDeriv f p) p := by
  let L : F →L[ℂ] (ℂ →L[ℂ] F) := ContinuousLinearMap.smulRightL ℂ ℂ F 1
  let D₁ : ℂ → ℂ → ℂ →L[ℂ] F := fun x y ↦ L (deriv (fun w ↦ f (w, y)) x)
  let D₂ : ℂ → ℂ → ℂ →L[ℂ] F := fun x y ↦ L (deriv (fun w ↦ f (x, w)) y)
  have hd₁ : ∀ᶠ z in 𝓝 p, HasFDerivAt (fun x ↦ f (x, z.2)) (D₁ z.1 z.2) z.1 := by
    filter_upwards [(hU.prod hV).mem_nhds hp] with z hz
    exact ((h₁ z.2 hz.2).differentiableAt (hU.mem_nhds hz.1)).hasDerivAt.hasFDerivAt
  have hd₂ : ∀ᶠ z in 𝓝 p, HasFDerivAt (fun y ↦ f (z.1, y)) (D₂ z.1 z.2) z.2 := by
    filter_upwards [(hU.prod hV).mem_nhds hp] with z hz
    exact ((h₂ z.1 hz.1).differentiableAt (hV.mem_nhds hz.2)).hasDerivAt.hasFDerivAt
  have hc₁ : ContinuousAt D₁.uncurry p :=
    L.continuous.continuousAt.comp (continuousAt_partial_deriv hU hV hf h₁ hp)
  have hfs : ContinuousOn (fun z : ℂ × ℂ ↦ f z.swap) (V ×ˢ U) :=
    hf.comp continuous_swap.continuousOn (fun z hz ↦ ⟨hz.2, hz.1⟩)
  have hds : ∀ y ∈ U, DifferentiableOn ℂ (fun x ↦ f (y, x)) V := h₂
  have hcs := continuousAt_partial_deriv hV hU hfs hds (p := p.swap) ⟨hp.2, hp.1⟩
  have hc₂ : ContinuousAt D₂.uncurry p := by
    exact L.continuous.continuousAt.comp (hcs.comp continuous_swap.continuousAt)
  have hs := (hasStrictFDerivAt_uncurry_coprod (𝕜 := ℂ) (f := fun x y ↦ f (x, y))
    (f₁ := D₁) (f₂ := D₂) (u := p) hd₁ hd₂ hc₁ hc₂)
  convert! hs using 1

theorem differentiableOn_of_continuousOn_of_separately
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f : ℂ × ℂ → F} (hf : ContinuousOn f (U ×ˢ V))
    (h₁ : ∀ y ∈ V, DifferentiableOn ℂ (fun x ↦ f (x, y)) U)
    (h₂ : ∀ x ∈ U, DifferentiableOn ℂ (fun y ↦ f (x, y)) V) :
    DifferentiableOn ℂ f (U ×ˢ V) := by
  intro p hp
  exact (hasStrictFDerivAt_of_continuousOn_of_separately hU hV hf h₁ h₂ hp
    ).hasFDerivAt.differentiableAt.differentiableWithinAt

end CauchyParameters
end UniversalCoverSplitting

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

namespace UniversalCoverSplitting
section CauchyParameters
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

open MeasureTheory

omit [CompleteSpace F] in

theorem differentiableAt_intervalIntegral_of_continuous_deriv
    {U : Set ℂ} (hU : IsOpen U) {G D : ℂ → ℝ → F}
    (hG : ContinuousOn G.uncurry (U ×ˢ univ))
    (hD : ContinuousOn D.uncurry (U ×ˢ univ))
    (hd : ∀ w ∈ U, ∀ t, HasDerivAt (fun z ↦ G z t) (D w t) w)
    {w : ℂ} (hw : w ∈ U) (a b : ℝ) :
    DifferentiableAt ℂ (fun z ↦ ∫ t in a..b, G z t) w := by
  obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hw)
  have hGc (z : ℂ) (hz : z ∈ U) : Continuous (G z) := by
    exact continuousOn_univ.mp (hG.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ ↦ ⟨hz,mem_univ _⟩))
  have hDc (z : ℂ) (hz : z ∈ U) : Continuous (D z) := by
    exact continuousOn_univ.mp (hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ ↦ ⟨hz,mem_univ _⟩))
  obtain ⟨C,hC⟩ := ((isCompact_closedBall w r).prod (isCompact_uIcc : IsCompact (uIcc a b))).exists_bound_of_continuousOn
    (hD.mono (fun p hp ↦ ⟨hrU hp.1,mem_univ _⟩))
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := G) (F' := D) (bound := fun _ ↦ C)
    (Metric.closedBall_mem_nhds w hr)
    (by filter_upwards [hU.mem_nhds hw] with z hz
        exact (hGc z hz).aestronglyMeasurable)
    ((hGc w hw).intervalIntegrable a b)
    (hDc w hw).aestronglyMeasurable
    (by filter_upwards with t ht z hz
        exact hC (z,t) ⟨hz,uIoc_subset_uIcc ht⟩)
    (intervalIntegrable_const)
    (by filter_upwards with t _ z hz; exact hd z (hrU hz) t)).2.differentiableAt

theorem differentiableOn_weighted_curveIntegral
    {f : ℂ × ℂ → F} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hf : DifferentiableOn ℂ f (U ×ˢ V))
    {γ K : ℝ → ℂ} (hγ : Continuous γ) (hK : Continuous K)
    (hm : ∀ t, γ t ∈ V) (a b : ℝ) :
    DifferentiableOn ℂ (fun w ↦ ∫ t in a..b, K t • f (w,γ t)) U := by
  let G : ℂ → ℝ → F := fun w t ↦ K t • f (w,γ t)
  let D : ℂ → ℝ → F := fun w t ↦ K t • deriv (fun z ↦ f (z,γ t)) w
  have hmap : MapsTo (fun p : ℂ × ℝ ↦ (p.1,γ p.2)) (U ×ˢ univ) (U ×ˢ V) :=
    fun p hp ↦ ⟨hp.1,hm p.2⟩
  have hcmap : Continuous (fun p : ℂ × ℝ ↦ (p.1,γ p.2)) :=
    continuous_fst.prodMk (hγ.comp continuous_snd)
  have hG : ContinuousOn G.uncurry (U ×ˢ univ) :=
    ((hK.comp continuous_snd).continuousOn).smul (hf.continuousOn.comp hcmap.continuousOn hmap)
  have hslice : ∀ y ∈ V, DifferentiableOn ℂ (fun x ↦ f (x,y)) U := by
    intro y hy
    exact hf.comp ((differentiable_id.prodMk (differentiable_const _)).differentiableOn)
      (fun z hz ↦ ⟨hz,hy⟩)
  have hD : ContinuousOn D.uncurry (U ×ˢ univ) := by
    apply ((hK.comp continuous_snd).continuousOn).smul
    have hpart : ContinuousOn (fun p : ℂ × ℂ ↦ deriv (fun z ↦ f (z,p.2)) p.1) (U ×ˢ V) :=
      fun p hp ↦ (continuousAt_partial_deriv hU hV hf.continuousOn hslice hp).continuousWithinAt
    exact hpart.comp hcmap.continuousOn hmap
  have hdG : ∀ w ∈ U, ∀ t, HasDerivAt (fun z ↦ G z t) (D w t) w := by
    intro w hw t
    exact ((hslice _ (hm t)).differentiableAt (hU.mem_nhds hw)).hasDerivAt.const_smul (K t)
  intro w hw
  exact (differentiableAt_intervalIntegral_of_continuous_deriv hU hG hD hdG hw a b).differentiableWithinAt

theorem differentiableOn_partial_deriv
    {f : ℂ × ℂ → F} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hf : DifferentiableOn ℂ f (U ×ˢ V)) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ ↦ deriv (fun z ↦ f (z,p.2)) p.1) (U ×ˢ V) := by
  have hslice : ∀ y ∈ V, DifferentiableOn ℂ (fun x ↦ f (x,y)) U := by
    intro y hy
    exact hf.comp ((differentiable_id.prodMk (differentiable_const _)).differentiableOn)
      (fun z hz ↦ ⟨hz,hy⟩)
  apply differentiableOn_of_continuousOn_of_separately hU hV
    (fun p hp ↦ (continuousAt_partial_deriv hU hV hf.continuousOn hslice hp).continuousWithinAt)
  · intro y hy
    exact (hslice y hy).deriv hU
  · intro x hx
    obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
    let K : ℝ → ℂ := fun t ↦ circleMap 0 r t * I * ((circleMap x r t - x) ^ 2)⁻¹
    have hK : Continuous K := by
      apply Continuous.mul (by fun_prop)
      apply Continuous.inv₀ (by fun_prop)
      intro t
      exact pow_ne_zero 2 (sub_ne_zero.mpr (circleMap_ne_center hr.ne'))
    have hfs : DifferentiableOn ℂ (fun p : ℂ × ℂ ↦ f p.swap) (V ×ˢ U) :=
      hf.comp ((differentiable_snd.prodMk differentiable_fst).differentiableOn)
        (fun p hp ↦ ⟨hp.2,hp.1⟩)
    have hi := differentiableOn_weighted_curveIntegral hV hU hfs
      (continuous_circleMap x r) hK (fun t ↦ hrU (circleMap_mem_closedBall _ hr.le t))
        0 (2 * Real.pi)
    have hci : DifferentiableOn ℂ (fun y ↦ cderiv r (fun z ↦ f (z,y)) x) V := by
      have heq : (fun y ↦ cderiv r (fun z ↦ f (z,y)) x) =
          fun y ↦ ((2 * Real.pi * I : ℂ)⁻¹) •
            ∫ t in (0:ℝ)..2 * Real.pi, K t • f (circleMap x r t,y) := by
        funext y
        simp only [cderiv,circleIntegral,deriv_circleMap,K,smul_smul]
      rw [heq]
      exact hi.const_smul _
    exact hci.congr (fun y hy ↦ (cderiv_eq_deriv hU (hslice y hy) hr hrU).symm)

theorem differentiableOn_partial_deriv_open
    {f : ℂ × ℂ → F} {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ ↦ deriv (fun z ↦ f (z,p.2)) p.1) Ω := by
  intro p hp
  obtain ⟨r,hr,hrs⟩ := Metric.isOpen_iff.mp hΩ p hp
  have hsub : Metric.ball p.1 r ×ˢ Metric.ball p.2 r ⊆ Ω := by
    rw [ball_prod_same]
    exact hrs
  have hd := differentiableOn_partial_deriv Metric.isOpen_ball Metric.isOpen_ball (hf.mono hsub)
  exact (hd.differentiableAt (prod_mem_nhds (Metric.ball_mem_nhds _ hr)
    (Metric.ball_mem_nhds _ hr))).differentiableWithinAt

theorem differentiableOn_fderiv_apply_open
    {f : ℂ × ℂ → F} {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (v : ℂ × ℂ) :
    DifferentiableOn ℂ (fun p ↦ fderiv ℂ f p v) Ω := by
  have h₁ : DifferentiableOn ℂ (fun p ↦ fderiv ℂ f p (1,0)) Ω := by
    apply (differentiableOn_partial_deriv_open hΩ hf).congr
    intro p hp
    exact ((hf.differentiableAt (hΩ.mem_nhds hp)).hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv.symm
  have hs : DifferentiableOn ℂ (fun p : ℂ × ℂ ↦ f p.swap) (Prod.swap ⁻¹' Ω) :=
    hf.comp ((differentiable_snd.prodMk differentiable_fst).differentiableOn)
      (mapsTo_preimage _ _)
  have h₂ : DifferentiableOn ℂ (fun p ↦ fderiv ℂ f p (0,1)) Ω := by
    have h := (differentiableOn_partial_deriv_open
      (hΩ.preimage continuous_swap) hs).comp
      ((differentiable_snd.prodMk differentiable_fst).differentiableOn)
      (fun p hp ↦ by simpa using hp)
    apply h.congr
    intro p hp
    exact ((hf.differentiableAt (hΩ.mem_nhds hp)).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv.symm
  apply ((h₁.const_smul v.1).add (h₂.const_smul v.2)).congr
  intro p hp
  change fderiv ℂ f p v = v.1 • fderiv ℂ f p (1,0) + v.2 • fderiv ℂ f p (0,1)
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  ext <;> simp

end CauchyParameters
end UniversalCoverSplitting

open scoped ContDiff
open Set
namespace UniversalCoverSplitting
section TwoDimSmooth
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem holomorphic_twoDim_contDiffOn_nat {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω) (k : ℕ)
    {f : ℂ × ℂ → F} (hf : DifferentiableOn ℂ f Ω) : ContDiffOn ℂ k f Ω := by
  induction k generalizing f with
  | zero => exact contDiffOn_zero.mpr hf.continuousOn
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_apply hΩ.uniqueDiffOn]
    refine ⟨hf, by simp, fun v ↦ ?_⟩
    apply (ih (differentiableOn_fderiv_apply_open hΩ hf v)).congr
    intro z hz
    rw [fderivWithin_of_isOpen hΩ hz]

theorem holomorphic_twoDim_contDiffOn {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {f : ℂ × ℂ → F} (hf : DifferentiableOn ℂ f Ω) : ContDiffOn ℂ ∞ f Ω :=
  contDiffOn_infty.mpr (fun k ↦ holomorphic_twoDim_contDiffOn_nat hΩ k hf)

end TwoDimSmooth
end UniversalCoverSplitting

open scoped Manifold ContDiff
open Set Filter Topology

open scoped Manifold ContDiff
open Set Filter Topology

open scoped Manifold ContDiff
open Set Filter Topology

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

namespace UniversalCoverSplitting

def alternatingEvalCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (v : Fin k → E) : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ where
  toFun B := B v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const v

abbrev Real3 := Fin 3 → ℝ

def realBasis3 (i : Fin 3) : Real3 := Pi.single i 1

def stokesCoefficient (B : Real3 → Real3 [⋀^Fin 2]→L[ℝ] ℝ) (i : Fin 3) : Real3 → ℝ :=
  fun x ↦ (-1) ^ i.val * B x (i.removeNth realBasis3)

def stokesCoefficientDeriv (B : Real3 → Real3 [⋀^Fin 2]→L[ℝ] ℝ) (i : Fin 3)
    (x : Real3) : Real3 →L[ℝ] ℝ :=
  (-1 : ℝ)^i.val • fderiv ℝ (fun y ↦ B y (i.removeNth realBasis3)) x

theorem stokesCoefficient_hasFDerivAt {B : Real3 → Real3 [⋀^Fin 2]→L[ℝ] ℝ}
    {x : Real3} (hB : DifferentiableAt ℝ B x) (i : Fin 3) :
    HasFDerivAt (stokesCoefficient B i) (stokesCoefficientDeriv B i x) x := by
  have h := (alternatingEvalCLM (i.removeNth realBasis3)).differentiableAt.comp x hB
  exact h.hasFDerivAt.const_mul ((-1 : ℝ)^i.val)

theorem sum_stokesCoefficientDeriv_eq_extDeriv {B : Real3 → Real3 [⋀^Fin 2]→L[ℝ] ℝ}
    {x : Real3} (hB : DifferentiableAt ℝ B x) :
    (∑ i : Fin 3, stokesCoefficientDeriv B i x (realBasis3 i)) =
      extDeriv B x realBasis3 := by
  rw [extDeriv_apply hB]
  simp [stokesCoefficientDeriv, zsmul_eq_mul]

theorem sum_faces_eq_zero_of_closed_twoForm
    {U : Set Real3} (hU : IsOpen U)
    {B : Real3 → Real3 [⋀^Fin 2]→L[ℝ] ℝ}
    (hB : ContDiffOn ℝ 1 B U) (hc : ∀ x ∈ U, extDeriv B x = 0)
    (a b : Real3) (hab : a ≤ b) (hbox : Icc a b ⊆ U) :
    (∑ i : Fin 3,
      ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          stokesCoefficient B i (i.insertNth (b i) y)) -
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          stokesCoefficient B i (i.insertNth (a i) y))) = 0 := by
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ B x := fun x hx ↦
    (hB.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)
  have hzero : ∀ x ∈ Icc a b,
      (∑ i : Fin 3, stokesCoefficientDeriv B i x (Pi.single i 1)) = 0 := by
    intro x hx
    change (∑ i : Fin 3, stokesCoefficientDeriv B i x (realBasis3 i)) = 0
    rw [sum_stokesCoefficientDeriv_eq_extDeriv (hdiff x (hbox hx)), hc x (hbox hx)]
    rfl
  have hi : IntegrableOn (fun x ↦ ∑ i : Fin 3,
      stokesCoefficientDeriv B i x (Pi.single i 1)) (Icc a b) := by
    refine (integrableOn_zero : IntegrableOn (fun _ : Real3 ↦ (0 : ℝ)) (Icc a b)).congr_fun ?_ measurableSet_Icc
    · intro x hx
      exact (hzero x hx).symm
  have hst := integral_divergence_of_hasFDerivAt_off_countable' a b hab
    (stokesCoefficient B) (stokesCoefficientDeriv B) ∅ Set.countable_empty
    (fun i ↦ (((alternatingEvalCLM (i.removeNth realBasis3)).continuous.comp_continuousOn
      hB.continuousOn).const_mul ((-1 : ℝ)^i.val)).mono hbox)
    (fun x hx i ↦ stokesCoefficient_hasFDerivAt (hdiff x (hbox ⟨
      fun j ↦ (hx.1 j (mem_univ j)).1.le, fun j ↦ (hx.1 j (mem_univ j)).2.le⟩)) i) hi
  rw [setIntegral_congr_fun measurableSet_Icc hzero, integral_zero] at hst
  exact hst.symm

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set MeasureTheory

theorem first_face_integral_le_of_closed
    {U : Set Real3} (hU : IsOpen U)
    {B : Real3 → Real3 [⋀^Fin 2]→L[ℝ] ℝ}
    (hB : ContDiffOn ℝ 1 B U) (hc : ∀ x ∈ U, extDeriv B x = 0)
    (a b : Real3) (hab : a ≤ b) (hbox : Icc a b ⊆ U)
    (hbottom : ∀ y ∈ Icc (a ∘ (1 : Fin 3).succAbove) (b ∘ (1 : Fin 3).succAbove),
      stokesCoefficient B 1 ((1 : Fin 3).insertNth (a 1) y) = 0)
    (htop : ∀ y ∈ Icc (a ∘ (1 : Fin 3).succAbove) (b ∘ (1 : Fin 3).succAbove),
      0 ≤ stokesCoefficient B 1 ((1 : Fin 3).insertNth (b 1) y))
    (hperiod : ∀ y ∈ Icc (a ∘ (2 : Fin 3).succAbove) (b ∘ (2 : Fin 3).succAbove),
      stokesCoefficient B 2 ((2 : Fin 3).insertNth (b 2) y) =
      stokesCoefficient B 2 ((2 : Fin 3).insertNth (a 2) y)) :
    (∫ y in Icc (a ∘ (0 : Fin 3).succAbove) (b ∘ (0 : Fin 3).succAbove),
      stokesCoefficient B 0 ((0 : Fin 3).insertNth (b 0) y)) ≤
    ∫ y in Icc (a ∘ (0 : Fin 3).succAbove) (b ∘ (0 : Fin 3).succAbove),
      stokesCoefficient B 0 ((0 : Fin 3).insertNth (a 0) y) := by
  have hs := sum_faces_eq_zero_of_closed_twoForm hU hB hc a b hab hbox
  have hb : (∫ y in Icc (a ∘ (1 : Fin 3).succAbove) (b ∘ (1 : Fin 3).succAbove),
      stokesCoefficient B 1 ((1 : Fin 3).insertNth (a 1) y)) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Icc hbottom, integral_zero]
  have ht : 0 ≤ (∫ y in Icc (a ∘ (1 : Fin 3).succAbove) (b ∘ (1 : Fin 3).succAbove),
      stokesCoefficient B 1 ((1 : Fin 3).insertNth (b 1) y)) :=
    setIntegral_nonneg measurableSet_Icc htop
  have hp := setIntegral_congr_fun (μ := volume) measurableSet_Icc hperiod
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  norm_num only [Fin.val_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hs
  rw [hb, hp] at hs
  linarith

end UniversalCoverSplitting

open scoped ContDiff
open Set
namespace UniversalCoverSplitting

def movingPolar (R : ℝ → ℝ) (x : Real3) : ℂ × ℂ :=
  ((x 0 : ℂ), ((R (x 0) * x 1 : ℝ) : ℂ) * Complex.exp ((x 2 : ℂ) * Complex.I))

theorem movingPolar_contDiffOn {R : ℝ → ℝ} {V : Set Real3} {J : Set ℝ}
    (hR : ContDiffOn ℝ ∞ R J) (hJ : MapsTo (fun x : Real3 ↦ x 0) V J) :
    ContDiffOn ℝ ∞ (movingPolar R) V := by
  have hr : ContDiffOn ℝ ∞ (fun x : Real3 ↦ R (x 0)) V :=
    hR.comp (by fun_prop) hJ
  have h0 : ContDiffOn ℝ ∞ (fun x : Real3 ↦ (x 0 : ℂ)) V :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (by fun_prop)
  have ha : ContDiffOn ℝ ∞ (fun x : Real3 ↦ ((R (x 0) * x 1 : ℝ) : ℂ)) V :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hr.mul (by fun_prop))
  have h2 : ContDiffOn ℝ ∞ (fun x : Real3 ↦ (x 2 : ℂ)) V :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (by fun_prop)
  exact h0.prodMk (ha.mul (Complex.contDiff_exp.comp_contDiffOn (h2.mul (contDiffOn_const (c := Complex.I)))))

theorem movingPolar_fderiv_apply {R : ℝ → ℝ} {x : Real3}
    (hR : DifferentiableAt ℝ R (x 0)) (v : Real3) :
    fderiv ℝ (movingPolar R) x v =
      ((v 0 : ℂ),
        (((deriv R (x 0) * v 0 * x 1 + R (x 0) * v 1 : ℝ) : ℂ) *
          Complex.exp ((x 2 : ℂ) * Complex.I)) +
        ((R (x 0) * x 1 : ℝ) : ℂ) * Complex.exp ((x 2 : ℂ) * Complex.I) *
          (v 2 : ℂ) * Complex.I) := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) x
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) x
  have hr := hR.hasDerivAt.hasFDerivAt.comp x h0
  have ha := Complex.ofRealCLM.hasFDerivAt.comp x (hr.mul h1)
  have he := ((Complex.ofRealCLM.hasFDerivAt.comp x h2).mul_const Complex.I).cexp
  have hh := (Complex.ofRealCLM.hasFDerivAt.comp x h0).prodMk (ha.mul he)
  change HasFDerivAt (movingPolar R) _ x at hh
  rw [hh.fderiv]
  ext <;> simp [ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring

theorem movingPolar_deriv_zero {R : ℝ → ℝ} {x : Real3}
    (hR : DifferentiableAt ℝ R (x 0)) :
    fderiv ℝ (movingPolar R) x (realBasis3 0) =
      (1, ((deriv R (x 0) * x 1 : ℝ) : ℂ) * Complex.exp ((x 2 : ℂ) * Complex.I)) := by
  rw [movingPolar_fderiv_apply hR]
  simp [realBasis3]

theorem movingPolar_deriv_one {R : ℝ → ℝ} {x : Real3}
    (hR : DifferentiableAt ℝ R (x 0)) :
    fderiv ℝ (movingPolar R) x (realBasis3 1) =
      (0, (R (x 0) : ℂ) * Complex.exp ((x 2 : ℂ) * Complex.I)) := by
  rw [movingPolar_fderiv_apply hR]
  simp [realBasis3]

theorem movingPolar_deriv_two {R : ℝ → ℝ} {x : Real3}
    (hR : DifferentiableAt ℝ R (x 0)) :
    fderiv ℝ (movingPolar R) x (realBasis3 2) =
      (0, ((R (x 0) * x 1 : ℝ) : ℂ) * Complex.exp ((x 2 : ℂ) * Complex.I) * Complex.I) := by
  rw [movingPolar_fderiv_apply hR]
  simp [realBasis3]

theorem movingPolar_deriv_zero' {R : ℝ → ℝ} {x : Real3}
    (hR : DifferentiableAt ℝ R (x 0)) :
    fderiv ℝ (movingPolar R) x (realBasis3 0) =
      (1, 0) + (deriv R (x 0) * x 1) • (0, Complex.exp ((x 2 : ℂ) * Complex.I)) := by
  rw [movingPolar_deriv_zero hR]
  ext <;> simp [Complex.real_smul]

theorem movingPolar_deriv_one' {R : ℝ → ℝ} {x : Real3}
    (hR : DifferentiableAt ℝ R (x 0)) :
    fderiv ℝ (movingPolar R) x (realBasis3 1) =
      R (x 0) • (0, Complex.exp ((x 2 : ℂ) * Complex.I)) := by
  rw [movingPolar_deriv_one hR]
  ext <;> simp [Complex.real_smul]

theorem movingPolar_deriv_two' {R : ℝ → ℝ} {x : Real3}
    (hR : DifferentiableAt ℝ R (x 0)) :
    fderiv ℝ (movingPolar R) x (realBasis3 2) =
      (R (x 0) * x 1) • (Complex.I • (0, Complex.exp ((x 2 : ℂ) * Complex.I))) := by
  rw [movingPolar_deriv_two hR]
  ext <;> simp [Complex.real_smul, mul_comm, mul_left_comm]

end UniversalCoverSplitting

open scoped Manifold ContDiff
open Set MeasureTheory

open scoped Manifold ContDiff
open Set MeasureTheory

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
open scoped Interval

lemma finTwo_box_integral_eq_prod (F : (Fin 2 → ℝ) → ℝ) (a b : Fin 2 → ℝ) :
    (∫ y in Icc a b, F y) =
      ∫ p in Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1), F ![p.1,p.2] := by
  let e : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) := MeasurableEquiv.finTwoArrow
  have hp : e ⁻¹' (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)) = Icc a b := by
    ext y
    simp only [e, MeasurableEquiv.finTwoArrow_apply, mem_preimage, mem_prod,
      mem_Icc, Pi.le_def, Fin.forall_fin_two]
    tauto
  have hh := ((volume_preserving_finTwoArrow ℝ).restrict_preimage_emb
    e.measurableEmbedding (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1))).integral_comp'
      (fun p ↦ F (e.symm p))
  rw [hp] at hh
  have he (p : ℝ × ℝ) : e.symm p = ![p.1,p.2] := by
    ext i
    fin_cases i <;> rfl
  change (∫ x in Icc a b, F (e.symm (e x))) =
    ∫ p in Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1), F (e.symm p) at hh
  simp only [MeasurableEquiv.symm_apply_apply] at hh
  simpa only [he] using hh

theorem normalized_polar_integral_eq_disk {f : ℂ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ContinuousOn f (closedBall 0 R)) :
    (∫ y in Icc (![0,0] : Fin 2 → ℝ) ![1,2 * Real.pi],
      y 0 * R^2 * f (((R * y 0 : ℝ) : ℂ) * Complex.exp ((y 1 : ℂ) * Complex.I))) =
    ∫ z in ball (0 : ℂ) R, f z := by
  let G : ℝ × ℝ → ℝ := fun p ↦ p.1 * R^2 *
    f (((R * p.1 : ℝ) : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))
  have hc : ContinuousOn G (Icc 0 1 ×ˢ Icc 0 (2 * Real.pi)) := by
    apply (continuousOn_fst.mul continuousOn_const).mul (hf.comp _ _)
    · fun_prop
    · intro p hp
      simp only [mem_closedBall, dist_zero_right, norm_mul,
        Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one]
      rw [Real.norm_of_nonneg hR, Real.norm_of_nonneg hp.1.1]
      nlinarith [hp.1.2]
  have hi : IntegrableOn G (Icc 0 1 ×ˢ Icc 0 (2 * Real.pi)) :=
    hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [finTwo_box_integral_eq_prod]
  change (∫ p in Icc 0 1 ×ˢ Icc 0 (2 * Real.pi), G p) = _
  rw [Measure.volume_eq_prod, setIntegral_prod G
    (by simpa only [← Measure.volume_eq_prod] using hi)]
  have hinner (r : ℝ) : (∫ θ in Icc 0 (2 * Real.pi), G (r,θ)) =
      r * R^2 * (2 * Real.pi * Real.circleAverage f 0 (R*r)) := by
    change (∫ θ in Icc 0 (2 * Real.pi), r * R^2 *
      f (((R*r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) = _
    rw [integral_const_mul, integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (show 0 ≤ 2 * Real.pi by positivity)]
    congr 1
    rw [Real.circleAverage_def]
    simp only [smul_eq_mul, mul_inv_cancel_left₀ (by positivity : 2 * Real.pi ≠ 0)]
    simp only [circleMap, zero_add]
  simp_rw [hinner]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    disk_integral_eq_polar hR hf]
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (a := (0:ℝ)) (b := 1) (fun t ↦ t * Real.circleAverage f 0 t) R
  simp only [smul_eq_mul, mul_zero, mul_one] at hs
  calc
    _ = 2 * Real.pi * (R * ∫ r in (0:ℝ)..1, (R*r) * Real.circleAverage f 0 (R*r)) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r hr
      ring
    _ = _ := by rw [hs]

end UniversalCoverSplitting

open Set Metric
open scoped ContDiff

namespace UniversalCoverSplitting

def shrinkingRadius (k x : ℝ) : ℝ := k * Real.sqrt (-x)

theorem shrinkingRadius_contDiffOn (k : ℝ) :
    ContDiffOn ℝ ∞ (shrinkingRadius k) (Iio 0) := by
  apply contDiffOn_const.mul
  apply ContDiffOn.sqrt (contDiffOn_id.neg)
  intro x hx
  exact ne_of_gt (neg_pos.mpr hx)

theorem shrinkingRadius_hasDerivAt (k : ℝ) {x : ℝ} (hx : x < 0) :
    HasDerivAt (shrinkingRadius k) (-k / (2 * Real.sqrt (-x))) x := by
  exact ((((hasDerivAt_id x).neg).sqrt (ne_of_gt (neg_pos.mpr hx))).const_mul k).congr_deriv
    (by change k * (-1 / (2 * Real.sqrt (-x))) = -k / (2 * Real.sqrt (-x)); ring)

theorem shrinkingRadius_nonneg {k x : ℝ} (hk : 0 ≤ k) :
    0 ≤ shrinkingRadius k x := mul_nonneg hk (Real.sqrt_nonneg _)

theorem exists_shrinkingRadius_deriv_le {k : ℝ} (hk : 0 < k) (C : ℝ) :
    ∃ x₀ : ℝ, x₀ < 0 ∧ ∀ x ∈ Ico x₀ 0, deriv (shrinkingRadius k) x ≤ -C := by
  let d : ℝ := k / (2 * (|C| + 1))
  have hCp : 0 < |C| + 1 := by positivity
  have hdp : 0 < d := div_pos hk (mul_pos (by norm_num) hCp)
  refine ⟨-d^2, neg_neg_of_pos (sq_pos_of_pos hdp), ?_⟩
  intro x hx
  rw [(shrinkingRadius_hasDerivAt k hx.2).deriv]
  have hs : 0 < Real.sqrt (-x) := Real.sqrt_pos.mpr (neg_pos.mpr hx.2)
  have hsd : Real.sqrt (-x) ≤ d := by
    apply (Real.sqrt_le_left hdp.le).mpr
    linarith [hx.1]
  have hmul : C * (2 * Real.sqrt (-x)) ≤ k := by
    calc
      C * (2 * Real.sqrt (-x)) ≤ (|C| + 1) * (2 * Real.sqrt (-x)) := by
        gcongr; exact (le_abs_self C).trans (by linarith)
      _ ≤ (|C| + 1) * (2 * d) := by gcongr
      _ = k := by dsimp [d]; field_simp
  have hp : 0 < 2 * Real.sqrt (-x) := mul_pos (by norm_num) hs
  apply (div_le_iff₀ hp).mpr
  linarith

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

open Set Metric Filter Topology

open Set Metric Filter Topology
open scoped Manifold ENNReal NNReal

open Set Metric Filter Topology
namespace UniversalCoverSplitting

theorem subset_of_uniform_local_continuation {E : Type*} [MetricSpace E]
    {W A : Set E} (hW : IsOpen W) (hWc : IsPreconnected W) (hA : IsOpen A)
    (hAW : A ⊆ W) (hAn : A.Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (hcont : ∀ u ∈ A, ∀ e : ℝ, 0 < e → e ≤ δ → ball u e ⊆ W → ball u e ⊆ A) :
    W ⊆ A := by
  apply hWc.subset_of_closure_inter_subset hA
  · obtain ⟨u,hu⟩ := hAn
    exact ⟨u,hAW hu,hu⟩
  intro x hx
  obtain ⟨ε,hε,hεW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hx.2)
  let d := min (ε/4) (δ/4)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdε : d ≤ ε/4 := min_le_left _ _
  have hdδ : d ≤ δ/4 := min_le_right _ _
  obtain ⟨u,hux,huA⟩ := mem_closure_iff.mp hx.1 (ball x d) isOpen_ball (mem_ball_self hd)
  have hux' : dist u x < d := hux
  have hballW : ball u (2*d) ⊆ W := by
    intro y hy
    apply hεW
    have hy' : dist y u < 2*d := hy
    have ht := dist_triangle y u x
    change dist y x < ε
    linarith
  apply hcont u huA (2*d) (by positivity) (by linarith) hballW
  change dist x u < 2*d
  rw [dist_comm]
  linarith

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold

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
variable {n r s : ℕ}

lemma mixed_shift_in_annulus {l η : ℝ} (hl : 0 < l) {c w v : ℂ}
    (hc : ‖c‖*η ≤ 1/8) (hw : ‖w‖ < η*l)
    (hv : l < ‖v‖ ∧ ‖v‖ < 5*l/4) :
    3*l/4 < ‖v+c*w‖ ∧ ‖v+c*w‖ < 3*l/2 := by
  have hcw : ‖c*w‖ ≤ l/8 := by
    rw [norm_mul]
    calc
      ‖c‖*‖w‖ ≤ ‖c‖*(η*l) := mul_le_mul_of_nonneg_left hw.le (norm_nonneg _)
      _ = (‖c‖*η)*l := by ring
      _ ≤ (1/8)*l := mul_le_mul_of_nonneg_right hc hl.le
      _ = l/8 := by ring
  have hl : ‖v‖ ≤ ‖v+c*w‖+‖c*w‖ := by
    calc
      ‖v‖ = ‖(v+c*w)-(c*w)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  have hu := norm_add_le v (c*w)
  constructor <;> linarith [hv.1,hv.2]

end UniversalCoverSplitting

open Set Metric
namespace UniversalCoverSplitting

def annulusPath (z : ℂ) (t : ℝ) : ℂ :=
  ((1 + t * (‖z‖ - 1) : ℝ) : ℂ) * Complex.exp (((t * z.arg : ℝ) : ℂ) * Complex.I)

@[simp] theorem annulusPath_zero (z : ℂ) : annulusPath z 0 = 1 := by
  simp [annulusPath]

@[simp] theorem annulusPath_one (z : ℂ) : annulusPath z 1 = z := by
  simp [annulusPath, Complex.norm_mul_exp_arg_mul_I]

theorem annulusPath_norm {z : ℂ} (hz : 3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    ‖annulusPath z t‖ = 1 + t * (‖z‖ - 1) := by
  have ha : 0 ≤ 1 + t * (‖z‖ - 1) := by nlinarith [hz.1, ht.1, ht.2]
  simp only [annulusPath, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_nonneg ha]

theorem annulusPath_mem {z : ℂ} (hz : 3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    3 / 4 ≤ ‖annulusPath z t‖ ∧ ‖annulusPath z t‖ ≤ 3 / 2 := by
  rw [annulusPath_norm hz ht]
  constructor <;> nlinarith [hz.1, hz.2, ht.1, ht.2]

theorem annulusPath_hasDerivAt (z : ℂ) (t : ℝ) :
    HasDerivAt (annulusPath z)
      ((((‖z‖ - 1 : ℝ) : ℂ) + ((1 + t * (‖z‖ - 1) : ℝ) : ℂ) *
        ((z.arg : ℂ) * Complex.I)) * Complex.exp (((t * z.arg : ℝ) : ℂ) * Complex.I)) t := by
  have h₁ := (((hasDerivAt_id t).mul_const (‖z‖ - 1)).const_add 1).ofReal_comp
  have h₂ := (((hasDerivAt_id t).mul_const z.arg).ofReal_comp.mul_const Complex.I).cexp
  exact (h₁.mul h₂).congr_deriv (by
    simp only [id_eq, one_mul]
    ring)

theorem annulusPath_deriv_bound {z : ℂ} (hz : 3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2)
    {t : ℝ} (ht : t ∈ Icc 0 1) : ‖deriv (annulusPath z) t‖ ≤ 7 := by
  rw [(annulusPath_hasDerivAt z t).deriv, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have ha : 0 ≤ 1 + t * (‖z‖ - 1) := by nlinarith [hz.1, ht.1, ht.2]
  have hb : 1 + t * (‖z‖ - 1) ≤ 3 / 2 := by nlinarith [hz.2, ht.1, ht.2]
  have hc : |‖z‖ - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hz.1,hz.2]
  calc
    _ ≤ ‖((‖z‖ - 1 : ℝ) : ℂ)‖ +
        ‖((1 + t * (‖z‖ - 1) : ℝ) : ℂ) * ((z.arg : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ = |‖z‖ - 1| + (1+t*(‖z‖-1)) * |z.arg| := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ 1 + (3/2) * Real.pi := by
      exact add_le_add hc (mul_le_mul hb (Complex.abs_arg_le_pi z) (abs_nonneg _) (by norm_num))
    _ ≤ 7 := by linarith [Real.pi_lt_four]

end UniversalCoverSplitting

open Set Metric
namespace UniversalCoverSplitting
section
variable {M E : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem chart_trapping_on_annulus (e : OpenPartialHomeomorph M E)
    {c : E} {R L : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (he : closedBall c R ⊆ e.target) {h : ℂ → M}
    (hc : ContinuousOn h {z | 3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2})
    (hzero : h 1 ∈ e.source ∧ dist (e (h 1)) c < R - 7 * L)
    (hder : ∀ z, 3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2 →
      h z ∈ e.symm '' closedBall c R →
      DifferentiableAt ℂ (e ∘ h) z ∧ ‖fderiv ℂ (e ∘ h) z‖ ≤ L) :
    ∀ z, 3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2 →
      h z ∈ e.source ∧ e (h z) ∈ ball c R := by
  intro z hz
  have hp : Continuous (annulusPath z) :=
    continuous_iff_continuousAt.mpr (fun t ↦ (annulusPath_hasDerivAt z t).continuousAt)
  have hγ : ContinuousOn (h ∘ annulusPath z) (Icc 0 1) :=
    hc.comp hp.continuousOn (fun t ht ↦ annulusPath_mem hz ht)
  have hinit : (h ∘ annulusPath z) 0 ∈ e.source ∧
      dist (e ((h ∘ annulusPath z) 0)) c < R - (7 * L) * 1 := by
    simpa only [Function.comp_apply, annulusPath_zero, mul_one] using hzero
  have htrap := chart_trapping_on_interval e hR (mul_nonneg (by norm_num) hL)
    zero_le_one he hγ hinit (fun t ht hk ↦ ?_) 1 (by norm_num)
  · simpa only [Function.comp_apply, annulusPath_one] using htrap
  obtain ⟨hd,hb⟩ := hder (annulusPath z t) (annulusPath_mem hz ht) hk
  refine ⟨fderiv ℂ (e ∘ h) (annulusPath z t) (deriv (annulusPath z) t), ?_, ?_⟩
  · have hh := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      (annulusPath_hasDerivAt z t |>.differentiableAt.hasDerivAt)
    exact hh.hasDerivWithinAt
  · calc
      _ ≤ ‖fderiv ℂ (e ∘ h) (annulusPath z t)‖ * ‖deriv (annulusPath z) t‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * 7 := mul_le_mul hb (annulusPath_deriv_bound hz ht) (norm_nonneg _) hL
      _ = 7 * L := mul_comm _ _

end
end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ}

def compactAnnulus : Set ℂ := {z | 3/4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3/2}
def openAnnulus : Set ℂ := {z | 1/2 < ‖z‖ ∧ ‖z‖ < 2}

theorem isCompact_compactAnnulus : IsCompact compactAnnulus := by
  have he : compactAnnulus = closedBall (0 : ℂ) (3/2) ∩ {z | 3/4 ≤ ‖z‖} := by
    ext z; simp [compactAnnulus, and_comm]
  rw [he]
  exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)

theorem isOpen_openAnnulus : IsOpen openAnnulus :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem compactAnnulus_subset_openAnnulus : compactAnnulus ⊆ openAnnulus := by
  intro z hz
  constructor <;> dsimp [compactAnnulus] at hz <;> linarith [hz.1,hz.2]

end UniversalCoverSplitting

open Set MeasureTheory Filter Topology
open scoped ENNReal
namespace UniversalCoverSplitting

def scaledAnnulus (r : ℝ) : Set ℂ := {z | r/2 < ‖z‖ ∧ ‖z‖ < 2*r}

lemma measurableSet_scaledAnnulus (r : ℝ) : MeasurableSet (scaledAnnulus r) :=
  ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)).measurableSet

lemma scaledAnnulus_disjoint {a b : ℝ} (ha : 0 < a) (hab : 5*a ≤ b) :
    Disjoint (scaledAnnulus a) (scaledAnnulus b) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have h₁ := hz.2
  have h₂ := hz'.1
  linarith

lemma geometric_annuli_pairwiseDisjoint {r : ℝ} (hr : 0 < r) :
    Pairwise fun i j : ℕ ↦ Disjoint (scaledAnnulus ((5:ℝ)^i*r))
      (scaledAnnulus ((5:ℝ)^j*r)) := by
  have H (i j : ℕ) (h : i < j) :
      Disjoint (scaledAnnulus ((5:ℝ)^i*r)) (scaledAnnulus ((5:ℝ)^j*r)) := by
    apply scaledAnnulus_disjoint (mul_pos (pow_pos (by norm_num) _) hr)
    have hj : i+1 ≤ j := h
    have hp : (5:ℝ)^(i+1) ≤ 5^j := pow_le_pow_right₀ (by norm_num) hj
    calc
      5*(5^i*r) = 5^(i+1)*r := by rw [pow_succ]; ring
      _ ≤ 5^j*r := mul_le_mul_of_nonneg_right hp hr.le
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact H i j h
  · exact (H j i h).symm

theorem exists_small_energy_annulus (q : ℂ → ℝ≥0∞) {D : Set ℂ}
    {N : ℕ} {r η : ℝ} {M : ℝ≥0∞}
    (hr : 0 < r)
    (hs : ∀ i < N, scaledAnnulus ((5:ℝ)^i*r) ⊆ D)
    (hbound : ∫⁻ z in D, q z ≤ M)
    (hlarge : M < N * ENNReal.ofReal η) :
    ∃ i < N, ∫⁻ z in scaledAnnulus ((5:ℝ)^i*r), q z < ENNReal.ofReal η := by
  classical
  by_contra! h
  have hpair : Set.PairwiseDisjoint (↑(Finset.range N) : Set ℕ)
      (fun i ↦ scaledAnnulus ((5:ℝ)^i*r)) := by
    intro i hi j hj hij
    exact geometric_annuli_pairwiseDisjoint hr hij
  have hsum : ∑ i ∈ Finset.range N, ∫⁻ z in scaledAnnulus ((5:ℝ)^i*r), q z ≤ M := by
    rw [← lintegral_biUnion_finset hpair (fun i _ ↦ measurableSet_scaledAnnulus _) q]
    apply le_trans (lintegral_mono_set _) hbound
    intro z hz
    simp only [mem_iUnion,Finset.mem_range,exists_prop] at hz
    obtain ⟨i,hi,hzi⟩ := hz
    exact hs i hi hzi
  have hlow : N*ENNReal.ofReal η ≤ ∑ i ∈ Finset.range N,
      ∫⁻ z in scaledAnnulus ((5:ℝ)^i*r), q z := by
    calc
      N*ENNReal.ofReal η = ∑ i ∈ Finset.range N, ENNReal.ofReal η := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi ↦ h i (Finset.mem_range.mp hi))
  exact (not_lt_of_ge (hlow.trans hsum)) hlarge

theorem exists_number_of_annuli {M : ℝ≥0∞} (hM : M ≠ ⊤) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ M < N*ENNReal.ofReal η := by
  obtain ⟨N,hN⟩ := exists_nat_gt (M.toReal/η+1)
  have hNN : (0:ℝ) < N := lt_trans (by positivity : (0:ℝ) < M.toReal/η+1) hN
  refine ⟨N,Nat.cast_pos.mp hNN,?_⟩
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg N),← ENNReal.ofReal_toReal hM]
  apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos hNN hη)).mpr
  have hR : M.toReal/η < (N:ℝ) := by linarith
  exact (div_lt_iff₀ hη).mp hR

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
namespace UniversalCoverSplitting
variable {n : ℕ}

lemma positive_smul_openAnnulus {l : ℝ} (hl : 0 < l) :
    (fun z : ℂ ↦ l • z) '' openAnnulus = scaledAnnulus l := by
  ext v
  constructor
  · rintro ⟨z,hz,rfl⟩
    change l/2 < ‖l • z‖ ∧ ‖l • z‖ < 2*l
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hl]
    constructor <;> nlinarith [hz.1,hz.2]
  · intro hv
    refine ⟨l⁻¹ • v,?_,?_⟩
    · change 1/2 < ‖l⁻¹ • v‖ ∧ ‖l⁻¹ • v‖ < 2
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hl)]
      have he : l⁻¹ * ‖v‖ = ‖v‖ / l := by ring
      rw [he]
      exact ⟨(lt_div_iff₀ hl).mpr (by linarith [hv.1]),
        (div_lt_iff₀ hl).mpr (by linarith [hv.2])⟩
    · dsimp only
      rw [smul_smul,mul_inv_cancel₀ hl.ne',one_smul]

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

namespace UniversalCoverSplitting

lemma exists_boundary_scales {x₀ k η : ℝ} (hx : x₀ < 0) (hk : 0 < k) (hη : 0 < η)
    (N : ℕ) : ∃ t : ℝ, 0 < t ∧ -t^4 ∈ Ico x₀ 0 ∧
      ∀ i ≤ N, t^4 < η*((5:ℝ)^i*t^3) ∧ 2*((5:ℝ)^i*t^3) < k*t^2 := by
  have h5 : 0 < (5:ℝ)^N := pow_pos (by norm_num) _
  have hneg : 0 < -x₀ := neg_pos.mpr hx
  have hmin : 0 < min 1 (min (-x₀) (min η (k/(2*(5:ℝ)^N)))) := by positivity
  obtain ⟨t,ht,htm⟩ := exists_between hmin
  have ht1 : t < 1 := htm.trans_le (min_le_left _ _)
  have htX : t < -x₀ := htm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htη : t < η := htm.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htk : t < k/(2*(5:ℝ)^N) := htm.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have ht4 : t^4 ≤ t := by
    calc
      t^4 = t*t^3 := by ring
      _ ≤ t*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ ht.le ht1.le) ht.le
      _ = t := mul_one _
  refine ⟨t,ht,⟨by linarith,neg_neg_of_pos (pow_pos ht _)⟩,?_⟩
  intro i hi
  have hp : 1 ≤ (5:ℝ)^i := one_le_pow₀ (by norm_num)
  have hpN : (5:ℝ)^i ≤ 5^N := pow_le_pow_right₀ (by norm_num) hi
  have ht3 : 0 < t^3 := pow_pos ht _
  have ht2 : 0 < t^2 := pow_pos ht _
  constructor
  · calc
      t^4 = t*(t^3) := by ring
      _ < η*t^3 := mul_lt_mul_of_pos_right htη ht3
      _ ≤ η*((5:ℝ)^i*t^3) := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left ht3.le hp) hη.le
  · have htk' : 2*(5:ℝ)^N*t < k := by
      have h := (lt_div_iff₀ (mul_pos (by norm_num) h5)).mp htk
      nlinarith
    calc
      2*((5:ℝ)^i*t^3) ≤ 2*((5:ℝ)^N*t^3) := by gcongr
      _ = (2*(5:ℝ)^N*t)*t^2 := by ring
      _ < k*t^2 := mul_lt_mul_of_pos_right htk' ht2

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology

open Set Metric Filter Topology

open Set Metric Filter Topology
open scoped Manifold

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

lemma normSq_hasFDerivAt (z : ℂ) : HasFDerivAt Complex.normSq
    ((2*z.re) • Complex.reCLM + (2*z.im) • Complex.imCLM) z := by
  convert! ((Complex.reCLM.hasFDerivAt.pow 2).add (Complex.imCLM.hasFDerivAt.pow 2)) using 1
  · ext x; simp [Complex.normSq_apply,pow_two]
  · simp [two_smul,two_mul]

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting

lemma normSqPow_fderiv_mul {m : ℕ} (hm : 0 < m) (p w : ℂ) :
    fderiv ℝ (fun z : ℂ ↦ Complex.normSq z ^ m) p (p*w) =
      (2*m*Complex.normSq p^m)*w.re := by
  rw [((normSq_hasFDerivAt p).pow m).fderiv]
  simp only [smul_apply,smul_eq_mul,nsmul_eq_mul,add_apply,Complex.reCLM_apply,
    Complex.imCLM_apply,Complex.mul_re,Complex.mul_im]
  have hp : Complex.normSq p^(m-1)*Complex.normSq p = Complex.normSq p^m := by
    rw [← pow_succ,Nat.sub_add_cancel hm]
  rw [← hp,Complex.normSq_apply]
  ring

def superSource (m : ℕ) (p : ℂ × ℂ) (q : ℂ × ℂ) : ℂ × ℂ :=
  (p.1*(1+q.1+(Complex.normSq p.2^m:ℝ)*q.2),
    p.2*(1+q.1-(Complex.normSq p.1^m:ℝ)*q.2))

lemma superSource_zero (m : ℕ) (p : ℂ × ℂ) : superSource m p 0 = p := by simp [superSource]

lemma superSource_contDiff (m : ℕ) (p : ℂ × ℂ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (superSource m p) := by
  change ContDiff ℝ k (fun q : ℂ × ℂ ↦
    (p.1*(1+q.1+(Complex.normSq p.2^m:ℝ)*q.2),p.2*(1+q.1-(Complex.normSq p.1^m:ℝ)*q.2)))
  fun_prop

lemma superSource_hasFDerivAt (m : ℕ) (p q : ℂ × ℂ) :
    HasFDerivAt (superSource m p)
      ((p.1 • (ContinuousLinearMap.fst ℂ ℂ ℂ + (Complex.normSq p.2^m:ℝ) • ContinuousLinearMap.snd ℂ ℂ ℂ)).prod
       (p.2 • (ContinuousLinearMap.fst ℂ ℂ ℂ - (Complex.normSq p.1^m:ℝ) • ContinuousLinearMap.snd ℂ ℂ ℂ))) q := by
  exact (((hasFDerivAt_fst.const_add 1).add (hasFDerivAt_snd.const_mul _)).const_mul _).prodMk
    (((hasFDerivAt_fst.const_add 1).sub (hasFDerivAt_snd.const_mul _)).const_mul _)

lemma superSource_fderiv (m : ℕ) (p q h : ℂ × ℂ) :
    fderiv ℝ (superSource m p) q h =
      (p.1*(h.1+(Complex.normSq p.2^m:ℝ)*h.2),p.2*(h.1-(Complex.normSq p.1^m:ℝ)*h.2)) := by
  rw [((superSource_hasFDerivAt m p q).restrictScalars ℝ).fderiv]
  rfl

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold

open Set Metric Filter Topology
open scoped Manifold

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
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
variable {n r s : ℕ}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma smul_unit_ball {a : ℂ} (ha : ‖a‖ ≤ 1) {p : E} (hp : p ∈ ball (0:E) 1) :
    a • p ∈ ball (0:E) 1 := by
  rw [mem_ball_zero_iff,norm_smul]
  exact (mul_le_mul_of_nonneg_right ha (norm_nonneg p)).trans_lt (by simpa using hp)

lemma radial_scaled_ball {a : ℝ} (ha : 0 < a) {p : E} (hp : ‖p‖ < a)
    {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) : (z/(a:ℂ)) • p ∈ ball (0:E) 1 := by
  rw [mem_ball_zero_iff,norm_smul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
  have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
  calc
    ‖z‖ / a * ‖p‖ ≤ 1 / a * ‖p‖ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hz1 ha.le) (norm_nonneg p)
    _ = ‖p‖ / a := by ring
    _ < 1 := (div_lt_one ha).mpr hp

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
open Set Filter Topology Metric MeasureTheory
namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem hasFDerivAt_compact_parametric_integral
    {U : Set E} (hU : IsOpen U) {K : Set ℝ} (hK : IsCompact K)
    {f : E → ℝ → F} {df : E → ℝ → E →L[ℂ] F}
    (hc : ContinuousOn f.uncurry (U ×ˢ K))
    (hdc : ContinuousOn df.uncurry (U ×ˢ K))
    (hd : ∀ x ∈ U, ∀ t ∈ K, HasFDerivAt (fun y ↦ f y t) (df x t) x)
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y ↦ ∫ t in K, f y t) (∫ t in K, df x t) x := by
  let : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hsub : closedBall x (r/2) ⊆ U := by
    intro y hy
    apply hrU
    exact lt_of_le_of_lt (mem_closedBall.mp hy) (by linarith : r/2 < r)
  have hcomp := (isCompact_closedBall x (r/2)).prod hK
  obtain ⟨C,hC⟩ := hcomp.exists_bound_of_continuousOn
    (hdc.mono (prod_mono hsub Subset.rfl))
  have hc_slice (y : E) (hy : y ∈ U) : ContinuousOn (f y) K :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht ↦ ⟨hy,ht⟩)
  have hdc_slice (y : E) (hy : y ∈ U) : ContinuousOn (df y) K :=
    hdc.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht ↦ ⟨hy,ht⟩)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball x (r/2)) (bound := fun _ ↦ C) (ball_mem_nhds x (by linarith))
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (hc_slice y hy).aestronglyMeasurable hK.measurableSet
  · exact (hc_slice x hx).integrableOn_compact hK
  · exact (hdc_slice x hx).aestronglyMeasurable hK.measurableSet
  · filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    intro y hy
    exact hC (y,t) ⟨ball_subset_closedBall hy,ht⟩
  · exact continuousOn_const.integrableOn_compact hK
  · filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    intro y hy
    exact hd y (hsub (ball_subset_closedBall hy)) t ht

end UniversalCoverSplitting

noncomputable section
open Set Filter Topology Metric MeasureTheory Complex
open scoped ContDiff
namespace UniversalCoverSplitting
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

lemma differentiableOn_directional_cauchy {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f : E → F} (hf : DifferentiableOn ℂ f U) (e : E) {r : ℝ} (hr : 0 < r)
    (hmap : ∀ z ∈ V, ∀ θ : ℝ, z+circleMap 0 r θ • e ∈ U) :
    DifferentiableOn ℂ (fun z ↦ cderiv r (fun w : ℂ ↦ f (z+w • e)) 0) V := by
  let k : ℝ → ℂ := fun θ ↦ (circleMap 0 r θ * Complex.I) * ((circleMap 0 r θ)^2)⁻¹
  let g : E → ℝ → F := fun z θ ↦ k θ • f (z+circleMap 0 r θ • e)
  let dg : E → ℝ → E →L[ℂ] F := fun z θ ↦ k θ • fderiv ℂ f (z+circleMap 0 r θ • e)
  have hne (θ : ℝ) : circleMap 0 r θ ≠ 0 := circleMap_ne_mem_ball (mem_ball_self hr) θ
  have hk : Continuous k := by
    apply Continuous.mul
    · exact (continuous_circleMap 0 r).mul continuous_const
    · exact ((continuous_circleMap 0 r).pow 2).inv₀ (fun θ ↦ pow_ne_zero 2 (hne θ))
  have hj : Continuous (fun p : E × ℝ ↦ p.1+circleMap 0 r p.2 • e) := by fun_prop
  have hm : MapsTo (fun p : E × ℝ ↦ p.1+circleMap 0 r p.2 • e) (V ×ˢ Icc 0 (2*Real.pi)) U :=
    fun p hp ↦ hmap p.1 hp.1 p.2
  have hdf : ContinuousOn (fderiv ℂ f) U := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    rw [continuousAt_clm_apply]
    exact continuousAt_directional_fderiv hU hf hp
  have hc : ContinuousOn g.uncurry (V ×ˢ Icc 0 (2*Real.pi)) :=
    (hk.comp continuous_snd).continuousOn.smul (hf.continuousOn.comp hj.continuousOn hm)
  have hdc : ContinuousOn dg.uncurry (V ×ˢ Icc 0 (2*Real.pi)) :=
    (hk.comp continuous_snd).continuousOn.smul (hdf.comp hj.continuousOn hm)
  have hd (z : E) (hz : z ∈ V) (θ : ℝ) : HasFDerivAt (fun y ↦ g y θ) (dg z θ) z := by
    have H := ((hf.differentiableAt (hU.mem_nhds (hmap z hz θ))).hasFDerivAt.comp z
      ((hasFDerivAt_id (𝕜 := ℂ) z).add_const (circleMap 0 r θ • e))).const_smul (k θ)
    convert H using 1 <;> simp only [g, dg, ContinuousLinearMap.comp_id, Function.comp_def, id_eq]
    rfl
  have heq : (fun z ↦ cderiv r (fun w : ℂ ↦ f (z+w • e)) 0)=
      (fun z ↦ ((2*Real.pi*Complex.I : ℂ)⁻¹) • ∫ θ in Icc 0 (2*Real.pi), g z θ) := by
    funext z
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
    simp only [cderiv,circleIntegral,deriv_circleMap,g,k,circleMap,zero_add,sub_zero,smul_smul]
  rw [heq]
  intro z hz
  exact ((hasFDerivAt_compact_parametric_integral hV isCompact_Icc hc hdc
    (fun y hy θ _ ↦ hd y hy θ) hz).const_smul _).differentiableAt.differentiableWithinAt

lemma differentiableAt_directional_fderiv {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) {p : E} (hp : p ∈ U) (e : E) :
    DifferentiableAt ℂ (fun z ↦ fderiv ℂ f z e) p := by
  obtain ⟨d,hd,hdU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let r : ℝ := d/(2*(‖e‖+1))
  have he : 0 < ‖e‖+1 := by positivity
  have hr : 0 < r := div_pos hd (by positivity)
  have hre : r*‖e‖ ≤ d/2 := by
    have hprod : r*(‖e‖+1)=d/2 := by dsimp [r]; field_simp
    nlinarith
  let V := ball p (d/2)
  have hV : V ∈ 𝓝 p := ball_mem_nhds _ (by linarith)
  have hmap (z : E) (hz : z ∈ V) (w : ℂ) (hw : w ∈ closedBall 0 r) : z+w • e ∈ U := by
    apply hdU
    rw [mem_ball,dist_eq_norm] at hz ⊢
    rw [mem_closedBall,dist_zero_right] at hw
    calc ‖z+w • e-p‖ = ‖(z-p)+w • e‖ := by congr 1; abel
         _ ≤ ‖z-p‖+‖w • e‖ := norm_add_le _ _
         _ = ‖z-p‖+‖w‖*‖e‖ := by rw [norm_smul]
         _ ≤ ‖z-p‖+r*‖e‖ := by gcongr
         _ < d := by linarith
  have hdiff := differentiableOn_directional_cauchy hU isOpen_ball hf e hr
    (fun z hz θ ↦ hmap z hz _ (circleMap_mem_closedBall _ hr.le _))
  apply (hdiff.differentiableAt hV).congr_of_eventuallyEq
  filter_upwards [hV] with z hz
  let W := (fun w : ℂ ↦ z+w • e) ⁻¹' U
  have hW : IsOpen W := hU.preimage (by fun_prop)
  have hline : DifferentiableOn ℂ (fun w : ℂ ↦ f (z+w • e)) W :=
    hf.comp (by fun_prop) (fun _ hw ↦ hw)
  rw [cderiv_eq_deriv hW hline hr (hmap z hz)]
  have hzU : z ∈ U := by simpa using hmap z hz 0 (mem_closedBall_self hr.le)
  have hdline : HasDerivAt (fun w : ℂ ↦ z+w • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const e).const_add z
  have H := (show HasFDerivAt f (fderiv ℂ f z) (z+(0:ℂ) • e) from by
    simpa using (hf.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt).comp_hasDerivAt 0 hdline
  exact H.deriv.symm

lemma finite_holomorphic_fderiv {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) : DifferentiableOn ℂ (fderiv ℂ f) U := by
  classical
  let b := Module.finBasis ℂ E
  let c := fun i ↦ (b.coord i).toContinuousLinearMap
  have heq : fderiv ℂ f=(fun z ↦ ∑ i, (c i).smulRight (fderiv ℂ f z (b i))) := by
    funext z
    ext v
    simp only [sum_apply,ContinuousLinearMap.smulRight_apply]
    change fderiv ℂ f z v=∑ i,b.repr v i • fderiv ℂ f z (b i)
    conv_lhs => rw [←b.sum_repr v]
    simp only [map_sum, map_smul]
  rw [heq]
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.fun_sum
  intro i _
  exact ((ContinuousLinearMap.smulRightL ℂ E F) (c i)).differentiableAt.comp z
    (differentiableAt_directional_fderiv hU hf hz (b i))

lemma finite_holomorphic_contDiffOn_nat (k : ℕ) {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ k f U := by
  induction k generalizing F with
  | zero => exact contDiffOn_zero.mpr hf.continuousOn
  | succ k ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨hf,by simp,ih (finite_holomorphic_fderiv hU hf)⟩

lemma finite_holomorphic_contDiffOn {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ ∞ f U := by
  rw [contDiffOn_infty]
  exact fun k ↦ finite_holomorphic_contDiffOn_nat k hU hf

end UniversalCoverSplitting
end
end
end

end OAI
end


