-- Prove2me | Definitions.Def_OAIQWQC000
-- name    : OAIQWQC000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T15:56:46.386001+00:00
-- url     : https://prove2.me/theorems/e74e535a-e88c-4f35-a779-cda0d472d28b
-- title:
--   OpenAI quadric-surface split: subharmonic functions in the plane (definitions bundle 1 of 5)
-- statement:
--   The first definitions bundle of the split of OpenAI's proof of the counterexample to Griffiths' positivity conjecture on the quadric surface (`OAI.QuadricCounterexample.main_theorem`). It holds OpenAI's Lean definitions for real functions on $\mathbb C$, from `DiskHessian.lean` and `Plurisubharmonic.lean` of `lean/OAI/Geometry/QuadricBundles` (OpenAI, *Ample rank-two bundles on the quadric surface without Griffiths-positive metrics*, OpenAI Math Release, September 24, 2026, result family 050, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a:
--   - `complexLaplacian u z`: the Laplacian $D^2u(z)(1,1) + D^2u(z)(i,i)$ of $u : \mathbb C \to \mathbb R$;
--   - `DiskSubharmonicOn Ω u`: upper semicontinuity on $\Omega$ and the disk submean inequality $|B(x,r)|\,u(x) \le \int_{B(x,r)} u$ whenever $\overline B(x,r) \subseteq \Omega$;
--   - `radialIntegral u c z` $= \int_{|a| \le 1} u(c + az)\,da$ and its first and second derivative fields (`radialLinear`, `radialFirst`, `radialSecond`), with six small lemmas about them.
--
--   It imports only Mathlib and is the whole import of the published statements `OAI.QuadricCounterexample.DiskSubharmonicOn.eq_const_of_max` and `OAI.QuadricCounterexample.DiskSubharmonicOn.of_C2_laplacian_nonneg`.
--
--   Modules: `DiskHessian.lean`, `Plurisubharmonic.lean`.
-- source:
--   OpenAI, Ample rank-two bundles on the quadric surface without Griffiths-positive metrics, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 050; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/ample-rank-two-bundles-on-the-quadric-surface-without-griffiths-positive-metrics-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/QuadricBundles at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQW_QuadricCounterexample.DiskHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory Laplacian InnerProductSpace
noncomputable section

def complexLaplacian (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  (fderiv ℝ (fderiv ℝ u) z 1) 1 +
  (fderiv ℝ (fderiv ℝ u) z Complex.I) Complex.I

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Plurisubharmonic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory
noncomputable section
open scoped Pointwise
def radialIntegral (u : ℂ → ℝ) (c z : ℂ) : ℝ :=
  ∫ a in closedBall (0 : ℂ) 1, u (c + a*z)

lemma radialIntegral_zero (u : ℂ → ℝ) (c : ℂ) :
    radialIntegral u c 0 = (volume (closedBall (0 : ℂ) 1)).toReal * u c := by
  simp [radialIntegral,measureReal_def]

lemma radialIntegral_rotation (u : ℂ → ℝ) (c z : ℂ) (η : Circle) :
    radialIntegral u c ((η : ℂ)*z) = radialIntegral u c z := by
  have he : (rotation η) ⁻¹' closedBall (0 : ℂ) 1 = closedBall 0 1 := by
    ext a
    simp only [mem_preimage,mem_closedBall,dist_zero_right,rotation_apply,
      norm_mul,Circle.norm_coe,one_mul]
  have hp := (rotation η).measurePreserving.restrict_preimage (s := closedBall (0 : ℂ) 1) measurableSet_closedBall
  rw [he] at hp
  have hi := hp.integral_comp (rotation η).toHomeomorph.measurableEmbedding
    (fun a : ℂ ↦ u (c+a*z))
  simpa only [radialIntegral,rotation_apply,mul_assoc,mul_left_comm] using hi

lemma radialIntegral_eq_of_norm_eq (u : ℂ → ℝ) (c : ℂ) {z w : ℂ}
    (h : ‖z‖ = ‖w‖) : radialIntegral u c z = radialIntegral u c w := by
  by_cases hw : w=0
  · have hz : z=0 := norm_eq_zero.mp (by simpa [hw] using h)
    simp [hw,hz]
  · let η : Circle := ⟨z/w,by change z/w ∈ sphere (0 : ℂ) 1; rw [mem_sphere_zero_iff_norm]; simp [h,norm_ne_zero_iff.mpr hw]⟩
    have he : (η : ℂ)*w=z := by simp [η,div_mul_cancel₀ _ hw]
    rw [← he]
    exact radialIntegral_rotation u c w η

lemma radialIntegral_pos_radius (u : ℂ → ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    radialIntegral u c (R : ℂ) = (R^2)⁻¹ * ∫ y in closedBall c R, u y := by
  have hs : R • closedBall (0 : ℂ) 1 = closedBall 0 R := by
    simpa [abs_of_nonneg hR.le] using smul_closedBall' hR.ne' (0 : ℂ) 1
  have hi := Measure.setIntegral_comp_smul_of_pos volume
    (fun y : ℂ ↦ u (c+y)) (closedBall 0 1) hR
  rw [hs] at hi
  have ht := (measurePreserving_add_left volume c).setIntegral_image_emb
    (Homeomorph.addLeft c).measurableEmbedding u (closedBall (0 : ℂ) R)
  have he : (fun y : ℂ ↦ c+y) '' closedBall 0 R = closedBall c R := by
    ext y
    constructor
    · rintro ⟨a,ha,rfl⟩
      simpa only [mem_closedBall,dist_zero_right,dist_self_add_left] using ha
    · intro hy
      refine ⟨y-c,?_,by ring⟩
      simpa only [mem_closedBall,dist_zero_right,dist_eq_norm,sub_zero] using hy
  rw [he] at ht
  simp only [Complex.finrank_real_complex,smul_eq_mul] at hi
  simpa only [radialIntegral,Complex.real_smul,mul_comm] using
    hi.trans (congrArg (fun t : ℝ ↦ (R^2)⁻¹*t) ht.symm)

attribute [local instance] Measure.Subtype.measureSpace

lemma complex_closedBall_ae_ball (c : ℂ) (r : ℝ) :
    closedBall c r =ᵐ[volume] ball c r := by
  have h := measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume c r)
  filter_upwards [h] with x hx
  apply propext
  exact ⟨fun hh ↦ lt_of_le_of_ne hh (by simpa only [mem_sphere] using hx),
    fun hx ↦ mem_closedBall.mpr (mem_ball.mp hx).le⟩

lemma compact_integral_continuousOn
    {α : Type u1} [TopologicalSpace α] [CompactSpace α] [T2Space α]
    [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
    {μ : Measure α} [IsFiniteMeasure μ] {c : ℂ} {r : ℝ}
    {F : α → ℂ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ closedBall c r)) :
    ContinuousOn (fun z ↦ ∫ a, F a z ∂μ) (closedBall c r) := by
  have hc : Continuous (fun p : (closedBall c r) × α ↦ F p.2 p.1) :=
    hF.comp_continuous (f := fun p : (closedBall c r) × α ↦ (p.2,(p.1 : ℂ)))
      (by fun_prop) (fun p ↦ ⟨mem_univ _,p.1.property⟩)
  have hi := continuous_parametric_integral_of_continuous (μ := μ)
    (f := fun z : closedBall c r ↦ fun a : α ↦ F a z) hc isCompact_univ
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert hi using 1
  ext z
  simp only [setIntegral_univ,Set.domRestrict_apply]

def radialLinear (a : ℂ) : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ a
@[simp] lemma radialLinear_apply (a z : ℂ) : radialLinear a z=a*z := rfl

def radialFirst (u : ℂ → ℝ) (c : ℂ) (a z : ℂ) : ℂ →L[ℝ] ℝ :=
  (fderiv ℝ u (c+a*z)).comp (radialLinear a)
def radialSecond (u : ℂ → ℝ) (c : ℂ) (a z : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip (radialLinear a)).comp
    ((fderiv ℝ (fderiv ℝ u) (c+a*z)).comp (radialLinear a))

@[simp] lemma radialSecond_apply (u : ℂ → ℝ) (c a z v w : ℂ) :
    radialSecond u c a z v w =
      (fderiv ℝ (fderiv ℝ u) (c+a*z) (a*v)) (a*w) := rfl

local instance realDualComplexGroup : NormedAddCommGroup (ℂ →L[ℝ] ℝ) := inferInstance
local instance realDualComplexSpace : NormedSpace ℝ (ℂ →L[ℝ] ℝ) := inferInstance

def DiskSubharmonicOn (Ω : Set ℂ) (u : ℂ → ℝ) : Prop :=
  UpperSemicontinuousOn u Ω ∧ ∀ x ∈ Ω, ∀ r : ℝ, 0 < r → closedBall x r ⊆ Ω →
    IntegrableOn u (ball x r) ∧
      (volume (ball x r)).toReal * u x ≤ ∫ y in ball x r, u y

end
end QuadricCounterexample

end OAI
end


