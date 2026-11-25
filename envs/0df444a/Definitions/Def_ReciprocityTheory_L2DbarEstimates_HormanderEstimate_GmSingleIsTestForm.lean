-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_GmSingleIsTestForm
-- name    : ReciprocityTheory_L2DbarEstimates_HormanderEstimate_GmSingleIsTestForm
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T16:26:45.52446+00:00
-- url     : https://prove2.me/theorems/9b69b85e-a4fa-59be-a512-f09d59f12674
-- title:
--   Gm Single Is Test Form
-- statement:
--   Definitions and structural lemmas for Gm Single Is Test Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/GmSingleIsTestForm.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_WeakAdj_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_const_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_isFiniteMeasureOnCompacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
section helpers
variable {M : Type*} [TopologicalSpace M]
theorem gm_cont_of_smoothR (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) : Continuous ph := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hx, he⟩ := hz x
  have hc : IsChart n z e := fun y _ => congrFun he y
  have h := (hph e hc).continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hx))
  have h2 := h.comp (e.continuousAt hx)
  have h3 : ContinuousAt (fun y => (ph y : ℂ)) x := by
    refine h2.congr ?_
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [e.left_inv hy]
  simpa [Function.comp_def] using Complex.continuous_re.continuousAt.comp h3
lemma natCast_le_coe_infty (k : ℕ) : (k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
  first
    | exact WithTop.coe_le_coe.2 le_top
    | exact_mod_cast le_top
    | (norm_cast; exact le_top)
    | simp
theorem gm_exp_ck (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : SmoothR n z ph) (s : ℝ) (k : ℕ) :
    Ck n z k (fun y => (Real.exp (s * ph y) : ℂ)) := by
  intro e he
  have h := hph e he
  have hre : ContDiffOn ℝ ∞ (fun w => ph (e.symm w)) e.target := by
    have := Complex.reCLM.contDiff.comp_contDiffOn h
    simpa [Function.comp_def] using this
  have hmul : ContDiffOn ℝ ∞ (fun w => s * ph (e.symm w)) e.target := contDiffOn_const.mul hre
  have hrexp : ContDiffOn ℝ ∞ (fun w => Real.exp (s * ph (e.symm w))) e.target :=
    Real.contDiff_exp.comp_contDiffOn hmul
  have hexp : ContDiffOn ℝ ∞ (fun w => (Real.exp (s * ph (e.symm w)) : ℂ)) e.target := by
    have := Complex.ofRealCLM.contDiff.comp_contDiffOn hrexp
    simpa [Function.comp_def] using this
  exact hexp.of_le (natCast_le_coe_infty k)
theorem gm_form_continuous {n : ℕ} (f : M → V n) (hf : ∀ k, Continuous fun x => f x k) :
    Continuous f := by
  first
    | exact continuous_pi hf
    | exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hf)
    | (have h1 : Continuous (fun x => WithLp.ofLp (f x)) := continuous_pi hf
       simpa using (PiLp.continuous_toLp 2 _).comp h1)
    | fun_prop
theorem gm_form_hcs {n : ℕ} (f : M → V n) (hf : ∀ k, HasCompactSupport (fun x => f x k)) :
    HasCompactSupport f := by
  refine HasCompactSupport.intro' (K := ⋃ k, tsupport (fun x => f x k))
    (isCompact_iUnion fun k => hf k) (isClosed_iUnion_of_finite fun k => isClosed_tsupport _) ?_
  intro x hx
  simp only [mem_iUnion, not_exists] at hx
  ext k
  first
    | simpa using image_eq_zero_of_notMem_tsupport (hx k)
    | simpa using image_eq_zero_of_nmem_tsupport (hx k)
end helpers
section forms
variable {M : Type*} [TopologicalSpace M]
def gmTestForms (n : ℕ) (z : M → V n) : Submodule ℂ (M → V n) where
  carrier := {f | IsTestForm n z f}
  add_mem' := by
    intro f g hf hg k
    refine ⟨?_, ?_⟩
    · have := Ck.add n z 2 _ _ (hf k).1 (hg k).1
      simpa using this
    · have e : (fun x => (f + g) x k) = (fun x => f x k) + (fun x => g x k) := by
        funext x; simp
      rw [e]; exact (hf k).2.add (hg k).2
  zero_mem' := by
    intro k
    refine ⟨?_, ?_⟩
    · simpa using Ck.const n z 2 0
    · have e : (fun x => (0 : M → V n) x k) = 0 := by
        funext x; simp
      rw [e]; exact HasCompactSupport.zero
  smul_mem' := by
    intro c f hf k
    refine ⟨?_, ?_⟩
    · have := Ck.mul n z 2 _ _ (Ck.const n z 2 c) (hf k).1
      simpa using this
    · have e : (fun x => (c • f) x k) = (fun _ => c) * (fun x => f x k) := by
        funext x; simp
      rw [e]; exact HasCompactSupport.mul_left (hf k).2
lemma continuous_d_of_ck_two {n : ℕ} {z : M → V n} (hz : IsLocalHomeomorph z) {g : M → ℂ}
    (hg : Ck n z 2 g) (j : Fin n) : Continuous (d n z j g) := by
  rw [continuous_iff_continuousAt]
  intro x0
  obtain ⟨e0, hx0, he0⟩ := hz x0
  have hc0 : IsChart n z e0 := fun y _ => congrFun he0 y
  have hloc : ∀ x ∈ e0.source, d n z j g x = wd n j (g ∘ e0.symm) (z x) := by
    intro x hx
    unfold d
    have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨e0, hc0, hx⟩
    rw [dif_pos hex]
    set e := Classical.choose hex with he_def
    have he : IsChart n z e ∧ x ∈ e.source := Classical.choose_spec hex
    have hzx : z x = e x := he.1 he.2
    have hT : Tendsto e.symm (𝓝 (z x)) (𝓝 x) := by
      have := (e.continuousAt_symm (e.map_source he.2)).tendsto
      rwa [e.left_inv he.2, ← hzx] at this
    have hev : (g ∘ e.symm) =ᶠ[𝓝 (z x)] (g ∘ e0.symm) := by
      have h1 : ∀ᶠ w in 𝓝 (z x), e.symm w ∈ e0.source := hT.eventually (e0.open_source.mem_nhds hx)
      have h2 : ∀ᶠ w in 𝓝 (z x), w ∈ e.target := by
        rw [hzx]
        exact e.open_target.mem_nhds (e.map_source he.2)
      filter_upwards [h1, h2] with w hw1 hw2
      have h3 : z (e.symm w) = w := by
        rw [he.1 (e.map_target hw2), e.right_inv hw2]
      have h4 : e0 (e.symm w) = w := by
        rw [← hc0 hw1, h3]
      have h5 : e.symm w = e0.symm w :=
        calc e.symm w = e0.symm (e0 (e.symm w)) := (e0.left_inv hw1).symm
          _ = e0.symm w := by rw [h4]
      simp only [Function.comp_apply, h5]
    unfold wd
    rw [hev.fderiv_eq (𝕜 := ℝ)]
  have hcont : ContinuousAt (fun x => wd n j (g ∘ e0.symm) (z x)) x0 := by
    have hG : ContinuousOn (fun y => fderiv ℝ (g ∘ e0.symm) y) e0.target := by
      first
        | exact (hg e0 hc0).continuousOn_fderiv_of_isOpen e0.open_target (by norm_num)
        | exact (hg e0 hc0).continuousOn_fderiv_of_isOpen e0.open_target (by simp)
    have hzc : ContinuousAt z x0 := by
      rw [he0]
      exact e0.continuousAt hx0
    have hmem : z x0 ∈ e0.target := by
      rw [he0]
      exact e0.map_source hx0
    have hGz : ContinuousAt (fun x => fderiv ℝ (g ∘ e0.symm) (z x)) x0 :=
      (hG.continuousAt (e0.open_target.mem_nhds hmem)).comp hzc
    unfold wd
    have hb1 := hGz.clm_apply (continuousAt_const : ContinuousAt (fun _ : M => bas n j) x0)
    have hb2 := hGz.clm_apply
      (continuousAt_const : ContinuousAt (fun _ : M => Complex.I • bas n j) x0)
    exact (hb1.sub (continuousAt_const.mul hb2)).div_const 2
  refine hcont.congr ?_
  filter_upwards [e0.open_source.mem_nhds hx0] with x hx
  exact (hloc x hx).symm
theorem gm_tstar_cont (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) (f : M → V n) (hf : IsTestForm n z f) :
    Continuous (tstar n z ph ph f) := by
  have hE1 : Ck n z 2 (fun y => (Real.exp (-ph y) : ℂ)) := by
    simpa [neg_one_mul] using gm_exp_ck n z ph hph (-1) 2
  have hph' := gm_cont_of_smoothR n z hz ph hph
  have hsum : Continuous (fun x => ∑ j, d n z j (fun y => (Real.exp (-ph y) : ℂ) * f y j) x) :=
    continuous_finset_sum _ fun j _ => continuous_d_of_ck_two hz (Ck.mul n z 2 _ _ hE1 (hf j).1) j
  have hE : Continuous (fun x => (Real.exp (ph x) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp hph')
  exact (hE.mul hsum).neg
lemma d_eq_zero_of_not_mem_tsupport {n : ℕ} {z : M → V n} {g : M → ℂ} {x : M} (j : Fin n)
    (hx : x ∉ tsupport g) : d n z j g x = 0 := by
  unfold d
  split_ifs with h
  · set e := Classical.choose h with he_def
    have he : IsChart n z e ∧ x ∈ e.source := Classical.choose_spec h
    have hU : g =ᶠ[𝓝 x] 0 := by
      first
        | exact notMem_tsupport_iff_eventuallyEq.1 hx
        | exact not_mem_tsupport_iff_eventuallyEq.1 hx
    have hT : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      have := (e.continuousAt_symm (e.map_source he.2)).tendsto
      rwa [e.left_inv he.2] at this
    have hev : (g ∘ e.symm) =ᶠ[𝓝 (z x)] fun _ => 0 := by
      rw [he.1 he.2]
      exact hT.eventually hU
    have hfd : fderiv ℝ (g ∘ e.symm) (z x) = 0 := by
      rw [hev.fderiv_eq]
      exact fderiv_const_apply _
    simp only [wd, hfd, ContinuousLinearMap.zero_apply, mul_zero, sub_zero, zero_div]
  · rfl
theorem gm_tstar_hcs (n : ℕ) (z : M → V n) (ph : M → ℝ) (f : M → V n) (hf : IsTestForm n z f) :
    HasCompactSupport (tstar n z ph ph f) := by
  refine HasCompactSupport.intro' (K := ⋃ k, tsupport (fun x => f x k))
    (isCompact_iUnion fun k => (hf k).2) (isClosed_iUnion_of_finite fun k => isClosed_tsupport _) ?_
  intro x hx
  simp only [mem_iUnion, not_exists] at hx
  have hzero : ∀ j, d n z j (fun y => (Real.exp (-ph y) : ℂ) * f y j) x = 0 := by
    intro j
    apply d_eq_zero_of_not_mem_tsupport
    intro hmem
    have hsub : Function.support (fun y => (Real.exp (-ph y) : ℂ) * f y j) ⊆
        Function.support (fun y => f y j) := fun y hy hy0 => hy (by simp [hy0])
    exact hx j (closure_mono hsub hmem)
  simp only [tstar]
  rw [Finset.sum_eq_zero (fun j _ => hzero j)]
  simp
lemma ck_one_of_ck_two {n : ℕ} {z : M → V n} {f : M → ℂ} (h : Ck n z 2 f) : Ck n z 1 f := by
  intro e he
  refine (h e he).of_le ?_
  first
    | norm_num
    | exact_mod_cast (show (1 : ℕ) ≤ 2 by norm_num)
    | exact WithTop.coe_le_coe.2 (by norm_num)
theorem gm_tstar_add (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : SmoothR n z ph)
    (f g : M → V n) (hf : IsTestForm n z f) (hg : IsTestForm n z g) (x : M) :
    tstar n z ph ph (f + g) x = tstar n z ph ph f x + tstar n z ph ph g x := by
  have hE : Ck n z 1 (fun y => (Real.exp (-ph y) : ℂ)) := by
    simpa [neg_one_mul] using gm_exp_ck n z ph hph (-1) 1
  have key : ∀ j, d n z j (fun y => (Real.exp (-ph y) : ℂ) * (f + g) y j) x =
      d n z j (fun y => (Real.exp (-ph y) : ℂ) * f y j) x +
        d n z j (fun y => (Real.exp (-ph y) : ℂ) * g y j) x := by
    intro j
    have hf1 : Ck n z 1 (fun y => (Real.exp (-ph y) : ℂ) * f y j) :=
      Ck.mul n z 1 _ _ hE (ck_one_of_ck_two (hf j).1)
    have hg1 : Ck n z 1 (fun y => (Real.exp (-ph y) : ℂ) * g y j) :=
      Ck.mul n z 1 _ _ hE (ck_one_of_ck_two (hg j).1)
    rw [← d_add n z _ _ hf1 hg1 j x]
    congr 1
    funext y
    simp [mul_add]
  simp only [tstar, key, Finset.sum_add_distrib]
  ring
theorem gm_tstar_smul (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : SmoothR n z ph)
    (c : ℂ) (f : M → V n) (hf : IsTestForm n z f) (x : M) :
    tstar n z ph ph (c • f) x = c * tstar n z ph ph f x := by
  have hE : Ck n z 1 (fun y => (Real.exp (-ph y) : ℂ)) := by
    simpa [neg_one_mul] using gm_exp_ck n z ph hph (-1) 1
  have key : ∀ j, d n z j (fun y => (Real.exp (-ph y) : ℂ) * (c • f) y j) x =
      c * d n z j (fun y => (Real.exp (-ph y) : ℂ) * f y j) x := by
    intro j
    rw [← d_const_mul n z c _ (Ck.mul n z 1 _ _ hE (ck_one_of_ck_two (hf j).1)) j x]
    congr 1
    funext y
    first
      | simp [mul_left_comm]
      | (simp <;> ring)
  simp only [tstar, key, ← Finset.mul_sum]
  ring
end forms
section meas
variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
theorem gm_lintegral_wvol {E : Type*} [NormedAddCommGroup E] (n : ℕ) (z : M → V n) (ph : M → ℝ)
    (hph : Measurable ph) (g : M → E) :
    ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂wvol n z ph =
      ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2 * Real.exp (-ph x)) ∂vol n z := by
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-ph x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hph.neg)
  rw [wvol, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [Pi.mul_apply, ← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two, ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
theorem gm_memLp_two_iff {E : Type*} [NormedAddCommGroup E] {μ : Measure M} (g : M → E)
    (hg : AEStronglyMeasurable g μ) :
    MemLp g 2 μ ↔ ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂μ < ⊤ := by
  first
    | (simp only [MemLp, hg, true_and]
       rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
       simp)
    | (rw [MemLp, and_iff_right hg, eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
       simp only [ENNReal.toReal_ofNat]
       rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num)])
end meas
section maps
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
theorem gm_hcs_of {E F : Type*} [Zero E] [Zero F] (t : M → E) (G : M → F) (ht : HasCompactSupport t)
    (h : ∀ x, t x = 0 → G x = 0) : HasCompactSupport G := by
  first
    | exact ht.mono fun x hx h0 => hx (h x h0)
    | exact ht.mono' (closure_mono fun x hx h0 => hx (h x h0))
theorem gm_memLp_tstar (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) (f : M → V n) (hf : IsTestForm n z f) :
    MemLp (tstar n z ph ph f) 2 (wvol n z ph) := by
  haveI := vol_isFiniteMeasureOnCompacts n z hz
  have hc : Continuous (tstar n z ph ph f) := gm_tstar_cont n z hz ph hph f hf
  have hs := gm_tstar_hcs n z ph f hf
  have hph' := gm_cont_of_smoothR n z hz ph hph
  rw [gm_memLp_two_iff _ hc.aestronglyMeasurable, gm_lintegral_wvol n z ph hph'.measurable]
  have hG : Continuous (fun x => ‖tstar n z ph ph f x‖ ^ 2 * Real.exp (-ph x)) :=
    (hc.norm.pow 2).mul (Real.continuous_exp.comp hph'.neg)
  have hGs : HasCompactSupport (fun x => ‖tstar n z ph ph f x‖ ^ 2 * Real.exp (-ph x)) :=
    gm_hcs_of _ _ hs fun x hx => by simp [hx]
  exact (hG.integrable_of_hasCompactSupport hGs (μ := vol n z)).lintegral_lt_top
lemma continuous_of_ck {n : ℕ} {z : M → V n} (hz : IsLocalHomeomorph z) {k : ℕ} {g : M → ℂ}
    (hg : Ck n z k g) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hx, he⟩ := hz x
  have hc : IsChart n z e := fun y _ => congrFun he y
  have h := (hg e hc).continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hx))
  have h2 := h.comp (e.continuousAt hx)
  refine h2.congr ?_
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  simp [e.left_inv hy]
theorem gm_ipV_integrable (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) (v : M → V n) (hv : Continuous v) (f : M → V n)
    (hf : IsTestForm n z f) :
    Integrable (fun x => ⟪v x, f x⟫_ℂ * (Real.exp (-ph x) : ℂ)) (vol n z) := by
  haveI := vol_isFiniteMeasureOnCompacts n z hz
  have hfc : Continuous f := gm_form_continuous f fun k => continuous_of_ck hz (hf k).1
  have hfs : HasCompactSupport f := gm_form_hcs f fun k => (hf k).2
  have hph' : Continuous ph := gm_cont_of_smoothR n z hz ph hph
  have hcont : Continuous (fun x => ⟪v x, f x⟫_ℂ * (Real.exp (-ph x) : ℂ)) := by
    have h1 : Continuous (fun x => ⟪v x, f x⟫_ℂ) := hv.inner hfc
    have h2 : Continuous (fun x => (Real.exp (-ph x) : ℂ)) :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp hph'.neg)
    exact h1.mul h2
  exact hcont.integrable_of_hasCompactSupport (gm_hcs_of f _ hfs fun x hx => by simp [hx])
theorem gm_ipV_add (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) (v : M → V n) (hv : Continuous v) (f g : M → V n)
    (hf : IsTestForm n z f) (hg : IsTestForm n z g) :
    ipV n z v (f + g) ph = ipV n z v f ph + ipV n z v g ph := by
  have h1 := gm_ipV_integrable n z hz ph hph v hv f hf
  have h2 := gm_ipV_integrable n z hz ph hph v hv g hg
  simp only [ipV, Pi.add_apply, inner_add_right, add_mul]
  exact integral_add h1 h2
theorem gm_ipV_smul (n : ℕ) (z : M → V n) (ph : M → ℝ) (v : M → V n) (c : ℂ) (f : M → V n) :
    ipV n z v (c • f) ph = c * ipV n z v f ph := by
  simp only [ipV, Pi.smul_apply, inner_smul_right, mul_assoc]
  first
    | exact integral_const_mul c _
    | exact integral_mul_left c _
def gmTheta (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) : gmTestForms n z →ₗ[ℂ] Lp ℂ 2 (wvol n z ph) where
  toFun f := (gm_memLp_tstar n z hz ph hph f f.2).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _
      (Eventually.of_forall fun x => gm_tstar_add n z ph hph f g f.2 g.2 x)
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => gm_tstar_smul n z ph hph c f f.2 x)
def gmEll (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) (v : M → V n) (hv : Continuous v) : gmTestForms n z →ₗ[ℂ] ℂ where
  toFun f := ipV n z v f ph
  map_add' f g := gm_ipV_add n z hz ph hph v hv f g f.2 g.2
  map_smul' c f := by
    rw [RingHom.id_apply, smul_eq_mul]
    exact gm_ipV_smul n z ph v c f
def gmSingle {n : ℕ} (ph : M → ℝ) (φ : M → ℂ) (j : Fin n) : M → V n :=
  fun y => EuclideanSpace.single j ((Real.exp (ph y) : ℂ) * conj (φ y))
end maps
section loc
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
end loc
end
end ReciprocityTheory.L2DbarEstimates.F


