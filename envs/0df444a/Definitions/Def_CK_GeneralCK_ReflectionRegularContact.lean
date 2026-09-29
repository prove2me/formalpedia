-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionRegularContact
-- name    : CK_GeneralCK_ReflectionRegularContact
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:04:02.236043+00:00
-- url     : https://prove2.me/theorems/d4500f6a-ff25-4458-8f3f-c34900a1bb2a
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionRegularContact` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionRegularContact` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionRegularContact` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionRegularContact (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionRegularContact.lean)

import Definitions.Def_CK_GeneralCK_ReflectionContactInverse
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface

namespace GeneralCK.Reflection
open Certificates.Reflection Set Filter
open scoped Topology








theorem regularContact_pos_eq {τ : ℝ} (hτ : 0<τ) :
    regularContact τ=biasContact τ⁻¹ := by simp [regularContact,hτ,hτ.ne']

theorem regularContact_neg_eq {τ : ℝ} (hτ : τ<0) :
    regularContact τ= -biasContact (-τ)⁻¹ := by
  simp [regularContact,hτ.ne,not_lt.mpr hτ.le]

theorem biasE_neg (c : ℝ) : biasE (-c)=biasE c := by
  unfold biasE
  rw [show 1+(-c)=1-c by ring,show 1-(-c)=1+c by ring]
  ring

theorem regularContact_mem (τ : ℝ) : regularContact τ ∈ Ioo (-1:ℝ) 1 := by
  rcases lt_trichotomy τ 0 with hτ | hτ | hτ
  · rw [regularContact_neg_eq hτ]
    have h := biasContact_mem (inv_pos.mpr (neg_pos.mpr hτ))
    constructor <;> linarith [h.1,h.2]
  · subst τ; norm_num
  · rw [regularContact_pos_eq hτ]
    have h := biasContact_mem (inv_pos.mpr hτ)
    exact ⟨by linarith [h.1],h.2⟩

theorem biasE_pos_wide {c : ℝ} (hc : -1<c) (hc' : c<1) : 0<biasE c := by
  rw [biasE_eq_binEntropy hc hc']
  exact Real.binEntropy_pos (by linarith) (by linarith)

theorem biasE_le_log_two_wide {c : ℝ} (hc : -1<c) (hc' : c<1) : biasE c≤Real.log 2 := by
  rw [biasE_eq_binEntropy hc hc']
  exact Real.binEntropy_le_log_two

theorem biasB_pos_wide {c : ℝ} (hc : -1<c) (hc' : c<1) : 0<biasB c := by
  have hlog := Real.log_nonpos (show 0≤1-c*c by nlinarith) (show 1-c*c≤1 by nlinarith)
  unfold biasB
  linarith [log_two_pos]

private theorem positive_contact_equation {τ : ℝ} (hτ : 0<τ) :
    biasContact τ⁻¹ = τ*biasE (biasContact τ⁻¹) := by
  have hc := biasContact_mem (inv_pos.mpr hτ)
  have h := biasR_biasContact (inv_pos.mpr hτ)
  unfold biasR at h
  have he := (div_eq_iff hc.1.ne').mp h
  rw [he]
  field_simp

/-- The nonsingular implicit equation holds on both sides of zero and at zero. -/
theorem regularContact_equation (τ : ℝ) : regularContact τ=τ*biasE (regularContact τ) := by
  rcases lt_trichotomy τ 0 with hτ | hτ | hτ
  · rw [regularContact_neg_eq hτ,biasE_neg]
    have h := positive_contact_equation (neg_pos.mpr hτ)
    linarith
  · subst τ; simp
  · rw [regularContact_pos_eq hτ]
    exact positive_contact_equation hτ

theorem abs_regularContact_le (τ : ℝ) : |regularContact τ| ≤ |τ| * Real.log 2 := by
  have hc := regularContact_mem τ
  have he := biasE_pos_wide hc.1 hc.2
  calc
    |regularContact τ| = |τ| * biasE (regularContact τ) := by
      conv_lhs => rw [regularContact_equation τ,abs_mul,abs_of_pos he]
    _ ≤ _ := mul_le_mul_of_nonneg_left (biasE_le_log_two_wide hc.1 hc.2) (abs_nonneg τ)

theorem continuousAt_regularContact_zero : ContinuousAt regularContact 0 := by
  rw [ContinuousAt,regularContact_zero]
  have ht : Tendsto (fun τ : ℝ => |τ| * Real.log 2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.continuousAt.tendsto.mul_const (Real.log 2) :
      Tendsto (fun τ : ℝ => |τ| * Real.log 2) (𝓝 0) (𝓝 (|0| * Real.log 2)))
  have hl : Tendsto (fun τ : ℝ => -(|τ| * Real.log 2)) (𝓝 0) (𝓝 0) := by simpa using ht.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl ht
    (fun τ => (abs_le.mp (abs_regularContact_le τ)).1)
    (fun τ => (abs_le.mp (abs_regularContact_le τ)).2)

theorem continuousAt_regularContact (τ : ℝ) : ContinuousAt regularContact τ := by
  rcases lt_trichotomy τ 0 with hτ | hτ | hτ
  · have hi : ContinuousAt (fun s : ℝ => (-s)⁻¹) τ :=
      (continuousAt_id : ContinuousAt (fun s : ℝ => s) τ).neg.inv₀ (neg_ne_zero.mpr hτ.ne)
    have hh := ((continuousAt_biasContact (inv_pos.mpr (neg_pos.mpr hτ))).comp
      (f := fun s : ℝ => (-s)⁻¹) hi).neg
    apply hh.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hτ] with s hs
    exact regularContact_neg_eq hs
  · subst τ; exact continuousAt_regularContact_zero
  · have hi : ContinuousAt (fun s : ℝ => s⁻¹) τ :=
      (continuousAt_id : ContinuousAt (fun s : ℝ => s) τ).inv₀ hτ.ne'
    have hh := (continuousAt_biasContact (inv_pos.mpr hτ)).comp hi
    apply hh.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hτ] with s hs
    exact regularContact_pos_eq hs

noncomputable def regularRatio (c : ℝ) : ℝ := c/biasE c

theorem regularRatio_regularContact (τ : ℝ) : regularRatio (regularContact τ)=τ := by
  have hc := regularContact_mem τ
  exact (div_eq_iff (biasE_pos_wide hc.1 hc.2).ne').mpr (regularContact_equation τ)

theorem hasDerivAt_regularRatio {c : ℝ} (hc : -1<c) (hc' : c<1) :
    HasDerivAt regularRatio (biasB c/(biasE c)^2) c := by
  have he := biasE_pos_wide hc hc'
  convert! (hasDerivAt_id c).div (hasDerivAt_biasE hc hc') he.ne' using 1
  rw [biasB_eq_biasE_add hc hc']
  simp only [id_eq]
  ring

/-- Unrestricted derivative, including the regular contact's zero extension. -/
theorem hasDerivAt_regularContact (τ : ℝ) :
    HasDerivAt regularContact ((biasE (regularContact τ))^2/biasB (regularContact τ)) τ := by
  have hc := regularContact_mem τ
  have he := (biasE_pos_wide hc.1 hc.2).ne'
  have hb := (biasB_pos_wide hc.1 hc.2).ne'
  have hd := (hasDerivAt_regularRatio hc.1 hc.2).of_local_left_inverse
    (continuousAt_regularContact τ) (div_ne_zero hb (pow_ne_zero 2 he))
    (Filter.Eventually.of_forall regularRatio_regularContact)
  simpa only [inv_div] using hd









/-- The regular inverse has an unrestricted second derivative even at contact zero. -/
theorem hasDerivAt_regularContactFirst (τ : ℝ) :
    HasDerivAt regularContactFirst (regularContactSecond τ) τ := by
  have hc := regularContact_mem τ
  have hb := (biasB_pos_wide hc.1 hc.2).ne'
  have hg : 1-(regularContact τ)^2 ≠ 0 := by nlinarith [hc.1,hc.2]
  have hd := hasDerivAt_regularContact τ
  have he := (hasDerivAt_biasE hc.1 hc.2).comp τ hd
  have hB := (hasDerivAt_biasB hc.1 hc.2).comp τ hd
  have hh := (he.pow 2).div hB hb
  convert! hh using 1
  norm_num only [regularContactSecond,Pi.pow_apply,Function.comp_apply]
  field_simp [hb,hg]

theorem hasDerivAt_deriv_regularContact (τ : ℝ) :
    HasDerivAt (deriv regularContact) (regularContactSecond τ) τ := by
  apply (hasDerivAt_regularContactFirst τ).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => (hasDerivAt_regularContact t).deriv)









theorem hasDerivAt_regularContact_zero : HasDerivAt regularContact (Real.log 2) 0 := by
  have h : HasDerivAt regularContact (regularContactFirst 0) 0 := hasDerivAt_regularContact 0
  simpa only [regularContactFirst_zero] using h

theorem hasDerivAt_deriv_regularContact_zero : HasDerivAt (deriv regularContact) 0 0 := by
  simpa only [regularContactSecond_zero] using hasDerivAt_deriv_regularContact 0

end GeneralCK.Reflection


