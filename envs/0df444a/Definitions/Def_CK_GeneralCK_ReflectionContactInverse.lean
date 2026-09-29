-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionContactInverse
-- name    : CK_GeneralCK_ReflectionContactInverse
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T02:54:41.871555+00:00
-- url     : https://prove2.me/theorems/0f075aee-6db2-4bf0-bc4e-54af3fa0a8a4
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionContactInverse` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionContactInverse` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionContactInverse` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionContactInverse (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionContactInverse.lean)

import Definitions.Def_CK_GeneralCK_Reflection
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data

namespace GeneralCK.Reflection
open Certificates.Reflection Set Filter
open scoped Topology






theorem biasE_eq_log_mul_E {c : ℝ} (hc : -1 < c) (hc' : c < 1) :
    biasE c = Real.log 2*E c := by
  rw [biasE_eq_binEntropy hc hc']
  unfold E H
  field_simp

theorem hasDerivAt_biasE {c : ℝ} (hc : -1 < c) (hc' : c < 1) :
    HasDerivAt biasE (-SmallMean.A c) c := by
  have hd := (hasDerivAt_E hc hc').const_mul (Real.log 2)
  have heq : biasE =ᶠ[𝓝 c] (fun t => Real.log 2*E t) := by
    filter_upwards [Ioo_mem_nhds hc hc'] with t ht
    exact biasE_eq_log_mul_E ht.1 ht.2
  convert! hd.congr_of_eventuallyEq heq using 1
  field_simp

theorem hasDerivAt_biasB {c : ℝ} (hc : -1 < c) (hc' : c < 1) :
    HasDerivAt biasB (c/(1-c^2)) c := by
  have hn : 1-c^2 ≠ 0 := by nlinarith
  have hd := ((((hasDerivAt_id c).pow 2).const_sub 1).log hn).div_const 2
  convert! hd.const_sub (Real.log 2) using 1
  · funext t; simp only [biasB,pow_two,Pi.mul_apply,id_eq]
  · simp only [Pi.pow_apply,id_eq]
    field_simp; ring

theorem biasB_eq_biasE_add {c : ℝ} (hc : -1 < c) (hc' : c < 1) :
    biasB c = biasE c+c*SmallMean.A c := by
  have hm : 1-c ≠ 0 := by linarith
  have hp : 1+c ≠ 0 := by linarith
  unfold biasB biasE SmallMean.A
  rw [show 1-c*c=(1+c)*(1-c) by ring,Real.log_mul hp hm,Real.log_div hp hm]
  ring

theorem hasDerivAt_biasR {c : ℝ} (hc : 0 < c) (hc' : c < 1) :
    HasDerivAt biasR (biasRprime c) c := by
  have hd := (hasDerivAt_biasE (by linarith) hc').div (hasDerivAt_id c) hc.ne'
  convert! hd using 1
  rw [biasRprime,biasB_eq_biasE_add (by linarith) hc']
  simp only [id_eq]
  ring

theorem hasDerivAt_biasRprime {c : ℝ} (hc : 0 < c) (hc' : c < 1) :
    HasDerivAt biasRprime (biasRsecond c) c := by
  have hd := (hasDerivAt_biasB (by linarith) hc').neg.div
    ((hasDerivAt_id c).pow 2) (pow_ne_zero 2 hc.ne')
  convert! hd using 1
  unfold biasRsecond
  simp only [Pi.pow_apply,Pi.neg_apply,id_eq]
  field_simp [hc.ne',show 1-c^2 ≠ 0 by nlinarith]
  ring

theorem biasContact_mem {y : ℝ} (hy : 0 < y) : biasContact y ∈ Ioo (0:ℝ) 1 := by
  have hh := div_pos hy log_two_pos
  have hv := radialContact_pos (by norm_num : (0:ℝ)<1) hh
  have hv' := radialContact_lt_half (by norm_num : (0:ℝ)<1) hh
  unfold biasContact
  constructor <;> linarith

theorem biasR_biasContact {y : ℝ} (hy : 0 < y) : biasR (biasContact y)=y := by
  have hc := biasContact_mem hy
  rw [biasR,biasE_eq_log_mul_E (by linarith [hc.1]) hc.2]
  unfold E biasContact
  rw [show (1-(1-2*radialContact 1 (y/Real.log 2)))/2=radialContact 1 (y/Real.log 2) by ring]
  have he := radialContact_equation (by norm_num : (0:ℝ)<1) (div_pos hy log_two_pos)
  apply (div_eq_iff (show 1-2*radialContact 1 (y/Real.log 2) ≠ 0 from hc.1.ne')).mpr
  field_simp at he
  nlinarith

theorem continuousAt_biasContact {y : ℝ} (hy : 0 < y) : ContinuousAt biasContact y := by
  have ht : ContinuousAt (fun t : ℝ => Real.log 2/t) y := continuousAt_const.div continuousAt_id hy.ne'
  have hc := (continuousAt_radialContact_radius (div_pos log_two_pos hy) (by norm_num : (0:ℝ)<1)).comp ht
  have heq : biasContact =ᶠ[𝓝 y] (fun t => 1-2*radialContact (Real.log 2/t) 1) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    unfold biasContact
    rw [radialContact_normalize_entropy 1 (div_pos (show 0<t from ht) log_two_pos).ne']
    simp only [one_div,inv_div]
  exact (continuousAt_const.sub (continuousAt_const.mul hc)).congr_of_eventuallyEq heq

theorem biasB_pos {c : ℝ} (hc : 0 < c) (hc' : c < 1) : 0 < biasB c := by
  have hlog : Real.log (1-c*c) ≤ 0 := Real.log_nonpos (by nlinarith) (by nlinarith)
  unfold biasB
  linarith [log_two_pos]

theorem hasDerivAt_biasContact {y : ℝ} (hy : 0 < y) :
    HasDerivAt biasContact (-(biasContact y)^2/biasB (biasContact y)) y := by
  have hc := biasContact_mem hy
  have hk := (biasB_pos hc.1 hc.2).ne'
  have hd := (hasDerivAt_biasR hc.1 hc.2).of_local_left_inverse (continuousAt_biasContact hy)
    (show biasRprime (biasContact y) ≠ 0 from div_ne_zero (neg_ne_zero.mpr hk) (pow_ne_zero 2 hc.1.ne')) (by
      filter_upwards [Ioi_mem_nhds hy] with t ht
      exact biasR_biasContact ht)
  convert! hd using 1
  unfold biasRprime
  rw [inv_div,div_neg,neg_div]

theorem hasDerivAt_biasContact_inv {y : ℝ} (hy : 0 < y) :
    HasDerivAt biasContact ((biasRprime (biasContact y))⁻¹) y := by
  convert! hasDerivAt_biasContact hy using 1
  unfold biasRprime
  rw [inv_div,div_neg,neg_div]

theorem hasDerivAt_deriv_biasContact {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv biasContact)
      (-biasRsecond (biasContact y)/(biasRprime (biasContact y))^3) y := by
  have hc := biasContact_mem hy
  have hn : biasRprime (biasContact y) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (biasB_pos hc.1 hc.2).ne') (pow_ne_zero 2 hc.1.ne')
  have hd := ((hasDerivAt_biasRprime hc.1 hc.2).comp y (hasDerivAt_biasContact_inv hy)).inv hn
  have heq : deriv biasContact =ᶠ[𝓝 y] (fun t => (biasRprime (biasContact t))⁻¹) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (hasDerivAt_biasContact_inv ht).deriv
  convert! hd.congr_of_eventuallyEq heq using 1
  simp only [Function.comp_apply]
  field_simp [hn]

theorem deriv2_biasContact {y : ℝ} (hy : 0 < y) :
    deriv (deriv biasContact) y =
      -biasRsecond (biasContact y)/(biasRprime (biasContact y))^3 :=
  (hasDerivAt_deriv_biasContact hy).deriv

end GeneralCK.Reflection


