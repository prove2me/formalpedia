-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionHighBiasEntropy
-- name    : CK_GeneralCK_ReflectionHighBiasEntropy
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:14:03.600034+00:00
-- url     : https://prove2.me/theorems/1b8bd124-f6f3-4bd6-8313-8a2edd292cef
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionHighBiasEntropy` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionHighBiasEntropy` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionHighBiasEntropy` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionHighBiasEntropy (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionHighBiasEntropy.lean)

import Definitions.Def_CK_GeneralCK_ReflectionRegularContact

-- ===== source module GeneralCK.ReflectionHighBiasEntropy =====
section

namespace GeneralCK.Reflection.HighBiasEntropy
open Certificates.Reflection

theorem binEntropy_lower {u : ℝ} (_hu : 0≤u) (hu' : u<1) :
    -u*Real.log u+u*(1-u)≤Real.binEntropy u := by
  have hp : 0<1-u := sub_pos.mpr hu'
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hp) hp.le
  simp only [Real.binEntropy,Real.log_inv]
  nlinarith

theorem binEntropy_upper {u : ℝ} (_hu : 0≤u) (hu' : u<1) :
    Real.binEntropy u≤-u*Real.log u+u := by
  have hp : 0<1-u := sub_pos.mpr hu'
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) hp.le
  have he : (1-u)*(1-(1-u)⁻¹) = -u := by field_simp; ring
  rw [he] at h
  simp only [Real.binEntropy,Real.log_inv]
  nlinarith

/-- The manuscript's entropy-separation sublemma, proved on the larger interval
`(0,1/16]` using elementary logarithm inequalities instead of a numerical gap. -/
theorem entropy_gap {t : ℝ} (ht : 0<t) (ht' : t≤1/16) :
    2*biasE (1-t)/(1-t)<biasE (1-4*t) := by
  have ht1 : t<1 := by linarith
  have he4 : biasE (1-4*t)=Real.binEntropy (2*t) := by
    rw [biasE_eq_binEntropy (by linarith) (by linarith)]
    congr 1
    ring
  have he1 : biasE (1-t)=Real.binEntropy (t/2) := by
    rw [biasE_eq_binEntropy (by linarith) (by linarith)]
    congr 1
    ring
  have h4 := binEntropy_lower (u := 2*t) (by linarith) (by linarith)
  have h1 := binEntropy_upper (u := t/2) (by linarith) (by linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) ht.ne'] at h4
  rw [Real.log_div ht.ne' (by norm_num : (2:ℝ)≠0)] at h1
  have hlog : Real.log t≤ -(4:ℝ)*Real.log 2 := by
    calc
      Real.log t≤Real.log (1/16) := Real.log_le_log ht ht'
      _ = -(4:ℝ)*Real.log 2 := by
        rw [show (1/16:ℝ)=(2^4)⁻¹ by norm_num,Real.log_inv,Real.log_pow]
        norm_num
  have hpositive : 0<t*((1-6*t)*(Real.log 2+1)+4*t^2) := by
    apply mul_pos ht
    exact add_pos_of_pos_of_nonneg
      (mul_pos (by linarith) (by linarith [log_two_pos])) (by positivity)
  have hlogterm : 0≤t*(1-2*t)*(-Real.log t-4*Real.log 2) :=
    mul_nonneg (mul_nonneg ht.le (by linarith)) (by linarith)
  have h4m := mul_le_mul_of_nonneg_right h4 (sub_nonneg.mpr ht1.le)
  rw [he1,he4]
  apply (div_lt_iff₀ (sub_pos.mpr ht1)).mpr
  nlinarith

theorem separation_of_latent_bound {b t : ℝ}
    (hb : 0≤b) (hb' : b≤1) (ht : 0<t) (ht' : t≤1/16)
    (hlatent : biasE b≤2*biasE (1-t)/(1-t)) : 1-b<4*t := by
  by_contra h
  have hb4 : b≤1-4*t := by linarith
  have hmono := biasE_antitone ⟨hb,hb'⟩
    (show 1-4*t ∈ Set.Icc (0:ℝ) 1 from ⟨by linarith,by linarith⟩) hb4
  exact (not_lt_of_ge (hmono.trans hlatent)) (entropy_gap ht ht')

/-- Entropy separation for the actual plus contact. The latent upper bound is
derived here; it is not an assumption of this theorem. -/
theorem actual_plus_contact {a b : ℝ} (ha : 0<a) (ha' : a<1)
    (hb : 0<b) (hb' : b<1)
    (ht : 1-biasContact ((biasE a+biasE b)/(a+b))≤1/16) :
    1-b<4*(1-biasContact ((biasE a+biasE b)/(a+b))) := by
  let y := (biasE a+biasE b)/(a+b)
  have hEa := biasE_pos_wide (by linarith : -1<a) ha'
  have hEb := biasE_pos_wide (by linarith : -1<b) hb'
  have hab : 0<a+b := by linarith
  have hy : 0<y := div_pos (add_pos hEa hEb) hab
  have hc := biasContact_mem hy
  have he : biasE (biasContact y)/biasContact y=y := biasR_biasContact hy
  have hlatent : biasE b≤2*biasE (biasContact y)/biasContact y := by
    calc
      biasE b≤biasE a+biasE b := by linarith
      _ = y*(a+b) := by dsimp [y]; field_simp
      _ ≤ y*2 := mul_le_mul_of_nonneg_left (by linarith) hy.le
      _ = (biasE (biasContact y)/biasContact y)*2 := congrArg (fun x : ℝ => x*2) he.symm
      _ = 2*biasE (biasContact y)/biasContact y := by ring
  have h := separation_of_latent_bound hb.le hb'.le
    (t := 1-biasContact y) (sub_pos.mpr hc.2) ht
    (by simpa only [sub_sub_cancel] using hlatent)
  exact h

/-- The near-contact branch of the manuscript's high-bias split satisfies the
entropy separation uniformly, including contacts arbitrarily close to one. -/
theorem large_partner_separation {a b : ℝ}
    (ha : (999/1000:ℝ)≤a) (ha' : a<1) (hb : (1/2:ℝ)≤b) (hba : b≤a)
    (ht : 1-biasContact ((biasE a+biasE b)/(a+b))<Real.sqrt (1-a)) :
    1-b<4*(1-biasContact ((biasE a+biasE b)/(a+b))) := by
  apply actual_plus_contact (by linarith) ha' (by linarith) (hba.trans_lt ha')
  have hs : Real.sqrt (1-a)≤(1/16:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith
  exact ht.le.trans hs

end GeneralCK.Reflection.HighBiasEntropy

end


