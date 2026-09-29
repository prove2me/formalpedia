-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionHighBiasLargeAlgebra
-- name    : CK_GeneralCK_ReflectionHighBiasLargeAlgebra
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T10:39:08.519108+00:00
-- url     : https://prove2.me/theorems/184eb5b9-7857-4e19-b322-65768b0c6ee9
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionHighBiasLargeAlgebra` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionHighBiasLargeAlgebra` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionHighBiasLargeAlgebra` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionHighBiasLargeAlgebra (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionHighBiasLargeAlgebra.lean)

import Definitions.Def_CK_GeneralCK_ReflectionHighBiasCore
import Definitions.Def_CK_GeneralCK_Certificates_MixedConstants

-- ===== source module GeneralCK.ReflectionHighBiasLargeAlgebra =====
section

namespace GeneralCK.Reflection.HighBiasLarge
open Certificates.Reflection SmallRatio
noncomputable section

def plusContact (a b : ℝ) : ℝ := biasContact ((biasE a+biasE b)/(a+b))
def Qtail (a c : ℝ) : ℝ :=
  ((1-a)/(1-c))*(1+(SmallMean.A a-SmallMean.A c)/biasB c)
def V1 (a b c e : ℝ) : ℝ :=
  (1-a)^2*K c e*(biasE c+c*SmallMean.A a)^2/(a^3*b)
def V2 (a b c : ℝ) : ℝ :=
  (1-a)^2*M c/((1-a^2)*(a^3*b))

theorem plus_contact_mem {a b : ℝ} (hb : 0<b) (hba : b≤a) (ha : a<1) :
    Bounds b a (plusContact a b) := by
  have ha0 : 0<a := hb.trans_le hba
  have hb1 : b<1 := hba.trans_lt ha
  have hEa := biasE_pos_wide (by linarith : -1<a) ha
  have hEb := biasE_pos_wide (by linarith : -1<b) hb1
  have hmono := biasE_antitone ⟨hb.le,hb1.le⟩ ⟨ha0.le,ha.le⟩ hba
  have hcross : b*biasE a ≤ a*biasE b :=
    (mul_le_mul_of_nonneg_left hmono hb.le).trans (mul_le_mul_of_nonneg_right hba hEb.le)
  have hab : 0<a+b := add_pos ha0 hb
  have hy := div_pos (add_pos hEa hEb) hab
  have hc := biasContact_mem hy
  have heq := (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  apply contact_bracket hc.1.le hc.2.le hb.le ha.le hba hy heq
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hab).mpr
    nlinarith
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hab).mpr
    nlinarith

theorem plus_contact_equation {a b : ℝ} (hb : 0<b) (hba : b≤a) (ha : a<1) :
    2*((biasE a+biasE b)/2)*plusContact a b = (a+b)*biasE (plusContact a b) := by
  have ha0 := hb.trans_le hba
  have hEa := biasE_pos_wide (by linarith : -1<a) ha
  have hEb := biasE_pos_wide (by linarith : -1<b) (hba.trans_lt ha)
  have hab := add_pos ha0 hb
  have hy := div_pos (add_pos hEa hEb) hab
  have hc := biasContact_mem hy
  have heq := (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  dsimp only [plusContact]
  field_simp [hab.ne'] at heq ⊢
  nlinarith

theorem A_mono {c a : ℝ} (hc : 0≤c) (hca : c≤a) (ha : a<1) :
    SmallMean.A c≤SmallMean.A a := by
  have hc1 : c<1 := hca.trans_lt ha
  have hp : 0<(1+c)/(1-c) := div_pos (by linarith) (by linarith)
  have hratio : (1+c)/(1-c)≤(1+a)/(1-a) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  exact div_le_div_of_nonneg_right (Real.log_le_log hp hratio) (by norm_num : (0:ℝ)≤2)

theorem biasS_nonneg {a c e : ℝ} (ha : 0<a) (ha1 : a<1)
    (hc : 0<c) (hc1 : c<1) (he : 0<e) : 0≤biasS c a e := by
  have hE := biasE_pos_wide (by linarith : -1<c) hc1
  have hB := biasB_pos hc hc1
  have hgap : 0<1-c^2 := by nlinarith
  have haGap : 0<1-a^2 := by nlinarith
  have hlog : Real.log (1-c*c)≤0 := Real.log_nonpos (by nlinarith) (by nlinarith)
  have hBge : Real.log 2≤biasB c := by unfold biasB; linarith
  have hfactor : 0≤2*biasB c-c^2 := by
    have hL := Certificates.Mixed.log_two_gt_69
    nlinarith
  have hK : 0≤K c e := by unfold K; positivity
  have hM : 0≤M c := by unfold M; positivity
  rw [biasS_factor]
  exact add_nonneg (mul_nonneg hK (sq_nonneg _)) (mul_nonneg (by positivity) hM)

theorem scaled_secant_eq (a b c e : ℝ) :
    (1-a)^2*biasS c a e/(a^3*b) = V1 a b c e+V2 a b c := by
  rw [biasS_factor]
  simp only [V1,V2,div_eq_mul_inv,mul_inv_rev]
  ring

theorem V1_eliminate_entropy {a b c e : ℝ} (ha : 0<a) (hb : 0<b)
    (hc : 0<c) (hc1 : c<1) (_he : 0<e)
    (heq : 2*e*c=(a+b)*biasE c) :
    V1 a b c e =
      (1-a)^2*(c*(2*biasB c-c^2)*(biasE c+c*SmallMean.A a)^2)/
        (a^3*b*(a+b)*(1-c^2)^2*(biasB c)^3) := by
  have hE := biasE_pos_wide (by linarith : -1<c) hc1
  have hB := biasB_pos hc hc1
  have hgap : 0<1-c^2 := by nlinarith
  have hab := add_pos ha hb
  have he' : e=(a+b)*biasE c/(2*c) := by apply (eq_div_iff (by positivity)).mpr; nlinarith
  rw [he']
  unfold V1 K
  field_simp [ha.ne',hb.ne',hc.ne',hE.ne',hB.ne',hgap.ne',hab.ne']

theorem V1_upper {a b c e : ℝ} (ha : 0<a) (ha1 : a<1) (hb : 0<b)
    (hc : 0<c) (hca : c≤a) (he : 0<e)
    (heq : 2*e*c=(a+b)*biasE c) :
    V1 a b c e ≤ 2*(Qtail a c)^2/(a^3*b*(a+b)*(2-(1-c))^2) := by
  have hc1 := hca.trans_lt ha1
  have hE := biasE_pos_wide (by linarith : -1<c) hc1
  have hB := biasB_pos hc hc1
  have hgap : 0<1-c^2 := by nlinarith
  have hAc := A_mono hc.le hca ha1
  have hAa : 0≤SmallMean.A a := ha.le.trans (SmallMean.A_lower ha.le ha1)
  have hX : 0≤biasE c+c*SmallMean.A a := by positivity
  have hY : 0≤biasB c+(SmallMean.A a-SmallMean.A c) := by linarith
  have hXY : biasE c+c*SmallMean.A a≤biasB c+(SmallMean.A a-SmallMean.A c) := by
    rw [biasB_eq_biasE_add (by linarith : -1<c) hc1]
    nlinarith [mul_nonneg (show 0≤1-c by linarith) (sub_nonneg.mpr hAc)]
  have hsq := (sq_le_sq₀ hX hY).mpr hXY
  have hfac : c*(2*biasB c-c^2)≤2*biasB c := by
    have hcube : 0≤c^3 := pow_nonneg hc.le 3
    nlinarith [mul_nonneg (show 0≤1-c by linarith) hB.le]
  have hn := (mul_le_mul_of_nonneg_right hfac (sq_nonneg (biasE c+c*SmallMean.A a))).trans
    (mul_le_mul_of_nonneg_left hsq (by positivity : 0≤2*biasB c))
  rw [V1_eliminate_entropy ha hb hc hc1 he heq]
  calc
    _ ≤ (1-a)^2*(2*biasB c*(biasB c+(SmallMean.A a-SmallMean.A c))^2)/
        (a^3*b*(a+b)*(1-c^2)^2*(biasB c)^3) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (sq_nonneg _)) (by positivity)
    _ = _ := by
      unfold Qtail
      have ht : 1-c≠0 := by linarith
      have hp : 1+c≠0 := by linarith
      rw [show 1-c^2=(1-c)*(1+c) by ring,show 2-(1-c)=1+c by ring]
      field_simp [ha.ne',hb.ne',hB.ne',ht,hp, (add_pos ha hb).ne']

theorem V2_upper {a b c : ℝ} (ha : 0<a) (ha1 : a<1) (hb : 0<b)
    (hc : 0<c) (hc1 : c<1) :
    V2 a b c ≤ ((1-a)/(1-c))/(a^3*b*(2-(1-a))*(2-(1-c))*biasB c) := by
  have hB := biasB_pos hc hc1
  have hgap : 1-c^2≠0 := by nlinarith
  have haGap : 1-a^2≠0 := by nlinarith
  have hr : 1-a≠0 := by linarith
  have ht : 1-c≠0 := by linarith
  have hpa : 0<2-(1-a) := by linarith
  have hpc : 0<2-(1-c) := by linarith
  have heq : V2 a b c = c^2*(((1-a)/(1-c))/(a^3*b*(2-(1-a))*(2-(1-c))*biasB c)) := by
    unfold V2 M
    rw [show 2-(1-a)=1+a by ring,show 2-(1-c)=1+c by ring,
      show 1-a^2=(1-a)*(1+a) by ring,show 1-c^2=(1-c)*(1+c) by ring]
    field_simp [ha.ne',hb.ne',hB.ne',hgap,haGap,hr,ht]
  rw [heq]
  have hsq : c^2≤1 := by nlinarith
  exact (mul_le_mul_of_nonneg_right hsq (by positivity)).trans_eq (one_mul _)

theorem scaled_base_lower {a b : ℝ} (ha : 0<a) (ha1 : a<1) (hb : 0<b) :
    (1/2:ℝ)≤(1-a)^2*(2*a*b/(1-a^2)^2)/(a^3*b) := by
  have hgap : 1-a^2≠0 := by nlinarith
  have hr : 1-a≠0 := by linarith
  have hp : 0<1+a := by linarith
  have heq : (1-a)^2*(2*a*b/(1-a^2)^2)/(a^3*b)=2/(a^2*(1+a)^2) := by
    rw [show 1-a^2=(1-a)*(1+a) by ring]
    field_simp [ha.ne',hb.ne',hr,hp.ne']
  rw [heq]
  apply (le_div_iff₀ (by positivity : 0<a^2*(1+a)^2)).mpr
  have hs : a^2≤1 := by nlinarith
  have ht : (1+a)^2≤4 := by nlinarith
  have h := mul_le_mul hs ht (sq_nonneg _) (by norm_num : (0:ℝ)≤1)
  nlinarith

theorem minus_secant_nonneg {a b : ℝ} (hb : 0<b) (hba : b<a) (ha : a<1) :
    0≤biasS (biasContact ((biasE a+biasE b)/(a-b))) a ((biasE a+biasE b)/2) := by
  have ha0 := hb.trans hba
  have hEa := biasE_pos_wide (by linarith : -1<a) ha
  have hEb := biasE_pos_wide (by linarith : -1<b) (hba.trans ha)
  have he : 0<(biasE a+biasE b)/2 := by positivity
  have hc := biasContact_mem (div_pos (add_pos hEa hEb) (sub_pos.mpr hba))
  exact biasS_nonneg ha0 ha hc.1 hc.2 he

/-- The remaining numerical tail bound implies actual curvature positivity;
the minus radius, entropy units, and normalization are all discharged here. -/
theorem curvature_pos_of_scaled_plus_lt {a b : ℝ} (hb : 0<b) (hba : b<a) (ha : a<1)
    (hplus : (1-a)^2*biasS (plusContact a b) a ((biasE a+biasE b)/2)/(a^3*b)<1/2) :
    0<curvature a b := by
  have ha0 : 0<a := hb.trans hba
  have hz : 0<b/a := div_pos hb ha0
  have hz1 : b/a<1 := (div_lt_one ha0).mpr hba
  have hab : a*(b/a)=b := by field_simp
  have hm : a*(1-b/a)/2=(a-b)/2 := by field_simp
  have hp : a*(1+b/a)/2=(a+b)/2 := by field_simp
  have hrm : ((biasE a+biasE b)/2)/((a-b)/2)=(biasE a+biasE b)/(a-b) := by
    field_simp [(sub_pos.mpr hba).ne']
  have hrp : ((biasE a+biasE b)/2)/((a+b)/2)=(biasE a+biasE b)/(a+b) := by
    field_simp [(add_pos ha0 hb).ne']
  have hnorm : Certificates.ReflectionExpression.normalizedValue a (b/a) =
      (2*a*b/(1-a^2)^2+
        biasS (biasContact ((biasE a+biasE b)/(a-b))) a ((biasE a+biasE b)/2)-
        biasS (plusContact a b) a ((biasE a+biasE b)/2))/(a^3*b) := by
    simp only [Certificates.ReflectionExpression.normalizedValue,hab,hm,hp,hrm,hrp,plusContact]
  have hden : 0<a^3*b := mul_pos (pow_pos ha0 3) hb
  have hr : 0<(1-a)^2 := sq_pos_of_pos (sub_pos.mpr ha)
  have hlt := hplus.trans_le (scaled_base_lower ha0 ha hb)
  have hsplus : biasS (plusContact a b) a ((biasE a+biasE b)/2)<2*a*b/(1-a^2)^2 :=
    (mul_lt_mul_iff_right₀ hr).mp ((div_lt_div_iff_of_pos_right hden).mp hlt)
  have hsminus := minus_secant_nonneg hb hba ha
  have hn : 0<Certificates.ReflectionExpression.normalizedValue a (b/a) := by
    rw [hnorm]
    exact div_pos (by linarith) hden
  simpa only [hab] using curvature_pos_of_normalizedValue_pos ha0 ha hz hz1 hn

theorem curvature_pos_of_V_lt {a b : ℝ} (hb : 0<b) (hba : b<a) (ha : a<1)
    (hV : V1 a b (plusContact a b) ((biasE a+biasE b)/2)+V2 a b (plusContact a b)<1/2) :
    0<curvature a b := by
  apply curvature_pos_of_scaled_plus_lt hb hba ha
  rw [scaled_secant_eq]
  exact hV

end
end GeneralCK.Reflection.HighBiasLarge

end


