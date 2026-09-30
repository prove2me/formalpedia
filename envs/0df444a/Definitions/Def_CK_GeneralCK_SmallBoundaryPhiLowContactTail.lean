-- Prove2me | Definitions.Def_CK_GeneralCK_SmallBoundaryPhiLowContactTail
-- name    : CK_GeneralCK_SmallBoundaryPhiLowContactTail
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:41:59.879755+00:00
-- url     : https://prove2.me/theorems/d710cbde-ae9f-4486-9b7f-e30c3ab8db18
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallBoundaryPhiLowContactTail` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallBoundaryPhiLowContactTail` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallBoundaryPhiLowContactTail` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallBoundaryPhiLowContactTail (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallBoundaryPhiLowContactTail.lean)

import Definitions.Def_CK_GeneralCK_SmallBoundaryPhiContactCertificate
import Definitions.Def_CK_GeneralCK_PsiNormalizedLowEntropy

-- ===== source module GeneralCK.SmallBoundaryPhiLowContactTail =====
section

namespace GeneralCK.SmallBoundaryPhiSchur

open Set
open SmallMeanPhiCutoff

set_option maxHeartbeats 800000

/-- Shared with the compact-contact lane; the seam belongs to its core. -/
noncomputable def tailDelta : ℝ := 1 / 10000000000000000000000

noncomputable def comparisonPotential (t : ℝ) : ℝ :=
  naturalA t - (1/10)*Real.log (H t/(1-2*t))

/-- A one-variable, bounded-logarithm replacement for the original tail
determinant. These scalar inequalities remain explicit premises here. -/
structure TailScalarBounds : Prop where
  lowerA : ∀ t, 0 < t → t ≤ 2*tailDelta → 99/100 ≤ naturalA t
  upperA : ∀ t, 0 < t → t ≤ 2*tailDelta → naturalA t ≤ 11/10
  upperK : ∀ t, 0 < t → t ≤ 2*tailDelta → naturalK t ≤ 11/10
  defect : ∀ t, 0 < t → t ≤ 2*tailDelta → naturalA t-naturalK t ≤ (2/5)*t
  comparison : AntitoneOn comparisonPotential (Ioc 0 (2*tailDelta))

private theorem log_two_bounds : (69/100:ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 7/10 := by
  have h := Certificates.PilotData.log_two
  norm_num at h
  constructor <;> linarith

theorem entropy_doubling_small {q : ℝ} (hq : 0 < q) (hqs : q ≤ retainedCutoff) :
    H q ≤ (3/4)*H (2*q) := by
  have hq1 : q < 1 := by dsimp [retainedCutoff] at hqs; linarith
  have h2q : 0 < 2*q := by positivity
  have h2q1 : 2*q < 1 := by dsimp [retainedCutoff] at hqs; linarith
  have hi : (2:ℝ)^6 ≤ q⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hq).mpr
    norm_num
    dsimp [retainedCutoff] at hqs
    linarith
  have hl := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)^6) hi
  rw [Real.log_pow] at hl
  norm_num at hl
  have hx : 4 ≤ Real.log q⁻¹ := by
    rw [Real.log_inv]
    linarith [log_two_bounds.1]
  have hu := H_mul_log_two_le hq hq1
  have hd := H_mul_log_two_ge h2q h2q1
  have heq : Real.log (2*q)⁻¹ = Real.log q⁻¹-Real.log 2 := by
    rw [show (2*q)⁻¹=q⁻¹/2 by field_simp [hq.ne'],
      Real.log_div (inv_ne_zero hq.ne') (by norm_num)]
  rw [heq] at hd
  have hxq := mul_le_mul_of_nonneg_left hx hq.le
  have hLq := mul_le_mul_of_nonneg_left log_two_bounds.2 hq.le
  have hsmall : q^2 ≤ q/10000 := by
    dsimp [retainedCutoff] at hqs
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hqs)]
  apply (mul_le_mul_iff_left₀ log_two_pos).mp
  nlinarith only [hu, hd, hxq, hLq, hsmall, hq]

/-- A uniform contact ratio bound on the entire SB-1 physical domain. -/
theorem contact_le_twice_inverse {m h : ℝ} (hp : (m,h) ∈ domain) :
    radialContact (1-2*m) h ≤ 2*entropyInverse h := by
  obtain ⟨hm, hm', hh, hh'⟩ := domain_bounds hp
  obtain ⟨hq, hqv, hvm⟩ := contact_brackets hp
  have hqm := hqv.trans hvm
  have hqs := hqm.trans hp.2.1
  have h2q : 2*entropyInverse h ≤ 1/2 := by
    dsimp [retainedCutoff] at hqs
    linarith
  have hs : 0 < 1-2*m := by linarith
  have hslo : 3/4 ≤ 1-2*m := by
    have hu := hp.2.1
    dsimp [retainedCutoff] at hu
    linarith
  have hHd := entropy_doubling_small hq hqs
  rw [(entropyInverse_spec hh.le hh'.le).2.2] at hHd
  apply (radialContact_le_iff hs hh (by positivity) h2q).mpr
  have hH : 0 ≤ H (2*entropyInverse h) :=
    H_nonneg (by positivity) (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hslo hH
  have hqmul : h*(1-2*(2*entropyInverse h)) ≤ h := by
    nlinarith [mul_nonneg hh.le hq.le]
  exact hqmul.trans (hHd.trans hmul)

theorem tail_contact_bound {m h : ℝ} (hp : (m,h) ∈ domain)
    (hq : entropyInverse h < tailDelta) :
    radialContact (1-2*m) h < 2*tailDelta :=
  (contact_le_twice_inverse hp).trans_lt (by linarith)

theorem comparison_increment_bound (hb : TailScalarBounds)
    {m h : ℝ} (hp : (m,h) ∈ domain) (hqtail : entropyInverse h < tailDelta) :
    naturalA (radialContact (1-2*m) h)-naturalA (entropyInverse h) ≤ (1-(1-2*m))/9 := by
  let q := entropyInverse h
  let v := radialContact (1-2*m) h
  let s := 1-2*m
  obtain ⟨hm, hm', hh, hh'⟩ := domain_bounds hp
  obtain ⟨hq, hqv, hvm⟩ := contact_brackets hp
  have hv : 0 < v := hq.trans_le hqv
  have hv' : v < 1/2 := hvm.trans_lt hm'
  have hq' : q < 1/2 := hqv.trans_lt hv'
  have hvsmall : v ≤ 2*tailDelta := (tail_contact_bound hp hqtail).le
  have hqsmall : q ≤ 2*tailDelta := hqv.trans hvsmall
  have hs : 0 < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hs9 : 9/10 ≤ s := by
    have hu := hp.2.1
    dsimp [retainedCutoff] at hu
    dsimp [s]
    linarith
  have hHq : 0 < H q := H_pos hq (by linarith)
  have hHv : 0 < H v := H_pos hv (by linarith)
  have heq : s*H v=H q*(1-2*v) := by
    rw [(entropyInverse_spec hh.le hh'.le).2.2]
    exact radialContact_equation hs hh
  have hratio : (H v/(1-2*v))/(H q/(1-2*q))=(1-2*q)/s := by
    apply (div_eq_iff (ne_of_gt (div_pos hHq (by linarith)))).mpr
    apply (div_eq_iff (by linarith : 1-2*v ≠ 0)).mpr
    field_simp [hs.ne', show 1-2*q ≠ 0 by linarith]
    nlinarith only [heq]
  have hant := hb.comparison ⟨hq,hqsmall⟩ ⟨hv,hvsmall⟩ hqv
  dsimp [comparisonPotential] at hant
  have hld : Real.log (H v/(1-2*v))-Real.log (H q/(1-2*q)) =
      Real.log ((1-2*q)/s) := by
    rw [← Real.log_div (ne_of_gt (div_pos hHv (by linarith)))
      (ne_of_gt (div_pos hHq (by linarith))), hratio]
  have hlog := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < 1-2*q) hs)
  have hinc : naturalA v-naturalA q ≤ (1/10)*(((1-2*q)/s)-1) := by
    linarith only [hant,hld,hlog]
  have hquot : (1/10)*(((1-2*q)/s)-1) ≤ (1-s)/(10*s) := by
    field_simp [hs.ne']
    nlinarith
  have hquot' : (1-s)/(10*s) ≤ (1-s)/9 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 10*s-9 by linarith) (show 0 ≤ 1-s by linarith)]
  exact hinc.trans (hquot.trans hquot')

theorem contactDeterminant_nonneg_of_tailScalarBounds (hb : TailScalarBounds)
    {m h : ℝ} (hp : (m,h) ∈ domain) (hqtail : entropyInverse h < tailDelta) :
    0 ≤ contactDeterminant (1-2*m) (entropyInverse h) (radialContact (1-2*m) h) := by
  let q := entropyInverse h
  let v := radialContact (1-2*m) h
  let s := 1-2*m
  obtain ⟨hm, hm', hh, hh'⟩ := domain_bounds hp
  obtain ⟨hq, hqv, hvm⟩ := contact_brackets hp
  have hv : 0 < v := hq.trans_le hqv
  have hvsmall : v ≤ 2*tailDelta := (tail_contact_bound hp hqtail).le
  have hqsmall : q ≤ 2*tailDelta := hqv.trans hvsmall
  have hs : 0 < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hs9 : 9/10 ≤ s := by
    have hu := hp.2.1
    dsimp [retainedCutoff] at hu
    dsimp [s]
    linarith
  have haLo := hb.lowerA v hv hvsmall
  have haHi := hb.upperA v hv hvsmall
  have hkHi := hb.upperK q hq hqsmall
  have hdef := hb.defect q hq hqsmall
  have hinc := comparison_increment_bound hb hp hqtail
  have hqm : 2*q ≤ 1-s := by dsimp [s]; linarith [hqv.trans hvm]
  have hdiff : (611/900)*(1-s) ≤ naturalK q-s*naturalA v := by
    have ha := mul_le_mul_of_nonneg_left haLo (show 0 ≤ 1-s by linarith)
    change naturalA v-naturalA q ≤ (1-s)/9 at hinc
    nlinarith only [ha,hinc,hdef,hqm]
  have hk0 : 0 ≤ naturalK q := by
    rw [naturalK_eq hq (hqv.trans_lt (hvm.trans_lt hm')),
      (entropyInverse_spec hh.le hh'.le).2.2]
    exact mul_nonneg (mul_nonneg log_two_pos.le (sq_nonneg h))
      (Scalar.etaCurvature_nonneg hh hh')
  have hprod : naturalA v*naturalK q ≤ 121/100 := by
    have ht := mul_le_mul haHi hkHi hk0 (by norm_num : (0:ℝ) ≤ 11/10)
    norm_num at ht
    exact ht
  have hgood := mul_le_mul_of_nonneg_left hdiff (show 0 ≤ 4*s by positivity)
  have hbad := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 1-s^2 by nlinarith)
  have hmargin : 0 ≤ 4*s*((611/900)*(1-s))-(1-s^2)*(121/100) := by
    have he : 4*s*((611/900)*(1-s))-(1-s^2)*(121/100) =
        (1-s)*((271/180)*s-121/100) := by ring
    rw [he]
    apply mul_nonneg (by linarith)
    linarith
  dsimp [contactDeterminant]
  change 0 ≤ 4*s*(naturalK q-s*naturalA v)-(1-s^2)*naturalA v*naturalK q
  nlinarith only [hgood,hbad,hmargin]

theorem lowContactTailOwner_of_scalarBounds (hb : TailScalarBounds) :
    LowContactTailOwner tailDelta := by
  intro p hp hq
  exact schur_nonneg_of_contactDeterminant hp
    (contactDeterminant_nonneg_of_tailScalarBounds hb hp hq)

#print axioms entropy_doubling_small
#print axioms contact_le_twice_inverse
#print axioms tail_contact_bound
#print axioms comparison_increment_bound
#print axioms contactDeterminant_nonneg_of_tailScalarBounds
#print axioms lowContactTailOwner_of_scalarBounds

end GeneralCK.SmallBoundaryPhiSchur

end


