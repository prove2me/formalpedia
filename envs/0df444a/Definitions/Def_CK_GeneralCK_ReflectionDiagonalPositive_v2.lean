-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionDiagonalPositive_v2
-- name    : CK_GeneralCK_ReflectionDiagonalPositive_v2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:37:27.88176+00:00
-- url     : https://prove2.me/theorems/162000a6-a582-4b42-9d24-51f00cbb0c3b
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionDiagonalPositive` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionDiagonalPositive` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionDiagonalPositive` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionDiagonalPositive (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionDiagonalPositive.lean)

import Definitions.Def_CK_GeneralCK_Certificates_RegularReflectionExpressionJet
import Definitions.Def_CK_GeneralCK_ReflectionNormalized
import Definitions.Def_CK_GeneralCK_SmallMeanEstimates
import Definitions.Def_CK_GeneralCK_Certificates_MixedConstants

-- ===== source module GeneralCK.ReflectionDiagonalPositive =====
section

namespace GeneralCK.Reflection
open Set Certificates.Reflection
open scoped Topology

theorem regularRatio_strictMonoOn : StrictMonoOn regularRatio (Ioo (-1:ℝ) 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo (-1) 1)
    (f' := fun c => biasB c/(biasE c)^2)
  · intro c hc
    exact (hasDerivAt_regularRatio hc.1 hc.2).continuousAt.continuousWithinAt
  · intro c hc
    rw [interior_Ioo] at hc
    exact (hasDerivAt_regularRatio hc.1 hc.2).hasDerivWithinAt
  · intro c hc
    rw [interior_Ioo] at hc
    exact div_pos (biasB_pos_wide hc.1 hc.2) (sq_pos_of_pos (biasE_pos_wide hc.1 hc.2))

theorem regularContact_regularRatio {c : ℝ} (hc : -1<c) (hc' : c<1) :
    regularContact (c/biasE c)=c := by
  apply regularRatio_strictMonoOn.injOn (regularContact_mem _) ⟨hc,hc'⟩
  exact regularRatio_regularContact (c/biasE c)

theorem biasE_le_quadratic {a : ℝ} (ha : 0≤a) (ha' : a<1) :
    biasE a≤Real.log 2-a^2/2 := by
  have h := SmallMean.Cn_ge_half_sq ha ha'.le
  have he : SmallMean.Cn a=Real.log 2-biasE a := by
    rw [biasE_eq_log_mul_E (by linarith) ha']
    unfold SmallMean.Cn E
    ring
  rw [he] at h
  linarith

theorem biasB_ge_quadratic {a : ℝ} (ha : -1<a) (ha' : a<1) :
    Real.log 2+a^2/2≤biasB a := by
  have hl := Real.log_le_sub_one_of_pos (show 0<1-a*a by nlinarith)
  unfold biasB
  nlinarith

theorem biasS_diagonal {a : ℝ} (ha : 0<a) (ha' : a<1) :
    biasS a a (biasE a)=(2*biasB a+a^2)/(2*(1-a^2)^2*biasB a) := by
  have he := (biasE_pos_wide (by linarith) ha').ne'
  have hb := (biasB_pos_wide (by linarith) ha').ne'
  have hd : 1-a^2≠0 := by nlinarith
  have heq := biasB_eq_biasE_add (by linarith : -1<a) ha'
  unfold SmallMean.A at heq
  unfold biasS
  rw [← heq]
  simp only [← pow_two]
  field_simp
  ring

/-- A positive algebraic lower bound using only quadratic entropy estimates. -/
theorem diagonal_rational_pos {L x e B : ℝ}
    (hL : 1/2<L) (hL' : L<1) (hx : 0<x) (hx' : x<1)
    (he : 0<e) (he' : e≤L-x/2) (hB : L+x/2≤B) :
    0<L/e+(2*x-1-x/(2*B))/(1-x)^2 := by
  have hLp : 0<L := by linarith
  have hminus : 0<2*L-x := by linarith
  have hplus : 0<2*L+x := by linarith
  have heupper : 0<L-x/2 := he.trans_le he'
  have hBp : 0<B := by linarith
  have hd : 0<(1-x)^2 := sq_pos_of_pos (sub_pos.mpr hx')
  have hfirst : L/(L-x/2)≤L/e := div_le_div_of_nonneg_left hLp.le he he'
  have hlast : x/(2*B)≤x/(2*L+x) := by
    apply div_le_div_of_nonneg_left hx.le hplus
    linarith
  have hN : 0<L*(2*L-1)+(1-L)*(1-x) :=
    add_pos (mul_pos hLp (by linarith))
      (mul_pos (sub_pos.mpr hL') (sub_pos.mpr hx'))
  have hpos : 0<2*x^2*(L*(2*L-1)+(1-L)*(1-x))/
      ((2*L-x)*(2*L+x)*(1-x)^2) := by positivity
  have heq : L/(L-x/2)+(2*x-1-x/(2*L+x))/(1-x)^2 =
      2*x^2*(L*(2*L-1)+(1-L)*(1-x))/((2*L-x)*(2*L+x)*(1-x)^2) := by
    have hLm : L*2-x≠0 := by linarith
    have hdx : 1-x≠0 := by linarith
    field_simp [hminus.ne',hplus.ne',heupper.ne',hLm,hdx]
    ring
  rw [← heq] at hpos
  exact hpos.trans_le (add_le_add hfirst
    (div_le_div_of_nonneg_right (by linarith) hd.le))

theorem regular_normalized_diagonal_eq {a : ℝ} (ha : 0<a) (ha' : a<1) :
    Certificates.RegularReflectionExpression.normalizedValue a 1 =
      (Real.log 2/biasE a+(2*a^2-1-a^2/(2*biasB a))/(1-a^2)^2)/a^4 := by
  have hc := regularContact_regularRatio (by linarith : -1<a) ha'
  have he : (biasE a+biasE a)/2=biasE a := by ring
  unfold Certificates.RegularReflectionExpression.normalizedValue
  simp only [mul_one,sub_self,mul_zero,zero_div,regularContact_zero,he]
  rw [show a*(1+1)/2=a by ring,hc,Certificates.ReflectionExpression.biasS_zero,biasS_diagonal ha ha']
  have hb := (biasB_pos_wide (by linarith : -1<a) ha').ne'
  have hd : 1-a^2≠0 := by nlinarith
  have he' := (biasE_pos_wide (by linarith : -1<a) ha').ne'
  field_simp [ha.ne']
  ring

/-- The smooth diagonal extension is strictly positive for every interior bias.
This does not identify the totalized second derivative of the raw zero-radius F. -/
theorem regular_normalized_diagonal_pos {a : ℝ} (ha : 0<a) (ha' : a<1) :
    0<Certificates.RegularReflectionExpression.normalizedValue a 1 := by
  rw [regular_normalized_diagonal_eq ha ha']
  apply div_pos _ (pow_pos ha 4)
  have hlog : Real.log 2<1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num)
    norm_num at h
    exact h
  apply diagonal_rational_pos (by linarith [Certificates.Mixed.log_two_gt_69])
    hlog
    (sq_pos_of_pos ha) (by nlinarith)
    (biasE_pos_wide (by linarith) ha') (biasE_le_quadratic ha.le ha')
    (biasB_ge_quadratic (by linarith) ha')

theorem continuousAt_regular_normalized_diagonal {a : ℝ} (ha : 0<a) (ha' : a<1) :
    ContinuousAt (fun z => Certificates.RegularReflectionExpression.normalizedValue a z) 1 := by
  let s : Set ℝ := {z | 0<z ∧ a*z<1}
  have hj := Certificates.RegularReflectionExpression.normalized_soundOn
    (Certificates.Jet2.soundOn_const a s) (Certificates.Jet2.soundOn_variable s)
    (fun _ _ => ⟨ha,ha'⟩) (fun _ hz => hz)
  have h := (hj 1 (show (1:ℝ) ∈ s by simpa [s] using And.intro (by norm_num : (0:ℝ)<1) ha')).1.continuousAt
  have heq : (Certificates.RegularReflectionExpression.normalized
      (Certificates.Jet2.const a) Certificates.Jet2.variableJet).value =
      (fun z => Certificates.RegularReflectionExpression.normalizedValue a z) := by
    funext z
    exact Certificates.RegularReflectionExpression.normalized_value _ _ z
  rw [heq] at h
  exact h

/-- For each interior bias, actual reflection curvature is positive sufficiently
close to the diagonal on its strict side. No numerical neighborhood size is assumed. -/
theorem curvature_pos_eventually_diagonal {a : ℝ} (ha : 0<a) (ha' : a<1) :
    ∀ᶠ z in 𝓝 (1:ℝ), 0<z → z<1 → 0<curvature a (a*z) := by
  have h := (continuousAt_regular_normalized_diagonal ha ha').tendsto.eventually
    (Ioi_mem_nhds (regular_normalized_diagonal_pos ha ha'))
  filter_upwards [h] with z hz hz0 hz1
  apply curvature_pos_of_normalizedValue_pos ha ha' hz0 hz1
  rw [← Certificates.RegularReflectionExpression.normalizedValue_eq ha ha' hz0 hz1]
  exact hz

end GeneralCK.Reflection

end


