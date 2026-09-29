-- Prove2me | Definitions.Def_CK_GeneralCK_PsiParentEntropyGain
-- name    : CK_GeneralCK_PsiParentEntropyGain
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:54:30.146988+00:00
-- url     : https://prove2.me/theorems/21321cfb-c332-434b-bb60-597af98ec627
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiParentEntropyGain` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiParentEntropyGain` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiParentEntropyGain` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiParentEntropyGain (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiParentEntropyGain.lean)

import Definitions.Def_CK_GeneralCK_ProfileLowerBounds
import Definitions.Def_CK_GeneralCK_SmallMeanEstimates
import Definitions.Def_CK_GeneralCK_Certificates_PilotData

-- ===== source module GeneralCK.PsiParentEntropyGain =====
section

/-!
# A global logarithmic lower bound for the parent entropy gain

The derivative estimate below uses only `log x ≤ x - 1`.  In particular it
does not need the manuscript's auxiliary function `T` or a finite certificate.
It is an input to the corrected active-psi argument retaining the child phi
terms and the endpoint entropy-imbalance gain.
-/

namespace GeneralCK
open Set

theorem entropy_logit_product_le {v : ℝ} (hv : 0 < v) (hvhalf : v < 1 / 2) :
    v * (1 - v) * Real.log ((1 - v) / v) ≤
      Real.binEntropy v * (1 - 2 * v) := by
  have hvc : 0 < 1 - v := by linarith
  have hr : 0 ≤ 1 - 2 * v := by linarith
  have hl : v * Real.log ((1 - v) / v) ≤ 1 - 2 * v := by
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hvc hv)) hv.le
    have he : v * ((1 - v) / v - 1) = 1 - 2 * v := by
      field_simp
      ring
    rwa [he] at h
  have hlog : -Real.log (1 - v) ≥ v := by
    linarith [Real.log_le_sub_one_of_pos hvc]
  have he : Real.binEntropy v =
      v * Real.log ((1 - v) / v) - Real.log (1 - v) := by
    rw [Real.binEntropy, Real.log_inv, Real.log_inv,
      Real.log_div hvc.ne' hv.ne']
    ring
  have h₁ := mul_le_mul_of_nonneg_left hl hv.le
  have h₂ := mul_le_mul_of_nonneg_left hlog hr
  rw [he]
  nlinarith

/-- The scalar entropy-production slope controls a logarithmic singularity
uniformly over its whole physical interior. -/
theorem neg_deriv_eta_ge_logarithmic {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    2 + 1 / (Real.log 2 * h) ≤ -deriv eta h := by
  let v := entropyInverse h
  have hv : 0 < v := entropyInverse_pos hh hh1.le
  have hvhalf : v < 1 / 2 := entropyInverse_lt_half hh.le hh1
  have hvc : 0 < 1 - v := by linarith
  have hJ : 0 < J v := J_pos hv hvhalf
  have hH : H v = h := (entropyInverse_spec hh.le hh1.le).2.2
  have hbin : Real.binEntropy v = Real.log 2 * h := by
    have h := hH
    unfold H at h
    exact (div_eq_iff log_two_pos.ne').mp h |>.trans (mul_comm _ _)
  have hb := entropy_logit_product_le hv hvhalf
  rw [hbin] at hb
  have hlog : Real.log ((1 - v) / v) = Real.log 2 * J v := by
    unfold J
    field_simp
  rw [hlog] at hb
  have hden : 0 < Real.log 2 * v * (1 - v) * J v := by positivity
  have hsmall : 0 < Real.log 2 * h := by positivity
  have hbound : 1 / (Real.log 2 * h) ≤
      (1 - 2 * v) / (Real.log 2 * v * (1 - v) * J v) := by
    apply (div_le_div_iff₀ hsmall hden).2
    nlinarith
  rw [deriv_eta hh hh1]
  change 2 + 1 / (Real.log 2 * h) ≤
    -(-2 - (1 - 2 * v) / (Real.log 2 * v * (1 - v) * J v))
  linarith

theorem eta_add_linear_log_antitone :
    AntitoneOn (fun h : ℝ => eta h + 2 * h + Real.log h / Real.log 2) (Ioc 0 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 1)
    (f' := fun h => deriv eta h + 2 + 1 / (Real.log 2 * h))
  · apply ContinuousOn.add
    · exact Scalar.eta_continuousOn.add (continuous_const.mul continuous_id).continuousOn
    · exact ((Real.continuousOn_log.mono (by intro h hh; exact ne_of_gt hh.1)).div_const _)
  · intro h hh
    have hi : h ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ioc] using hh
    have hd := ((hasDerivAt_eta hi.1 hi.2).add ((hasDerivAt_id h).const_mul 2)).add
      ((Real.hasDerivAt_log hi.1.ne').div_const (Real.log 2))
    rw [← (hasDerivAt_eta hi.1 hi.2).deriv] at hd
    convert! hd.hasDerivWithinAt using 1
    field_simp
  · intro h hh
    have hi : h ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ioc] using hh
    linarith [neg_deriv_eta_ge_logarithmic hi.1 hi.2]

/-- Integrated form, including the entropy endpoint `a + c = 1`. -/
theorem eta_increment_ge_linear_log {a c : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hac : a + c ≤ 1) :
    2 * c + Real.log (1 + c / a) / Real.log 2 ≤ eta a - eta (a + c) := by
  have hb : 0 < a + c := by linarith
  have hm := eta_add_linear_log_antitone
    (show a ∈ Ioc (0 : ℝ) 1 from ⟨ha, by linarith⟩)
    (show a + c ∈ Ioc (0 : ℝ) 1 from ⟨hb, hac⟩) (by linarith)
  have he : 1 + c / a = (a + c) / a := by field_simp
  rw [he, Real.log_div hb.ne' ha.ne', sub_div]
  linarith

/-- A rational lower bound following from the logarithmic increment. -/
theorem eta_increment_ge_rational {a c : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hac : a + c ≤ 1) :
    c / (Real.log 2 * (a + c)) ≤ eta a - eta (a + c) := by
  have hb : 0 < a + c := by linarith
  have hi := eta_increment_ge_linear_log ha hc hac
  have hp : 0 < 1 + c / a := by positivity
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have he : 1 - (1 + c / a)⁻¹ = c / (a + c) := by
    field_simp
    ring
  rw [he] at hl
  have hd := div_le_div_of_nonneg_right hl log_two_pos.le
  have he' : c / (a + c) / Real.log 2 = c / (Real.log 2 * (a + c)) := by
    rw [div_div, mul_comm (a + c)]
  rw [he'] at hd
  linarith

/-- The normalized low-entropy parent gain has a completely analytic bound;
there is no finite subdivision and the zero-bias face is included. -/
theorem eta_parent_gain_small_entropy {E q : ℝ}
    (hE : 0 < E) (hEcap : E ≤ 1 / 1000000)
    (hq : 0 ≤ q) (hqE : q ≤ 8 * E)
    (hphysical : E + (1 - H ((1 - q) / 2)) ≤ 1) :
    q ^ 2 / E ≤ eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  let L := Real.log 2
  let c := 1 - H ((1 - q) / 2)
  let c₀ := q^2 / (2 * L)
  have hL : 0 < L := log_two_pos
  have hLcap : L ≤ 7 / 10 := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    exact h.trans (by norm_num)
  have hq1 : q ≤ 1 := by linarith
  have hc : 0 ≤ c := sub_nonneg.mpr (H_le_one _)
  have hc₀ : 0 ≤ c₀ := by dsimp [c₀]; positivity
  have hcle : c₀ ≤ c := by
    have h := SmallMean.Cn_ge_half_sq hq hq1
    unfold SmallMean.Cn at h
    dsimp [c₀, c, L]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log 2)).2
    nlinarith
  have hgain : c / (L * (E + c)) ≤ eta E - eta (E + c) :=
    eta_increment_ge_rational hE hc hphysical
  have hmono : c₀ / (L * (E + c₀)) ≤ c / (L * (E + c)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have h := mul_le_mul_of_nonneg_left hcle (mul_nonneg hL.le hE.le)
    nlinarith
  have heq : c₀ / (L * (E + c₀)) = q^2 / (L * (2 * L * E + q^2)) := by
    dsimp [c₀]
    field_simp
  have hqSq : q^2 ≤ 64 * E^2 := by
    nlinarith [sq_nonneg (8 * E - q)]
  have hLE : L * E ≤ (7 / 10 : ℝ) * (1 / 1000000) :=
    mul_le_mul hLcap hEcap hE.le (by norm_num)
  have hLsq : L^2 ≤ (49 / 100 : ℝ) := by nlinarith
  have hcoef : 2 * L^2 + 64 * L * E ≤ 1 := by nlinarith
  have hden : L * (2 * L * E + q^2) ≤ E := by
    have h₁ := mul_le_mul_of_nonneg_right hcoef hE.le
    have h₂ := mul_le_mul_of_nonneg_left hqSq hL.le
    nlinarith
  have hb : q^2 / E ≤ q^2 / (L * (2 * L * E + q^2)) :=
    div_le_div_of_nonneg_left (sq_nonneg q) (by positivity) hden
  rw [heq] at hmono
  exact hb.trans (hmono.trans hgain)

#print axioms entropy_logit_product_le
#print axioms neg_deriv_eta_ge_logarithmic
#print axioms eta_add_linear_log_antitone
#print axioms eta_increment_ge_linear_log
#print axioms eta_increment_ge_rational
#print axioms eta_parent_gain_small_entropy

end GeneralCK

end


