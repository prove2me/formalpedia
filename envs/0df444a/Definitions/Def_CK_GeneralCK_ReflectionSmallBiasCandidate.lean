-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasCandidate
-- name    : CK_GeneralCK_ReflectionSmallBiasCandidate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T13:04:05.374769+00:00
-- url     : https://prove2.me/theorems/881709f9-8ffc-476a-b0c5-5f0a59c30731
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasCandidate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasCandidate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasCandidate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasCandidate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasCandidate.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasCoefficientData
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasComplexDifference

-- ===== source module GeneralCK.ReflectionSmallBiasCandidate =====
section

/-! The factored degree-22 candidate and its bound on the complex bidisc. -/

namespace GeneralCK.Reflection.SmallBiasCandidate

open SmallBiasCoefficientBounds

noncomputable def coefficient (r : CoefficientRow) : ℝ :=
  SmallBiasCoefficientBounds.eval r.coefficients (Real.log 2)⁻¹

noncomputable def quotient : List CoefficientRow → ℂ × ℂ → ℂ
  | [], _ => 0
  | r :: rs, z => (coefficient r : ℂ) * z.1 ^ (2 * r.i) * z.2 ^ (2 * r.j) + quotient rs z

noncomputable def polynomial (z : ℂ × ℂ) : ℂ :=
  z.1 * z.2 * (z.1 ^ 2 - z.2 ^ 2) ^ 2 * quotient SmallBiasCoefficientData.rows z

theorem analyticAt_quotient (rs : List CoefficientRow) (z : ℂ × ℂ) :
    AnalyticAt ℂ (quotient rs) z := by
  induction rs with
  | nil => exact analyticAt_const
  | cons r rs ih =>
    exact ((analyticAt_const.mul (analyticAt_fst.pow (2*r.i))).mul
      (analyticAt_snd.pow (2*r.j))).add ih

theorem analyticAt_polynomial (z : ℂ × ℂ) : AnalyticAt ℂ polynomial z :=
  ((analyticAt_fst.mul analyticAt_snd).mul
    (((analyticAt_fst.pow 2).sub (analyticAt_snd.pow 2)).pow 2)).mul
    (analyticAt_quotient _ z)

theorem norm_quotient_le (rs : List CoefficientRow) {z : ℂ × ℂ}
    (ha : ‖z.1‖ ≤ 1) (hb : ‖z.2‖ ≤ 1)
    (hc : ∀ r ∈ rs, 0 ≤ coefficient r ∧ coefficient r ≤ 1) :
    ‖quotient rs z‖ ≤ rs.length := by
  induction rs with
  | nil => simp [quotient]
  | cons r rs ih =>
    have hr := hc r (by simp)
    have hrs := ih (fun s hs => hc s (by simp [hs]))
    have hnorm : ‖(coefficient r : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1] using hr.2
    have hpa : ‖z.1‖ ^ (2*r.i) ≤ 1 := pow_le_one₀ (norm_nonneg _) ha
    have hpb : ‖z.2‖ ^ (2*r.j) ≤ 1 := pow_le_one₀ (norm_nonneg _) hb
    have ht : ‖(coefficient r : ℂ) * z.1 ^ (2*r.i) * z.2 ^ (2*r.j)‖ ≤ 1 := by
      simp only [norm_mul, norm_pow]
      calc
        _ ≤ (1:ℝ) * 1 * 1 := by gcongr
        _ = 1 := by norm_num
    calc
      _ ≤ ‖(coefficient r : ℂ) * z.1 ^ (2*r.i) * z.2 ^ (2*r.j)‖ + ‖quotient rs z‖ := norm_add_le _ _
      _ ≤ 1 + rs.length := add_le_add ht hrs
      _ = (r :: rs).length := by simp; ring

theorem norm_polynomial_le_one {z : ℂ × ℂ}
    (ha : ‖z.1‖ ≤ (21/50:ℝ)) (hb : ‖z.2‖ ≤ (21/50:ℝ)) :
    ‖polynomial z‖ ≤ 1 := by
  have hq : ‖quotient SmallBiasCoefficientData.rows z‖ ≤ 45 := by
    have hh := norm_quotient_le SmallBiasCoefficientData.rows
      (ha.trans (by norm_num)) (hb.trans (by norm_num)) (fun r hr => by
        have hc := SmallBiasCoefficientData.all_coefficients_positive r hr
        exact ⟨hc.1.le, hc.2.le⟩)
    simpa only [SmallBiasCoefficientData.rows_length, Nat.cast_ofNat] using hh
  have hd : ‖z.1 ^ 2 - z.2 ^ 2‖ ≤ 2 * (21/50:ℝ)^2 := by
    calc
      _ ≤ ‖z.1 ^ 2‖ + ‖z.2 ^ 2‖ := norm_sub_le _ _
      _ ≤ (21/50:ℝ)^2 + (21/50:ℝ)^2 := by simp only [norm_pow]; gcongr
      _ = _ := by ring
  calc
    _ = ‖z.1‖ * ‖z.2‖ * ‖z.1 ^ 2 - z.2 ^ 2‖ ^ 2 * ‖quotient SmallBiasCoefficientData.rows z‖ := by
      simp only [polynomial, norm_mul, norm_pow]
    _ ≤ (21/50:ℝ) * (21/50:ℝ) * (2*(21/50:ℝ)^2)^2 * 45 := by gcongr
    _ ≤ 1 := by norm_num

@[simp] theorem polynomial_axis (a : ℂ) : polynomial (a, 0) = 0 := by
  simp [polynomial]

end GeneralCK.Reflection.SmallBiasCandidate

end


