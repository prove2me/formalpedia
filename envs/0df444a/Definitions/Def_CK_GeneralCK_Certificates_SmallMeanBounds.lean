-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_SmallMeanBounds
-- name    : CK_GeneralCK_Certificates_SmallMeanBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:22:31.683035+00:00
-- url     : https://prove2.me/theorems/496a20dc-e0ca-4778-b405-0bafe6fbd91e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.SmallMeanBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.SmallMeanBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.SmallMeanBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.SmallMeanBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/SmallMeanBounds.lean)

import Definitions.Def_CK_GeneralCK_Statement
import Definitions.Def_CK_GeneralCK_Certificates_MixedBounds

namespace GeneralCK.Certificates.SmallMean

theorem entropy_log_identity (q : ℝ) :
    H q * Real.log 2 = q*(-Real.log q)+(1-q)*(-Real.log (1-q)) := by
  unfold H Real.binEntropy
  rw [div_mul_cancel₀ _ log_two_pos.ne']
  simp only [Real.log_inv]

theorem entropy_bounds {q a b c d lo hi : ℝ}
    (hq : 0 ≤ q) (hq' : q ≤ 1) (hl : 0 ≤ lo) (hh : 0 ≤ hi)
    (ha : a ≤ -Real.log q) (hb : b ≤ -Real.log (1-q))
    (hc : -Real.log q ≤ c) (hd : -Real.log (1-q) ≤ d)
    (hlo : lo*(693147181/1000000000) ≤ q*a+(1-q)*b)
    (hhi : q*c+(1-q)*d ≤ hi*(69314718/100000000)) :
    lo ≤ H q ∧ H q ≤ hi := by
  have ht := PilotData.log_two
  norm_num only [div_one] at ht
  have he := entropy_log_identity q
  have hnlo := add_le_add (mul_le_mul_of_nonneg_left ha hq)
    (mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ 1-q))
  have hnhi := add_le_add (mul_le_mul_of_nonneg_left hc hq)
    (mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ 1-q))
  constructor
  · apply (mul_le_mul_iff_left₀ log_two_pos).mp
    have hscale := mul_le_mul_of_nonneg_left ht.2 hl
    nlinarith only [he, hnlo, hlo, hscale]
  · apply (mul_le_mul_iff_left₀ log_two_pos).mp
    have hscale := mul_le_mul_of_nonneg_left ht.1 hh
    nlinarith only [he, hnhi, hhi, hscale]

noncomputable def gammaExpr (r : ℝ) : ℝ :=
  2*r^2/((1+r)*(1+r/31)*(1-H ((1-r)/2)))

noncomputable def W (gamma : ℝ → ℝ) (r : ℝ) : ℝ :=
  (1862/2883)*r^2-(23/10)*(201/1000)+gamma r*((201/1000)-(1/31)*r^2)

theorem gamma_lower {r e g : ℝ} (hr : 0 < r) (hr' : r ≤ 1)
    (he : e ≤ H ((1-r)/2)) (hg : g*((1+r)*(1+r/31)*(1-e)) ≤ 2*r^2)
    (hg0 : 0 ≤ g) : g ≤ gammaExpr r := by
  have hq : 0 ≤ (1-r)/2 := by linarith
  have hq' : (1-r)/2 < 1/2 := by linarith
  have hH : H ((1-r)/2) < 1 := by
    have h := Real.binEntropy_strictMonoOn (a := (1-r)/2) (b := 1/2)
      (by simpa using And.intro hq hq'.le) (by norm_num) hq'
    apply (div_lt_one log_two_pos).mpr
    simpa using h
  have hp : 0 < (1+r)*(1+r/31)*(1-H ((1-r)/2)) := by positivity
  unfold gammaExpr
  apply (le_div_iff₀ hp).mpr
  have hfac : (1+r)*(1+r/31)*(1-H ((1-r)/2)) ≤ (1+r)*(1+r/31)*(1-e) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact (mul_le_mul_of_nonneg_left hfac hg0).trans hg

theorem leaf_sound (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    {l u g r : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u ≤ 1)
    (hr : l ≤ r) (hr' : r ≤ u) (hg : g ≤ gamma u) (hg0 : 0 ≤ g)
    (hcheck : 0 < (1862/2883)*l^2-(23/10)*(201/1000)+g*((201/1000)-(1/31)*u^2)) :
    0 < W gamma r := by
  have hgp : g ≤ gamma r := hg.trans (hmono ⟨by linarith, hr'.trans hu⟩
    ⟨hl.trans_le hlu, hu⟩ hr')
  have hsq₀ : l^2 ≤ r^2 := pow_le_pow_left₀ hl.le hr 2
  have hsq₁ : r^2 ≤ u^2 := pow_le_pow_left₀ (hl.le.trans hr) hr' 2
  have hsq₂ : r^2 ≤ 1 := by nlinarith [hl.le.trans hr, hr'.trans hu]
  have hp : 0 ≤ (201/1000 : ℝ)-(1/31)*r^2 := by linarith
  have hmul := mul_le_mul hgp (by linarith : (201/1000 : ℝ)-(1/31)*u^2 ≤
    (201/1000 : ℝ)-(1/31)*r^2) (by nlinarith [pow_le_pow_left₀ (hl.le.trans hlu) hu 2])
    (hg0.trans hgp)
  unfold W
  nlinarith only [hsq₀, hmul, hcheck]

end GeneralCK.Certificates.SmallMean


