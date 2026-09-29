-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_DyadicFastLog
-- name    : CK_GeneralCK_Certificates_DyadicFastLog
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:19:04.579296+00:00
-- url     : https://prove2.me/theorems/03a29e0f-15a1-4833-a365-ec44f41aeb5c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.DyadicFastLog` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.DyadicFastLog` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.DyadicFastLog` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.DyadicFastLog (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/DyadicFastLog.lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicLogSeries
import Definitions.Def_GeneralCK_E8_interval_checkers

namespace GeneralCK.Certificates.DyadicFastLog





theorem fraction_sound (p : ℕ) (a : ℤ) {b : ℤ} (hb : 0 < b) :
    (fraction p a b).Contains ((a:ℝ)/b) := by
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  have hl : (DyadicInterval.floorDiv (DyadicInterval.scale p*a) b:ℝ)*b ≤
      (DyadicInterval.scale p:ℝ)*a := by
    exact_mod_cast DyadicInterval.floorDiv_mul_le (DyadicInterval.scale p*a) hb
  have hu : (DyadicInterval.scale p:ℝ)*a ≤
      (DyadicInterval.ceilDiv (DyadicInterval.scale p*a) b:ℝ)*b := by
    exact_mod_cast DyadicInterval.le_ceilDiv_mul (DyadicInterval.scale p*a) hb
  change _ ≤ _ ∧ _ ≤ _
  rw [← mul_div_assoc]
  exact ⟨(le_div_iff₀ hb').mpr hl,(div_le_iff₀ hb').mpr hu⟩















theorem check_sound {p : ℕ} {a b : ℤ} {e n : ℕ} {out : DyadicInterval p}
    (hc : check a b e n out=true) : out.Contains (Real.log ((a:ℝ)/b)) := by
  have h3 := Bool.and_eq_true_iff.mp hc
  have h2 := Bool.and_eq_true_iff.mp h3.1
  have h1 := Bool.and_eq_true_iff.mp h2.1
  have hab : 0<a ∧ 0<b := of_decide_eq_true h1.1
  have ha : (0:ℝ)<a := by exact_mod_cast hab.1
  have hb : (0:ℝ)<b := by exact_mod_cast hab.2
  have ht := DyadicLogSeries.enclosure_sound h1.2 (fraction_sound p 1 (by norm_num : (0:ℤ)<3)) n
  norm_num at ht
  have hd : 0 < b+a*2^e := add_pos hab.2 (mul_pos hab.1 (by positivity))
  have hr := DyadicLogSeries.enclosure_sound h2.2 (fraction_sound p (b-a*2^e) hd) n
  have heq : (1+((b-a*2^e:ℤ):ℝ)/(b+a*2^e:ℤ))/
      (1-((b-a*2^e:ℤ):ℝ)/(b+a*2^e:ℤ)) = (b:ℝ)/(a*2^e) := by
    push_cast
    have hp : (0:ℝ)<2^e := by positivity
    field_simp
    ring
  rw [heq] at hr
  have hs := DyadicInterval.neg_sound (DyadicInterval.add_sound
    (DyadicInterval.mul_sound (DyadicInterval.ofInt_sound p e) ht) hr)
  have hl : -((e:ℝ)*Real.log 2+Real.log ((b:ℝ)/(a*2^e))) = Real.log ((a:ℝ)/b) := by
    rw [Real.log_div hb.ne' (mul_pos ha (by positivity)).ne',
      Real.log_mul ha.ne' (by positivity),Real.log_pow,Real.log_div ha.ne' hb.ne']
    ring
  simp only [Int.cast_natCast] at hs
  rw [hl] at hs
  exact DyadicInterval.subsetCheck_sound h3.2 hs

end GeneralCK.Certificates.DyadicFastLog


