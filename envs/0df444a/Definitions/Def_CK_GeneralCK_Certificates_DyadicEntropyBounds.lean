-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_DyadicEntropyBounds
-- name    : CK_GeneralCK_Certificates_DyadicEntropyBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:31:53.703915+00:00
-- url     : https://prove2.me/theorems/ddc7882f-614b-4e29-81be-55dceba99e95
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.DyadicEntropyBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.DyadicEntropyBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.DyadicEntropyBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.DyadicEntropyBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/DyadicEntropyBounds.lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicLogBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data

namespace GeneralCK.Certificates.DyadicEntropy
open DyadicInterval














theorem half_contains (p : ℕ) : (half p).Contains ((2:ℝ)⁻¹) := by
  have htwo : (ofInt p 2).Contains (2:ℝ) := by simpa using ofInt_sound p 2
  exact recip_sound (by dsimp [ofInt]; have := scale_pos p; positivity) htwo

def raw {p : ℕ} (c : DyadicInterval p) (w : Witness p) : DyadicInterval p :=
  w.logTwo.sub ((((ofInt p 1).add c).mul w.logPlus).add
    (((ofInt p 1).sub c).mul w.logMinus) |>.mul (half p))

/-- Every logarithm domain and its range-reduction certificate is checked. -/
def check {p : ℕ} (c out : DyadicInterval p) (w : Witness p) : Bool :=
  DyadicLog.check (ofInt p 2) w.logTwo w.two w.two &&
  DyadicLog.check ((ofInt p 1).add c) w.logPlus w.plusLo w.plusHi &&
  DyadicLog.check ((ofInt p 1).sub c) w.logMinus w.minusLo w.minusHi &&
  (raw c w).subsetCheck out

theorem check_sound {p : ℕ} {c out : DyadicInterval p} {w : Witness p}
    (hc : check c out w=true) {x : ℝ} (hx : c.Contains x) :
    out.Contains (Reflection.biasE x) := by
  have h0 := Bool.and_eq_true_iff.mp hc
  have h1 := Bool.and_eq_true_iff.mp h0.1
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have hone : (ofInt p 1).Contains (1:ℝ) := by simpa using ofInt_sound p 1
  have htwo : (ofInt p 2).Contains (2:ℝ) := by simpa using ofInt_sound p 2
  have hp := add_sound hone hx
  have hm := sub_sound hone hx
  have hl2 := DyadicLog.check_sound h2.1 htwo
  have hlp := DyadicLog.check_sound h2.2 hp
  have hlm := DyadicLog.check_sound h1.2 hm
  apply subsetCheck_sound h0.2
  simpa only [raw,Reflection.biasE,div_eq_mul_inv] using
    sub_sound hl2 (mul_sound (add_sound (mul_sound hp hlp) (mul_sound hm hlm)) (half_contains p))









def rawB {p : ℕ} (w : BWitness p) : DyadicInterval p :=
  w.logTwo.sub (w.logGap.mul (half p))

def checkB {p : ℕ} (c out : DyadicInterval p) (w : BWitness p) : Bool :=
  DyadicLog.check (ofInt p 2) w.logTwo w.two w.two &&
  DyadicLog.check ((ofInt p 1).sub (c.mul c)) w.logGap w.gapLo w.gapHi &&
  (rawB w).subsetCheck out

theorem checkB_sound {p : ℕ} {c out : DyadicInterval p} {w : BWitness p}
    (hc : checkB c out w=true) {x : ℝ} (hx : c.Contains x) :
    out.Contains (Reflection.biasB x) := by
  have h0 := Bool.and_eq_true_iff.mp hc
  have h1 := Bool.and_eq_true_iff.mp h0.1
  have hone : (ofInt p 1).Contains (1:ℝ) := by simpa using ofInt_sound p 1
  have htwo : (ofInt p 2).Contains (2:ℝ) := by simpa using ofInt_sound p 2
  have hg := sub_sound hone (mul_sound hx hx)
  have hl2 := DyadicLog.check_sound h1.1 htwo
  have hlg := DyadicLog.check_sound h1.2 hg
  apply subsetCheck_sound h0.2
  simpa only [rawB,Reflection.biasB,div_eq_mul_inv] using
    sub_sound hl2 (mul_sound hlg (half_contains p))

end GeneralCK.Certificates.DyadicEntropy


