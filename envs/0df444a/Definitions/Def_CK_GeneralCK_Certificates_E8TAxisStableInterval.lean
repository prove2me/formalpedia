-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval
-- name    : CK_GeneralCK_Certificates_E8TAxisStableInterval
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:05:52.809752+00:00
-- url     : https://prove2.me/theorems/6bb968a3-0dc5-4836-b0ed-7d344ebd9f9d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisStableInterval` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisStableInterval` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisStableInterval` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisStableInterval (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisStableInterval.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableJet5
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisReparamInterval
import Definitions.Def_CK_GeneralCK_Certificates_DyadicLogBounds
import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core

-- ===== source module GeneralCK.Certificates.E8TAxisStableInterval =====
section

/-! The stable `xy_jets5` interval graph.  Only primitive exp/log enclosures
and positive denominator checks are supplied by a numerical replay. -/

namespace GeneralCK.Certificates.E8TAxisStableInterval

open DyadicInterval E8TAxisStableJet5 E8TAxisReparamInterval




theorem constant_sound {p : ℕ} {v : DyadicInterval p} {r a : ℝ}
    (hv : v.Contains r) : (constant v).Contains (Jet5.const r) a := by
  have hz : (ofInt p 0).Contains (0 : ℝ) := by simpa using ofInt_sound p 0
  exact ⟨hv, hz, hz, hz, hz, hz⟩




theorem negative_sound {p : ℕ} {v : DyadicJet5Enclosure p} {j : Jet5} {a : ℝ}
    (hv : v.Contains j a) : (negative v).Contains j.neg a :=
  ⟨neg_sound hv.1, neg_sound hv.2.1, neg_sound hv.2.2.1,
    neg_sound hv.2.2.2.1, neg_sound hv.2.2.2.2.1, neg_sound hv.2.2.2.2.2⟩












theorem zBox_sound {p : ℕ} {i : Inputs p} {a : ℝ}
    (he : i.expNegTwo.Contains (Real.exp (-2 * a))) :
    (zBox i).Contains zJet a := by
  dsimp only [zBox, zJet, Jet5.expAffine, DyadicJet5Enclosure.Contains]
  simp only [zero_add]
  refine ⟨he, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using mul_sound he (ofInt_sound p (-2))
  · norm_num at *
    exact mul_sound he (ofInt_sound p 4)
  · norm_num at *
    simpa using mul_sound he (ofInt_sound p (-8))
  · norm_num at *
    exact mul_sound he (ofInt_sound p 16)
  · norm_num at *
    simpa using mul_sound he (ofInt_sound p (-32))



























theorem xyBox_sound {p : ℕ} {i : Inputs p} {a : ℝ}
    (ha : i.alpha.Contains a)
    (he : i.expNegTwo.Contains (Real.exp (-2 * a)))
    (hl : i.logOnePlusExp.Contains (Real.log (1 + Real.exp (-2 * a))))
    (hL : i.logTwo.Contains (Real.log 2)) (hp : DenominatorsPositive i) :
    (xBox i).Contains xJet a ∧ (yBox i).Contains yJet a := by
  have a0 := DyadicJet5Enclosure.contains_variable ha
  have c1 : (DyadicJet5Enclosure.const p 1).Contains (Jet5.const 1) a := by
    simpa using DyadicJet5Enclosure.contains_const p 1 a
  have c2 : (DyadicJet5Enclosure.const p 2).Contains (Jet5.const 2) a := by
    simpa using DyadicJet5Enclosure.contains_const p 2 a
  have c4 : (DyadicJet5Enclosure.const p 4).Contains (Jet5.const 4) a := by
    simpa using DyadicJet5Enclosure.contains_const p 4 a
  have hz := zBox_sound he
  have ho : (onePlusZBox i).Contains onePlusZJet a := c1.add hz
  have hr : (rBox i).Contains rJet a :=
    (c1.add (negative_sound hz)).mul (ho.inv hp.1)
  have hq : (qBox i).Contains qJet a :=
    (c4.mul hz).mul ((ho.mul ho).inv hp.2.1)
  have hlog : (l1Box i).Contains l1Jet a := by
    apply ho.log hp.1
    simpa [onePlusZJet, zJet, Jet5.add, Jet5.const, Jet5.expAffine] using hl
  have hell : (ellBox i).Contains ellJet a := a0.add hlog
  have hh : (hBox i).Contains hJet a :=
    hlog.add (((c2.mul a0).mul hz).mul (ho.inv hp.1))
  have htwo : (constant i.logTwo).Contains log2Jet a := constant_sound hL
  exact ⟨(htwo.mul hr).mul ((c2.mul hh).inv hp.2.2.1),
    (c2.mul (htwo.inv hp.2.2.2.2)).mul
      (a0.add ((hr.mul hh).mul ((hq.mul hell).inv hp.2.2.2.1)))⟩

/-- Stable interval evaluation encloses the concrete inverse derivatives for
every positive parameter in the supplied alpha box. -/
theorem stable_contains_canonical {p : ℕ} {i : Inputs p} {a : ℝ}
    (ha : i.alpha.Contains a) (hapos : 0 < a)
    (he : i.expNegTwo.Contains (Real.exp (-2 * a)))
    (hl : i.logOnePlusExp.Contains (Real.log (1 + Real.exp (-2 * a))))
    (hL : i.logTwo.Contains (Real.log 2)) (hp : DenominatorsPositive i)
    (hyp : 0 < (yBox i).d1.lo) :
    (eval (xBox i) (yBox i)).Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (E8TAxisStableScalar.Y a) := by
  have hxy := xyBox_sound ha he hl hL hp
  have result := eval_contains_canonical isOpen_Ioi xJet_soundOn yJet_soundOn
    (fun b hb => by simpa using Y_mem_e8SlopeRange hb)
    (fun b hb => by simpa using (E8TAxisStableScalar.e8Q_Y hb).symm)
    hapos hxy.1 hxy.2 hyp
  simpa only [yJet_d0] using result












theorem logBoxCheck_sound {p : ℕ} {input out : DyadicInterval p} {w : FastLogBoxWitness}
    (hc : logBoxCheck input out w = true) {x : ℝ} (hx : input.Contains x) :
    out.Contains (Real.log x) := by
  have htop := Bool.and_eq_true_iff.mp hc
  have hbot := Bool.and_eq_true_iff.mp htop.1
  have hlo : 0 < input.lo := of_decide_eq_true hbot.1
  have hl0 := DyadicFastLog.check_sound hbot.2
  have hu0 := DyadicFastLog.check_sound htop.2
  have hl : out.Contains (-Real.log ((scale p : ℝ) / input.lo)) := by
    simpa only [DyadicInterval.neg, neg_neg] using neg_sound hl0
  have hu : out.Contains (-Real.log ((scale p : ℝ) / input.hi)) := by
    simpa only [DyadicInterval.neg, neg_neg] using neg_sound hu0
  have hs := scale_cast_pos p
  have hlReal : (0 : ℝ) < input.lo := by exact_mod_cast hlo
  have hiReal : (0 : ℝ) < input.hi := lt_of_lt_of_le hlReal (hx.1.trans hx.2)
  have hscale : (0 : ℝ) < scale p := scale_cast_pos p
  have hlEq : -Real.log ((scale p : ℝ) / input.lo) =
      Real.log ((input.lo : ℝ) / scale p) := by
    rw [Real.log_div hscale.ne' hlReal.ne', Real.log_div hlReal.ne' hscale.ne']
    ring
  have huEq : -Real.log ((scale p : ℝ) / input.hi) =
      Real.log ((input.hi : ℝ) / scale p) := by
    rw [Real.log_div hscale.ne' hiReal.ne', Real.log_div hiReal.ne' hscale.ne']
    ring
  rw [hlEq] at hl
  rw [huEq] at hu
  have hlow : (input.lo : ℝ) / scale p ≤ x := (div_le_iff₀ hs).mpr (by
    simpa only [mul_comm] using hx.1)
  have hupp : x ≤ (input.hi : ℝ) / scale p := (le_div_iff₀ hs).mpr (by
    simpa only [mul_comm] using hx.2)
  have hxpos : 0 < x := (div_pos hlReal hs).trans_le hlow
  exact ⟨hl.1.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (div_pos hlReal hs) hlow) hs.le),
    (mul_le_mul_of_nonneg_left (Real.log_le_log hxpos hupp) hs.le).trans hu.2⟩


















theorem expBoxCheck_sound {p : ℕ} {input out : DyadicInterval p} {w : ExpWitness p}
    (hc : expBoxCheck input out w = true) {x : ℝ} (hx : input.Contains x) :
    out.Contains (Real.exp x) := by
  have hh := Bool.and_eq_true_iff.mp hc
  exact subsetCheck_sound hh.2 (DyadicExp.check_sound hh.1 hx)

/-- The primitive assumptions are fully executable checks.  A production
record supplies these witnesses and the five positive denominator checks. -/
theorem checked_stable_contains_canonical {p : ℕ} {i : Inputs p}
    {we : ExpWitness p} {wl wL : FastLogBoxWitness}
    (he : expBoxCheck ((ofInt p (-2)).mul i.alpha) i.expNegTwo we = true)
    (hl : logBoxCheck ((ofInt p 1).add i.expNegTwo) i.logOnePlusExp wl = true)
    (hL : logBoxCheck (ofInt p 2) i.logTwo wL = true)
    (hp : DenominatorsPositive i) (hyp : 0 < (yBox i).d1.lo)
    {a : ℝ} (ha : i.alpha.Contains a) (hapos : 0 < a) :
    (eval (xBox i) (yBox i)).Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (E8TAxisStableScalar.Y a) := by
  have hz : i.expNegTwo.Contains (Real.exp (-2 * a)) := by
    simpa using expBoxCheck_sound he (mul_sound (ofInt_sound p (-2)) ha)
  have hc1 : (ofInt p 1).Contains (1 : ℝ) := by simpa using ofInt_sound p 1
  have hc2 : (ofInt p 2).Contains (2 : ℝ) := by simpa using ofInt_sound p 2
  exact stable_contains_canonical ha hapos hz
    (logBoxCheck_sound hl (add_sound hc1 hz))
    (logBoxCheck_sound hL hc2) hp hyp

#print axioms stable_contains_canonical
#print axioms checked_stable_contains_canonical

end GeneralCK.Certificates.E8TAxisStableInterval

end


