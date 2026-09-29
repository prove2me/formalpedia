-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_DyadicLogBounds
-- name    : CK_GeneralCK_Certificates_DyadicLogBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:29:23.390528+00:00
-- url     : https://prove2.me/theorems/d67046a8-a499-4fc0-aba8-f5379cff927a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.DyadicLogBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.DyadicLogBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.DyadicLogBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.DyadicLogBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/DyadicLogBounds.lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicJetBounds
import Definitions.Def_CK_GeneralCK_Certificates_LogBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data

namespace GeneralCK.Certificates.DyadicLog














def sumLo (w : Witness) : ℚ := w.exponent*w.twoLo+w.lo
def sumHi (w : Witness) : ℚ := w.exponent*w.twoHi+w.hi
def lower (w : Witness) : ℚ := if w.reciprocal then -sumHi w else sumLo w
def upper (w : Witness) : ℚ := if w.reciprocal then -sumLo w else sumHi w
def transformed (w : Witness) (q : ℚ) : ℚ := if w.reciprocal then q⁻¹ else q

def checkRational (q : ℚ) (w : Witness) : Bool :=
  decide (0 < q ∧ transformed w q=2^w.exponent*((1+w.w)/(1-w.w))) &&
    checkLog w.w w.terms w.lo w.hi && checkLog (1/3) w.twoTerms w.twoLo w.twoHi

theorem checkRational_sound {q : ℚ} {w : Witness} (hc : checkRational q w=true) :
    (lower w:ℝ) ≤ Real.log (q:ℝ) ∧ Real.log (q:ℝ) ≤ (upper w:ℝ) := by
  have htop := Bool.and_eq_true_iff.mp hc
  have hpair := Bool.and_eq_true_iff.mp htop.1
  have hdata : 0 < q ∧ transformed w q=2^w.exponent*((1+w.w)/(1-w.w)) := by
    simpa using hpair.1
  have hb := checkLog_sound hpair.2
  have ht := checkLog_sound htop.2
  have ht' : (w.twoLo:ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (w.twoHi:ℝ) := by
    norm_num at ht
    exact ht
  have hw : 0 ≤ w.w ∧ w.w < 1 ∧ w.lo ≤ logLower w.w w.terms ∧
      logUpper w.w w.terms ≤ w.hi := of_decide_eq_true hpair.2
  have hw0 : (0:ℝ) ≤ w.w := by exact_mod_cast hw.1
  have hw1 : (w.w:ℝ) < 1 := by exact_mod_cast hw.2.1
  have hs : 0 < (1+(w.w:ℝ))/(1-(w.w:ℝ)) := div_pos (by linarith) (by linarith)
  have hl : Real.log ((2:ℝ)^w.exponent*((1+(w.w:ℝ))/(1-(w.w:ℝ)))) =
      (w.exponent:ℝ)*Real.log 2+Real.log ((1+(w.w:ℝ))/(1-(w.w:ℝ))) := by
    rw [Real.log_mul (by positivity) hs.ne',Real.log_pow]
  have hlow := mul_le_mul_of_nonneg_left ht'.1 (Nat.cast_nonneg w.exponent)
  have hupp := mul_le_mul_of_nonneg_left ht'.2 (Nat.cast_nonneg w.exponent)
  have hh : (sumLo w:ℝ) ≤ Real.log (transformed w q:ℝ) ∧
      Real.log (transformed w q:ℝ) ≤ (sumHi w:ℝ) := by
    have heq : (transformed w q:ℝ)=(2:ℝ)^w.exponent*((1+(w.w:ℝ))/(1-(w.w:ℝ))) := by
      exact_mod_cast hdata.2
    rw [heq,hl]
    push_cast [sumLo,sumHi]
    constructor <;> linarith [hb.1,hb.2]
  cases he : w.reciprocal with
  | false => simpa [lower,upper,transformed,he] using hh
  | true =>
    simp only [transformed,he,↓reduceIte,Rat.cast_inv,Real.log_inv] at hh
    simp only [lower,upper,he,↓reduceIte,Rat.cast_neg]
    constructor <;> linarith [hh.1,hh.2]

def endpoint (p : ℕ) (z : ℤ) : ℚ := (z:ℚ)/(DyadicInterval.scale p:ℚ)

def checkEndpoint {p : ℕ} (z : ℤ) (out : DyadicInterval p) (w : Witness) : Bool :=
  checkRational (endpoint p z) w &&
    decide (endpoint p out.lo ≤ lower w ∧ upper w ≤ endpoint p out.hi)

theorem checkEndpoint_pos {p : ℕ} {z : ℤ} {out : DyadicInterval p} {w : Witness}
    (hc : checkEndpoint z out w=true) : 0 < z := by
  have hh := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1
  have hq : 0 < endpoint p z := (of_decide_eq_true hh.1).1
  have hs : (0:ℚ) < DyadicInterval.scale p := by exact_mod_cast DyadicInterval.scale_pos p
  have hz := (div_pos_iff_of_pos_right hs).mp hq
  exact_mod_cast hz

theorem checkEndpoint_sound {p : ℕ} {z : ℤ} {out : DyadicInterval p} {w : Witness}
    (hc : checkEndpoint z out w=true) :
    out.Contains (Real.log ((z:ℝ)/(DyadicInterval.scale p:ℝ))) := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hb := checkRational_sound hh.1
  have hw : endpoint p out.lo ≤ lower w ∧ upper w ≤ endpoint p out.hi := of_decide_eq_true hh.2
  dsimp [endpoint] at hw
  have hl : (out.lo:ℝ)/(DyadicInterval.scale p:ℝ) ≤ (lower w:ℝ) := by exact_mod_cast hw.1
  have hu : (upper w:ℝ) ≤ (out.hi:ℝ)/(DyadicInterval.scale p:ℝ) := by exact_mod_cast hw.2
  have hb' : (lower w:ℝ) ≤ Real.log ((z:ℝ)/(DyadicInterval.scale p:ℝ)) ∧
      Real.log ((z:ℝ)/(DyadicInterval.scale p:ℝ)) ≤ (upper w:ℝ) := by
    simpa only [endpoint,Rat.cast_div,Rat.cast_intCast] using hb
  apply DyadicInterval.contains_toReal_iff.mp
  exact ⟨hl.trans hb'.1,hb'.2.trans hu⟩

def check {p : ℕ} (input out : DyadicInterval p) (wl wu : Witness) : Bool :=
  checkEndpoint input.lo out wl && checkEndpoint input.hi out wu

theorem check_sound {p : ℕ} {input out : DyadicInterval p} {wl wu : Witness}
    (hc : check input out wl wu=true) {x : ℝ} (hx : input.Contains x) :
    out.Contains (Real.log x) := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hl := DyadicInterval.contains_toReal_iff.mpr (checkEndpoint_sound hh.1)
  have hu := DyadicInterval.contains_toReal_iff.mpr (checkEndpoint_sound hh.2)
  have hi := DyadicInterval.contains_toReal_iff.mpr hx
  have hp : 0 < input.toReal.lo := DyadicInterval.toReal_positive_iff.mpr (checkEndpoint_pos hh.1)
  apply DyadicInterval.contains_toReal_iff.mp
  exact ⟨hl.1.trans (Real.log_le_log hp hi.1),
    (Real.log_le_log (hp.trans_le hi.1) hi.2).trans hu.2⟩






theorem jetLog_sound {p : ℕ} {b : DyadicJetEnclosure p} {out : DyadicInterval p}
    {j : Jet2} {t : ℝ} {wl wu : Witness}
    (hb : b.Contains j t) (hc : check b.value out wl wu=true) :
    (jetLog b out).Contains j.log t := by
  have hr := DyadicInterval.recip_sound (checkEndpoint_pos (Bool.and_eq_true_iff.mp hc).1) hb.1
  refine ⟨check_sound hc hb.1,?_,?_⟩
  · simpa only [jetLog,Jet2.log,div_eq_mul_inv] using DyadicInterval.mul_sound hb.2.1 hr
  · convert! DyadicInterval.sub_sound (DyadicInterval.mul_sound hb.2.2 hr)
      (DyadicInterval.mul_sound (DyadicInterval.mul_sound hb.2.1 hb.2.1) (DyadicInterval.mul_sound hr hr)) using 1
    simp only [Jet2.log,div_eq_mul_inv]
    ring

def checkJet {p : ℕ} (input out : DyadicJetEnclosure p) (wl wu : Witness) : Bool :=
  check input.value out.value wl wu && (jetLog input out.value).subsetCheck out

theorem checkJet_sound {p : ℕ} {input out : DyadicJetEnclosure p} {wl wu : Witness}
    (hc : checkJet input out wl wu=true) {j : Jet2} {t : ℝ} (hj : input.Contains j t) :
    out.Contains j.log t := by
  have hh := Bool.and_eq_true_iff.mp hc
  exact DyadicJetEnclosure.subsetCheck_sound hh.2 (jetLog_sound hj hh.1)

theorem checkJet_soundOn {p : ℕ} {input out : DyadicJetEnclosure p} {wl wu : Witness}
    (hc : checkJet input out wl wu=true) {j : Jet2} {s : Set ℝ} (hj : input.ContainsOn j s) :
    out.ContainsOn j.log s := fun t ht => checkJet_sound hc (hj t ht)

def pilotWitness : Witness := ⟨false,0,1/3,3,2/3,7/10,3,2/3,7/10⟩
def pilotInput : DyadicInterval 8 := ⟨512,512⟩
def pilotOutput : DyadicInterval 8 := ⟨170,180⟩

theorem pilot_accepts : check pilotInput pilotOutput pilotWitness pilotWitness=true := by
  norm_num [check,checkEndpoint,checkRational,endpoint,pilotInput,pilotOutput,pilotWitness,
    transformed,lower,upper,sumLo,sumHi,DyadicInterval.scale,checkLog,logLower,logUpper,Finset.sum_range_succ]

theorem pilot_log_two : pilotOutput.Contains (Real.log 2) :=
  check_sound pilot_accepts (by norm_num [pilotInput,DyadicInterval.Contains,DyadicInterval.scale])

theorem pilot_too_high_lower_rejected :
    check pilotInput (⟨180,180⟩ : DyadicInterval 8) pilotWitness pilotWitness=false := by
  norm_num [check,checkEndpoint,checkRational,endpoint,pilotInput,pilotWitness,
    transformed,lower,upper,sumLo,sumHi,DyadicInterval.scale,checkLog,logLower,logUpper,Finset.sum_range_succ]

theorem pilot_bad_reduction_rejected :
    check (⟨513,513⟩ : DyadicInterval 8) pilotOutput pilotWitness pilotWitness=false := by
  norm_num [check,checkEndpoint,checkRational,endpoint,pilotOutput,pilotWitness,
    transformed,DyadicInterval.scale]

theorem pilot_nonpositive_rejected :
    check (⟨0,512⟩ : DyadicInterval 8) pilotOutput pilotWitness pilotWitness=false := by
  norm_num [check,checkEndpoint,checkRational,endpoint,pilotOutput,pilotWitness,
    transformed,DyadicInterval.scale]

/-- The reciprocal branch and a nonzero power-of-two reduction are both exercised. -/
def rangeWitness : Witness := ⟨true,2,0,0,0,0,3,2/3,7/10⟩

theorem range_pilot_accepts :
    check (⟨64,64⟩ : DyadicInterval 8) ⟨-359,-341⟩ rangeWitness rangeWitness=true := by
  norm_num [check,checkEndpoint,checkRational,endpoint,rangeWitness,
    transformed,lower,upper,sumLo,sumHi,DyadicInterval.scale,checkLog,logLower,logUpper,Finset.sum_range_succ]

theorem pilot_log_quarter : (⟨-359,-341⟩ : DyadicInterval 8).Contains (Real.log (1/4)) :=
  check_sound range_pilot_accepts (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])

end GeneralCK.Certificates.DyadicLog


