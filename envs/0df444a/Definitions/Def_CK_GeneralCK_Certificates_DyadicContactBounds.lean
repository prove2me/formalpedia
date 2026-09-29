-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_DyadicContactBounds
-- name    : CK_GeneralCK_Certificates_DyadicContactBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:14:01.896693+00:00
-- url     : https://prove2.me/theorems/a9a3cae5-2057-4c19-acfe-3f9c4647184f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.DyadicContactBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.DyadicContactBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.DyadicContactBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.DyadicContactBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/DyadicContactBounds.lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicEntropyBounds
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionContactBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data

namespace GeneralCK.Certificates.DyadicContact
open DyadicInterval
open GeneralCK.Reflection



theorem point_contains (p : ℕ) (z : ℤ) :
    (point z : DyadicInterval p).Contains ((z:ℝ)/(scale p:ℝ)) := by
  have hs := (scale_cast_pos p).ne'
  simp [point,DyadicInterval.Contains,mul_div_cancel₀,hs]

/-- The entropy-one-bias endpoint is an exact zero, so no log(0) witness is required. -/
def endpointCheck {p : ℕ} (z : ℤ) (out : DyadicInterval p) (w : DyadicEntropy.Witness p) : Bool :=
  if z=scale p then (ofInt p 0).subsetCheck out else DyadicEntropy.check (point z) out w

theorem endpointCheck_sound {p : ℕ} {z : ℤ} {out : DyadicInterval p}
    {w : DyadicEntropy.Witness p} (hc : endpointCheck z out w=true) :
    out.Contains (Reflection.biasE ((z:ℝ)/(scale p:ℝ))) := by
  by_cases hz : z=scale p
  · rw [endpointCheck,if_pos hz] at hc
    have hh := subsetCheck_sound hc (ofInt_sound p 0)
    rw [hz,div_self (scale_cast_pos p).ne']
    have he : Reflection.biasE 1=0 := by norm_num [Reflection.biasE]
    rw [he]
    simpa only [Int.cast_zero] using hh
  · rw [endpointCheck,if_neg hz] at hc
    exact DyadicEntropy.check_sound hc (point_contains p z)







def bracketCheck {p : ℕ} (Y c : DyadicInterval p) (w : BracketWitness p) : Bool :=
  decide (0 ≤ c.lo ∧ c.hi ≤ scale p ∧ c.lo ≤ c.hi ∧ 0 < Y.lo) &&
  endpointCheck c.lo w.entropyLo w.loWitness && endpointCheck c.hi w.entropyHi w.hiWitness &&
  decide ((Y.mul (point c.lo)).hi ≤ w.entropyLo.lo ∧ w.entropyHi.hi ≤ (Y.mul (point c.hi)).lo)

theorem bracketCheck_positive {p : ℕ} {Y c : DyadicInterval p} {w : BracketWitness p}
    (hc : bracketCheck Y c w=true) : 0 < Y.lo := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1).1
  exact (of_decide_eq_true h).2.2.2

theorem bracketCheck_sound {p : ℕ} {Y c : DyadicInterval p} {w : BracketWitness p}
    (hc : bracketCheck Y c w=true) {y : ℝ} (hy : Y.Contains y) : c.Contains (biasContact y) := by
  have h0 := Bool.and_eq_true_iff.mp hc
  have h1 := Bool.and_eq_true_iff.mp h0.1
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have guards : 0 ≤ c.lo ∧ c.hi ≤ scale p ∧ c.lo ≤ c.hi ∧ 0 < Y.lo := of_decide_eq_true h2.1
  have compares : (Y.mul (point c.lo)).hi ≤ w.entropyLo.lo ∧
      w.entropyHi.hi ≤ (Y.mul (point c.hi)).lo := of_decide_eq_true h0.2
  have hyp : 0 < y := positiveCheck_sound (by simpa [positiveCheck] using guards.2.2.2) hy
  have hs := scale_cast_pos p
  have hl : 0 ≤ (c.lo:ℝ)/(scale p:ℝ) := div_nonneg (by exact_mod_cast guards.1) hs.le
  have hu : (c.hi:ℝ)/(scale p:ℝ) ≤ 1 := (div_le_one hs).mpr (by exact_mod_cast guards.2.1)
  have hlu : (c.lo:ℝ)/(scale p:ℝ) ≤ (c.hi:ℝ)/(scale p:ℝ) :=
    (div_le_div_iff_of_pos_right hs).mpr (by exact_mod_cast guards.2.2.1)
  have hel := endpointCheck_sound h2.2
  have heu := endpointCheck_sound h1.2
  have hpl := mul_sound hy (point_contains p c.lo)
  have hpu := mul_sound hy (point_contains p c.hi)
  have hc0 := biasContact_mem hyp
  have heq : Reflection.biasE (biasContact y)=y*biasContact y :=
    (div_eq_iff hc0.1.ne').mp (biasR_biasContact hyp)
  apply contains_toReal_iff.mp
  apply Reflection.contact_bracket hc0.1.le hc0.2.le hl hu hlu hyp heq
  · have hcmp : ((Y.mul (point c.lo)).hi:ℝ) ≤ (w.entropyLo.lo:ℝ) := by exact_mod_cast compares.1
    exact (mul_le_mul_iff_right₀ hs).mp (hpl.2.trans (hcmp.trans hel.1))
  · have hcmp : (w.entropyHi.hi:ℝ) ≤ ((Y.mul (point c.hi)).lo:ℝ) := by exact_mod_cast compares.2
    exact (mul_le_mul_iff_right₀ hs).mp (heu.2.trans (hcmp.trans hpu.1))












theorem enclosure_sound {p : ℕ} {c B : DyadicInterval p} {y : ℝ} (hy : 0 < y)
    (hc : c.Contains (biasContact y)) (hB : B.Contains (Reflection.biasB (biasContact y)))
    (hBp : 0 < B.lo) (hgap : 0 < (gap c).lo) :
    (enclosure c B).Contains reflectionContactJet y := by
  have hr := recip_sound hBp hB
  have hc2 := mul_sound hc hc
  have hc3 := mul_sound hc2 hc
  have hr2 := mul_sound hr hr
  have hr3 := mul_sound hr2 hr
  have hone : (ofInt p 1).Contains (1:ℝ) := by simpa using ofInt_sound p 1
  have htwo : (ofInt p 2).Contains (2:ℝ) := by simpa using ofInt_sound p 2
  have hg := recip_sound hgap (sub_sound hone hc2)
  refine ⟨hc,?_,?_⟩
  · rw [ReflectionContactBounds.first_eq hy]
    simpa only [enclosure,div_eq_mul_inv,pow_two,neg_mul] using neg_sound (mul_sound hc2 hr)
  · rw [ReflectionContactBounds.second_eq hy]
    convert! sub_sound (mul_sound (mul_sound htwo hc3) hr2)
      (mul_sound (mul_sound (mul_sound hc3 hc2) hg) hr3) using 1
    simp only [div_eq_mul_inv,mul_inv_rev,pow_two]
    ring

def jetCheck {p : ℕ} (Y c B : DyadicInterval p) (out : DyadicJetEnclosure p)
    (w : BracketWitness p) (bw : DyadicEntropy.BWitness p) : Bool :=
  bracketCheck Y c w && DyadicEntropy.checkB c B bw &&
    decide (0 < B.lo ∧ 0 < (gap c).lo) && (enclosure c B).subsetCheck out

theorem jetCheck_sound {p : ℕ} {Y c B : DyadicInterval p} {out : DyadicJetEnclosure p}
    {w : BracketWitness p} {bw : DyadicEntropy.BWitness p}
    (h : jetCheck Y c B out w bw=true) {y : ℝ} (hy : Y.Contains y) :
    out.Contains reflectionContactJet y := by
  have h0 := Bool.and_eq_true_iff.mp h
  have h1 := Bool.and_eq_true_iff.mp h0.1
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have hp : 0 < B.lo ∧ 0 < (gap c).lo := of_decide_eq_true h1.2
  have hc := bracketCheck_sound h2.1 hy
  have hB := DyadicEntropy.checkB_sound h2.2 hc
  have hyp : 0 < y := positiveCheck_sound (by simpa [positiveCheck] using bracketCheck_positive h2.1) hy
  exact DyadicJetEnclosure.subsetCheck_sound h0.2 (enclosure_sound hyp hc hB hp.1 hp.2)

theorem jetCheck_comp_sound {p : ℕ} {input out : DyadicJetEnclosure p} {c B : DyadicInterval p}
    {w : BracketWitness p} {bw : DyadicEntropy.BWitness p}
    (h : jetCheck input.value c B out w bw=true) {j : Jet2} {t : ℝ} (hj : input.Contains j t) :
    (out.comp input).Contains (reflectionContactJet.comp j) t :=
  (jetCheck_sound h hj.1).comp hj

theorem jetCheck_comp_soundOn {p : ℕ} {input out : DyadicJetEnclosure p} {c B : DyadicInterval p}
    {w : BracketWitness p} {bw : DyadicEntropy.BWitness p}
    (h : jetCheck input.value c B out w bw=true) {j : Jet2} {s : Set ℝ} (hj : input.ContainsOn j s) :
    (out.comp input).ContainsOn (reflectionContactJet.comp j) s :=
  fun t ht => jetCheck_comp_sound h (hj t ht)

end GeneralCK.Certificates.DyadicContact


