-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_DyadicBivariateJetBounds
-- name    : CK_GeneralCK_Certificates_DyadicBivariateJetBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:32:22.790316+00:00
-- url     : https://prove2.me/theorems/a9ff1cf9-040d-44fd-a3f1-d515298d4e76
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.DyadicBivariateJetBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.DyadicBivariateJetBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.DyadicBivariateJetBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.DyadicBivariateJetBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/DyadicBivariateJetBounds.lean)

import Definitions.Def_CK_GeneralCK_Certificates_BivariateJet2
import Definitions.Def_CK_GeneralCK_Certificates_BivariateJetBounds
import Definitions.Def_CK_GeneralCK_Certificates_DyadicLogBounds
import Definitions.Def_CK_GeneralCK_Certificates_DyadicContactBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data

namespace GeneralCK.Certificates
open DyadicInterval

namespace DyadicInterval.Contains

theorem add {p : ℕ} {a b : DyadicInterval p} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := add_sound hx hy

theorem neg {p : ℕ} {a : DyadicInterval p} {x : ℝ} (hx : a.Contains x) :
    a.neg.Contains (-x) := neg_sound hx

theorem mul {p : ℕ} {a b : DyadicInterval p} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := mul_sound hx hy

end DyadicInterval.Contains










namespace DyadicBivariateJetEnclosure
variable {p : ℕ}













theorem contains_toReal_iff {b : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {t : ℝ} :
    b.toReal.Contains j t ↔ b.Contains j t := by
  simp only [toReal,BivariateJetEnclosure.Contains,Contains,DyadicInterval.contains_toReal_iff]

theorem containsOn_toReal_iff {b : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {s : Set ℝ} :
    b.toReal.ContainsOn j s ↔ b.ContainsOn j s := by
  simp only [BivariateJetEnclosure.ContainsOn,ContainsOn,contains_toReal_iff]







theorem contains_coordinateA {value : DyadicInterval p} {f : ℝ→ℝ} {t : ℝ}
    (h : value.Contains (f t)) : (coordinateA value).Contains (BivariateJet2.coordinateA f) t := by
  have h0 : (ofInt p 0).Contains (0:ℝ) := by simpa only [Int.cast_zero] using ofInt_sound p 0
  have h1 : (ofInt p 1).Contains (1:ℝ) := by simpa only [Int.cast_one] using ofInt_sound p 1
  exact ⟨h,h1,h0,h0,h0,h0⟩

theorem contains_coordinateZ {value : DyadicInterval p} {f : ℝ→ℝ} {t : ℝ}
    (h : value.Contains (f t)) : (coordinateZ value).Contains (BivariateJet2.coordinateZ f) t := by
  have h0 : (ofInt p 0).Contains (0:ℝ) := by simpa only [Int.cast_zero] using ofInt_sound p 0
  have h1 : (ofInt p 1).Contains (1:ℝ) := by simpa only [Int.cast_one] using ofInt_sound p 1
  exact ⟨h,h0,h1,h0,h0,h0⟩






























theorem contains_const (p : ℕ) (c : ℤ) (t : ℝ) :
    (const p c).Contains (BivariateJet2.const c) t := by
  exact ⟨ofInt_sound p c,by simpa only [const,BivariateJet2.const,Int.cast_zero] using ofInt_sound p 0,by simpa only [const,BivariateJet2.const,Int.cast_zero] using ofInt_sound p 0,
    by simpa only [const,BivariateJet2.const,Int.cast_zero] using ofInt_sound p 0,by simpa only [const,BivariateJet2.const,Int.cast_zero] using ofInt_sound p 0,by simpa only [const,BivariateJet2.const,Int.cast_zero] using ofInt_sound p 0⟩

theorem Contains.add {b c : DyadicBivariateJetEnclosure p} {j k : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) (hk : c.Contains k t) : (b.add c).Contains (j.add k) t :=
  ⟨hj.1.add hk.1,hj.2.1.add hk.2.1,hj.2.2.1.add hk.2.2.1,
    hj.2.2.2.1.add hk.2.2.2.1,hj.2.2.2.2.1.add hk.2.2.2.2.1,
    hj.2.2.2.2.2.add hk.2.2.2.2.2⟩

theorem Contains.neg {b : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) : b.neg.Contains j.neg t :=
  ⟨hj.1.neg,hj.2.1.neg,hj.2.2.1.neg,hj.2.2.2.1.neg,hj.2.2.2.2.1.neg,hj.2.2.2.2.2.neg⟩

theorem Contains.mul {b c : DyadicBivariateJetEnclosure p} {j k : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) (hk : c.Contains k t) : (b.mul c).Contains (j.mul k) t := by
  have htwo : (ofInt p 2).Contains (2:ℝ) := by simpa using ofInt_sound p 2
  exact ⟨hj.1.mul hk.1,(hj.2.1.mul hk.1).add (hj.1.mul hk.2.1),
    (hj.2.2.1.mul hk.1).add (hj.1.mul hk.2.2.1),
    ((hj.2.2.2.1.mul hk.1).add ((htwo.mul hj.2.1).mul hk.2.1)).add (hj.1.mul hk.2.2.2.1),
    (((hj.2.2.2.2.1.mul hk.1).add (hj.2.1.mul hk.2.2.1)).add
      (hj.2.2.1.mul hk.2.1)).add (hj.1.mul hk.2.2.2.2.1),
    ((hj.2.2.2.2.2.mul hk.1).add ((htwo.mul hj.2.2.1).mul hk.2.2.1)).add
      (hj.1.mul hk.2.2.2.2.2)⟩

theorem Contains.outerCompose {outer : DyadicJetEnclosure p} {b : DyadicBivariateJetEnclosure p}
    {f : Jet2} {j : BivariateJet2} {t : ℝ} (hf : outer.Contains f (j.value t))
    (hj : b.Contains j t) : (outerCompose outer b).Contains (BivariateJet2.outerCompose f j) t := by
  exact ⟨hf.1,hf.2.1.mul hj.2.1,hf.2.1.mul hj.2.2.1,
    by simpa only [DyadicBivariateJetEnclosure.outerCompose,BivariateJet2.outerCompose,pow_two,mul_assoc] using
      ((hf.2.2.mul hj.2.1).mul hj.2.1).add (hf.2.1.mul hj.2.2.2.1),
    ((hf.2.2.mul hj.2.1).mul hj.2.2.1).add (hf.2.1.mul hj.2.2.2.2.1),
    by simpa only [DyadicBivariateJetEnclosure.outerCompose,BivariateJet2.outerCompose,pow_two,mul_assoc] using
      ((hf.2.2.mul hj.2.2.1).mul hj.2.2.1).add (hf.2.1.mul hj.2.2.2.2.2)⟩






theorem subsetCheck_sound {b out : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {t : ℝ}
    (h : b.subsetCheck out=true) (hj : b.Contains j t) : out.Contains j t := by
  simp only [subsetCheck,Bool.and_eq_true_iff] at h
  exact ⟨DyadicInterval.subsetCheck_sound h.1.1.1.1.1 hj.1,
    DyadicInterval.subsetCheck_sound h.1.1.1.1.2 hj.2.1,
    DyadicInterval.subsetCheck_sound h.1.1.1.2 hj.2.2.1,
    DyadicInterval.subsetCheck_sound h.1.1.2 hj.2.2.2.1,
    DyadicInterval.subsetCheck_sound h.1.2 hj.2.2.2.2.1,
    DyadicInterval.subsetCheck_sound h.2 hj.2.2.2.2.2⟩




theorem Contains.inv {b : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) (hpos : 0<b.value.lo) :
    b.inv.Contains (BivariateJet2.outerCompose Jet2.variableJet.inv j) t :=
  Contains.outerCompose (DyadicJetEnclosure.Contains.inv (DyadicJetEnclosure.contains_variable hj.1) hpos) hj




theorem invCheck_positive {b out : DyadicBivariateJetEnclosure p} (h : invCheck b out=true) :
    0<b.value.lo := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem invCheck_sound {b out : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {t : ℝ}
    (h : invCheck b out=true) (hj : b.Contains j t) :
    out.Contains (BivariateJet2.outerCompose Jet2.variableJet.inv j) t := by
  have hh := Bool.and_eq_true_iff.mp h
  exact subsetCheck_sound hh.2 (hj.inv (of_decide_eq_true hh.1))




theorem log_sound {b : DyadicBivariateJetEnclosure p} {value : DyadicInterval p}
    {wl wu : DyadicLog.Witness} {j : BivariateJet2} {t : ℝ}
    (h : DyadicLog.check b.value value wl wu=true) (hj : b.Contains j t) :
    (b.log value).Contains (BivariateJet2.outerCompose Jet2.variableJet.log j) t :=
  Contains.outerCompose (DyadicLog.jetLog_sound (DyadicJetEnclosure.contains_variable hj.1) h) hj

def logCheck (b out : DyadicBivariateJetEnclosure p) (wl wu : DyadicLog.Witness) : Bool :=
  DyadicLog.check b.value out.value wl wu && (b.log out.value).subsetCheck out

theorem logCheck_positive {b out : DyadicBivariateJetEnclosure p} {wl wu : DyadicLog.Witness}
    (h : logCheck b out wl wu=true) : 0<b.value.lo :=
  DyadicLog.checkEndpoint_pos (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

theorem logCheck_sound {b out : DyadicBivariateJetEnclosure p} {wl wu : DyadicLog.Witness}
    {j : BivariateJet2} {t : ℝ} (h : logCheck b out wl wu=true) (hj : b.Contains j t) :
    out.Contains (BivariateJet2.outerCompose Jet2.variableJet.log j) t := by
  have hh := Bool.and_eq_true_iff.mp h
  exact subsetCheck_sound hh.2 (log_sound hh.1 hj)

def contactCheck (b out : DyadicBivariateJetEnclosure p) (c B : DyadicInterval p)
    (outer : DyadicJetEnclosure p) (w : DyadicContact.BracketWitness p)
    (bw : DyadicEntropy.BWitness p) : Bool :=
  DyadicContact.jetCheck b.value c B outer w bw && (outerCompose outer b).subsetCheck out

theorem contactCheck_positive {b out : DyadicBivariateJetEnclosure p} {c B : DyadicInterval p}
    {outer : DyadicJetEnclosure p} {w : DyadicContact.BracketWitness p} {bw : DyadicEntropy.BWitness p}
    (h : contactCheck b out c B outer w bw=true) : 0<b.value.lo := by
  have hj := (Bool.and_eq_true_iff.mp h).1
  have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hj).1).1).1
  exact DyadicContact.bracketCheck_positive hb

theorem contactCheck_sound {b out : DyadicBivariateJetEnclosure p} {c B : DyadicInterval p}
    {outer : DyadicJetEnclosure p} {w : DyadicContact.BracketWitness p} {bw : DyadicEntropy.BWitness p}
    {j : BivariateJet2} {t : ℝ} (h : contactCheck b out c B outer w bw=true) (hj : b.Contains j t) :
    out.Contains (BivariateJet2.outerCompose reflectionContactJet j) t := by
  have hh := Bool.and_eq_true_iff.mp h
  exact subsetCheck_sound hh.2 (Contains.outerCompose (DyadicContact.jetCheck_sound hh.1 hj.1) hj)

end DyadicBivariateJetEnclosure
end GeneralCK.Certificates


