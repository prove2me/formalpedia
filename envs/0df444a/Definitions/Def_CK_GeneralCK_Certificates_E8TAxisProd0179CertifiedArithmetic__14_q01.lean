-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0179CertifiedArithmetic__14_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0179CertifiedArithmetic__14_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T14:55:29.321945+00:00
-- url     : https://prove2.me/theorems/54eb350e-9662-4ac6-b889-ad82785f7cdb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0181CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0182CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0183CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0184CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0187CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0188CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0190CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0191CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0192CertifiedArithmetic) (piece 2 of 14)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0181CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0182CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0183CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0184CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0187CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0188CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0190CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0191CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0192CertifiedArithmetic) (piece 2 of 14)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0181CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0182CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0183CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0184CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0185CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0186CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0187CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0188CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0189CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0190CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0191CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0192CertifiedArithmetic) (piece 2 of 14) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0179CertifiedArithmetic (+13 modules: GeneralCK/Certificates/E8TAxisProd0180CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0181CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0182CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0183CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0184CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0185CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0186CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0187CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0188CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0189CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0190CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0191CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0192CertifiedArithmetic) (piece 2 of 14).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0179CertifiedArithmetic__14_q00

-- ===== source module GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0180GraphCenterA.qJetBox,
   E8TAxisProd0180GraphCenterB.qJetBox,
   E8TAxisProd0180GraphCenterC.qJetBox,
   E8TAxisProd0180GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0180GraphWholeA.qJetBox,
   E8TAxisProd0180GraphWholeB.qJetBox,
   E8TAxisProd0180GraphWholeC.qJetBox,
   E8TAxisProd0180GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨56479558139468821558212094043646189980149593, 56479558139468821558212094043651096429767411⟩
  | 0, 2 => ⟨290490173052715460567384730432416209874755503, 290490173052715460567384730432427122337972335⟩
  | 1, 1 => ⟨296535117235986377351874173430975605755404276, 296535117235986377351874173430990415337761750⟩
  | 0, 3 => ⟨886845175062491677633930944708253429109320302, 886845175062491677633930944708279311690862623⟩
  | 1, 2 => ⟨1337941658418660699385679453835429376907471647, 1337941658418660699385679453835464675419831529⟩
  | 2, 1 => ⟨1360903886503771406648067464553954863083129712, 1360903886503771406648067464554009758475142194⟩
  | 0, 4 => ⟨2021292407248667853997894435836901081536439042, 2021292407248667853997894435836971162151330236⟩
  | 1, 3 => ⟨3706876629202445233797458806080097665394649592, 3706876629202445233797458806080196618600654346⟩
  | 2, 2 => ⟨5415462879513847749107071788052537830224229214, 5415462879513847749107071788052695142969584185⟩
  | 3, 1 => ⟨5492690842423605175928783641140043438194941649, 5492690842423605175928783641140305159280327206⟩
  | 0, 5 => ⟨-14894749161164474150372036475963899516133243130537, 15008636323104384953457415931643274682241007101327⟩
  | 1, 4 => ⟨-27584222560288050816342737225887843758774225614824, 27696651584124743037072718770910984521596705164245⟩
  | 2, 3 => ⟨-51404293958786120506337508379888861890424963564513, 51514885604961703257937021774846682233583114066630⟩
  | 3, 2 => ⟨-96008259192909173309232554733086493705547892156318, 96120719982012640680781390345731568245336910521209⟩
  | 4, 1 => ⟨-179364772171004994183804123147395186212521593767624, 179491876523471975262545313937554527272391201540442⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0180Geometry.ds, E8TAxisProd0180Geometry.dt, coeff⟩

theorem center_0_1_checked :
    centerBoxes.coeff 0 1 = data.coeff 0 1 := by decide

theorem center_0_2_checked :
    centerBoxes.coeff 0 2 = data.coeff 0 2 := by decide

theorem center_1_1_checked :
    centerBoxes.coeff 1 1 = data.coeff 1 1 := by decide

theorem center_0_3_checked :
    centerBoxes.coeff 0 3 = data.coeff 0 3 := by decide

theorem center_1_2_checked :
    centerBoxes.coeff 1 2 = data.coeff 1 2 := by decide

theorem center_2_1_checked :
    centerBoxes.coeff 2 1 = data.coeff 2 1 := by decide

theorem center_0_4_checked :
    centerBoxes.coeff 0 4 = data.coeff 0 4 := by decide

theorem center_1_3_checked :
    centerBoxes.coeff 1 3 = data.coeff 1 3 := by decide

theorem center_2_2_checked :
    centerBoxes.coeff 2 2 = data.coeff 2 2 := by decide

theorem center_3_1_checked :
    centerBoxes.coeff 3 1 = data.coeff 3 1 := by decide

theorem whole_0_5_checked :
    wholeBoxes.coeff 0 5 = data.coeff 0 5 := by decide

theorem whole_1_4_checked :
    wholeBoxes.coeff 1 4 = data.coeff 1 4 := by decide

theorem whole_2_3_checked :
    wholeBoxes.coeff 2 3 = data.coeff 2 3 := by decide

theorem whole_3_2_checked :
    wholeBoxes.coeff 3 2 = data.coeff 3 2 := by decide

theorem whole_4_1_checked :
    wholeBoxes.coeff 4 1 = data.coeff 4 1 := by decide

theorem replay_positive : data.replay.positiveCheck = true := by decide

theorem replay_lo : data.replay.lo = 38337509119799481696987965474522198248608929 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsAt s t) :
    data.CenterEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsAt s t) :
    data.RemainderEnclosed (mixed qJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisProd0180CertifiedArithmetic

end


