-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0122CertifiedArithmetic__18
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0122CertifiedArithmetic__18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T14:25:05.260996+00:00
-- url     : https://prove2.me/theorems/582c63a1-e309-4a85-992b-110b2926291c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0122CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0123CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0122CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0123CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0124CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0125CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0126CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0127CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0128CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0129CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0130CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0131CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0132CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0133CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0134CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0135CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0136CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0137CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0138CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0139CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0122CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0123CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0124CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0125CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0126CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0127CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0128CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0129CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0130CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0131CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0132CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0133CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0134CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0135CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0136CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0137CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0138CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0139CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0122CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0123CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0124CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0125CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0126CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0127CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0128CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0129CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0130CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0131CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0132CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0133CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0134CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0135CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0136CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0137CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0138CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0139CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0122CertifiedArithmetic (+17 modules: GeneralCK/Certificates/E8TAxisProd0123CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0124CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0125CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0126CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0127CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0128CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0129CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0130CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0131CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0132CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0133CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0134CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0135CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0136CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0137CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0138CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0139CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0122GraphCenterA__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0120GraphCenterB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0114GraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0122GraphCenterD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0114GraphWholeA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0120GraphWholeB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0119GraphWholeC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0112GraphWholeD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0101Geometry__22
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0123Geometry__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0124GraphWholeD__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0125GraphCenterC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0125GraphWholeA__18
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0133GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0136GraphCenterD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0136GraphWholeC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0137GraphWholeB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0139GraphCenterA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0139GraphCenterC__15

-- ===== source module GeneralCK.Certificates.E8TAxisProd0122CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0122CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0122GraphCenterA.qJetBox,
   E8TAxisProd0122GraphCenterB.qJetBox,
   E8TAxisProd0122GraphCenterC.qJetBox,
   E8TAxisProd0122GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0122GraphWholeA.qJetBox,
   E8TAxisProd0122GraphWholeB.qJetBox,
   E8TAxisProd0122GraphWholeC.qJetBox,
   E8TAxisProd0122GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨924488238823924338155474333090711762093951986, 924488238823924338155474333090726058884440639⟩
  | 0, 2 => ⟨3608028992660611855547683793677418766208908738, 3608028992660611855547683793677456893612098801⟩
  | 1, 1 => ⟨3650315376139648376010009639624615848425522879, 3650315376139648376010009639624675573710208827⟩
  | 0, 3 => ⟨9275125789764010922487783457459149364782452919, 9275125789764010922487783457459256256059014176⟩
  | 1, 2 => ⟨13100921618897861233093267643918604086735954707, 13100921618897861233093267643918773435040856304⟩
  | 2, 1 => ⟨13234937495354157105706917573941924621665594332, 13234937495354157105706917573942210605783553440⟩
  | 0, 4 => ⟨19757474498044968817232926295582264805153000025, 19757474498044968817232926295582585589896499079⟩
  | 1, 3 => ⟨31767833621986516978786385795498103153745285566, 31767833621986516978786385795498628367826053939⟩
  | 2, 2 => ⟨43876908335017890406099674933567282187643320143, 43876908335017890406099674933568189341942585939⟩
  | 3, 1 => ⟨44269901694023888569591880562140639328135322259, 44269901694023888569591880562142238446466961171⟩
  | 0, 5 => ⟨-179678017141160842597461125340655177779873564951464, 180931438735391093029605416649193157591575537600069⟩
  | 1, 4 => ⟨-346189508257414229226951542192966476638308411614016, 347978431613263395301201511601791765237469445462376⟩
  | 2, 3 => ⟨-668321860136231965697323662165127222284657521131637, 670822747727847566531351040965777765768940290444743⟩
  | 3, 2 => ⟨-1291419876893411552885359194045343049737320696039229, 1294675957711513900651467718550105666835530083269610⟩
  | 4, 1 => ⟨-2496600990127588645466676874091538368906277097330056, 2500036556940179991824235003322104785507508972122801⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0122Geometry.ds, E8TAxisProd0122Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 690838431472611920502368031439253988132749153 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0122CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0123CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0123CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0123GraphCenterA.qJetBox,
   E8TAxisProd0123GraphCenterB.qJetBox,
   E8TAxisProd0123GraphCenterC.qJetBox,
   E8TAxisProd0123GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0123GraphWholeA.qJetBox,
   E8TAxisProd0123GraphWholeB.qJetBox,
   E8TAxisProd0123GraphWholeC.qJetBox,
   E8TAxisProd0123GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨720475360994254173936853561610554364180942083, 720475360994254173936853561610567064925054644⟩
  | 0, 2 => ⟨2869648913503759203847689060272333022896594307, 2869648913503759203847689060272366126247978896⟩
  | 1, 1 => ⟨2904285768954848423238521957759130067732859767, 2904285768954848423238521957759181256705058093⟩
  | 0, 3 => ⟨7473430407230364703680571487052807849638022678, 7473430407230364703680571487052899477550696559⟩
  | 1, 2 => ⟨10607958947443486307303009951374356326728160244, 10607958947443486307303009951374499770257634536⟩
  | 2, 1 => ⟨10719362477886826234260621060392779924491760887, 10719362477886826234260621060393020601221420778⟩
  | 0, 4 => ⟨16071664434168125738925852118307793298104550505, 16071664434168125738925852118308065663647052583⟩
  | 1, 3 => ⟨26055974030449322282371563216093944125201682605, 26055974030449322282371563216094385274512223114⟩
  | 2, 2 => ⟨36124585548873174383304625295605323386995161157, 36124585548873174383304625295606080732413093423⟩
  | 3, 1 => ⟨36456650678097633242059202118209868442529410676, 36456650678097633242059202118211197341747096930⟩
  | 0, 5 => ⟨-133138779733146992500352351127021352786795388056199, 134148172089727756458308812593252004209745897034059⟩
  | 1, 4 => ⟨-255720015006671010671686550740237041317999193054970, 257144219224944512817392066312498110396487592851932⟩
  | 2, 3 => ⟨-492287786712544344748754821131683756689861729412762, 494263294855790959941017262143003867884919161329859⟩
  | 3, 2 => ⟨-948724038865070411875400570229547806510651169456604, 951284833432582203486402615717715058932608659334583⟩
  | 4, 1 => ⟨-1829264453039094318120769997516200263522719683487505, 1831966218069540042980135171811800041373526649571625⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0123Geometry.ds, E8TAxisProd0123Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 541231896536418062715263458348033335780576842 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0123CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0124CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0124CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0124GraphCenterA.qJetBox,
   E8TAxisProd0124GraphCenterB.qJetBox,
   E8TAxisProd0124GraphCenterC.qJetBox,
   E8TAxisProd0124GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0124GraphWholeA.qJetBox,
   E8TAxisProd0124GraphWholeB.qJetBox,
   E8TAxisProd0124GraphWholeC.qJetBox,
   E8TAxisProd0124GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨564181259331178594433688064567340367834790650, 564181259331178594433688064567351721555754450⟩
  | 0, 2 => ⟨2287828041921374314742536609162930853113659999, 2287828041921374314742536609162959799114621341⟩
  | 1, 1 => ⟨2322542555823466488668669078960101508358595739, 2322542555823466488668669078960145677436967024⟩
  | 0, 3 => ⟨6031098802989742902493692279807002391125080128, 6031098802989742902493692279807081434740690546⟩
  | 1, 2 => ⟨8612420474753323347535804605214419587810647734, 8612420474753323347535804605214541790533893523⟩
  | 2, 1 => ⟨8725701252831368233229245233096744937581851389, 8725701252831368233229245233096948604004068336⟩
  | 0, 4 => ⟨13076844028443535035480028201592619620405117050, 13076844028443535035480028201592852255407325075⟩
  | 1, 3 => ⟨21398864237232237500863857160280234397291620852, 21398864237232237500863857160280606863311299351⟩
  | 2, 2 => ⟨29808896295998849280643617448282040182658434871, 29808896295998849280643617448282675527961074649⟩
  | 3, 1 => ⟨30151659212682038394347689049379610477914399027, 30151659212682038394347689049380719993607809228⟩
  | 0, 5 => ⟨-103431733822532708571382782155485942357708774656496, 104222344062820428655201979483033858174143523277721⟩
  | 1, 4 => ⟨-198095026693211433714716419023187614581431458965938, 199191181844001532486902704969824417072084132906626⟩
  | 2, 3 => ⟨-380369586548961406703734546702726929653198041970113, 381872636413464163501050131415910824432822336244998⟩
  | 3, 2 => ⟨-731215815787815281535289122550977571912466451923698, 733155664893134403597816917134453610136784532486252⟩
  | 4, 1 => ⟨-1406386950721736303403464991208287752474905217489243, 1408450323188411191562216007513175393851910389755271⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0124Geometry.ds, E8TAxisProd0124Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 423192433379752156537326701418951805591939624 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0124CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0125CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0125CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0125GraphCenterA.qJetBox,
   E8TAxisProd0125GraphCenterB.qJetBox,
   E8TAxisProd0125GraphCenterC.qJetBox,
   E8TAxisProd0125GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0125GraphWholeA.qJetBox,
   E8TAxisProd0125GraphWholeB.qJetBox,
   E8TAxisProd0125GraphWholeC.qJetBox,
   E8TAxisProd0125GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨434896861102258607594136975691501183263292942, 434896861102258607594136975691511326390267774⟩
  | 0, 2 => ⟨1804067445261677676803598803789299543437559829, 1804067445261677676803598803789324839731417775⟩
  | 1, 1 => ⟨1832333924978458548720244942390032500693617248, 1832333924978458548720244942390070566978989986⟩
  | 0, 3 => ⟨4821998599270090331146820098323715746039269380, 4821998599270090331146820098323783805014973275⟩
  | 1, 2 => ⟨6924545707484676049920286622464213928282695377, 6924545707484676049920286622464317738920381239⟩
  | 2, 1 => ⟨7018178463315779041643260530964678629385892176, 7018178463315779041643260530964850392491365765⟩
  | 0, 4 => ⟨10537959736151914196854863092654120152545960262, 10537959736151914196854863092654318272384607470⟩
  | 1, 3 => ⟨17416611104490296002491843389293506279266829491, 17416611104490296002491843389293819477957788311⟩
  | 2, 2 => ⟨24370005290065016134886459597447988003239832602, 24370005290065016134886459597448518485529280777⟩
  | 3, 1 => ⟨24657412837695546582478004733087681605247881525, 24657412837695546582478004733088603175429720556⟩
  | 0, 5 => ⟨-79987591261404654667298370184720849338716812847112, 80601810799885033905596615625056282594038214732016⟩
  | 1, 4 => ⟨-152706914293917930719104551481252095071256527085390, 153539607247187740900232598569767481749788430173074⟩
  | 2, 3 => ⟨-292376111040076039024971803993287928703234772284863, 293499538499299478756472070929695454300901545800308⟩
  | 3, 2 => ⟨-560502359177931284378370210296218060478370441742519, 561939652140436014866129690563879047700022796868797⟩
  | 4, 1 => ⟨-1075062615990977234109196192749095120087786004078072, 1076595324545687210102405663201968044186821055310977⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0125Geometry.ds, E8TAxisProd0125Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 325073220480443033393782220998264873027505571 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0125CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0126CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0126CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0126GraphCenterA.qJetBox,
   E8TAxisProd0126GraphCenterB.qJetBox,
   E8TAxisProd0126GraphCenterC.qJetBox,
   E8TAxisProd0126GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0126GraphWholeA.qJetBox,
   E8TAxisProd0126GraphWholeB.qJetBox,
   E8TAxisProd0126GraphWholeC.qJetBox,
   E8TAxisProd0126GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨558480502398140234718723444819382480138532789, 558480502398140234718723444819393795706742097⟩
  | 0, 2 => ⟨2272791092407454945525513425837586401151860049, 2272791092407454945525513425837615236481804095⟩
  | 1, 1 => ⟨2301078259901567122329020661902907926238779365, 2301078259901567122329020661902951920128840407⟩
  | 0, 3 => ⟨5998487835252127965429495768668875831808476966, 5998487835252127965429495768668954557909848317⟩
  | 1, 2 => ⟨8559062682836078698632626051134219776794627376, 8559062682836078698632626051134341469361830135⟩
  | 2, 1 => ⟨8651396923450352896121979937601804557161824413, 8651396923450352896121979937602007349046856195⟩
  | 0, 4 => ⟨13011978953824930045860646801833463432944085484, 13011978953824930045860646801833695085235494468⟩
  | 1, 3 => ⟨21287456034219584848462853837279495941404402851, 21287456034219584848462853837279866788946007378⟩
  | 2, 2 => ⟨29634709323278085879923753677819801747074876391, 29634709323278085879923753677820434257541848476⟩
  | 3, 1 => ⟨29914175165333807269112437174834518110978657868, 29914175165333807269112437174835622550008531781⟩
  | 0, 5 => ⟨-102789324666108928949519514355380944153566149505844, 103573943824864702423885132896911267053540673998999⟩
  | 1, 4 => ⟨-196848863377317992717756172093510844132650217488183, 197935443476785988845830401030774496700419791543885⟩
  | 2, 3 => ⟨-377947006461822241181646830285732087502845899443623, 379434715385620796671267807008063713077640114406518⟩
  | 3, 2 => ⟨-726500335690193417089711695690202338952550169741905, 728415929428909061274468134444392107520684818189285⟩
  | 4, 1 => ⟨-1397201204935118262944648977193316627849545292138450, 1399227619547209198961201067750890369938553034915373⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0126Geometry.ds, E8TAxisProd0126Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 418618494596573673260554884449591857845309675 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0126CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0127CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0127CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0127GraphCenterA.qJetBox,
   E8TAxisProd0127GraphCenterB.qJetBox,
   E8TAxisProd0127GraphCenterC.qJetBox,
   E8TAxisProd0127GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0127GraphWholeA.qJetBox,
   E8TAxisProd0127GraphWholeB.qJetBox,
   E8TAxisProd0127GraphWholeC.qJetBox,
   E8TAxisProd0127GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨430401733826623463972276327718443923266894669, 430401733826623463972276327718454032661842716⟩
  | 0, 2 => ⟨1792045324700672276788535699432090556067092856, 1792045324700672276788535699432115756739930151⟩
  | 1, 1 => ⟨1815076891908808376423633379974477084177661658, 1815076891908808376423633379974515001072385337⟩
  | 0, 3 => ⟨4795719898959158856526316463601459590665209210, 4795719898959158856526316463601527377418739742⟩
  | 1, 2 => ⟨6881118986932117511920074518797102688466502099, 6881118986932117511920074518797206066515268887⟩
  | 2, 1 => ⟨6957434122801568026754273223831718436008467354, 6957434122801568026754273223831889461607247309⟩
  | 0, 4 => ⟨10485041099784535765165368311505136076713544475, 10485041099784535765165368311505333360507233355⟩
  | 1, 3 => ⟨17324838202037285390388915713940216557493871899, 17324838202037285390388915713940528392834891740⟩
  | 2, 2 => ⟨24225587290420522236129261863455225939203019325, 24225587290420522236129261863455754044531542660⟩
  | 3, 1 => ⟨24459903066616921343303301846343659778520493475, 24459903066616921343303301846344577106056489641⟩
  | 0, 5 => ⟨-79493567030955962611214489624394072995905011562903, 80103427294860055894867344910742018887366365504068⟩
  | 1, 4 => ⟨-151750489936100944112136886717812306771125027727145, 152576331905436580412139291373820844111380857295432⟩
  | 2, 3 => ⟨-290519999021626883590716860337839815666896108863641, 291632580799924041325059582783234981487094382657537⟩
  | 3, 2 => ⟨-556895256618209692395241914196864827709339611346500, 558315552957464953006729513741890154836478273487766⟩
  | 4, 1 => ⟨-1068046751228971586357745607939464647942543440386422, 1069553771822009253060523026563139080010654779220969⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0127Geometry.ds, E8TAxisProd0127Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 321468444943529580168984782122404477185283348 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0127CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0128CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0128CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0128GraphCenterA.qJetBox,
   E8TAxisProd0128GraphCenterB.qJetBox,
   E8TAxisProd0128GraphCenterC.qJetBox,
   E8TAxisProd0128GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0128GraphWholeA.qJetBox,
   E8TAxisProd0128GraphWholeB.qJetBox,
   E8TAxisProd0128GraphWholeC.qJetBox,
   E8TAxisProd0128GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2369885681344245351806504027346517178182912931, 2369885681344245351806504027346541038129579125⟩
  | 0, 2 => ⟨8622351049108776402118171265516532117237874771, 8622351049108776402118171265516602771203805830⟩
  | 1, 1 => ⟨8693030956608297909970347219647309410817255332, 8693030956608297909970347219647425682355644116⟩
  | 0, 3 => ⟨21075876618057912427251840497354862366556587508, 21075876618057912427251840497355071034420097978⟩
  | 1, 2 => ⟨29258922129972487391139654500322298117315097886, 29258922129972487391139654500322643702668794027⟩
  | 2, 1 => ⟨29469580430254812787096399045884938402763737863, 29469580430254812787096399045885536410560168875⟩
  | 0, 4 => ⟨42869464992564109812543409644267257145402441623, 42869464992564109812543409644267909783413273197⟩
  | 1, 3 => ⟨67092374988968393535358488353204591444263495298, 67092374988968393535358488353205702935954364976⟩
  | 2, 2 => ⟨91454206434015175303124750269735906118314305484, 91454206434015175303124750269737869751214845650⟩
  | 3, 1 => ⟨92027237135872361930363009258759001785622857351, 92027237135872361930363009258762523508575092408⟩
  | 0, 5 => ⟨-756465445997090844178092532789679586062700838642284, 758055906006852694323146545101658219226866073630049⟩
  | 1, 4 => ⟨-1474365264039797038267088200892038649593610334789758, 1476521111186883107929646406348245648682791118374666⟩
  | 2, 3 => ⟨-2876028443964972081623961518864981858118768762534044, 2878918012332017284548395416234897359981772953261777⟩
  | 3, 2 => ⟨-5612762589063654826999262019541768739099644585124247, 5616446969145706801297073343231721604354630657499484⟩
  | 4, 1 => ⟨-10956504615142072963010395786588700686800284264810672, 10960450429781117711628995391768959689198666491791715⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0128Geometry.ds, E8TAxisProd0128Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1599025248572141921365174645442401700076362947 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0128CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0129CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0129CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0129GraphCenterA.qJetBox,
   E8TAxisProd0129GraphCenterB.qJetBox,
   E8TAxisProd0129GraphCenterC.qJetBox,
   E8TAxisProd0129GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0129GraphWholeA.qJetBox,
   E8TAxisProd0129GraphWholeB.qJetBox,
   E8TAxisProd0129GraphWholeC.qJetBox,
   E8TAxisProd0129GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1880545166584800063804461085327817129147530482, 1880545166584800063804461085327837941825880972⟩
  | 0, 2 => ⟨6962135194390744328919430086088075351086866795, 6962135194390744328919430086088135174235525669⟩
  | 1, 1 => ⟨7020714078337293399268372329019704951399976439, 7020714078337293399268372329019802192826697408⟩
  | 0, 3 => ⟨17240792514020151368942708411546978152395788917, 17240792514020151368942708411547152168188515918⟩
  | 1, 2 => ⟨24024236909080502495216998552517236216343133767, 24024236909080502495216998552517521222056435158⟩
  | 2, 1 => ⟨24201650465356287537059721740574150632303056700, 24201650465356287537059721740574640740088030629⟩
  | 0, 4 => ⟨35525067473185541985176269060747493145953436085, 35525067473185541985176269060748030212133677026⟩
  | 1, 3 => ⟨55926835200580014070255045514431757689823324752, 55926835200580014070255045514432663248972092605⟩
  | 2, 2 => ⟨76448967683808670586456908601953422488921725869, 76448967683808670586456908601955012956233236659⟩
  | 3, 1 => ⟨76941429436112053137568267867971190663141164589, 76941429436112053137568267867974030391968578602⟩
  | 0, 5 => ⟨-523202631918264272020266237681698820597989966041401, 524717331227579787259572270983058428911165940466161⟩
  | 1, 4 => ⟨-1017143967512279673587687091467488124781115646649969, 1019234477986378309690544121371559936139815436720568⟩
  | 2, 3 => ⟨-1979483359302095752315069947790106880290645668451656, 1982327349982670303672733801425050569424036025150843⟩
  | 3, 2 => ⟨-3854379675882057864327541894106994039346793995562763, 3858031126400560974199570348783756933520053494354511⟩
  | 4, 1 => ⟨-7507310194026301239309716804049943849290227272144275, 7511190825107161594977693609522931665495034783095686⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0129Geometry.ds, E8TAxisProd0129Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1315473444252966952993075835943164736245480902 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0129CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0130CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0130CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0130GraphCenterA.qJetBox,
   E8TAxisProd0130GraphCenterB.qJetBox,
   E8TAxisProd0130GraphCenterC.qJetBox,
   E8TAxisProd0130GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0130GraphWholeA.qJetBox,
   E8TAxisProd0130GraphWholeB.qJetBox,
   E8TAxisProd0130GraphWholeC.qJetBox,
   E8TAxisProd0130GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2348395554322727992826470631635207089000547210, 2348395554322727992826470631635230859876632841⟩
  | 0, 2 => ⟨8569795122993707042108076719008790204325370036, 8569795122993707042108076719008860554225706326⟩
  | 1, 1 => ⟨8620092983690322357032828626343708177089021237, 8620092983690322357032828626343823930699191417⟩
  | 0, 3 => ⟨20968944853590465186945921849423271144533291604, 20968944853590465186945921849423478874314856461⟩
  | 1, 2 => ⟨29091588575494230253832652878121779585309344617, 29091588575494230253832652878122123567553904086⟩
  | 2, 1 => ⟨29241547794666458075705139820477457193140407883, 29241547794666458075705139820478052365124195594⟩
  | 0, 4 => ⟨42676073927092898531784067683429931435123168088, 42676073927092898531784067683430580972026613618⟩
  | 1, 3 => ⟨66774684308237154928376202911193663667178935426, 66774684308237154928376202911194769756150671796⟩
  | 2, 2 => ⟨90972243675981407850105669698296943244702860967, 90972243675981407850105669698298897152950701608⟩
  | 3, 1 => ⟨91380329165075057254146475728890761561043803077, 91380329165075057254146475728894265541760960545⟩
  | 0, 5 => ⟨-750197151245723904173917568893091092277424549496093, 751787977573181309623414874281764145908275772394589⟩
  | 1, 4 => ⟨-1462063229254503039422922989564389159009977574154220, 1464222591591759181428313427000502148827637246273686⟩
  | 2, 3 => ⟨-2851870651363050985396702080737461302932135483130910, 2854770319339438350347070798537315532641896703019586⟩
  | 3, 2 => ⟨-5565306071705834539007079778472351704636957840448540, 5569013477267675027973392532923341915010639845614465⟩
  | 4, 1 => ⟨-10863255677273031946073066151948193204722931069851175, 10867249266401291727260814758760296636031073326997433⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0130Geometry.ds, E8TAxisProd0130Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1584016077378274851935508514756729153426384012 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0130CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0131CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0131CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0131GraphCenterA.qJetBox,
   E8TAxisProd0131GraphCenterB.qJetBox,
   E8TAxisProd0131GraphCenterC.qJetBox,
   E8TAxisProd0131GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0131GraphWholeA.qJetBox,
   E8TAxisProd0131GraphWholeB.qJetBox,
   E8TAxisProd0131GraphWholeC.qJetBox,
   E8TAxisProd0131GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1863193613668600711182565096569195526837302596, 1863193613668600711182565096569216262863870990⟩
  | 0, 2 => ⟨6919144058787543304406921963801778831138522977, 6919144058787543304406921963801838398720036938⟩
  | 1, 1 => ⟨6960827976165244107245437759996470000358525188, 6960827976165244107245437759996566810839051962⟩
  | 0, 3 => ⟨17152183961398845381946891950930633061499442170, 17152183961398845381946891950930806295777945989⟩
  | 1, 2 => ⟨23884757215025269748515764609467921856447886759, 23884757215025269748515764609468205537306453535⟩
  | 2, 1 => ⟨24011042059267388283807069246129856085381192518, 24011042059267388283807069246130343860251243895⟩
  | 0, 4 => ⟨35361884575946674294687014363779860082682132596, 35361884575946674294687014363780394585297277496⟩
  | 1, 3 => ⟨55657107615738364657384262000131756143017161335, 55657107615738364657384262000132657266621211699⟩
  | 2, 2 => ⟨76038055799165583870918659075491413292827253864, 76038055799165583870918659075492995806007294527⟩
  | 3, 1 => ⟨76388734330465790656937209339614739261107576735, 76388734330465790656937209339617564519828878232⟩
  | 0, 5 => ⟨-518856589649918679559757951221303111292717751921454, 520368978277824347161296555207396206702954955871553⟩
  | 1, 4 => ⟨-1008629467544382101337972261009802205773653103033073, 1010717765049321576580679348390178723305854044113057⟩
  | 2, 3 => ⟨-1962790664877202753194196407713909036709963023644337, 1965632947129722477288109905516931893450120488937783⟩
  | 3, 2 => ⟨-3821639732142435273393660322870616966707559484691801, 3825290460547293985813940433986207311439415050458478⟩
  | 4, 1 => ⟨-7443078043726293078035744754915240603486294856587092, 7446959405269724730735703303576899040268224483790675⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0131Geometry.ds, E8TAxisProd0131Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1302915670046743055141063531608716441433284457 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0131CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0132CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0132CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0132GraphCenterA.qJetBox,
   E8TAxisProd0132GraphCenterB.qJetBox,
   E8TAxisProd0132GraphCenterC.qJetBox,
   E8TAxisProd0132GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0132GraphWholeA.qJetBox,
   E8TAxisProd0132GraphWholeB.qJetBox,
   E8TAxisProd0132GraphWholeC.qJetBox,
   E8TAxisProd0132GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1486025877512116255275980071907120660893872291, 1486025877512116255275980071907138878137783599⟩
  | 0, 2 => ⟨5601267866359004403874968183836729522239931537, 5601267866359004403874968183836780358433019288⟩
  | 1, 1 => ⟨5649672505406546915369004318564720349483271642, 5649672505406546915369004318564801917785004598⟩
  | 0, 3 => ⟨14050313451161237659839807368372177434790157308, 14050313451161237659839807368372323066389463265⟩
  | 1, 2 => ⟨19656727554296794889924619135127254319522552649, 19656727554296794889924619135127490026490249194⟩
  | 2, 1 => ⟨19805629713296189737132297754592702015221456992, 19805629713296189737132297754593104719302485969⟩
  | 0, 4 => ⟨29303789306851290942120368038251059800825263658, 29303789306851290942120368038251503599600175858⟩
  | 1, 3 => ⟨46428053247628798342557463539076206787412200636, 46428053247628798342557463539076947119348529197⟩
  | 2, 2 => ⟨63656206328541403064516400648404069124285779598, 63656206328541403064516400648405361421539131278⟩
  | 3, 1 => ⟨64077625943906521216489756199436686712623264215, 64077625943906521216489756199438983438571759391⟩
  | 0, 5 => ⟨-363118759800841355134194071954369296004373179351588, 364595398458363026585736944654454071985503542807291⟩
  | 1, 4 => ⟨-703971698465778055230075355144293781447578871375734, 706048060182959928125820642079783468982116432759952⟩
  | 2, 3 => ⟨-1366547819930238792600719578275460783268962805750931, 1369415067875102720183144330043234557035350473858141⟩
  | 3, 2 => ⟨-2654452562982331723712575821927541848488685212510579, 2658161591711447921253996366378658338347955568296013⟩
  | 4, 1 => ⟨-5157883970425412526352639213711552780133680724089201, 5161806916143848101972562004907278672668960851159258⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0132Geometry.ds, E8TAxisProd0132Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1069115055708185225655593824318894893202583707 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0132CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0133CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0133CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0133GraphCenterA.qJetBox,
   E8TAxisProd0133GraphCenterB.qJetBox,
   E8TAxisProd0133GraphCenterC.qJetBox,
   E8TAxisProd0133GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0133GraphWholeA.qJetBox,
   E8TAxisProd0133GraphWholeB.qJetBox,
   E8TAxisProd0133GraphWholeC.qJetBox,
   E8TAxisProd0133GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1169113546356187082176633841576226405784353100, 1169113546356187082176633841576242491232974957⟩
  | 0, 2 => ⟨4489687365524012099388547953427592589029682247, 4489687365524012099388547953427636462677635447⟩
  | 1, 1 => ⟨4529566759974973314929742607083239101364419161, 4529566759974973314929742607083308673423516412⟩
  | 0, 3 => ⟨11406972883496261509816136013230771564543623838, 11406972883496261509816136013230895973253526281⟩
  | 1, 2 => ⟨16026896721741972102146324124168252371113125389, 16026896721741972102146324124168451652514124355⟩
  | 2, 1 => ⟨16151451692848524897426945958410202970924596087, 16151451692848524897426945958410541515292200338⟩
  | 0, 4 => ⟨24059869302538744599640231113059401565746178255, 24059869302538744599640231113059778006355191713⟩
  | 1, 3 => ⟨38384970510766251247599581715447939045482984603, 38384970510766251247599581715448561420140782248⟩
  | 2, 2 => ⟨52799403866651517342470005263176573484200942859, 52799403866651517342470005263177654357443582777⟩
  | 3, 1 => ⟨53158477447448593587679094366311472566905280794, 53158477447448593587679094366313385921832404276⟩
  | 0, 5 => ⟨-253582525228974782185044242378708812104244081140839, 254978287648402998389877228588735325797671075286070⟩
  | 1, 4 => ⟨-490148676845162012956260058212141490447681170611123, 492133944478683567213908946983139279224299505611879⟩
  | 2, 3 => ⟨-948922975711904428881044984384230383748764863174761, 951689029699051975512309137851293342681908067247021⟩
  | 3, 2 => ⟨-1838541291924226836206733507925322186156157503111414, 1842133949286419158872107854325053526109435453929457⟩
  | 4, 1 => ⟨-3563580100726404724073142272781204168507307705654647, 3567364112719419120683832523732063288048441767538590⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0133Geometry.ds, E8TAxisProd0133Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 859293154581076619222001985176526246690067611 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0133CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0134CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0134CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0134GraphCenterA.qJetBox,
   E8TAxisProd0134GraphCenterB.qJetBox,
   E8TAxisProd0134GraphCenterC.qJetBox,
   E8TAxisProd0134GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0134GraphWholeA.qJetBox,
   E8TAxisProd0134GraphWholeB.qJetBox,
   E8TAxisProd0134GraphWholeC.qJetBox,
   E8TAxisProd0134GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1472066538853088700703832897241337516159121553, 1472066538853088700703832897241355667938157506⟩
  | 0, 2 => ⟨5566233514243986600538011789042744256452259683, 5566233514243986600538011789042794882697684138⟩
  | 1, 1 => ⟨5600675536542744384212900695871347825993811054, 5600675536542744384212900695871429045214633158⟩
  | 0, 3 => ⟨13977225313271545051302954143010583456455688397, 13977225313271545051302954143010728462100095708⟩
  | 1, 2 => ⟨19540942493027603598476116058848877190275557488, 19540942493027603598476116058849111849531496970⟩
  | 2, 1 => ⟨19646925422498560043552367530903745722805297216, 19646925422498560043552367530904146594519246229⟩
  | 0, 4 => ⟨29166815469151458948519744947512792602856645499, 29166815469151458948519744947513234402010743576⟩
  | 1, 3 => ⟨46200158111539365146360453819321194773689267487, 46200158111539365146360453819321931689658573990⟩
  | 2, 2 => ⟨63307486137456176451769638442566231415292796362, 63307486137456176451769638442567517626922883552⟩
  | 3, 1 => ⟨63607550232235837272475549920709416559673824592, 63607550232235837272475549920711702262680858236⟩
  | 0, 5 => ⟨-360142860352919382731509631681094405148600069006633, 361616008274823549157430174668609270550339057940559⟩
  | 1, 4 => ⟨-698153482579743238130978129838096928321593743764202, 700224613043225739004843063570884148661812796563269⟩
  | 2, 3 => ⟨-1355162908765034597891650692227498653287586979656141, 1358021410319589168226538566737443354145436290528601⟩
  | 3, 2 => ⟨-2632163662813279229512163523599635792349211416850204, 2635856340869878286570333337826084942361243885544544⟩
  | 4, 1 => ⟨-5114233448869193311003179247299452817470786980507938, 5118123319991894897175927651819505359112361452649756⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0134Geometry.ds, E8TAxisProd0134Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1058697395926342282532913680006542353181531301 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0134CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0135CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0135CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0135GraphCenterA.qJetBox,
   E8TAxisProd0135GraphCenterB.qJetBox,
   E8TAxisProd0135GraphCenterC.qJetBox,
   E8TAxisProd0135GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0135GraphWholeA.qJetBox,
   E8TAxisProd0135GraphWholeB.qJetBox,
   E8TAxisProd0135GraphWholeC.qJetBox,
   E8TAxisProd0135GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1157924912151267726487272219320725011580429204, 1157924912151267726487272219320741041067612568⟩
  | 0, 2 => ⟨4461245001169051280860692126806631870984373342, 4461245001169051280860692126806675571875690527⟩
  | 1, 1 => ⟨4489619271417004483111996359913610860094477063, 4489619271417004483111996359913680149041022290⟩
  | 0, 3 => ⟨11346966245131539412891123293624452154070590343, 11346966245131539412891123293624576058069886483⟩
  | 1, 2 => ⟨15931173951829756714963444150899326538943409553, 15931173951829756714963444150899524986338820385⟩
  | 2, 1 => ⟨16019821641550174411071900933094663708559099311, 16019821641550174411071900933095000802959706612⟩
  | 0, 4 => ⟨23945522091377106888939419971237283715145044000, 23945522091377106888939419971237658569870485590⟩
  | 1, 3 => ⟨38193385186973526469498188393866493089941881434, 38193385186973526469498188393867112788463404237⟩
  | 2, 2 => ⟨52504862096334716208680049468758997237336479773, 52504862096334716208680049468760073369429874312⟩
  | 3, 1 => ⟨52760511812302376522226019769598271698723705202, 52760511812302376522226019769600176492700729559⟩
  | 0, 5 => ⟨-251541231575237720344341121194955327674068976354232, 252930252608709492410048845241412666197151864551118⟩
  | 1, 4 => ⟨-486166033733632152937963148898822608403858217015687, 488140255167472962470705241243882355942621168997412⟩
  | 2, 3 => ⟨-941144559914573396010656770936585812768562358118669, 943891866810843735866786499689175744925864882818603⟩
  | 3, 2 => ⟨-1823340142872492472823733955583987680871160054028028, 1826900069408949093802971023234458738498324539334238⟩
  | 4, 1 => ⟨-3533861430813865742126981560817707667875442642549590, 3537587295136786736843017819690966646176858354365848⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0135Geometry.ds, E8TAxisProd0135Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 850741793571163101654173757645536617339214338 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0135CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0136CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0136CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0136GraphCenterA.qJetBox,
   E8TAxisProd0136GraphCenterB.qJetBox,
   E8TAxisProd0136GraphCenterC.qJetBox,
   E8TAxisProd0136GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0136GraphWholeA.qJetBox,
   E8TAxisProd0136GraphWholeB.qJetBox,
   E8TAxisProd0136GraphWholeC.qJetBox,
   E8TAxisProd0136GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2327036483457859800757964227159498362478350605, 2327036483457859800757964227159522044627605693⟩
  | 0, 2 => ⟨8517505922737973171690862884770828115278181091, 8517505922737973171690862884770898162421516836⟩
  | 1, 1 => ⟨8547572353222231177926668396410876746800968651, 8547572353222231177926668396410991984773600781⟩
  | 0, 3 => ⟨20862495612756498358425572375802154453778330824, 20862495612756498358425572375802361249630144105⟩
  | 1, 2 => ⟨28925047631698501339707730309369193681072200351, 28925047631698501339707730309369536067427976818⟩
  | 2, 1 => ⟨29014717506646281951180467744688070991996338321, 29014717506646281951180467744688663341099744143⟩
  | 0, 4 => ⟨42483445660989689574118721445244115399102652868, 42483445660989689574118721445244761849077481495⟩
  | 1, 3 => ⟨66458285707283118686764547605619052222994552731, 66458285707283118686764547605620152934253698766⟩
  | 2, 2 => ⟨90492327192976124291224814298967118469458716253, 90492327192976124291224814298969062698413677653⟩
  | 3, 1 => ⟨90736447058609989491339749472961479268178297001, 90736447058609989491339749472964965590055665479⟩
  | 0, 5 => ⟨-743978916379338287192294534198779359750281951626011, 745575524415009437723939952590163626563409603315202⟩
  | 1, 4 => ⟨-1449859886159726288526434735549397567585499619841725, 1452029137715965662546199255029717786024112355188392⟩
  | 2, 3 => ⟨-2827907508936458440316623380943434050633736934698422, 2830823346532767445267414521913812518369932285451142⟩
  | 3, 2 => ⟨-5518233575513080026096685659985706332501990468282905, 5521967255980985250565367865896395128213389690930706⟩
  | 4, 1 => ⟨-10770764532420314022199431212306164285253160165014348, 10774803535268843492680262100982176189096379443385221⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0136Geometry.ds, E8TAxisProd0136Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1569091393865276014106339634397986435506435337 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0136CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0137CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0137CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0137GraphCenterA.qJetBox,
   E8TAxisProd0137GraphCenterB.qJetBox,
   E8TAxisProd0137GraphCenterC.qJetBox,
   E8TAxisProd0137GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0137GraphWholeA.qJetBox,
   E8TAxisProd0137GraphWholeB.qJetBox,
   E8TAxisProd0137GraphWholeC.qJetBox,
   E8TAxisProd0137GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1845949262114208674417865638393076235242436982, 1845949262114208674417865638393096894909895397⟩
  | 0, 2 => ⟨6876373935305954928052750474393313066115076458, 6876373935305954928052750474393372379226680831⟩
  | 1, 1 => ⟨6901289731500931414968596923190884993884347856, 6901289731500931414968596923190981375326041184⟩
  | 0, 3 => ⟨17063982542319563184314172355654261886914228304, 17063982542319563184314172355654434343147343465⟩
  | 1, 2 => ⟨23745950434780479990605011585772263193095056632, 23745950434780479990605011585772545555098537011⟩
  | 2, 1 => ⟨23821458695962515970296893331173189376099201544, 23821458695962515970296893331173674828769704981⟩
  | 0, 4 => ⟨35199360263936389036609222390611129149839621199, 35199360263936389036609222390611661100727777585⟩
  | 1, 3 => ⟨55388503496864894835813552586023342518619209757, 55388503496864894835813552586024239227472010127⟩
  | 2, 2 => ⟨75628932392662647763553508261668854355617548830, 75628932392662647763553508261670428952308528707⟩
  | 3, 1 => ⟨75838693292128311296797957263852999482942088299, 75838693292128311296797957263855810340664031559⟩
  | 0, 5 => ⟨-514545733494332833623592539788572810371630515076083, 516060061853320245762400076963270812176911424001738⟩
  | 1, 4 => ⟨-1000184244684270802299955940278226291221478516956181, 1002275352015422402702886613429930606844633145976687⟩
  | 2, 3 => ⟨-1946234435612397295156946074928625910717011653870303, 1949079844611741516829742013452630749132973127738245⟩
  | 3, 2 => ⟨-3789168692493699145056794618089124017184250057062658, 3792821434939750950996540837588895572695618981573277⟩
  | 4, 1 => ⟨-7379375896817762763042955788377054262841835271243411, 7383256558242334887040096959231288218374818938795493⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0137Geometry.ds, E8TAxisProd0137Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1290430623358401697121731797461713592305682884 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0137CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0138CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0138CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0138GraphCenterA.qJetBox,
   E8TAxisProd0138GraphCenterB.qJetBox,
   E8TAxisProd0138GraphCenterC.qJetBox,
   E8TAxisProd0138GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0138GraphWholeA.qJetBox,
   E8TAxisProd0138GraphWholeB.qJetBox,
   E8TAxisProd0138GraphWholeC.qJetBox,
   E8TAxisProd0138GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1458194558030251745948996701437014632945243762, 1458194558030251745948996701437032720807849457⟩
  | 0, 2 => ⟨5531381455020333341780514833142385743022174989, 5531381455020333341780514833142436168372941968⟩
  | 1, 1 => ⟨5551967319173551705277472211836331608127590484, 5551967319173551705277472211836412494823801260⟩
  | 0, 3 => ⟨13904478902323647826436981725713076421717157818, 13904478902323647826436981725713220838697173453⟩
  | 1, 2 => ⟨19425725953478588719100692991671404035109169649, 19425725953478588719100692991671637714198464862⟩
  | 2, 1 => ⟨19489090985853748103168018173184342576319918300, 19489090985853748103168018173184741737437294358⟩
  | 0, 4 => ⟨29030407421832595780492742026320593135174329746, 29030407421832595780492742026321033083745739465⟩
  | 1, 3 => ⟨45973235288395810432908323234923850610086101889, 45973235288395810432908323234924584384036395616⟩
  | 2, 2 => ⟨62960322053114524504451147239585991287206985444, 62960322053114524504451147239587271916392904113⟩
  | 3, 1 => ⟨63139792106605010459942767440889988619869088807, 63139792106605010459942767440892264221440919982⟩
  | 0, 5 => ⟨-357191015704581422835712379829670543792570300887428, 358663961584075348519058078002319612137698187101828⟩
  | 1, 4 => ⟨-692382549298538973933935595726771573375101917598781, 694452313151492388417211259810467554299871699459678⟩
  | 2, 3 => ⟨-1343870992256686539528660590489632260116747493424383, 1346724415134763319401429858299384082485309158644765⟩
  | 3, 2 => ⟨-2610057734272708271331719543843263443393724402271763, 2613735997728779475724687145709855478079367324766773⟩
  | 4, 1 => ⟨-5070943033904206046432023856553775788400209027774520, 5074798344975731141475986088092889263110015952423768⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0138Geometry.ds, E8TAxisProd0138Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1048341919328545177833119781438214187496265910 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0138CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0139CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0139CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0139GraphCenterA.qJetBox,
   E8TAxisProd0139GraphCenterB.qJetBox,
   E8TAxisProd0139GraphCenterC.qJetBox,
   E8TAxisProd0139GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0139GraphWholeA.qJetBox,
   E8TAxisProd0139GraphWholeB.qJetBox,
   E8TAxisProd0139GraphWholeC.qJetBox,
   E8TAxisProd0139GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1146807196633955064144003590263654220612307167, 1146807196633955064144003590263670194337454630⟩
  | 0, 2 => ⟨4432952296578899672193743333718354606597707105, 4432952296578899672193743333718398135414503594⟩
  | 1, 1 => ⟨4449910491952420383396115844993862218286039595, 4449910491952420383396115844993931225268563205⟩
  | 0, 3 => ⟨11287244870258342705925746443112506606297031838, 11287244870258342705925746443112630007599159176⟩
  | 1, 2 => ⟨15835929098261141559989171176980167656852534573, 15835929098261141559989171176980365273615986982⟩
  | 2, 1 => ⟨15888926259875643280018922716082970125881765525, 15888926259875643280018922716083305776235625751⟩
  | 0, 4 => ⟨23831658217619938637793379048123999377130902707, 23831658217619938637793379048124372652370316343⟩
  | 1, 3 => ⟨38002636918640641129327262694441723619148662012, 38002636918640641129327262694442340652404393745⟩
  | 2, 2 => ⟨52211667315971875606114250625541714017494594930, 52211667315971875606114250625542785427765463286⟩
  | 3, 1 => ⟨52364559701725192011404702317711163036513030081, 52364559701725192011404702317713059304609531632⟩
  | 0, 5 => ⟨-249516300534807699704831737232559398878991729469392, 250901247877555637218417255196857255056639179104559⟩
  | 1, 4 => ⟨-482215498546468198202040650019769883577916754149588, 484181874317410762079900638006657980618660650055586⟩
  | 2, 3 => ⟨-933429194160763852118860345486216302920449246033162, 936160955752092828518664603970111326882866891791788⟩
  | 3, 2 => ⟨-1808262862461896106701456270983088142413759300024967, 1811792200479502040584457705974479080132780201986482⟩
  | 4, 1 => ⟨-3504386194290988759029250109364093424401560018493187, 3508053942254093827817902970560221339045334335750592⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0139Geometry.ds, E8TAxisProd0139Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 842242814605883254463331344829628698281426397 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0139CertifiedArithmetic

end


