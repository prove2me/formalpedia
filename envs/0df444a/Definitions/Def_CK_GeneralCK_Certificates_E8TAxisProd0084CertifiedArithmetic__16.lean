-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0084CertifiedArithmetic__16
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0084CertifiedArithmetic__16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T13:49:10.236983+00:00
-- url     : https://prove2.me/theorems/821a51e4-ba41-4928-9c4e-5d3b175aadf3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0084CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0085CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0084CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0085CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0086CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0089CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0090CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0091CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0092CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0094CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0095CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0096CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0097CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0098CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0099CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0100CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0101CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0102CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0084CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0085CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0086CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0089CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0090CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0091CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0092CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0094CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0095CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0096CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0097CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0098CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0099CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0100CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0101CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0102CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0084CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0085CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0086CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0089CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0090CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0091CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0092CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0094CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0095CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0096CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0097CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0098CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0099CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0100CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0101CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0102CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0084CertifiedArithmetic (+15 modules: GeneralCK/Certificates/E8TAxisProd0085CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0086CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0089CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0090CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0091CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0092CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0094CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0095CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0096CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0097CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0098CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0099CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0100CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0101CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0102CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0071GraphCenterA__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0071GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0083GraphCenterC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0075GraphCenterD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0083GraphWholeA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0069GraphWholeB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0076GraphWholeC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0077GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0077Geometry__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0089GraphWholeB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0092GraphCenterD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0094GraphCenterA__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0095GraphCenterB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0095GraphWholeD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0097GraphWholeC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0099GraphWholeA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0100GraphCenterC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0101Geometry__22

-- ===== source module GeneralCK.Certificates.E8TAxisProd0084CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0084CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0084GraphCenterA.qJetBox,
   E8TAxisProd0084GraphCenterB.qJetBox,
   E8TAxisProd0084GraphCenterC.qJetBox,
   E8TAxisProd0084GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0084GraphWholeA.qJetBox,
   E8TAxisProd0084GraphWholeB.qJetBox,
   E8TAxisProd0084GraphWholeC.qJetBox,
   E8TAxisProd0084GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨999152456440435458928148611267728951232714, 999152456440435458928148611269648586322643⟩
  | 0, 2 => ⟨9518477781972690624077583860212463558885768, 9518477781972690624077583860217080352311678⟩
  | 1, 1 => ⟨9846930821155052355909090284571682363761063, 9846930821155052355909090284577333043739029⟩
  | 0, 3 => ⟨47394310245749309280014309932165021196236508, 47394310245749309280014309932173679896027116⟩
  | 1, 2 => ⟨77616779433383951945260635254485681609451462, 77616779433383951945260635254495764658859179⟩
  | 2, 1 => ⟨79681860837975487030805024998729317468779098, 79681860837975487030805024998743246777463298⟩
  | 0, 4 => ⟨129130531032126518298160388267334687454051992, 129130531032126518298160388267358216523385857⟩
  | 1, 3 => ⟨313530912338087038212785553436827587288186256, 313530912338087038212785553436855467945395461⟩
  | 2, 2 => ⟨501925284793658838593802862256136806865068490, 501925284793658838593802862256176029799453311⟩
  | 3, 1 => ⟨511610741730474471002954328980327040910779105, 511610741730474471002954328980388060505218539⟩
  | 0, 5 => ⟨-508577937796097657180833037611298660562983526088, 515059266802820683000109572684066181340963826565⟩
  | 1, 4 => ⟨-849531486614052405743620156559532809078200030695, 850850258709910063413534784100577013251924474763⟩
  | 2, 3 => ⟨-1452484902908429609947268419419332512383135741248, 1447489475646941659839312196674963747802589319295⟩
  | 3, 2 => ⟨-2496349434055697751040311476551303648880841340976, 2485365770867133663859487045584167602097393035192⟩
  | 4, 1 => ⟨-4272234955978155395738036228757916862385965373137, 4262504641747528171317182824715366574311690919516⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0084Geometry.ds, E8TAxisProd0084Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 808973535194491807261627027018773968742263 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0084CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0085CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0085CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0085GraphCenterA.qJetBox,
   E8TAxisProd0085GraphCenterB.qJetBox,
   E8TAxisProd0085GraphCenterC.qJetBox,
   E8TAxisProd0085GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0085GraphWholeA.qJetBox,
   E8TAxisProd0085GraphWholeB.qJetBox,
   E8TAxisProd0085GraphWholeC.qJetBox,
   E8TAxisProd0085GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5419540550378359522220496053178847368296266, 5419540550378359522220496053181543242804121⟩
  | 0, 2 => ⟨39319623805064292043126160426980486913522460, 39319623805064292043126160426986521060385948⟩
  | 1, 1 => ⟨39981796959029839900522789493880381150653286, 39981796959029839900522789493887965040649488⟩
  | 0, 3 => ⟨153994031238055177784753871153265963348554796, 153994031238055177784753871153278425780652502⟩
  | 1, 2 => ⟨243896682124662194970366404029401941547621928, 243896682124662194970366404029417238026034745⟩
  | 2, 1 => ⟨247129665477709637331869247649110647997207131, 247129665477709637331869247649132827704936168⟩
  | 0, 4 => ⟨375852509806937532288309999892011432903506748, 375852509806937532288309999892044722127910548⟩
  | 1, 3 => ⟨808629387813896603306110082540974752417616453, 808629387813896603306110082541016721693866821⟩
  | 2, 2 => ⟨1245999118081424988432141500914945554987882144, 1245999118081424988432141500915007623942937927⟩
  | 3, 1 => ⟨1258619025288210501007731530498034226526738793, 1258619025288210501007731530498133255898978369⟩
  | 0, 5 => ⟨-5280642589760598867295154262255931817391365923106, 5307028790133527692654888831207167538313933927728⟩
  | 1, 4 => ⟨-9449832417169798100614387321989746436658025650946, 9452980524207425288999473047194186694081625041947⟩
  | 2, 3 => ⟨-17079441680403106376807571894325307796008363821842, 17052499398311216567413584530830124147337253686552⟩
  | 3, 2 => ⟨-30938160523139146204545471782993864994824205504313, 30883771108361796544628876241776912176969806453248⟩
  | 4, 1 => ⟨-55951502813740484648249548974196176087082565917399, 55908847633661980227638181779349221001792539331477⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0085Geometry.ds, E8TAxisProd0085Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1280052181231084586759796257234335000221627 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0085CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0086CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0086CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0086GraphCenterA.qJetBox,
   E8TAxisProd0086GraphCenterB.qJetBox,
   E8TAxisProd0086GraphCenterC.qJetBox,
   E8TAxisProd0086GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0086GraphWholeA.qJetBox,
   E8TAxisProd0086GraphWholeB.qJetBox,
   E8TAxisProd0086GraphWholeC.qJetBox,
   E8TAxisProd0086GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3355350745736789656642017316731176460845618, 3355350745736789656642017316733609404174325⟩
  | 0, 2 => ⟨26308041486313010822773298755360413276455333, 26308041486313010822773298755365945963143927⟩
  | 1, 1 => ⟨26791207219550438225180971129195398115232538, 26791207219550438225180971129202285166772250⟩
  | 0, 3 => ⟨109844400892171382621907012959622948983808766, 109844400892171382621907012959634063355923219⟩
  | 1, 2 => ⟨175522980640576383076187890982367578894662565, 175522980640576383076187890982380992487237774⟩
  | 2, 1 => ⟨178042541986943900233315970336069911321601521, 178042541986943900233315970336089092249041232⟩
  | 0, 4 => ⟨274788258327082028317375020502963744075776276, 274788258327082028317375020502993518873015580⟩
  | 1, 3 => ⟨611976716047804571713159715889197991926687066, 611976716047804571713159715889234807772251018⟩
  | 2, 2 => ⟨953055890802302640953287204032793881022865668, 953055890802302640953287204032847542317294055⟩
  | 3, 1 => ⟨963340802102477468619002035290740475638982441, 963340802102477468619002035290825436995717391⟩
  | 0, 5 => ⟨-4435038234294210065274412585843157758763469519092, 4456253291683382282627402518283628326760925942677⟩
  | 1, 4 => ⟨-7883555415458535774560755184041857918378229742441, 7882220855467840141035893108028175904870594099178⟩
  | 2, 3 => ⟨-14160595653552919020174427911206363560361696877447, 14130020792407638345212822105827917857412667822028⟩
  | 3, 2 => ⟨-25487920966705264326331405807256764973931207437880, 25430276905229000954130282189513991373323275130553⟩
  | 4, 1 => ⟨-45774195460366672608080041261654983984856716711756, 45726197823272142440438588724605192272594463585603⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0086Geometry.ds, E8TAxisProd0086Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 179985948695772840223022883771577573953815 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0086CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0089CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0089CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0089GraphCenterA.qJetBox,
   E8TAxisProd0089GraphCenterB.qJetBox,
   E8TAxisProd0089GraphCenterC.qJetBox,
   E8TAxisProd0089GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0089GraphWholeA.qJetBox,
   E8TAxisProd0089GraphWholeB.qJetBox,
   E8TAxisProd0089GraphWholeC.qJetBox,
   E8TAxisProd0089GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1318156639859333749031504820843862520243889, 1318156639859333749031504820845884281565033⟩
  | 0, 2 => ⟨12057581010701223309167449636186264605125869, 12057581010701223309167449636191056202856689⟩
  | 1, 1 => ⟨12364749613104982681024089101657481541359743, 12364749613104982681024089101663364819978884⟩
  | 0, 3 => ⟨57628799517040358004525613314026570749370923, 57628799517040358004525613314035698783224058⟩
  | 1, 2 => ⟨93652113187385064589309150305514831482967805, 93652113187385064589309150305525541819034073⟩
  | 2, 1 => ⟨95496312716128602276989332260810774692461706, 95496312716128602276989332260825689597406656⟩
  | 0, 4 => ⟨153514822662573160972460019460173863027154183, 153514822662573160972460019460198568159145357⟩
  | 1, 3 => ⟨365067974641140094676959536000215332913678246, 365067974641140094676959536000244877610243419⟩
  | 2, 2 => ⟨579999975188822559599308574438660850446009802, 579999975188822559599308574438702750805369023⟩
  | 3, 1 => ⟨588346075587505634584189538976724660856284980, 588346075587505634584189538976790094831611451⟩
  | 0, 5 => ⟨-541097904641137617615284405990944082970513588127, 547800077966644260486543855688745596140958776371⟩
  | 1, 4 => ⟨-906804460990610190413917303807017790086328093264, 908158120174234360263238063442538379391962024870⟩
  | 2, 3 => ⟨-1555074218453759432081841275365176513814007565927, 1549873153738812116401780231305826124400167390592⟩
  | 3, 2 => ⟨-2681150343596820651270047989476490618244504295599, 2669753871092858907636048460055077299833052923790⟩
  | 4, 1 => ⟨-4605391558880359362412804759419561671658600247513, 4595468193919002705955264509235637960965434880908⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0089Geometry.ds, E8TAxisProd0089Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1082165574313236493510194446425650468964414 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0089CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0090CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0090CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0090GraphCenterA.qJetBox,
   E8TAxisProd0090GraphCenterB.qJetBox,
   E8TAxisProd0090GraphCenterC.qJetBox,
   E8TAxisProd0090GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0090GraphWholeA.qJetBox,
   E8TAxisProd0090GraphWholeB.qJetBox,
   E8TAxisProd0090GraphWholeC.qJetBox,
   E8TAxisProd0090GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨975504033318090519250283174634679374677676, 975504033318090519250283174636591585647564⟩
  | 0, 2 => ⟨9400394914681133505447943248770269772810779, 9400394914681133505447943248774873321110977⟩
  | 1, 1 => ⟨9653866716977099504623388036251407398019156, 9653866716977099504623388036257042355542832⟩
  | 0, 3 => ⟨47072233016763092146010267411014841127494177, 47072233016763092146010267411023465704191315⟩
  | 1, 2 => ⟨76835278762133686004489236417860985471679864, 76835278762133686004489236417871027710155028⟩
  | 2, 1 => ⟨78432076253061162058093182991263285842143899, 78432076253061162058093182991277155825777081⟩
  | 0, 4 => ⟨128531900526917963606893929536327804452280988, 128531900526917963606893929536351249839884819⟩
  | 1, 3 => ⟨311671263856072958236150196072221394388030875, 311671263856072958236150196072249172701550327⟩
  | 2, 2 => ⟨497906067478024680965589770322514714531802085, 497906067478024680965589770322553781165809107⟩
  | 3, 1 => ⟨505406880548214545347936705379141793042217412, 505406880548214545347936705379202554122142383⟩
  | 0, 5 => ⟨-506566686843881243017482927884942018616598714566, 513122044043712412420372440342912657486157480102⟩
  | 1, 4 => ⟨-845978222333418211386912810721258543632062478347, 847422913801622106713567968022034089560215350672⟩
  | 2, 3 => ⟨-1446041677902937564714076709326737057984875010473, 1441229812444924338481057659728157952757645587876⟩
  | 3, 2 => ⟨-2484508871511866991957192182929448646843881032487, 2473772332312888663904947178267629567379232380587⟩
  | 4, 1 => ⟨-4250304351560758038544552919015450203257864432523, 4240921700236765498319638964406807704595587672785⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0090Geometry.ds, E8TAxisProd0090Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 788726507057132190297500587597723901405042 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0090CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0091CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0091CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0091GraphCenterA.qJetBox,
   E8TAxisProd0091GraphCenterB.qJetBox,
   E8TAxisProd0091GraphCenterC.qJetBox,
   E8TAxisProd0091GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0091GraphWholeA.qJetBox,
   E8TAxisProd0091GraphWholeB.qJetBox,
   E8TAxisProd0091GraphWholeC.qJetBox,
   E8TAxisProd0091GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1288192378027167563199279763034955577069651, 1288192378027167563199279763036969671530415⟩
  | 0, 2 => ⟨11913987987121147130562170797372144442207833, 11913987987121147130562170797376922143152458⟩
  | 1, 1 => ⟨12131757932167754167761367927340295515515152, 12131757932167754167761367927346162162889814⟩
  | 0, 3 => ⟨57245922310621495181343160259257245838742775, 57245922310621495181343160259266338157381374⟩
  | 1, 2 => ⟨92742124526800893426466810338424449864343528, 92742124526800893426466810338435117071088303⟩
  | 2, 1 => ⟨94051984095294329596069761223223623751358149, 94051984095294329596069761223238475530577798⟩
  | 0, 4 => ⟨152787709699079338831153039976269006200049679, 152787709699079338831153039976293623081024651⟩
  | 1, 3 => ⟨362924859031668213881006219113540608741743704, 362924859031668213881006219113570044365126422⟩
  | 2, 2 => ⟨575467088179627041165110604229701836419613560, 575467088179627041165110604229743569287458016⟩
  | 3, 1 => ⟨581403333055223015713185752861559401151355500, 581403333055223015713185752861624557402217667⟩
  | 0, 5 => ⟨-538954237744731008463356084024184586129260195643, 545733343434864805015541046243475630761989890524⟩
  | 1, 4 => ⟨-903008710039305301396327462850508636399616451806, 904491799928544520425946808585283777163709506449⟩
  | 2, 3 => ⟨-1548180329484341878305894856187584737308753641448, 1543166778782283108814162648640501785904636486663⟩
  | 3, 2 => ⟨-2668465415572701662206500919376798204634917734251, 2657320266037136358205526655516739280139299500364⟩
  | 4, 1 => ⟨-4581870792268160542219811343613179618928986317053, 4572300701595143973386988944279967108655741979644⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0091Geometry.ds, E8TAxisProd0091Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1056289984739821350382947576873363976030150 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0091CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0092CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0092CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0092GraphCenterA.qJetBox,
   E8TAxisProd0092GraphCenterB.qJetBox,
   E8TAxisProd0092GraphCenterC.qJetBox,
   E8TAxisProd0092GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0092GraphWholeA.qJetBox,
   E8TAxisProd0092GraphWholeB.qJetBox,
   E8TAxisProd0092GraphWholeC.qJetBox,
   E8TAxisProd0092GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨952149812429036870089847354998783846022589, 952149812429036870089847355000688650279503⟩
  | 0, 2 => ⟨9283115373789890681827979655986305660791705, 9283115373789890681827979655990896009848953⟩
  | 1, 1 => ⟨9462750563306540537539237502208409111343696, 9462750563306540537539237502214028401935676⟩
  | 0, 3 => ⟨46751647507879633424442990568034067538918164, 46751647507879633424442990568042658100288284⟩
  | 1, 2 => ⟨76058414940830521717096616698547385337115008, 76058414940830521717096616698557386898778842⟩
  | 2, 1 => ⟨77192312130778286299814187487133215760425445, 77192312130778286299814187487147026626350540⟩
  | 0, 4 => ⟨127937152307157434308214815497275180137511608, 127937152307157434308214815497298542151280099⟩
  | 1, 3 => ⟨309821423310330117391133856955120185793631434, 309821423310330117391133856955147862148809435⟩
  | 2, 2 => ⟨493908893951549321918679794487703436274208307, 493908893951549321918679794487742347210338402⟩
  | 3, 1 => ⟨499243618033987482820708459885775736470000916, 499243618033987482820708459885836240050928906⟩
  | 0, 5 => ⟨-504563119110095760760666800089086908277074197509, 511192716474346398257105187853833503606767645127⟩
  | 1, 4 => ⟨-842438306580059041030938625425730770264082621482, 844008797899172367990996250634874856821620352375⟩
  | 2, 3 => ⟨-1439622794370802168734726717990512034090747395395, 1434994108539789398792786569067106120837268036819⟩
  | 3, 2 => ⟨-2472713747780635531515189602182552352988461385516, 2462223811143524802899506397762085873424909588824⟩
  | 4, 1 => ⟨-4228459269842436116425076404070191623798353624110, 4219423508097513676783536055056088850153994438710⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0092Geometry.ds, E8TAxisProd0092Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 768740645143038236622899856859690114818045 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0092CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0094CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0094CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0094GraphCenterA.qJetBox,
   E8TAxisProd0094GraphCenterB.qJetBox,
   E8TAxisProd0094GraphCenterC.qJetBox,
   E8TAxisProd0094GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0094GraphWholeA.qJetBox,
   E8TAxisProd0094GraphWholeB.qJetBox,
   E8TAxisProd0094GraphWholeC.qJetBox,
   E8TAxisProd0094GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1258585904153210378918651125299421802979123, 1258585904153210378918651125301428248757749⟩
  | 0, 2 => ⟨11771349889119260960627498192173334254802105, 11771349889119260960627498192178098106957524⟩
  | 1, 1 => ⟨11901034537536981465971576847036053744032754, 11901034537536981465971576847041903818875645⟩
  | 0, 3 => ⟨56864857140430100501289244607211798486977458, 56864857140430100501289244607220855204221043⟩
  | 1, 2 => ⟨91837479392209961944388751996076877995851491, 91837479392209961944388751996087502216508296⟩
  | 2, 1 => ⟨92618956500077891135705092842720846299023935, 92618956500077891135705092842735635175009588⟩
  | 0, 4 => ⟨152065190477355267186069246361114569684953243, 152065190477355267186069246361139098640163275⟩
  | 1, 3 => ⟨360793143452259084635356364681596774404955233, 360793143452259084635356364681626101367177138⟩
  | 2, 2 => ⟨570959131376756434901297102403299394799679550, 570959131376756434901297102403340960823452815⟩
  | 3, 1 => ⟨574505782358422358161472029677274241296478736, 574505782358422358161472029677339120916679628⟩
  | 0, 5 => ⟨-536818456438517983964963558274198118546869436239, 543674214769917765566087551108110892204401931418⟩
  | 1, 4 => ⟨-899227172456808890336794547900832363375856208884, 900839292513705183147934613527959680964001692498⟩
  | 2, 3 => ⟨-1541312657577059876333472217423749216942582954491, 1536486119363345867721948594034706143051645764249⟩
  | 3, 2 => ⟨-2655829480816933246740303958436663083633860443703, 2644935079134749006692809653162057358845960045454⟩
  | 4, 1 => ⟨-4558442312749813708404535030938634002856278351500, 4549224792277950173659501033279597054501755755741⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0094Geometry.ds, E8TAxisProd0094Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1030733758810969683866078976665103932680606 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0094CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0095CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0095CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0095GraphCenterA.qJetBox,
   E8TAxisProd0095GraphCenterB.qJetBox,
   E8TAxisProd0095GraphCenterC.qJetBox,
   E8TAxisProd0095GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0095GraphWholeA.qJetBox,
   E8TAxisProd0095GraphWholeB.qJetBox,
   E8TAxisProd0095GraphWholeC.qJetBox,
   E8TAxisProd0095GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨929087790108799238712063146632837579720878, 929087790108799238712063146634734994617749⟩
  | 0, 2 => ⟨9166635442114356122961305221639272668855461, 9166635442114356122961305221643849864409689⟩
  | 1, 1 => ⟨9273570798611687611732209165115095620663766, 9273570798611687611732209165120699299665992⟩
  | 0, 3 => ⟨46432544033164267184639606105101659750691795, 46432544033164267184639606105110216404094412⟩
  | 1, 2 => ⟨75286163517552109133769392825045552736522557, 75286163517552109133769392825055513754983123⟩
  | 2, 1 => ⟨75962513516923161830295772777578600849798795, 75962513516923161830295772777592352804563828⟩
  | 0, 4 => ⟨127346270566374720014986056369658609732062421, 127346270566374720014986056369681888678744943⟩
  | 1, 3 => ⟨307981336409046213607714442469809324318653140, 307981336409046213607714442469836899099364576⟩
  | 2, 2 => ⟨489933640101938262842376028378041401608351825, 489933640101938262842376028378080157446772253⟩
  | 3, 1 => ⟨493120726350943290951448077292039112534090840, 493120726350943290951448077292099359627575531⟩
  | 0, 5 => ⟨-502566863543412806795228172201772629904995178008, 509270428855929970949591739916490141138101964231⟩
  | 1, 4 => ⟨-838911547044715468974923444946019463815684190043, 840607441244409977442369978635832556480021777930⟩
  | 2, 3 => ⟨-1433228148661129820745566279055052718281964014019, 1428782132921332683716963143881031108208962205375⟩
  | 3, 2 => ⟨-2460963877409169449934189989524057645320960811902, 2450719936057838542638272100680542095179781828481⟩
  | 4, 1 => ⟨-4206699368913537426249439365206858552428285870111, 4198009721205029248667969214628184261193819649269⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0095Geometry.ds, E8TAxisProd0095Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 749014139449917015342268889380519224089581 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0095CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0096CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0096CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0096GraphCenterA.qJetBox,
   E8TAxisProd0096GraphCenterB.qJetBox,
   E8TAxisProd0096GraphCenterC.qJetBox,
   E8TAxisProd0096GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0096GraphWholeA.qJetBox,
   E8TAxisProd0096GraphWholeB.qJetBox,
   E8TAxisProd0096GraphWholeC.qJetBox,
   E8TAxisProd0096GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2457170162974894966214484463279463774918984460, 2457170162974894966214484463279487994613252273⟩
  | 0, 2 => ⟨8835266257919945378210070005389698066751619794, 8835266257919945378210070005389769950179130408⟩
  | 1, 1 => ⟨8988996105873461332555538682686567590609349027, 8988996105873461332555538682686685956967802236⟩
  | 0, 3 => ⟨21508467211945002380085767057186529600519762621, 21508467211945002380085767057186742062596374575⟩
  | 1, 2 => ⟨29936247335335675852931159185674851348269156009, 29936247335335675852931159185675203418897464930⟩
  | 2, 1 => ⟨30393837208221432212113069356595681158827190759, 30393837208221432212113069356596290640335593095⟩
  | 0, 4 => ⟨43650708394708143405095553626485488147418041885, 43650708394708143405095553626486153332886774096⟩
  | 1, 3 => ⟨68376147102689693949516969910013840646660681355, 68376147102689693949516969910014974001478836898⟩
  | 2, 2 => ⟨93402663107430290031225670290389691851936983477, 93402663107430290031225670290391694841003872460⟩
  | 3, 1 => ⟨94645345564679402048111138990606212591082797820, 94645345564679402048111138990609806124195610190⟩
  | 0, 5 => ⟨-782046936580877593198082386064846668365529194598564, 783634301074866667998270999465728726437547552327210⟩
  | 1, 4 => ⟨-1524575388902774906788339626277992265707305461830837, 1526713993556576944821560625237901651958690610519638⟩
  | 2, 3 => ⟨-2974635801580571956855750738187977340314677421414387, 2977478678851771404965927567709872621251143416409621⟩
  | 3, 2 => ⟨-5806487545467811524147420355076331908902322755706846, 5810067389311561496130188883800258244180217987361734⟩
  | 4, 1 => ⟨-11337194377680956361653440115224738684508406118955346, 11340924678919898862531193121377835826335079981581847⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0096Geometry.ds, E8TAxisProd0096Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1659914239926501600290228037028697633819380834 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0096CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0097CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0097CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0097GraphCenterA.qJetBox,
   E8TAxisProd0097GraphCenterB.qJetBox,
   E8TAxisProd0097GraphCenterC.qJetBox,
   E8TAxisProd0097GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0097GraphWholeA.qJetBox,
   E8TAxisProd0097GraphWholeB.qJetBox,
   E8TAxisProd0097GraphWholeC.qJetBox,
   E8TAxisProd0097GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1951034506339457709110694758292548812657902518, 1951034506339457709110694758292569934893647299⟩
  | 0, 2 => ⟨7136330317944226304642596059298116664356528403, 7136330317944226304642596059298177520953935052⟩
  | 1, 1 => ⟨7263770883934318899445041949555047851251406319, 7263770883934318899445041949555146835816683935⟩
  | 0, 3 => ⟨17599331130419081847304696566757404943342204188, 17599331130419081847304696566757582120884574520⟩
  | 1, 2 => ⟨24588941243143669342966522267993208547823902916, 24588941243143669342966522267993498914219044907⟩
  | 2, 1 => ⟨24974424341542474956982561450337482129556122993, 24974424341542474956982561450337981677877722838⟩
  | 0, 4 => ⟨36184430142453273714601128820396063773858259714, 36184430142453273714601128820396611216793935946⟩
  | 1, 3 => ⟨57017059122122487676300249219477161667962031292, 57017059122122487676300249219478085182372753371⟩
  | 2, 2 => ⟨78110628131758573346596248914912092559111047240, 78110628131758573346596248914913715226284151015⟩
  | 3, 1 => ⟨79178946966153846076899628142036990705590629497, 79178946966153846076899628142039889015913069398⟩
  | 0, 5 => ⟨-540947641739304695199305712496742043604072420292196, 542470563709233185481244096029881939025410788003235⟩
  | 1, 4 => ⟨-1051912258989175028556524051876734832618691783896417, 1054009664233355700523740493725880814258875931325595⟩
  | 2, 3 => ⟨-2047653192310180721058236261948574596238985206011990, 2050500178747224077394611520898305171579971545413297⟩
  | 3, 2 => ⟨-3988096218053167037732365299254333698791478367862471, 3991743023952095160328837851971123096465970372333776⟩
  | 4, 1 => ⟨-7769672236964012069138315258729627449595367046742023, 7773535275138640270726637427297138973365821437293245⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0097Geometry.ds, E8TAxisProd0097Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1366436312818526258359064777434276985334841514 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0097CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0098CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0098CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0098GraphCenterA.qJetBox,
   E8TAxisProd0098GraphCenterB.qJetBox,
   E8TAxisProd0098GraphCenterC.qJetBox,
   E8TAxisProd0098GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0098GraphWholeA.qJetBox,
   E8TAxisProd0098GraphWholeB.qJetBox,
   E8TAxisProd0098GraphWholeC.qJetBox,
   E8TAxisProd0098GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2435149097744472677639575437596043517362753455, 2435149097744472677639575437596067646597536784⟩
  | 0, 2 => ⟨8781631293498129433524062535575079525159293457, 8781631293498129433524062535575151099230142956⟩
  | 1, 1 => ⟨8914368826295461488126645972450732256330649120, 8914368826295461488126645972450850095497862372⟩
  | 0, 3 => ⟨21399586187095439057232200942641575271390695449, 21399586187095439057232200942641786778594703487⟩
  | 1, 2 => ⟨29765710870086392342862844159249178964043825189, 29765710870086392342862844159249529402363982579⟩
  | 2, 1 => ⟨30160943757670809289804439759948652346519858337, 30160943757670809289804439759949258939916580570⟩
  | 0, 4 => ⟨43454240541266705051584089460770308153683690147, 43454240541266705051584089460770970180708992438⟩
  | 1, 3 => ⟨68053243774917309901379439743255025510569467809, 68053243774917309901379439743256153361548550359⟩
  | 2, 2 => ⟨92912443752514987066907402686317613581437533775, 92912443752514987066907402686319606662431785773⟩
  | 3, 1 => ⟨93986225107213912395038574584279341020762882948, 93986225107213912395038574584282916474422168060⟩
  | 0, 5 => ⟨-775574516987253308072775008765158452210595181817964, 777162942808879206620079099938128049304445730471080⟩
  | 1, 4 => ⟨-1511871026674432326735973238988803733698208026042470, 1514014452093670694388279119466493209577587773711602⟩
  | 2, 3 => ⟨-2949684533574385553210002706424572958034246996556791, 2952540059381257597681593892358390178357720744095778⟩
  | 3, 2 => ⟨-5757465551138647142062522474047662765459138510738798, 5761073443110286570936463432177965384210554263670182⟩
  | 4, 1 => ⟨-11240856129712403750138324853295896187170855853788318, 11244644053598611444761970172734006014402945790005858⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0098Geometry.ds, E8TAxisProd0098Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1644563431259135902753717245957362734985269701 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0098CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0099CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0099CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0099GraphCenterA.qJetBox,
   E8TAxisProd0099GraphCenterB.qJetBox,
   E8TAxisProd0099GraphCenterC.qJetBox,
   E8TAxisProd0099GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0099GraphWholeA.qJetBox,
   E8TAxisProd0099GraphWholeB.qJetBox,
   E8TAxisProd0099GraphWholeC.qJetBox,
   E8TAxisProd0099GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1933248584332192184910594298045042074592402098, 1933248584332192184910594298045063118993891877⟩
  | 0, 2 => ⟨7092444893538328336591443899106314351657679460, 7092444893538328336591443899106374948220369006⟩
  | 1, 1 => ⟨7202476423150498186002630307953169260954121980, 7202476423150498186002630307953267806828913808⟩
  | 0, 3 => ⟨17509077494228214062559414782146045772549389558, 17509077494228214062559414782146222154357042101⟩
  | 1, 2 => ⟨24446741659276052407077388950873122437507966771, 24446741659276052407077388950873411454581585428⟩
  | 2, 1 => ⟨24779670812219403278711860073420272602014233573, 24779670812219403278711860073420769773870697717⟩
  | 0, 4 => ⟨36018590275020327830407085109074792211742445273, 36018590275020327830407085109075337042391828082⟩
  | 1, 3 => ⟨56742798184183782305329653245302556330766928580, 56742798184183782305329653245303475324626271226⟩
  | 2, 2 => ⟨77692498224762920355931255919286001120072597041, 77692498224762920355931255919287615679889605300⟩
  | 3, 1 => ⟨78615537304051647471536796537618414842860873800, 78615537304051647471536796537621298402514820634⟩
  | 0, 5 => ⟨-536454668247573090598378239855573461764025997062849, 537975704035173163877406527174462874076565312429781⟩
  | 1, 4 => ⟨-1043108595463727096857725422801954602501240031450655, 1045204560000001337962577141567844566352432472324302⟩
  | 2, 3 => ⟨-2030390998538701173351575548312013192710078407232161, 2033237773985643124776597899915949120275435736493321⟩
  | 3, 2 => ⟨-3954234191027316250795787458030387723325456611805303, 3957883231265374373458007262997684409975669273835069⟩
  | 4, 1 => ⟨-7703228687793104016332631261720619434014903773609388, 7707098262179529352558325592959382103615040746270739⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0099Geometry.ds, E8TAxisProd0099Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1353586466357102480863578172051707554737781043 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0099CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0100CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0100CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0100GraphCenterA.qJetBox,
   E8TAxisProd0100GraphCenterB.qJetBox,
   E8TAxisProd0100GraphCenterC.qJetBox,
   E8TAxisProd0100GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0100GraphWholeA.qJetBox,
   E8TAxisProd0100GraphWholeB.qJetBox,
   E8TAxisProd0100GraphWholeC.qJetBox,
   E8TAxisProd0100GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1542745978765263482230140226429301656765412846, 1542745978765263482230140226429320141171324694⟩
  | 0, 2 => ⟨5743245378787795654493501217313517939152207555, 5743245378787795654493501217313569641781995467⟩
  | 1, 1 => ⟨5848576474351064308136291187027090461275162875, 5848576474351064308136291187027173473868700701⟩
  | 0, 3 => ⟨14346111686332918156622556598556449535690713579, 14346111686332918156622556598556597773461894392⟩
  | 1, 2 => ⟨20125601851493965306304098618072758804452760661, 20125601851493965306304098618072998885498299885⟩
  | 2, 1 => ⟨20449223581798788636503812741638463486691646198, 20449223581798788636503812741638873849611679888⟩
  | 0, 4 => ⟨29857382488037302537329728135945651847949847246, 29857382488037302537329728135946104039354230545⟩
  | 1, 3 => ⟨47349427144028165530084834155301058315477957126, 47349427144028165530084834155301813028494490126⟩
  | 2, 2 => ⟨65066762955027253647911943100320611713722759414, 65066762955027253647911943100321929666249648219⟩
  | 3, 1 => ⟨65981281632308936584430765774299723546915966902, 65981281632308936584430765774302066768518520829⟩
  | 0, 5 => ⟨-375266821776864089998368365334504907806898530534961, 376756254935393722269482066943781441851315409528134⟩
  | 1, 4 => ⟨-727724962524038037389445039875961360409653028086444, 729820046224823556704506403799838199605002212707795⟩
  | 2, 3 => ⟨-1413032259153103192474634832038081638552100001818572, 1415930265109864075887609734208381143138339166424422⟩
  | 3, 2 => ⟨-2745467141937948158417662437566829256821433237041052, 2749233453896585262204443033583282414136171025504380⟩
  | 4, 1 => ⟨-5336144868782097055108438252825053021861362499524800, 5340184625642176822176277306260450263140829309316263⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0100Geometry.ds, E8TAxisProd0100Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1111413468780208373554935926439240559572836637 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0100CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0101CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0101CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0101GraphCenterA.qJetBox,
   E8TAxisProd0101GraphCenterB.qJetBox,
   E8TAxisProd0101GraphCenterC.qJetBox,
   E8TAxisProd0101GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0101GraphWholeA.qJetBox,
   E8TAxisProd0101GraphWholeB.qJetBox,
   E8TAxisProd0101GraphWholeC.qJetBox,
   E8TAxisProd0101GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1214584797796897934867634900232859334151811610, 1214584797796897934867634900232875645455518750⟩
  | 0, 2 => ⟨4604967759554772991373130687193389937408144118, 4604967759554772991373130687193434508958835466⟩
  | 1, 1 => ⟨4691767832220897215804678974727639266332388390, 4691767832220897215804678974727709982420461937⟩
  | 0, 3 => ⟨11649876348428283387025663240016901292166187386, 11649876348428283387025663240017027740012709119⟩
  | 1, 2 => ⟨16414609012123260305674186972638333334508496153, 16414609012123260305674186972638535985934641244⟩
  | 2, 1 => ⟨16685386264058933096443880498819291659692238888, 16685386264058933096443880498819636063595347148⟩
  | 0, 4 => ⟨24522126648668156527594426683075589466260262807, 24522126648668156527594426683075972314865842437⟩
  | 1, 3 => ⟨39159744658722803468948148613788500867489736102, 39159744658722803468948148613789134056211266460⟩
  | 2, 2 => ⟨53991143421422676573807860964123776122465740881, 53991143421422676573807860964124876155001443790⟩
  | 3, 1 => ⟨54770634282060797105207918392448747088782312200, 54770634282060797105207918392450695040773695257⟩
  | 0, 5 => ⟨-261914028538807170981127857242774224058011780765145, 263336726920369750517297881556588658818946323205488⟩
  | 1, 4 => ⟨-506405515047028698751087266333154112644185567638010, 508434962946867960650024707766085129207318587589554⟩
  | 2, 3 => ⟨-980677270053206884122159304319894855218698647984470, 983518325882887576696546145629647924444591701811068⟩
  | 3, 2 => ⟨-1900604502030964126354796517332857953668600708032223, 1904328125761268613714851781125657287674564183647721⟩
  | 4, 1 => ⟨-3684928379327582056923872514832289312050514374201642, 3688945159011718018225022327306599165472153505514844⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0101Geometry.ds, E8TAxisProd0101Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 894027605474669761529794719580129087661610538 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0101CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0102CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0102CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0102GraphCenterA.qJetBox,
   E8TAxisProd0102GraphCenterB.qJetBox,
   E8TAxisProd0102GraphCenterC.qJetBox,
   E8TAxisProd0102GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0102GraphWholeA.qJetBox,
   E8TAxisProd0102GraphWholeB.qJetBox,
   E8TAxisProd0102GraphWholeC.qJetBox,
   E8TAxisProd0102GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1528432619254487935209442175583993623563649082, 1528432619254487935209442175584012040799608158⟩
  | 0, 2 => ⟨5707473258683183750967169277392078843812236092, 5707473258683183750967169277392130328447783884⟩
  | 1, 1 => ⟨5798410194946119734038613023420727477234388599, 5798410194946119734038613023420810126369871613⟩
  | 0, 3 => ⟨14271642421082701542152919488117867199131667180, 14271642421082701542152919488118014781072932898⟩
  | 1, 2 => ⟨20007518263905569280510713145791366399435866489, 20007518263905569280510713145791605379616424811⟩
  | 2, 1 => ⟨20287000756567610765171287349493305482219038605, 20287000756567610765171287349493713917382725491⟩
  | 0, 4 => ⟨29718125511835536893355600100371711627062700194, 29718125511835536893355600100372161706058147660⟩
  | 1, 3 => ⟨47117607619661411877675838474928801003742125588, 47117607619661411877675838474929552096700506672⟩
  | 2, 2 => ⟨64711760898133018053440856632129501397512262265, 64711760898133018053440856632130812891600101757⟩
  | 3, 1 => ⟨65501847022066854692301551050473623575462739721, 65501847022066854692301551050475955091567728872⟩
  | 0, 5 => ⟨-372192717945088381588979468541948111482874556271237, 373679168202566032867604073756825268777327491831021⟩
  | 1, 4 => ⟨-721713807755052014030006379462952767662481855752868, 723804571466415642610812942626684115599453700002741⟩
  | 2, 3 => ⟨-1401267924324104507277255683789082880258818783462456, 1404158902299045099450445937213381141803767525763662⟩
  | 3, 2 => ⟨-2722431691784024709760371841182267516438067094195608, 2726184941012046655554444491999687060455405421592278⟩
  | 4, 1 => ⟨-5291024994342699789413693364163417450806940996198621, 5295037935815079261678575260671630007412054703711495⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0102Geometry.ds, E8TAxisProd0102Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1100744121441572678157133794321086384562463204 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0102CertifiedArithmetic

end


