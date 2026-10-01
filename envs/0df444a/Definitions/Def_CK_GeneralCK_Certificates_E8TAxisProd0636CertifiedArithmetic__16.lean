-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0636CertifiedArithmetic__16
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0636CertifiedArithmetic__16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T14:02:01.446565+00:00
-- url     : https://prove2.me/theorems/d67829de-2bee-4479-a510-18287563f4eb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0636CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0637CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0636CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0637CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0638CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0639CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0640CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0641CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0642CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0643CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0644CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0645CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0646CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0647CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0648CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0649CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0650CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0651CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0636CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0637CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0638CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0639CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0640CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0641CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0642CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0643CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0644CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0645CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0646CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0647CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0648CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0649CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0650CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0651CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0636CertifiedArithmetic (+15 modules: GeneralCK.Certificates.E8TAxisProd0637CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0638CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0639CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0640CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0641CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0642CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0643CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0644CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0645CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0646CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0647CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0648CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0649CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0650CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0651CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0636CertifiedArithmetic (+15 modules: GeneralCK/Certificates/E8TAxisProd0637CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0638CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0639CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0640CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0641CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0642CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0643CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0644CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0645CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0646CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0647CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0648CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0649CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0650CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0651CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0630GraphCenterA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0623GraphCenterB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0633GraphCenterC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0629GraphCenterD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0627GraphWholeA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0628GraphWholeB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0631GraphWholeC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0629GraphWholeD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0629Geometry__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0637GraphCenterB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0641GraphWholeA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0642GraphWholeB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0643GraphCenterD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0643GraphWholeC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0643GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0644GraphCenterA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0644Geometry__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0648GraphCenterC__11

-- ===== source module GeneralCK.Certificates.E8TAxisProd0636CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0636CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0636GraphCenterA.qJetBox,
   E8TAxisProd0636GraphCenterB.qJetBox,
   E8TAxisProd0636GraphCenterC.qJetBox,
   E8TAxisProd0636GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0636GraphWholeA.qJetBox,
   E8TAxisProd0636GraphWholeB.qJetBox,
   E8TAxisProd0636GraphWholeC.qJetBox,
   E8TAxisProd0636GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5360761761384626954488795159871021334265203680, 5360761761384626954488795159871061858343644013⟩
  | 0, 2 => ⟨18341989140422962778249226146540716546689592968, 18341989140422962778249226146540849313961815831⟩
  | 1, 1 => ⟨18488882003406517327703728661427621576648902903, 18488882003406517327703728661427848630959038735⟩
  | 0, 3 => ⟨42641822782063334862117006202971034516300296828, 42641822782063334862117006202971444162327740296⟩
  | 1, 2 => ⟨58516076569609121532166938053775510551695598627, 58516076569609121532166938053776211859102821457⟩
  | 2, 1 => ⟨58927348876410147837026154464325741326741480394, 58927348876410147837026154464326978671224910904⟩
  | 0, 4 => ⟨82250917882126848246749616221240607177805763112, 82250917882126848246749616221241936592493831376⟩
  | 1, 3 => ⟨126393516621139565528028684335430215042328838510, 126393516621139565528028684335432544351185586848⟩
  | 2, 2 => ⟨170780310354774594077240514589760902430877318696, 170780310354774594077240514589765089059537847488⟩
  | 3, 1 => ⟨171815435630378716270141422494354182807512718177, 171815435630378716270141422494361794481912215388⟩
  | 0, 5 => ⟨-176382782109337513117778727252317349573209291047011, 177722966448464036398044346308246747949903134841426⟩
  | 1, 4 => ⟨-340806868580305470163053468433868278060215268566900, 342776775569138357065549566738788900959555425642145⟩
  | 2, 3 => ⟨-659756746124109340039899927650106826681207233479914, 662551429619776801420342757759959970039885376233032⟩
  | 3, 2 => ⟨-1278530931280667797706506314448557943804505781400013, 1282171500544844369593493986216052782776591446595311⟩
  | 4, 1 => ⟨-2479222734990561007475284348151436559464513641378008, 2482953367361948667511032306213536192307378255484490⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0636Geometry.ds, E8TAxisProd0636Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4995132274403122082481740573178015943790557203 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0636CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0637CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0637CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0637GraphCenterA.qJetBox,
   E8TAxisProd0637GraphCenterB.qJetBox,
   E8TAxisProd0637GraphCenterC.qJetBox,
   E8TAxisProd0637GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0637GraphWholeA.qJetBox,
   E8TAxisProd0637GraphWholeB.qJetBox,
   E8TAxisProd0637GraphWholeC.qJetBox,
   E8TAxisProd0637GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4733071592557634148047596541762824113052269680, 4733071592557634148047596541762861304217779853⟩
  | 0, 2 => ⟨16345966807357164939262084777768442850922773479, 16345966807357164939262084777768562907743826727⟩
  | 1, 1 => ⟨16478730845994831284811739306019797571795593044, 16478730845994831284811739306020001791351234945⟩
  | 0, 3 => ⟨38309845051740373358692246097584981643365176222, 38309845051740373358692246097585349982647291142⟩
  | 1, 2 => ⟨52659130354871852363900087038900306816085125414, 52659130354871852363900087038900934578487921795⟩
  | 2, 1 => ⟨53034627547463609257614514494593839790849895416, 53034627547463609257614514494594944368424104243⟩
  | 0, 4 => ⟨74544827725892250219648130657618973883052317984, 74544827725892250219648130657620163781312404760⟩
  | 1, 3 => ⟨114849764368047050772804044914385120319717684539, 114849764368047050772804044914387197427337600524⟩
  | 2, 2 => ⟨155381315102733026576452279746872656396075974390, 155381315102733026576452279746876381066408941941⟩
  | 3, 1 => ⟨156338013841388365491482681218099503269454316037, 156338013841388365491482681218106262312372365251⟩
  | 0, 5 => ⟨-149672842643008391613366310011930734453107666585832, 150859455114239963454531524677102350697336971244537⟩
  | 1, 4 => ⟨-288792950377811065111254665023591923786291615181665, 290531694030384081504929913300779030823897199164010⟩
  | 2, 3 => ⟨-558364577708790399721422125803712755235833152170403, 560826521546298029094656322496423892798611431005895⟩
  | 3, 2 => ⟨-1080762479329996590555424475615640075974247330030981, 1083966789145496192237378128407717353157910234487370⟩
  | 4, 1 => ⟨-2093301878881951263328433701588379006563172665312357, 2096587706070321688752291290347594156744013985290119⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0637Geometry.ds, E8TAxisProd0637Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4407645302196930150432284302047675373557109388 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0637CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0638CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0638CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0638GraphCenterA.qJetBox,
   E8TAxisProd0638GraphCenterB.qJetBox,
   E8TAxisProd0638GraphCenterC.qJetBox,
   E8TAxisProd0638GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0638GraphWholeA.qJetBox,
   E8TAxisProd0638GraphWholeB.qJetBox,
   E8TAxisProd0638GraphWholeC.qJetBox,
   E8TAxisProd0638GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5337867562122883645179986135636431959871842961, 5337867562122883645179986135636472404873051137⟩
  | 0, 2 => ⟨18288751075281557218184500478605485113376221338, 18288751075281557218184500478605617590053516121⟩
  | 1, 1 => ⟨18415835579865877758116259506466791877443593923, 18415835579865877758116259506467018421536493535⟩
  | 0, 3 => ⟨42539117582357823737709892973995907629566103757, 42539117582357823737709892973996316358857215956⟩
  | 1, 2 => ⟨58358259278792446354290925669185976573035564484, 58358259278792446354290925669186676276283657033⟩
  | 2, 1 => ⟨58714134779942032356930691999118463620023998246, 58714134779942032356930691999119698086951062540⟩
  | 0, 4 => ⟨82077454646850971854528199934339993627668604248, 82077454646850971854528199934341319962049102397⟩
  | 1, 3 => ⟨126114236391243512554973922585367006679014402791, 126114236391243512554973922585369330515867198721⟩
  | 2, 2 => ⟨170362380479308257392944513596081710395748229443, 170362380479308257392944513596085887067479857553⟩
  | 3, 1 => ⟨171258267804640115647301862805586311072632578613, 171258267804640115647301862805593904424005272070⟩
  | 0, 5 => ⟨-175811633098166441916131223111865908359090328358522, 177148650284911227722929148816058235898000133780194⟩
  | 1, 4 => ⟨-339694522262538138190799662624823274106168520469027, 341659691938667988436092757825711537848552339135556⟩
  | 2, 3 => ⟨-657587097782031526691499932141934884458837308768273, 660374986780560741837609026052405976119197972238285⟩
  | 3, 2 => ⟨-1274294965755955855308318976180100693556273938560553, 1277926553712331109772119649781993071988668650719530⟩
  | 4, 1 => ⟨-2470947064221876820255016449840554321494084451051554, 2474668005142977590839168678184999289332934442848195⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0638Geometry.ds, E8TAxisProd0638Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4973659321042652076210101842828231150414932430 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0638CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0639CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0639CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0639GraphCenterA.qJetBox,
   E8TAxisProd0639GraphCenterB.qJetBox,
   E8TAxisProd0639GraphCenterC.qJetBox,
   E8TAxisProd0639GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0639GraphWholeA.qJetBox,
   E8TAxisProd0639GraphWholeB.qJetBox,
   E8TAxisProd0639GraphWholeC.qJetBox,
   E8TAxisProd0639GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4712669039361926906299102964850594518060289617, 4712669039361926906299102964850631637091947465⟩
  | 0, 2 => ⟨16298137697794633014750715990151963393099580747, 16298137697794633014750715990152083187537257972⟩
  | 1, 1 => ⟨16412996592585462302961258130048435188287527376, 16412996592585462302961258130048638949048237698⟩
  | 0, 3 => ⟨38216763348596629934946829804583980125620380468, 38216763348596629934946829804584347639376655817⟩
  | 1, 2 => ⟨52515728550020484007105776461960145925871212559, 52515728550020484007105776461960772248309600035⟩
  | 2, 1 => ⟨52840641426618865658175022952451601065000522628, 52840641426618865658175022952452703064540568830⟩
  | 0, 4 => ⟨74385946345638756457085323331112618321635902065, 74385946345638756457085323331113805450157177312⟩
  | 1, 3 => ⟨114593204825325529340291666810722219491841167364, 114593204825325529340291666810724291691542671929⟩
  | 2, 2 => ⟨154996605297573290662539159532609659450912644954, 154996605297573290662539159532613375203513543506⟩
  | 3, 1 => ⟨155824600837591264455080142256238896987397884834, 155824600837591264455080142256245639638526103842⟩
  | 0, 5 => ⟨-149181162636755511659515872383243840777153487146815, 150364982025469339520621166986164598117539079569294⟩
  | 1, 4 => ⟨-287836288250726692327262513643146695546959440767532, 289570825151949184211838008209801929754904588814507⟩
  | 2, 3 => ⟨-556500226010076848243850087263249084334428311010546, 558956088125329327153165228756644682187414918673892⟩
  | 3, 2 => ⟨-1077125605377393572124011437747637433569389512800551, 1080321790986903366298551143795817072123116936805203⟩
  | 4, 1 => ⟨-2086202427262184939668095459812262425653449430724574, 2089479297411572247751483706392460620115621331620368⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0639Geometry.ds, E8TAxisProd0639Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4388520425434297564407907957404559632259955611 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0639CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0640CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0640CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0640GraphCenterA.qJetBox,
   E8TAxisProd0640GraphCenterB.qJetBox,
   E8TAxisProd0640GraphCenterC.qJetBox,
   E8TAxisProd0640GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0640GraphWholeA.qJetBox,
   E8TAxisProd0640GraphWholeB.qJetBox,
   E8TAxisProd0640GraphWholeC.qJetBox,
   E8TAxisProd0640GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6795627867586345184830801239150634348121358985, 6795627867586345184830801239150682411475392134⟩
  | 0, 2 => ⟨22886437545918686623493618150292266582647304115, 22886437545918686623493618150292428491402043096⟩
  | 1, 1 => ⟨23017452804041686234122466701327899861142851739, 23017452804041686234122466701328179513071133299⟩
  | 0, 3 => ⟨52391083017327564605506958552860419121318767870, 52391083017327564605506958552860923672173541736⟩
  | 1, 2 => ⟨71627639048036022514306521160056100787638127921, 71627639048036022514306521160056971703518912936⟩
  | 2, 1 => ⟨71987156961178508055267014539439819836110814349, 71987156961178508055267014539441364210017974870⟩
  | 0, 4 => ⟨99334629206906601838784758825913514771134963853, 99334629206906601838784758825915164667890787191⟩
  | 1, 3 => ⟨151863280944015839393721251010976698519607241581, 151863280944015839393721251010979608802501739686⟩
  | 2, 2 => ⟨204598798687653317848151784077334144707563539847, 204598798687653317848151784077339397700120209334⟩
  | 3, 1 => ⟨205482564371669787661690101683884501071490140360, 205482564371669787661690101683894084597198639543⟩
  | 0, 5 => ⟨-241587068639369289149658279693508999879524896551760, 243293163912837295287822216514132284003062338102029⟩
  | 1, 4 => ⟨-467962948705553491529704924039507883832272312497037, 470482230936315946794111934528571319382976494857691⟩
  | 2, 3 => ⟨-907959670598820777823401142358373462529968978827635, 911543560622874208496670695709615831606045028565282⟩
  | 3, 2 => ⟨-1763297789831236261988218102234436974016737114755838, 1767971925959219004262559851264870511598196868682515⟩
  | 4, 1 => ⟨-3426430663927003736706254351834517901012552009371418, 3431214304867859549036567695568405036510206208913518⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0640Geometry.ds, E8TAxisProd0640Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6339071285974626073734799847742819558238981912 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0640CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0641CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0641CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0641GraphCenterA.qJetBox,
   E8TAxisProd0641GraphCenterB.qJetBox,
   E8TAxisProd0641GraphCenterC.qJetBox,
   E8TAxisProd0641GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0641GraphWholeA.qJetBox,
   E8TAxisProd0641GraphWholeB.qJetBox,
   E8TAxisProd0641GraphWholeC.qJetBox,
   E8TAxisProd0641GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6013370300241944224205794072578889320114223547, 6013370300241944224205794072578933345955028112⟩
  | 0, 2 => ⟨20440482409657947800058521004594742654913889723, 20440482409657947800058521004594888913841701889⟩
  | 1, 1 => ⟨20559133864830937634950651916893742226162297568, 20559133864830937634950651916893993611088833077⟩
  | 0, 3 => ⟨47180122714454449197220878743797595627206860459, 47180122714454449197220878743798049223679481070⟩
  | 1, 2 => ⟨64603017632826471567111279964098615544117767076, 64603017632826471567111279964099395340042890830⟩
  | 2, 1 => ⟨64931964243593345397302282478896164659155489482, 64931964243593345397302282478897543981789457496⟩
  | 0, 4 => ⟨90256735044119389256984490126135864859174081273, 90256735044119389256984490126137342741835097091⟩
  | 1, 3 => ⟨138320478388879555219694985805246879537637677995, 138320478388879555219694985805249477879255416058⟩
  | 2, 2 => ⟨186576523402226912083084238108252254760820962816, 186576523402226912083084238108256934955225852889⟩
  | 3, 1 => ⟨187394835286212678644434331552037807634428933512, 187394835286212678644434331552046331497917698056⟩
  | 0, 5 => ⟨-206034469138284415215731601750878537008343951545476, 207543080978749617755432999560323988314569339945597⟩
  | 1, 4 => ⟨-398603700626812464585149768301306760847464532684349, 400826256108697005990917057236376990590640070577892⟩
  | 2, 3 => ⟨-772520674631544207778196990198768993544602056790673, 775678068666819605409811774728785147478116428144163⟩
  | 3, 2 => ⟨-1498667343323067291780641154753683046186154103586507, 1502782664578928228929542661073600540680467580065730⟩
  | 4, 1 => ⟨-2909152621428900175216779452813592781984150116698343, 2913366353008210456635461045611521708622083087519306⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0641Geometry.ds, E8TAxisProd0641Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5606167577084596355464985079622506485245985543 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0641CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0642CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0642CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0642GraphCenterA.qJetBox,
   E8TAxisProd0642GraphCenterB.qJetBox,
   E8TAxisProd0642GraphCenterC.qJetBox,
   E8TAxisProd0642GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0642GraphWholeA.qJetBox,
   E8TAxisProd0642GraphWholeB.qJetBox,
   E8TAxisProd0642GraphWholeC.qJetBox,
   E8TAxisProd0642GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6767060718868781635378179546073996689369775839, 6767060718868781635378179546074044657880088049⟩
  | 0, 2 => ⟨22821026243830751191685158928269805299046249358, 22821026243830751191685158928269966852682373834⟩
  | 1, 1 => ⟨22928036812787604278934833424066512773936614395, 22928036812787604278934833424066791797643731878⟩
  | 0, 3 => ⟨52267043100382294600637055844855013993514724892, 52267043100382294600637055844855517419479128753⟩
  | 1, 2 => ⟨71438015432646853270950573054282406921611468833, 71438015432646853270950573054283275857680723220⟩
  | 2, 1 => ⟨71731714715849134365563743165539816862679194740, 71731714715849134365563743165541357672560854217⟩
  | 0, 4 => ⟨99129299533952665368968303129680939925532830159, 99129299533952665368968303129682586039091686095⟩
  | 1, 3 => ⟨151534604999190045778291801014866774564189998852, 151534604999190045778291801014869678096606492822⟩
  | 2, 2 => ⟨204108950731085455694667624105712778037753300168, 204108950731085455694667624105718018716029168513⟩
  | 3, 1 => ⟨204831069640718151293709662113644332189622817163, 204831069640718151293709662113653893008002847310⟩
  | 0, 5 => ⟨-240825717455682020112682316414963637842365352282390, 242527820150162195073691592201476715654772451089694⟩
  | 1, 4 => ⟨-466477588587480103442681751024638683596807018449830, 468990873676657997385819100693590075464649888736405⟩
  | 2, 3 => ⟨-905057761117977463763815066696036869735674133379049, 908633067827140271631428223924878751060165180792069⟩
  | 3, 2 => ⟨-1757623351707990784680707803167116045728331765946230, 1762286277094540665436074180602219697250315211794420⟩
  | 4, 1 => ⟨-3415327759836793831125262275939629565179073559717366, 3420099774752059963995487547731573847469403875434124⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0642Geometry.ds, E8TAxisProd0642Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6312247592499647188931648219638608470217272861 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0642CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0643CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0643CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0643GraphCenterA.qJetBox,
   E8TAxisProd0643GraphCenterB.qJetBox,
   E8TAxisProd0643GraphCenterC.qJetBox,
   E8TAxisProd0643GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0643GraphWholeA.qJetBox,
   E8TAxisProd0643GraphWholeB.qJetBox,
   E8TAxisProd0643GraphWholeC.qJetBox,
   E8TAxisProd0643GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5987856527335641741232645056522453355877789932, 5987856527335641741232645056522497295316637207⟩
  | 0, 2 => ⟨20381577720233545620633223136014901874923961808, 20381577720233545620633223136015047813332199566⟩
  | 1, 1 => ⟨20478488076836851339242327765080394539196081681, 20478488076836851339242327765080645359206384077⟩
  | 0, 3 => ⟨47067419631221385182176591017484446865682424410, 47067419631221385182176591017484899448816447353⟩
  | 1, 2 => ⟨64430306189728301034860797902982338100336358445, 64430306189728301034860797902983116117824791762⟩
  | 2, 1 => ⟨64699026050865447559526293328274565660638988885, 64699026050865447559526293328275941787355615460⟩
  | 0, 4 => ⟨90068255199811795169744236048791423385881914491, 90068255199811795169744236048792897861431813588⟩
  | 1, 3 => ⟨138017924693439914839981311084728914099155450807, 138017924693439914839981311084731506374374048375⟩
  | 2, 2 => ⟨186124731063481054424929019824074488185590802239, 186124731063481054424929019824079157327153751296⟩
  | 3, 1 => ⟨186793358166463358385025394078733336846607479318, 186793358166463358385025394078741840349086821052⟩
  | 0, 5 => ⟨-205377274233444375979968046491186730161764573430570, 206882350525591783813878962154398153036647624348741⟩
  | 1, 4 => ⟨-397322650618120251774253595425186719369656125280594, 399539927297071946038022607000165120317309087826083⟩
  | 2, 3 => ⟨-770019954101839303817848970379452100037335246617269, 773169806489024410514375429138646452245925512212974⟩
  | 3, 2 => ⟨-1493781247573402117039715545245973307295930284470161, 1497886678619120233648120041233799214295530576971357⟩
  | 4, 1 => ⟨-2899599644920588570493844251084925324542294131312200, 2903802922107495334570468927952850481230674767756997⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0643Geometry.ds, E8TAxisProd0643Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5582224498171702823871300487248043649255472571 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0643CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0644CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0644CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0644GraphCenterA.qJetBox,
   E8TAxisProd0644GraphCenterB.qJetBox,
   E8TAxisProd0644GraphCenterC.qJetBox,
   E8TAxisProd0644GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0644GraphWholeA.qJetBox,
   E8TAxisProd0644GraphWholeB.qJetBox,
   E8TAxisProd0644GraphWholeC.qJetBox,
   E8TAxisProd0644GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5315039830260569849021733236230425801916227203, 5315039830260569849021733236230466167997584679⟩
  | 0, 2 => ⟨18235641256204410875649548051802739294267130321, 18235641256204410875649548051802871480975935617⟩
  | 1, 1 => ⟨18342986209888063888200182797723416222543440756, 18342986209888063888200182797723642257538689718⟩
  | 0, 3 => ⟨42436629013050961215660081944385438403613347360, 42436629013050961215660081944385846218167159986⟩
  | 1, 2 => ⟨58200790759544982335089205893377638016877589356, 58200790759544982335089205893378336119499159725⟩
  | 2, 1 => ⟨58501442584281322689292610778915267881328126997, 58501442584281322689292610778916499477082163978⟩
  | 0, 4 => ⟨81904309160189923762748061080405526138625956788, 81904309160189923762748061080406849399479731248⟩
  | 1, 3 => ⟨125835481967863801284629003688278741249621907656, 125835481967863801284629003688281059626570154157⟩
  | 2, 2 => ⟨169945268837243596930468202313798143586152344227, 169945268837243596930468202313802310323028659416⟩
  | 3, 1 => ⟨170702295225149602818740791285848554976974804344, 170702295225149602818740791285856130046070284441⟩
  | 0, 5 => ⟨-175242418931924544279040610887862018413681895590009, 176576279500357043341209596584907471633155715849598⟩
  | 1, 4 => ⟨-338585961664989282603978412957726102804913082990046, 340546409844631543751080009682107693205880101541350⟩
  | 2, 3 => ⟨-655424865474617014711126133261446870953478094812338, 658205982065672155495464887181069869282886065154282⟩
  | 3, 2 => ⟨-1270073539377331367713266550662045808493125040721581, 1273696172861804122764941495576420833236292798553988⟩
  | 4, 1 => ⟨-2462699913912830016847355471644937140397022912622550, 2466411185086368410141103268519233999066410748604250⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0644Geometry.ds, E8TAxisProd0644Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4952248991648809483979511001221245714541572910 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0644CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0645CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0645CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0645GraphCenterA.qJetBox,
   E8TAxisProd0645GraphCenterB.qJetBox,
   E8TAxisProd0645GraphCenterC.qJetBox,
   E8TAxisProd0645GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0645GraphWholeA.qJetBox,
   E8TAxisProd0645GraphWholeB.qJetBox,
   E8TAxisProd0645GraphWholeC.qJetBox,
   E8TAxisProd0645GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4692326199884787509274783505829962138608794333, 4692326199884787509274783505829999185649618292⟩
  | 0, 2 => ⟨16250424816311549327763400419567007825766437176, 16250424816311549327763400419567127358386643916⟩
  | 1, 1 => ⟨16347441391122199120388293945416848143598205599, 16347441391122199120388293945417051446572562205⟩
  | 0, 3 => ⟨38123880063370105597409708291496347465380463769, 38123880063370105597409708291496714155461548720⟩
  | 1, 2 => ⟨52372647139396600200300942691797187795719258636, 52372647139396600200300942691797812681467322801⟩
  | 2, 1 => ⟨52647135716861325248263180047795819881301500700, 52647135716861325248263180047796919308734131788⟩
  | 0, 4 => ⟨74227358980217313214309077215572936676890559574, 74227358980217313214309077215574121042327407306⟩
  | 1, 3 => ⟨114337133471295859203562733839700397794018958595, 114337133471295859203562733839702465097734365263⟩
  | 2, 2 => ⟨154612657152520475049642178164563356830676033100, 154612657152520475049642178164567063687400677493⟩
  | 3, 1 => ⟨155312302466762815344788623551585025400973943826, 155312302466762815344788623551591751700788801721⟩
  | 0, 5 => ⟨-148690955108894791591936497376152807256790559385995, 149871986794449446405966725283747744691911664239628⟩
  | 1, 4 => ⟨-286882506058818343800870212373886154834887414144213, 288612844131753535442826831330044278871466060846674⟩
  | 2, 3 => ⟨-554641515128763282697272245760072524078525829787040, 557091306259621064888581706351913962643698628153700⟩
  | 3, 2 => ⟨-1073499790333967870571246009870613616280620585207259, 1076687864151328618425454828488160969686822371519120⟩
  | 4, 1 => ⟨-2079124671641411985058292441528815902664099440535887, 2082392593453171585828463274221407109335122926850846⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0645Geometry.ds, E8TAxisProd0645Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4369451788908157893566575120029792088158703068 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0645CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0646CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0646CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0646GraphCenterA.qJetBox,
   E8TAxisProd0646GraphCenterB.qJetBox,
   E8TAxisProd0646GraphCenterC.qJetBox,
   E8TAxisProd0646GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0646GraphWholeA.qJetBox,
   E8TAxisProd0646GraphWholeB.qJetBox,
   E8TAxisProd0646GraphWholeC.qJetBox,
   E8TAxisProd0646GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5292278405659244348194828981560013417286745156, 5292278405659244348194828981560053704605313617⟩
  | 0, 2 => ⟨18182659412651635186965345202466102989364125305, 18182659412651635186965345202466234886729545546⟩
  | 1, 1 => ⟨18270333457919177914033739676278836606857890725, 18270333457919177914033739676279062133872678170⟩
  | 0, 3 => ⟨42334356677272201250798139403276993278326616631, 42334356677272201250798139403277400180137899908⟩
  | 1, 2 => ⟨58043670355142830443367344683415101546355948609, 58043670355142830443367344683415798051876077584⟩
  | 2, 1 => ⟨58289271267482130429618784702725790881524602989, 58289271267482130429618784702727019612475366475⟩
  | 0, 4 => ⟨81731480917907176498974013114681499381983887707, 81731480917907176498974013114682819576077599351⟩
  | 1, 3 => ⟨125557252496422742001109607160428240965795457381, 125557252496422742001109607160430553894913405896⟩
  | 2, 2 => ⟨169528974075552719111511034045725270333198532070, 169528974075552719111511034045729427157247504655⟩
  | 3, 1 => ⟨170147515858734630148797075744818884912559682310, 170147515858734630148797075744826441740043749490⟩
  | 0, 5 => ⟨-174674868460918068533072386798412985251095082783280, 176005578635435952905770894025676126241627319450994⟩
  | 1, 4 => ⟨-337480657438538214089695008719567171737446342584443, 339436393022573036247438522826781302911760408874378⟩
  | 2, 3 => ⟨-653269015642124688489357821137730017252504072578030, 656043371538297880316309771112517589515940761932958⟩
  | 3, 2 => ⟨-1265864633942963420081213693208558733480634020746671, 1269478325903569310512578389536713268712140422249618⟩
  | 4, 1 => ⟨-2454477342999870302638140892501957200644333524432049, 2458178951994456369722109624501059153535493071201347⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0646Geometry.ds, E8TAxisProd0646Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4930901152694732853132599053931386555227584904 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0646CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0647CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0647CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0647GraphCenterA.qJetBox,
   E8TAxisProd0647GraphCenterB.qJetBox,
   E8TAxisProd0647GraphCenterC.qJetBox,
   E8TAxisProd0647GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0647GraphWholeA.qJetBox,
   E8TAxisProd0647GraphWholeB.qJetBox,
   E8TAxisProd0647GraphWholeC.qJetBox,
   E8TAxisProd0647GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4672042928996034974687961961374797893010485391, 4672042928996034974687961961374834868203203742⟩
  | 0, 2 => ⟨16202827915115094415487415606243893156810121181, 16202827915115094415487415606244012428177556036⟩
  | 1, 1 => ⟨16282064841493447412320777668797085334203206141, 16282064841493447412320777668797288180397623425⟩
  | 0, 3 => ⟨38031194828835089572576106543710820328045967072, 38031194828835089572576106543711186196252637891⟩
  | 1, 2 => ⟨52229885513261996952261473501596962144490670868, 52229885513261996952261473501597585596723663637⟩
  | 2, 1 => ⟨52454109466905526015753578046916147415807510514, 52454109466905526015753578046917244276863144350⟩
  | 0, 4 => ⟨74069065161210792286579795297148941720183968716, 74069065161210792286579795297150123328653210943⟩
  | 1, 3 => ⟨114081549509899735488505931122658261026025622109, 114081549509899735488505931122660323444652807470⟩
  | 2, 2 => ⟨154229469404424876215221165690988543150861568710, 154229469404424876215221165690992241131576642932⟩
  | 3, 1 => ⟨154801116827664908780821110115566367905638858190, 154801116827664908780821110115573077890796280814⟩
  | 0, 5 => ⟨-148202216025719614642621142973437063929947431298298, 149380465568577487667418316053382627446792059160524⟩
  | 1, 4 => ⟨-285931596139333483355766884672453397121622139717501, 287657743456883831032153740574224065651446426787488⟩
  | 2, 3 => ⟨-552788430311872470732412008096370831584432002337983, 555232161309681001221737719408413505588878985406415⟩
  | 3, 2 => ⟨-1069885005520110313508873767861088592683263494623600, 1073064980038845264572450361994470147461844113879322⟩
  | 4, 1 => ⟨-2072068555886362462552046421757474355149063768277326, 2075327538114770668276873467702593873975704826660177⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0647Geometry.ds, E8TAxisProd0647Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4350439255256515188186152445117135138240213633 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0647CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0648CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0648CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0648GraphCenterA.qJetBox,
   E8TAxisProd0648GraphCenterB.qJetBox,
   E8TAxisProd0648GraphCenterC.qJetBox,
   E8TAxisProd0648GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0648GraphWholeA.qJetBox,
   E8TAxisProd0648GraphWholeB.qJetBox,
   E8TAxisProd0648GraphWholeC.qJetBox,
   E8TAxisProd0648GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4173933309649651647662745022201865995225607194, 4173933309649651647662745022201900162160528126⟩
  | 0, 2 => ⟨14550750965988756223369103598499078974148976075, 14550750965988756223369103598499187600735071695⟩
  | 1, 1 => ⟨14670622299420137442059991501753946791208762009, 14670622299420137442059991501754130535408852424⟩
  | 0, 3 => ⟨34375938026550077620179869455390097353849620643, 34375938026550077620179869455390428605288271255⟩
  | 1, 2 => ⟨47333471915057104671328911926730018036816061559, 47333471915057104671328911926730579923321218196⟩
  | 2, 1 => ⟨47675921502859607791986272757626699116787806213, 47675921502859607791986272757627684989164129585⟩
  | 0, 4 => ⟨67469593222601292718273241069422313077871837072, 67469593222601292718273241069423377867402326317⟩
  | 1, 3 => ⟨104229249983579514353431330441008128259992582991, 104229249983579514353431330441009979628602356063⟩
  | 2, 2 => ⟨141198998113205729893420610028277465670976920760, 141198998113205729893420610028280777443833886868⟩
  | 3, 1 => ⟨142082279803479843393181429478949997029650497596, 142082279803479843393181429478955995004411416123⟩
  | 0, 5 => ⟨-126703662967623056137979917397539914579381475691918, 127754292376811940859911447471646598824546012537715⟩
  | 1, 4 => ⟨-244107966511718882393109695289474531531396788489965, 245642156066923701240058044808217949354493931039674⟩
  | 2, 3 => ⟨-471341338749011130634447875666051791171557782104299, 473508947103501761989992089208374992222168094601350⟩
  | 3, 2 => ⟨-911179001460340563645008228925456083415852352010124, 913997420733361616256741694696928157315518075985128⟩
  | 4, 1 => ⟨-1762688026653200376803383349792035007158771083640803, 1765580190022844542158474672363853791632900928975940⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0648Geometry.ds, E8TAxisProd0648Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3884602713780822958830056250108627741660935314 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0648CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0649CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0649CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0649GraphCenterA.qJetBox,
   E8TAxisProd0649GraphCenterB.qJetBox,
   E8TAxisProd0649GraphCenterC.qJetBox,
   E8TAxisProd0649GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0649GraphWholeA.qJetBox,
   E8TAxisProd0649GraphWholeB.qJetBox,
   E8TAxisProd0649GraphWholeC.qJetBox,
   E8TAxisProd0649GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3676421558200981278386795879942464312275892084, 3676421558200981278386795879942495733501051733⟩
  | 0, 2 => ⟨12938016346753152466019748343461078764864252982, 12938016346753152466019748343461177111761261957⟩
  | 1, 1 => ⟨13046136243902504052628422799466105839190377983, 13046136243902504052628422799466271224745768852⟩
  | 0, 3 => ⟨30808059113013582895133738409057810658013316829, 30808059113013582895133738409058108609037845727⟩
  | 1, 2 => ⟨42496853940975313408746191499446872872612464842, 42496853940975313408746191499447375756236671598⟩
  | 2, 1 => ⟨42808808806296136228399500905360787845522769837, 42808808806296136228399500905361667594981317689⟩
  | 0, 4 => ⟨60981363535245391055468884917545877776908256384, 60981363535245391055468884917546830320560989535⟩
  | 1, 3 => ⟨94469407058636265329664417124296300624207279163, 94469407058636265329664417124297949840963617032⟩
  | 2, 2 => ⟨128152018140263196393622047573115401985383443904, 128152018140263196393622047573118344529103745081⟩
  | 3, 1 => ⟨128966596522778952811245680505761790029600135227, 128966596522778952811245680505767108322588945817⟩
  | 0, 5 => ⟨-107039682973295680412444255117016455787420743357236, 107969806756997772643156236108757374575840445060900⟩
  | 1, 4 => ⟨-205893992371324638838394533973156882036903568655738, 207247153576663396427868493776830675974673338207895⟩
  | 2, 3 => ⟨-396995964143479094474155317305072124534048851787508, 398903322208125184822707171393887909191194861875640⟩
  | 3, 2 => ⟨-766445455633435410697665959909787575971497256349305, 768922831545567945273911901254136486451840029274234⟩
  | 4, 1 => ⟨-1480800981936434389420078428798800118298961604929503, 1483345220918872881649019906895205060951725871865078⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0649Geometry.ds, E8TAxisProd0649Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3419459689930558216953848903807225710180139485 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0649CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0650CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0650CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0650GraphCenterA.qJetBox,
   E8TAxisProd0650GraphCenterB.qJetBox,
   E8TAxisProd0650GraphCenterC.qJetBox,
   E8TAxisProd0650GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0650GraphWholeA.qJetBox,
   E8TAxisProd0650GraphWholeB.qJetBox,
   E8TAxisProd0650GraphWholeC.qJetBox,
   E8TAxisProd0650GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4155771705192825644003982972471490151363742481, 4155771705192825644003982972471524252451368843⟩
  | 0, 2 => ⟨14507833716207106332648161912314972001283670339, 14507833716207106332648161912315080390904490491⟩
  | 1, 1 => ⟨14611536827292716965064861782374775308631384762, 14611536827292716965064861782374958640272472684⟩
  | 0, 3 => ⟨34291691904448888882528309712486336193413704110, 34291691904448888882528309712486666701449447688⟩
  | 1, 2 => ⟨47203332533315257648117107471023561048219338651, 47203332533315257648117107471024121642343531813⟩
  | 2, 1 => ⟨47499643913524160927046431880868875767390649962, 47499643913524160927046431880869859330603310579⟩
  | 0, 4 => ⟨67324247491454587486543427983871542958564250876, 67324247491454587486543427983872605258787690473⟩
  | 1, 3 => ⟨103993836373113263333204824174834900991978202106, 103993836373113263333204824174836747961532628833⟩
  | 2, 2 => ⟨140845263041433022879090919166329876408481259960, 140845263041433022879090919166333180200509486573⟩
  | 3, 1 => ⟨141609703673406096576267919495592531126135065690, 141609703673406096576267919495598514449354750663⟩
  | 0, 5 => ⟨-126281802873128321972625389404586863271467742196152, 127329938179085478387185204294093644929596886585871⟩
  | 1, 4 => ⟨-243287995783484644631760297875317951477919942903595, 244818422450032461972990100979956174527537348175759⟩
  | 2, 3 => ⟨-469744862059477175887855647744818313363540706346568, 471907008635782266468270090144198014747977557930983⟩
  | 3, 2 => ⟨-908067436217784605136960613978756244504874470948567, 910878500572161396173778134609321943562963505904103⟩
  | 4, 1 => ⟨-1756619241971105407734250570801406587550370754965514, 1759503135099632708648696235274313027297028393612695⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0650Geometry.ds, E8TAxisProd0650Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3867588386977607709236132813202232708023435949 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0650CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0651CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0651CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0651GraphCenterA.qJetBox,
   E8TAxisProd0651GraphCenterB.qJetBox,
   E8TAxisProd0651GraphCenterC.qJetBox,
   E8TAxisProd0651GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0651GraphWholeA.qJetBox,
   E8TAxisProd0651GraphWholeB.qJetBox,
   E8TAxisProd0651GraphWholeC.qJetBox,
   E8TAxisProd0651GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3660273086723830063166729982373055909723415511, 3660273086723830063166729982373087270794730455⟩
  | 0, 2 => ⟨12899553879955552755784001542133324967319484507, 12899553879955552755784001542133423100150877080⟩
  | 1, 1 => ⟨12993088924490217786239110880500917555022995950, 12993088924490217786239110880501082569585016313⟩
  | 0, 3 => ⟨30731915427322644768208184084084106891607838136, 30731915427322644768208184084084404173204167520⟩
  | 1, 2 => ⟨42378902065042279650140424344691215062795913235, 42378902065042279650140424344691716786753077491⟩
  | 2, 1 => ⟨42648821893657405589936512177264407226962355900, 42648821893657405589936512177265284908731261469⟩
  | 0, 4 => ⟨60848575480364876086110806307175889515540825006, 60848575480364876086110806307176839821939617505⟩
  | 1, 3 => ⟨94253664521149817746045006178163832626500256830, 94253664521149817746045006178165477900868375890⟩
  | 2, 2 => ⟨127827152022415898525301526298472838994467496451, 127827152022415898525301526298475774397207540583⟩
  | 3, 1 => ⟨128532118746996335847236945701541295786893240491, 128532118746996335847236945701546600986696830191⟩
  | 0, 5 => ⟨-106679314845695322586404277768548101271010166164672, 107607211030499230457319044585952854228434226981517⟩
  | 1, 4 => ⟨-205194327493142413557479458541474199352622297573306, 206544121610578891811132506054602652499199453200231⟩
  | 2, 3 => ⟨-395635098371725479313121768070988167933712056163088, 397537547986432904248699694258008578584067080888092⟩
  | 3, 2 => ⟨-763795633400071716002219179278514969646559067503192, 766266342479878219505511994102229010649362199058461⟩
  | 4, 1 => ⟨-1475637571305340813408615606681567567641079210259097, 1478174158504231620725079924894796027332323121067391⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0651Geometry.ds, E8TAxisProd0651Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3404340183236952756942589140386875839595073196 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0651CertifiedArithmetic

end


