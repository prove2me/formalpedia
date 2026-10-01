-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0335CertifiedArithmetic__9
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0335CertifiedArithmetic__9
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:26:05.526034+00:00
-- url     : https://prove2.me/theorems/4a322175-c320-4f4e-a803-d23d121c6644
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0335CertifiedArithmetic (+8 modules: GeneralCK.Certificates.E8TAxisProd0336CertifiedArithmetic, GeneralCK.Certificates.E8TAx…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0335CertifiedArithmetic (+8 modules: GeneralCK.Certificates.E8TAxisProd0336CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0337CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0338CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0339CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0340CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0341CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0342CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0343CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0335CertifiedArithmetic (+8 modules: GeneralCK.Certificates.E8TAxisProd0336CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0337CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0338CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0339CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0340CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0341CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0342CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0343CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0335CertifiedArithmetic (+8 modules: GeneralCK.Certificates.E8TAxisProd0336CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0337CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0338CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0339CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0340CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0341CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0342CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0343CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0335CertifiedArithmetic (+8 modules: GeneralCK/Certificates/E8TAxisProd0336CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0337CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0338CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0339CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0340CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0341CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0342CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0343CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0332GraphCenterA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0335GraphCenterB__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0328GraphCenterC__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0330GraphCenterD__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0332GraphWholeA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0332GraphWholeB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0331GraphWholeC__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0328GraphWholeD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0321Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0336GraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0337GraphCenterD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0338GraphWholeD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0340GraphWholeC__6
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0342GraphCenterA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0342GraphWholeB__9

-- ===== source module GeneralCK.Certificates.E8TAxisProd0335CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0335CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0335GraphCenterA.qJetBox,
   E8TAxisProd0335GraphCenterB.qJetBox,
   E8TAxisProd0335GraphCenterC.qJetBox,
   E8TAxisProd0335GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0335GraphWholeA.qJetBox,
   E8TAxisProd0335GraphWholeB.qJetBox,
   E8TAxisProd0335GraphWholeC.qJetBox,
   E8TAxisProd0335GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨19668212665992106871325154086695410320827552795, 19668212665992106871325154086695520960139739595⟩
  | 0, 2 => ⟨60777080681344141756150246238829883483135258537, 60777080681344141756150246238830298524511673306⟩
  | 1, 1 => ⟨61252117300753527489225234708137179642184584273, 61252117300753527489225234708137922717270089162⟩
  | 0, 3 => ⟨128706047295668437916428398361749045235123160820, 128706047295668437916428398361750385907744590156⟩
  | 1, 2 => ⟨174010663728875484634177180714047734281314777250, 174010663728875484634177180714050118270405023120⟩
  | 2, 1 => ⟨175200798236365783439612327341405221217196304725, 175200798236365783439612327341409533382179924627⟩
  | 0, 4 => ⟨225291852003385679334705577637237043776015371017, 225291852003385679334705577637241564306628250330⟩
  | 1, 3 => ⟨338034173100887196942791706708350391197032241109, 338034173100887196942791706708358553317875591176⟩
  | 2, 2 => ⟨451381126972900709097338683268029694819623259646, 451381126972900709097338683268044661791129599773⟩
  | 3, 1 => ⟨454048460045838315179099526550173418928807316206, 454048460045838315179099526550201098391370475426⟩
  | 0, 5 => ⟨-883940196810529929250695953482715700783551132855915, 889070969598961545468627746617490345567471812802390⟩
  | 1, 4 => ⟨-1726446127937346786223215334785604392455840388178006, 1734149697553286697743580859175181226193467449191397⟩
  | 2, 3 => ⟨-3375655000729411212726970473511206342639134847225368, 3386733035051200037480168485438326429702207377381449⟩
  | 3, 2 => ⟨-6604894919782811503356515904257927714834397297440155, 6619423689161059851111965962752530841631638937628026⟩
  | 4, 1 => ⟨-12929987641917682436429666685141176874052521515014002, 12944845733460004684590328364372566038822239765345788⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0335Geometry.ds, E8TAxisProd0335Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 18438516773964755068131246545052457460023775103 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0335CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0336CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0336CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0336GraphCenterA.qJetBox,
   E8TAxisProd0336GraphCenterB.qJetBox,
   E8TAxisProd0336GraphCenterC.qJetBox,
   E8TAxisProd0336GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0336GraphWholeA.qJetBox,
   E8TAxisProd0336GraphWholeB.qJetBox,
   E8TAxisProd0336GraphWholeC.qJetBox,
   E8TAxisProd0336GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨94379287955187795426134346418112056847147657997, 94379287955187795426134346418112546694890965999⟩
  | 0, 2 => ⟨256517239980737762767553318587010270122146652907, 256517239980737762767553318587012334649326726614⟩
  | 1, 1 => ⟨258007078786608746896025385143585302710702824086, 258007078786608746896025385143589136410877032713⟩
  | 0, 3 => ⟨483393035758086289335036476870724955044100544815, 483393035758086289335036476870732000654431118062⟩
  | 1, 2 => ⟨643973216799864787310660533398500782881049714040, 643973216799864787310660533398513731055760205796⟩
  | 2, 1 => ⟨647299992750918368484429629967753019912363241383, 647299992750918368484429629967777052200266810909⟩
  | 0, 4 => ⟨765062142561934006266518340373598658035330278742, 765062142561934006266518340373624137717988184197⟩
  | 1, 3 => ⟨1121852193515242253550277112350765891081648666665, 1121852193515242253550277112350813134741647360228⟩
  | 2, 2 => ⟨1480156333064507471264424225527143775604373140919, 1480156333064507471264424225527232222758734321291⟩
  | 3, 1 => ⟨1487049517314527825083426268337565708203951599985, 1487049517314527825083426268337732422605060094694⟩
  | 0, 5 => ⟨-4697223065696227832788532363590346611952468679426121, 4718315205183488078165190171404047507374451000015344⟩
  | 1, 4 => ⟨-9243191434816340844960275787879185670867015940070228, 9274906923543765487850014013106171284725373818570103⟩
  | 2, 3 => ⟨-18205109169033265412772337136874111072918751112686893, 18250719643326351247298129789336131134763412689063808⟩
  | 3, 2 => ⟨-35879414119141858407448007391080051463439565086253517, 35939175552214489277603404592488170486269970715729381⟩
  | 4, 1 => ⟨-70750530251258804991318213222681049151178122477259750, 70811471587103080804851245194039956789293194415495985⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0336Geometry.ds, E8TAxisProd0336Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 89139597551678348710198724853879547804861815121 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0336CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0337CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0337CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0337GraphCenterA.qJetBox,
   E8TAxisProd0337GraphCenterB.qJetBox,
   E8TAxisProd0337GraphCenterC.qJetBox,
   E8TAxisProd0337GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0337GraphWholeA.qJetBox,
   E8TAxisProd0337GraphWholeB.qJetBox,
   E8TAxisProd0337GraphWholeC.qJetBox,
   E8TAxisProd0337GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨85513867069556815832640373935131589083198637630, 85513867069556815832640373935132031243387894432⟩
  | 0, 2 => ⟨234306365258700495177349103579930183410557821700, 234306365258700495177349103579932036372905518499⟩
  | 1, 1 => ⟨235680995269120774925153784570075505742877669490, 235680995269120774925153784570078940303763609657⟩
  | 0, 3 => ⟨444591723778939229852082490021528968998727634123, 444591723778939229852082490021535271728243101573⟩
  | 1, 2 => ⟨592763373037298479415177814177555910685748752802, 592763373037298479415177814177567473431937759748⟩
  | 2, 1 => ⟨595851062293928111375632508424794555974506199620, 595851062293928111375632508424815985391124427475⟩
  | 0, 4 => ⟨707386698601739914177887452404365920622146584443, 707386698601739914177887452404388605898004707007⟩
  | 1, 3 => ⟨1038539223594556476817000768330205840144681808135, 1038539223594556476817000768330247842522589810160⟩
  | 2, 2 => ⟨1371103149281562307336874522313815247801165741189, 1371103149281562307336874522313893788917079390798⟩
  | 3, 1 => ⟨1377521255743425073785415900001558012599310549825, 1377521255743425073785415900001705889464149667802⟩
  | 0, 5 => ⟨-4278625402832872975440675889606049138610909028116586, 4298164802829854295065362655950833809442227447450650⟩
  | 1, 4 => ⟨-8416609777433419870421752575186291894982949850341189, 8446014100804276636259461208578097096731769512494885⟩
  | 2, 3 => ⟨-16571442436716616513039669683035338393612486424681579, 16613757007681934870828422263273842800738334885858640⟩
  | 3, 2 => ⟨-32648459239263436323812843063381961805165843196835336, 32703928939401213724458879824738737398591770262176050⟩
  | 4, 1 => ⟨-64356940821818022370510987750433046262358380058923709, 64413532490621498247237981044176345802754706952504472⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0337Geometry.ds, E8TAxisProd0337Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 80728034153544240908452064453572891098140442575 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0337CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0338CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0338CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0338GraphCenterA.qJetBox,
   E8TAxisProd0338GraphCenterB.qJetBox,
   E8TAxisProd0338GraphCenterC.qJetBox,
   E8TAxisProd0338GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0338GraphWholeA.qJetBox,
   E8TAxisProd0338GraphWholeB.qJetBox,
   E8TAxisProd0338GraphWholeC.qJetBox,
   E8TAxisProd0338GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨94059018807088094230916119452189716980245567542, 94059018807088094230916119452190205801461464360⟩
  | 0, 2 => ⟨255913596036624287885971916073147237201505509956, 255913596036624287885971916073149297227712366210⟩
  | 1, 1 => ⟨257202988170947074551653254703595957079339924245, 257202988170947074551653254703599782374772622741⟩
  | 0, 3 => ⟨482437558078870256482888418916403082253436871273, 482437558078870256482888418916410112209500467316⟩
  | 1, 2 => ⟨642572201425175568586889493493238728586007937412, 642572201425175568586889493493251647853967741703⟩
  | 2, 1 => ⟨645451674297678769052813076046983383722239804319, 645451674297678769052813076047007362118730666456⟩
  | 0, 4 => ⟨763702516601099479146512216629219628227536788645, 763702516601099479146512216629245048996527390518⟩
  | 1, 3 => ⟨1119772994871850721423989764341114346221693111660, 1119772994871850721423989764341161480475104100901⟩
  | 2, 2 => ⟨1477154080059323290837186888705563495287408130820, 1477154080059323290837186888705651737219292208529⟩
  | 3, 1 => ⟨1483120758326117110457044286168332400648666627353, 1483120758326117110457044286168498727349634677633⟩
  | 0, 5 => ⟨-4688369800569127112763168110829214029468835726833371, 4709421291582778942431884684962397953979820255763723⟩
  | 1, 4 => ⟨-9225740361154965201004243507595562421985302275789559, 9257393018759716576930632741294480682366059564520766⟩
  | 2, 3 => ⟨-18170672833620328856480829728100172193818731690555017, 18216187723718832694026691806056040173524294788869556⟩
  | 3, 2 => ⟨-35811408357096735719009856901033898511798960298532594, 35871028216020510915117229009931046909819319621504826⟩
  | 4, 1 => ⟨-70616149911462001775156839926393430948575758414151582, 70676892364885611749339761315295529198264378633623422⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0338Geometry.ds, E8TAxisProd0338Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 88835099461206089771386706898605150095928563936 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0338CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0339CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0339CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0339GraphCenterA.qJetBox,
   E8TAxisProd0339GraphCenterB.qJetBox,
   E8TAxisProd0339GraphCenterC.qJetBox,
   E8TAxisProd0339GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0339GraphWholeA.qJetBox,
   E8TAxisProd0339GraphWholeB.qJetBox,
   E8TAxisProd0339GraphWholeC.qJetBox,
   E8TAxisProd0339GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨85221331220101253786426055336838777856860580936, 85221331220101253786426055336839219091138284275⟩
  | 0, 2 => ⟨233751177921161719125806974412680511757412240998, 233751177921161719125806974412682360675246548072⟩
  | 1, 1 => ⟨234940851908423167210710909681766741285752489475, 234940851908423167210710909681770168304282013468⟩
  | 0, 3 => ⟨443708279113513381630824634121479346729434149362, 443708279113513381630824634121485635434124817956⟩
  | 1, 2 => ⟨591466406443045535510995086638962580677142010999, 591466406443045535510995086638974117559065713010⟩
  | 2, 1 => ⟨594138928117919226447670940538410896769211958534, 594138928117919226447670940538432278017594450278⟩
  | 0, 4 => ⟨706125112576574763020420682505144218338022775659, 706125112576574763020420682505166851045781937483⟩
  | 1, 3 => ⟨1036607875483434060891299465171046101124997874942, 1036607875483434060891299465171088005991064511284⟩
  | 2, 2 => ⟨1368312359296564423890634696255004396144623666387, 1368312359296564423890634696255082754513863135678⟩
  | 3, 1 => ⟨1373867809484051689307938967337207568042585607272, 1373867809484051689307938967337355099948214978266⟩
  | 0, 5 => ⟨-4270329248416784706366917094398158359420553784565986, 4289830348057207344937223423496321383218244209883622⟩
  | 1, 4 => ⟨-8400258943816131677269246779579734920119836142024513, 8429603934161623695986796827576653612856771657218019⟩
  | 2, 3 => ⟨-16539181949254220825344670769351341934619699464675064, 16581406100020281248435376140882057520572899887396453⟩
  | 3, 2 => ⟨-32584760561097451712066224943978444165406525717390431, 32640096212120994581843526934410965614881819401680036⟩
  | 4, 1 => ⟨-64231092624435637401360875476054869570174906558506330, 64287496077106144655287486535965738449026864232422260⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0339Geometry.ds, E8TAxisProd0339Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 80450026783617194712704929556906557471603189993 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0339CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0340CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0340CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0340GraphCenterA.qJetBox,
   E8TAxisProd0340GraphCenterB.qJetBox,
   E8TAxisProd0340GraphCenterC.qJetBox,
   E8TAxisProd0340GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0340GraphWholeA.qJetBox,
   E8TAxisProd0340GraphWholeB.qJetBox,
   E8TAxisProd0340GraphWholeC.qJetBox,
   E8TAxisProd0340GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨77418398655634806441053390069270333839253859573, 77418398655634806441053390069270733103166911260⟩
  | 0, 2 => ⟨213867098540807118535387510437754098165535687910, 213867098540807118535387510437755761397645461187⟩
  | 1, 1 => ⟨215134812256840891017711190770325323993380234004, 215134812256840891017711190770328401039212945948⟩
  | 0, 3 => ⟨408677678820434938289214076161920787577108505855, 408677678820434938289214076161926425651257026447⟩
  | 1, 2 => ⟨545333574698641958292063804584612333760346239565, 545333574698641958292063804584622658524739241054⟩
  | 2, 1 => ⟨548198660599446051432246347863805647631821166836, 548198660599446051432246347863824753899583456026⟩
  | 0, 4 => ⟨653817533608597868866685613529718909955570155798, 653817533608597868866685613529739104871904839363⟩
  | 1, 3 => ⟨961099924922703982162600926229065299891724738382, 961099924922703982162600926229102636178305638110⟩
  | 2, 2 => ⟨1269698089298280069356151605382393810318932021046, 1269698089298280069356151605382463540925931363968⟩
  | 3, 1 => ⟨1275673566564931070772133849775561542604921581436, 1275673566564931070772133849775692680785632785024⟩
  | 0, 5 => ⟨-3885798436652792839368532723189944360294276564582853, 3903870820402324774847581562589018141642810904185994⟩
  | 1, 4 => ⟨-7641094088036093851098490983516700750360520599016029, 7668308855504276309920730206467607533803119457130674⟩
  | 2, 3 => ⟨-15039087485633059018564138122640167959389997670025344, 15078272867031192885421435330200315958177554630847589⟩
  | 3, 2 => ⟨-29618680105743528680537617604306462671742023686613871, 29670069087779798466631433859406229896326555255918518⟩
  | 4, 1 => ⟨-58363128611587124062198477346621375771032413077737402, 58415579843917219383262457711236327927123479659198995⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0340Geometry.ds, E8TAxisProd0340Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 73050806879775742963109947024626028113972522045 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0340CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0341CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0341CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0341GraphCenterA.qJetBox,
   E8TAxisProd0341GraphCenterB.qJetBox,
   E8TAxisProd0341GraphCenterC.qJetBox,
   E8TAxisProd0341GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0341GraphWholeA.qJetBox,
   E8TAxisProd0341GraphWholeB.qJetBox,
   E8TAxisProd0341GraphWholeC.qJetBox,
   E8TAxisProd0341GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨70031310781432231328765722601811892942398519595, 70031310781432231328765722601812253610840426455⟩
  | 0, 2 => ⟨195068418330154075555031788709477339667524712946, 195068418330154075555031788709478832736340286036⟩
  | 1, 1 => ⟨196236936362214643973453166562348600090994274049, 196236936362214643973453166562351356889715743026⟩
  | 0, 3 => ⟨375447149313957898581972166263517160817874163255, 375447149313957898581972166263522204246971138448⟩
  | 1, 2 => ⟨501418504988537077618296254044623572370115679780, 501418504988537077618296254044632790988648563306⟩
  | 2, 1 => ⟨504076344139413392059055688137674038946170879606, 504076344139413392059055688137691071943071766006⟩
  | 0, 4 => ⟨604071934520695477934165110432297775179410761016, 604071934520695477934165110432315751122647275423⟩
  | 1, 3 => ⟨889130796109916890755040981215727785551037573823, 889130796109916890755040981215760968735154788118⟩
  | 2, 2 => ⟨1175416382417489823353906583123187339571327300737, 1175416382417489823353906583123249235980859189759⟩
  | 3, 1 => ⟨1180979510730432394459445224720419286570514556089, 1180979510730432394459445224720535555096685791090⟩
  | 0, 5 => ⟨-3518567512922733324005754186359067605110158003538353, 3535246522444536006707465670545921367705432497593131⟩
  | 1, 4 => ⟨-6916297018902091983353400817822665157920746228238287, 6941427324212226282065528440670681346277863107758229⟩
  | 2, 3 => ⟨-13607342785783908865977241914136416799542376209534682, 13643543505097692047966287856573392464252774853461774⟩
  | 3, 2 => ⟨-26788645271141821014441699949895490391740885105865217, 26836136385435476044675801839945521646648247279794993⟩
  | 4, 1 => ⟨-52766150712166143425278949590652108060576921320968035, 52814640873808065553282329359079558264750169870643586⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0341Geometry.ds, E8TAxisProd0341Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 66048850670971290470140629147250657502584364824 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0341CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0342CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0342CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0342GraphCenterA.qJetBox,
   E8TAxisProd0342GraphCenterB.qJetBox,
   E8TAxisProd0342GraphCenterC.qJetBox,
   E8TAxisProd0342GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0342GraphWholeA.qJetBox,
   E8TAxisProd0342GraphWholeB.qJetBox,
   E8TAxisProd0342GraphWholeC.qJetBox,
   E8TAxisProd0342GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨77151383849159435494999301533804770177300902422, 77151383849159435494999301533805168605811446536⟩
  | 0, 2 => ⟨213356761932333690767113748043973885488642798237, 213356761932333690767113748043975545085983410376⟩
  | 1, 1 => ⟨214453895680484578327470136850034852584437853324, 214453895680484578327470136850037922861360511209⟩
  | 0, 3 => ⟨407861138553128784956992460188299201173460188743, 407861138553128784956992460188304826682286827908⟩
  | 1, 2 => ⟨544133321151433884154518464097015307260962971729, 544133321151433884154518464097025608883750378713⟩
  | 2, 1 => ⟨546613159617498003715210902057482239591322257787, 546613159617498003715210902057501302808244859645⟩
  | 0, 4 => ⟨652647216378826118228221749293184422799111640977, 652647216378826118228221749293204570812331814428⟩
  | 1, 3 => ⟨959306260958810748612513522003670676416993936244, 959306260958810748612513522003707925801880458314⟩
  | 2, 2 => ⟨1267104251843420859161590189623801959851584274403, 1267104251843420859161590189623871527746180114504⟩
  | 3, 1 => ⟨1272276562308752373665298046153976718289119921730, 1272276562308752373665298046154107549583521579631⟩
  | 0, 5 => ⟨-3878043570491257890940622104381011876464150903923715, 3896080109639466129680578237220697928224012284952134⟩
  | 1, 4 => ⟨-7625812313856033008099411213749817766122992095124953, 7652971419295050606621648597769577509711631127948340⟩
  | 2, 3 => ⟨-15008941229671361344171165712014994158403338437580600, 15048041658443389501004344981474981058313621215027916⟩
  | 3, 2 => ⟨-29559166521041535524442745368292347617984484467133278, 29610429543326056858385992921188671916100038288211042⟩
  | 4, 1 => ⟨-58245570691971991007974839663926313222232259861791984, 58297845460513773175862928463405743587600154076916184⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0342Geometry.ds, E8TAxisProd0342Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 72797167815609752358664665939340350108582854817 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0342CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0343CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0343CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0343GraphCenterA.qJetBox,
   E8TAxisProd0343GraphCenterB.qJetBox,
   E8TAxisProd0343GraphCenterC.qJetBox,
   E8TAxisProd0343GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0343GraphWholeA.qJetBox,
   E8TAxisProd0343GraphWholeB.qJetBox,
   E8TAxisProd0343GraphWholeC.qJetBox,
   E8TAxisProd0343GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨69787768380055312387686278243591263803311493660, 69787768380055312387686278243591623717786612269⟩
  | 0, 2 => ⟨194599581041944638018288040422698776447646603714, 194599581041944638018288040422700266249553093105⟩
  | 1, 1 => ⟨195610857430511171583556749505195602728894128258, 195610857430511171583556749505198353452464464424⟩
  | 0, 3 => ⟨374692737940136797229704981951227612782133745858, 374692737940136797229704981951232644953871328250⟩
  | 1, 2 => ⟨500308132710386460248806144725133638079124992332, 500308132710386460248806144725142835993786702861⟩
  | 2, 1 => ⟨502608580628954277734685050607138460875840277675, 502608580628954277734685050607155455400096911673⟩
  | 0, 4 => ⟨602986563300587594041343953370233509964444988011, 602986563300587594041343953370251444067536389430⟩
  | 1, 3 => ⟨887465323868991725800940592958166500634981393461, 887465323868991725800940592958199606392326575052⟩
  | 2, 2 => ⟨1173005951182456741193296939083795121185860709157, 1173005951182456741193296939083856872761349048335⟩
  | 3, 1 => ⟨1177821333188517256316567458370177243601560161671, 1177821333188517256316567458370293239195252661858⟩
  | 0, 5 => ⟨-3511373643585054121274705935958147680485225187609990, 3528018778596474839499122416666824642466147927582471⟩
  | 1, 4 => ⟨-6902123660053709558903905188493545311588608383510139, 6927201303525231017238056441403395165838595871886671⟩
  | 2, 3 => ⟨-13579389089619980762589858744133938499734452200055358, 13615509442343113843655657076227336460441765809284283⟩
  | 3, 2 => ⟨-26733472340675413270322558662469953600934011289066461, 26780844558286807949963444565180403079256337806116997⟩
  | 4, 1 => ⟨-52657191545563923824074460247570804820280279312333656, 52705516179408561911196972085547656236653296969146422⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0343Geometry.ds, E8TAxisProd0343Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 65817612336625530401265472991770028396964348165 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0343CertifiedArithmetic

end


