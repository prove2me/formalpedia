-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0582CertifiedArithmetic__15
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0582CertifiedArithmetic__15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T16:14:05.803962+00:00
-- url     : https://prove2.me/theorems/ca9dc182-1cff-4e91-b3b2-c0811a21ed95
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0582CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0583CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0582CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0583CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0584CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0585CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0586CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0587CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0588CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0589CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0590CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0591CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0592CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0593CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0594CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0595CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0596CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0582CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0583CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0584CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0585CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0586CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0587CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0588CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0589CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0590CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0591CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0592CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0593CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0594CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0595CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0596CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0582CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0583CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0584CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0585CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0586CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0587CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0588CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0589CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0590CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0591CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0592CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0593CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0594CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0595CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0596CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0582CertifiedArithmetic (+14 modules: GeneralCK/Certificates/E8TAxisProd0583CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0584CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0585CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0586CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0587CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0588CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0589CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0590CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0591CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0592CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0593CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0594CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0595CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0596CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0578GraphCenterA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0571GraphCenterB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0576GraphCenterC__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0581GraphCenterD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0579GraphWholeA__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0581GraphWholeB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0576GraphWholeC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0572GraphWholeD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0581Geometry__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0583GraphCenterC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0585GraphCenterB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0587GraphWholeA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0587GraphWholeD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0590GraphWholeC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0591GraphWholeB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0592GraphCenterD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0592Geometry__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0593GraphCenterA__13

-- ===== source module GeneralCK.Certificates.E8TAxisProd0582CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0582CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0582GraphCenterA.qJetBox,
   E8TAxisProd0582GraphCenterB.qJetBox,
   E8TAxisProd0582GraphCenterC.qJetBox,
   E8TAxisProd0582GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0582GraphWholeA.qJetBox,
   E8TAxisProd0582GraphWholeB.qJetBox,
   E8TAxisProd0582GraphWholeC.qJetBox,
   E8TAxisProd0582GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨13882744076231430101566434202067896279292337616, 13882744076231430101566434202067979322439522091⟩
  | 0, 2 => ⟨44192317843162371685171411584488015685264404717, 44192317843162371685171411584488317131828527555⟩
  | 1, 1 => ⟨44467611130882658417821533070591919677827459974, 44467611130882658417821533070592453714134217104⟩
  | 0, 3 => ⟨96104742369830711934025443928748269600419668070, 96104742369830711934025443928749231492892779273⟩
  | 1, 2 => ⟨130342299981400585075413319632464255440731723833, 130342299981400585075413319632465950655390081273⟩
  | 2, 1 => ⟨131052726975694750209869518984635335971250060209, 131052726975694750209869518984638383027342596457⟩
  | 0, 4 => ⟨172672095409864475522137336424400950146791899683, 172672095409864475522137336424404152053673189708⟩
  | 1, 3 => ⟨260553014942626686512630494681360471939977561215, 260553014942626686512630494681366212335169372067⟩
  | 2, 2 => ⟨348808487199430444747526747263950870112080320895, 348808487199430444747526747263961343360509606828⟩
  | 3, 1 => ⟨350444521475755800838397578165386595021285919575, 350444521475755800838397578165405877904907395937⟩
  | 0, 5 => ⟨-591152731577235279588810138963543425889922161604940, 594726469599829799831246466142833948040362406848112⟩
  | 1, 4 => ⟨-1151984160770567773265933441493242987525217250176038, 1157323829784107026059542444188319446766870815888120⟩
  | 2, 3 => ⟨-2247592574397387469174172559175581589346739809014056, 2255245794959205421113898087263939041931410485065423⟩
  | 3, 2 => ⟨-4388439132251109431966191435470495281840857070364749, 4398456816344290898516981155261685044038996765407561⟩
  | 4, 1 => ⟨-8572954917415622917230216053372002294557864201035520, 8583191959809641749345115411690852236003182055856829⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0582Geometry.ds, E8TAxisProd0582Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 12993069074279744998147679703655133408924057418 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0582CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0583CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0583CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0583GraphCenterA.qJetBox,
   E8TAxisProd0583GraphCenterB.qJetBox,
   E8TAxisProd0583GraphCenterC.qJetBox,
   E8TAxisProd0583GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0583GraphWholeA.qJetBox,
   E8TAxisProd0583GraphWholeB.qJetBox,
   E8TAxisProd0583GraphWholeC.qJetBox,
   E8TAxisProd0583GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12366663123975926437726857318877817514600634171, 12366663123975926437726857318877893195314623658⟩
  | 0, 2 => ⟨39727072612936490714843438625257871452844333833, 39727072612936490714843438625258142958768010534⟩
  | 1, 1 => ⟨39977866091318363350018776334476023506663835288, 39977866091318363350018776334476502665065882224⟩
  | 0, 3 => ⟨87136824352596478588616748987816589885295231194, 87136824352596478588616748987817452365417296679⟩
  | 1, 2 => ⟨118330663988428692119545520608383779918677359171, 118330663988428692119545520608385295022667261216⟩
  | 2, 1 => ⟨118984397084591160959183543053218654751320518553, 118984397084591160959183543053221372045884205995⟩
  | 0, 4 => ⟨157938765136316157105808858642969008873385247058, 157938765136316157105808858642971866836404430584⟩
  | 1, 3 => ⟨238809399553204569150691669567666488514948586542, 238809399553204569150691669567671598970345059645⟩
  | 2, 2 => ⟨320029329375238005094856769068220539598517850536, 320029329375238005094856769068229846744737168007⟩
  | 3, 1 => ⟨321549746318373656452792897995871151079571065456, 321549746318373656452792897995888260219567493996⟩
  | 0, 5 => ⟨-513778111095314219122395372929070053193689255681966, 516942409289267801201778961922824163659740535921074⟩
  | 1, 4 => ⟨-1000350749070078639434699896911906401987702557841047, 1005070299576413195677140594073661702095548134267373⟩
  | 2, 3 => ⟨-1950184226028099642847193092819359512623763801644375, 1956940699328982339730800981594856865119518088983058⟩
  | 3, 2 => ⟨-3804779570579939334516250669612271144751813463555614, 3813617893939431126710222136319550005850771339818382⟩
  | 4, 1 => ⟨-7427010250292734262844710598354918071173691812993675, 7436042143341872769652915713593561235023000416739554⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0583Geometry.ds, E8TAxisProd0583Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 11567915700884196908916445284958159771488172049 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0583CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0584CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0584CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0584GraphCenterA.qJetBox,
   E8TAxisProd0584GraphCenterB.qJetBox,
   E8TAxisProd0584GraphCenterC.qJetBox,
   E8TAxisProd0584GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0584GraphWholeA.qJetBox,
   E8TAxisProd0584GraphWholeB.qJetBox,
   E8TAxisProd0584GraphWholeC.qJetBox,
   E8TAxisProd0584GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17371955219264389063669546366911156603707278185, 17371955219264389063669546366911256604276883774⟩
  | 0, 2 => ⟨54369595436722720503997804171435039109828137460, 54369595436722720503997804171435410183437639592⟩
  | 1, 1 => ⟨54649055881779750478115667013153653544902262423, 54649055881779750478115667013154315620116496832⟩
  | 0, 3 => ⟨116284410901866288040414246785894768871098833175, 116284410901866288040414246785895962784813612068⟩
  | 1, 2 => ⟨157286909486597172726429500976624277654523670139, 157286909486597172726429500976626394485695641513⟩
  | 2, 1 => ⟨157994157236124565992355292670825444603323514247, 157994157236124565992355292670829265516756516045⟩
  | 0, 4 => ⟨205428733961860910320813679506030353567163326374, 205428733961860910320813679506034361875185058921⟩
  | 1, 3 => ⟨308737285863845775254418245971880564278750864073, 308737285863845775254418245971887785020792673286⟩
  | 2, 2 => ⟨412409572232637374135836536459762656482955588018, 412409572232637374135836536459775875304390270496⟩
  | 3, 1 => ⟨414008861965537500105598607803184893602462083561, 414008861965537500105598607803209303923599392752⟩
  | 0, 5 => ⟨-771416952254470783094586288163783312243459061117499, 775946069424471010359292306044219669189699896697179⟩
  | 1, 4 => ⟨-1505569167712679713872133694813139312135999345684550, 1512358412852142972585788229289543411630255195712577⟩
  | 2, 3 => ⟨-2941716628865063762246714344933595705682616187307398, 2951468891289031157610692130013125596788862743387280⟩
  | 3, 2 => ⟨-5751861903449079449325747902424624542758262388939347, 5764642384873048622510547417373056514249019037453602⟩
  | 4, 1 => ⟨-11252284839210099259118847453965971497108381461937085, 11265345427654256416950852998056336156379760179315886⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0584Geometry.ds, E8TAxisProd0584Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16275749283643598334683890598186544872398571611 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0584CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0585CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0585CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0585GraphCenterA.qJetBox,
   E8TAxisProd0585GraphCenterB.qJetBox,
   E8TAxisProd0585GraphCenterC.qJetBox,
   E8TAxisProd0585GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0585GraphWholeA.qJetBox,
   E8TAxisProd0585GraphWholeB.qJetBox,
   E8TAxisProd0585GraphWholeC.qJetBox,
   E8TAxisProd0585GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨15506893500833404543726039131694712934769947410, 15506893500833404543726039131694803938423231444⟩
  | 0, 2 => ⟨48976085430845293111705085201400008969674820913, 48976085430845293111705085201400343011747495035⟩
  | 1, 1 => ⟨49231137360307907297081952443663808260836129729, 49231137360307907297081952443664402185760963451⟩
  | 0, 3 => ⟨105649271741136588193391399167295712271204686468, 105649271741136588193391399167296782681467186896⟩
  | 1, 2 => ⟨143073713817092173197692092044014919308286442017, 143073713817092173197692092044016811554521455678⟩
  | 2, 1 => ⟨143725524306186613544357072909667068851496237185, 143725524306186613544357072909670477276173103319⟩
  | 0, 4 => ⟨188238311773538553310599124857382701066899299341, 188238311773538553310599124857386279499926640497⟩
  | 1, 3 => ⟨283451583771500234108885532653216488526104350086, 283451583771500234108885532653222919720044071937⟩
  | 2, 2 => ⟨379004207196169375320427884666201709385554157662, 379004207196169375320427884666213463130844245345⟩
  | 3, 1 => ⟨380491411946231821079958378776825504085706765426, 380491411946231821079958378776847176976177755638⟩
  | 0, 5 => ⟨-675695699430671863735592025799261137971009076318898, 679716821453834457522872492129779888328168184306243⟩
  | 1, 4 => ⟨-1317765869744610919390905712151549051574546678753494, 1323783991159225815404304740314860882770676835709752⟩
  | 2, 3 => ⟨-2572944354663139824417271357680138759602093028111430, 2581579642928647591144001370622668997782600741070639⟩
  | 3, 2 => ⟨-5027316836911038654713613791616835511336422482010922, 5038626796595929445213666545480774864399224950241243⟩
  | 4, 1 => ⟨-9828065368179005741162952321103935644798880516709328, 9839622459617993576638897499946324165100817245438410⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0585Geometry.ds, E8TAxisProd0585Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 14520556280676966894779773464783120653466284213 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0585CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0586CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0586CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0586GraphCenterA.qJetBox,
   E8TAxisProd0586GraphCenterB.qJetBox,
   E8TAxisProd0586GraphCenterC.qJetBox,
   E8TAxisProd0586GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0586GraphWholeA.qJetBox,
   E8TAxisProd0586GraphWholeB.qJetBox,
   E8TAxisProd0586GraphWholeC.qJetBox,
   E8TAxisProd0586GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17304084005325389728902932007025104102268810097, 17304084005325389728902932007025203898846134837⟩
  | 0, 2 => ⟨54224400311199765228160245972291589434757096397, 54224400311199765228160245972291959690106924441⟩
  | 1, 1 => ⟨54452688284174508995913086394054141616218935353, 54452688284174508995913086394054802207620937811⟩
  | 0, 3 => ⟨116027872374655870816320109693445434898876510080, 116027872374655870816320109693446626138588683586⟩
  | 1, 2 => ⟨156901376025974409981945710795041827891874739866, 156901376025974409981945710795043939919685560551⟩
  | 2, 1 => ⟨157479215748316603551392590123430358977423972625, 157479215748316603551392590123434171123946018785⟩
  | 0, 4 => ⟨205033022934092214489770276816238495347055723005, 205033022934092214489770276816242494353870795139⟩
  | 1, 3 => ⟨308116433744918969517164942971423557026854293823, 308116433744918969517164942971430760905260404433⟩
  | 2, 2 => ⟨411497086779764378667289130545108034470174915274, 411497086779764378667289130545121222214651578074⟩
  | 3, 1 => ⟨412803946379309242794265870246547361207292929405, 412803946379309242794265870246571713728112129048⟩
  | 0, 5 => ⟨-769391529369951994410064807148961865656787485595236, 773910211024836143236760308111497476284737441218553⟩
  | 1, 4 => ⟨-1501597233976961279895881718826662018866371601231993, 1508370701661519133021988475263189223923927036550282⟩
  | 2, 3 => ⟨-2933918645369948281151927303577645697124893066752011, 2943648111017577970923367495985063497707415258172364⟩
  | 3, 2 => ⟨-5736540507084945888518280066834302359294107348183747, 5749290727216872082852978087911883737321208147500196⟩
  | 4, 1 => ⟨-11222163835855682836329223328990692653430202973052248, 11235191654913207433922033991275988777919335419643294⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0586Geometry.ds, E8TAxisProd0586Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16211726573455076450233200001274065592953288441 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0586CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0587CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0587CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0587GraphCenterA.qJetBox,
   E8TAxisProd0587GraphCenterB.qJetBox,
   E8TAxisProd0587GraphCenterC.qJetBox,
   E8TAxisProd0587GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0587GraphWholeA.qJetBox,
   E8TAxisProd0587GraphWholeB.qJetBox,
   E8TAxisProd0587GraphWholeC.qJetBox,
   E8TAxisProd0587GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨15445755871292650885959172755225057266457562185, 15445755871292650885959172755225148085062514297⟩
  | 0, 2 => ⟨48844170807166766193525589939956980196326427114, 48844170807166766193525589939957313501347999317⟩
  | 1, 1 => ⟨49052516514909159567361470809195227572080804941, 49052516514909159567361470809195820163870624707⟩
  | 0, 3 => ⟨105414202258209491289387126170105873891701481879, 105414202258209491289387126170106941900729035600⟩
  | 1, 2 => ⟨142719758509655603995110025292274989519445893099, 142719758509655603995110025292276877461719647962⟩
  | 2, 1 => ⟨143252297772814948622708850711329046839536310584, 143252297772814948622708850711332447420905111224⟩
  | 0, 4 => ⟨187872965982468868291719538778537493077277993373, 187872965982468868291719538778541063186463408531⟩
  | 1, 3 => ⟨282877077736975886144884932357286413751173185245, 282877077736975886144884932357292829880626724843⟩
  | 2, 2 => ⟨378158505267125675342708180855200734458710889286, 378158505267125675342708180855212460476202564747⟩
  | 3, 1 => ⟨379373769111696550602680831736581112650423552395, 379373769111696550602680831736602734023512578887⟩
  | 0, 5 => ⟨-673871732264762509509773974517631452657726225950069, 677883573259907306312511498203052760662820487599502⟩
  | 1, 4 => ⟨-1314190736311392406477625675227802531472423130691028, 1320194873056742612920399239115465560564078814982241⟩
  | 2, 3 => ⟨-2565928728253728468301951365784968758333224438761872, 2574543901066096745350535933667619752389753123766268⟩
  | 3, 2 => ⟨-5013539104471476391379000846207371949121075637786911, 5024822561652528150495671151383825044078500438319264⟩
  | 4, 1 => ⟨-9800991917487451566484247753664387675513601449845832, 9812520837585881067603573121123489517271386095736165⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0587Geometry.ds, E8TAxisProd0587Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 14462918565263463778707705158913302063218928251 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0587CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0588CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0588CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0588GraphCenterA.qJetBox,
   E8TAxisProd0588GraphCenterB.qJetBox,
   E8TAxisProd0588GraphCenterC.qJetBox,
   E8TAxisProd0588GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0588GraphWholeA.qJetBox,
   E8TAxisProd0588GraphWholeB.qJetBox,
   E8TAxisProd0588GraphWholeC.qJetBox,
   E8TAxisProd0588GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨13827578704576587721518344544642405202780133741, 13827578704576587721518344544642488077645091398⟩
  | 0, 2 => ⟨44072321727286898702964458647835535449523837904, 44072321727286898702964458647835836230679832743⟩
  | 1, 1 => ⟨44304886674257292182430362821943875109318550541, 44304886674257292182430362821944407945275460720⟩
  | 0, 3 => ⟨95889113390619311954158132232139706292264416282, 95889113390619311954158132232140666023797944484⟩
  | 1, 2 => ⟨130016941523095985106708607934824448953257812031, 130016941523095985106708607934826140303115010011⟩
  | 2, 1 => ⟨130617207116699913935934932032398996908750019410, 130617207116699913935934932032402036932606065293⟩
  | 0, 4 => ⟨172334368866827155754925596347218684932225103565, 172334368866827155754925596347221879373093471201⟩
  | 1, 3 => ⟨260020676145986730582459755063757800294489392452, 260020676145986730582459755063763527200039403289⟩
  | 2, 2 => ⟨348023528617615195715757202809876728009707355561, 348023528617615195715757202809887176456485035947⟩
  | 3, 1 => ⟨349406105635566145656426617730917039448124294162, 349406105635566145656426617730936276296006651923⟩
  | 0, 5 => ⟨-589514545421844791155084412277481503246388153675370, 593080008959742905226002554359911987912950383957065⟩
  | 1, 4 => ⟨-1148774843255744705865897628646060896323866052577004, 1154102082913753817080389433475601305398029216091788⟩
  | 2, 3 => ⟨-2241297973668647899421435189501015488072532652348692, 2248933389108525244602096492473791479133499023703067⟩
  | 3, 2 => ⟨-4376083544389847679873534756645526454989345073177228, 4386077929543429862271594542033271093564550722113311⟩
  | 4, 1 => ⟨-8548688062177079262653760826726976186134884620473030, 8558900762705914433777526304954491240636564600589656⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0588Geometry.ds, E8TAxisProd0588Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 12941090942191910617447891968007850256203516330 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0588CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0589CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0589CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0589GraphCenterA.qJetBox,
   E8TAxisProd0589GraphCenterB.qJetBox,
   E8TAxisProd0589GraphCenterC.qJetBox,
   E8TAxisProd0589GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0589GraphWholeA.qJetBox,
   E8TAxisProd0589GraphWholeB.qJetBox,
   E8TAxisProd0589GraphWholeC.qJetBox,
   E8TAxisProd0589GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12317072307466784818205181692084684954856194821, 12317072307466784818205181692084760482774647139⟩
  | 0, 2 => ⟨39618274891004765701127857529950198950853195893, 39618274891004765701127857529950469857277994639⟩
  | 1, 1 => ⟨39830139202952887910826897450647080658689747092, 39830139202952887910826897450647558738681793402⟩
  | 0, 3 => ⟨86939595630904143021114531426567800379298109439, 86939595630904143021114531426568660918753706610⟩
  | 1, 2 => ⟨118032459929188660523198616477516302801986108779, 118032459929188660523198616477517814443283369527⟩
  | 2, 1 => ⟨118584814893066515441818266582726843261730717940, 118584814893066515441818266582729554265929184911⟩
  | 0, 4 => ⟨157627279967145243167274250156598250828036759229, 157627279967145243167274250156601102107919619884⟩
  | 1, 3 => ⟨238317241817364289191321452849825740452450934096, 238317241817364289191321452849830838855351319135⟩
  | 2, 2 => ⟨319302401715695999538494022579906363231748671523, 319302401715695999538494022579915648245834375739⟩
  | 3, 1 => ⟨320587264549889440813253274021590855754385640985, 320587264549889440813253274021607923856965293466⟩
  | 0, 5 => ⟨-512317235642136901382758462996252719291670510478560, 515474177279778644200315224984468809792463761258374⟩
  | 1, 4 => ⟨-997490421979037296022761586555997427649420013744756, 1002198955925165666871761348338000473305354161343452⟩
  | 2, 3 => ⟨-1944577188370881242947816756416651753895822210118377, 1951317944204511788745649300072460287592365466396496⟩
  | 3, 2 => ⟨-3793779518213051187336332100923760997753898802639368, 3802597414506619917278760688338552680757922659596583⟩
  | 4, 1 => ⟨-7405417307138869122866280718529585963230358998217999, 7414428236163377410364073304519860719973173508589921⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0589Geometry.ds, E8TAxisProd0589Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 11521216975415067326845339407623751333924371341 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0589CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0590CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0590CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0590GraphCenterA.qJetBox,
   E8TAxisProd0590GraphCenterB.qJetBox,
   E8TAxisProd0590GraphCenterC.qJetBox,
   E8TAxisProd0590GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0590GraphWholeA.qJetBox,
   E8TAxisProd0590GraphWholeB.qJetBox,
   E8TAxisProd0590GraphWholeC.qJetBox,
   E8TAxisProd0590GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨13772563159716339088381917708238067913417382207, 13772563159716339088381917708238150620342371795⟩
  | 0, 2 => ⟨43952594883938921819237956494824607543460013355, 43952594883938921819237956494824907660644136854⟩
  | 1, 1 => ⟨44142568500061585577492355329435987179091809615, 44142568500061585577492355329436518817316275013⟩
  | 0, 3 => ⟨95673906204010255279986253353324405170464699477, 95673906204010255279986253353325362745819832123⟩
  | 1, 2 => ⟨129692247896854717433078717358092896439575854023, 129692247896854717433078717358094583933198942946⟩
  | 2, 1 => ⟨130182667551093273529334274535354875413770607818, 130182667551093273529334274535357908421055224027⟩
  | 0, 4 => ⟨171997227091968019875776542634360254886214869036, 171997227091968019875776542634363441877992403972⟩
  | 1, 3 => ⟨259489283383590422377379009996306453152200244157, 259489283383590422377379009996312166598748880701⟩
  | 2, 2 => ⟨347240017373787634007680790105076874626128051267, 347240017373787634007680790105087298327668447625⟩
  | 3, 1 => ⟨348369778816015428503222080984475933103777698388, 348369778816015428503222080984495124020835341482⟩
  | 0, 5 => ⟨-587880083358452979856030435082561193897153882135008, 591437290420316613681615665391557431477685493966627⟩
  | 1, 4 => ⟨-1145572842267913557805665284376120579068460748329467, 1150887681326237511993742012054581315428509347221735⟩
  | 2, 3 => ⟨-2235017767159537116756261582587399897554093958187137, 2242635421386092970129324592511329224869238733983739⟩
  | 3, 2 => ⟨-4363756301156406675156211330933568993049404759460275, 4373727450548115369142656715055282089905853110565653⟩
  | 4, 1 => ⟨-8524477060038968756159784116584122705400200336223592, 8534665500671866663588038442241709265877793655731481⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0590Geometry.ds, E8TAxisProd0590Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 12889254739647192427541762115573630791729675554 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0590CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0591CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0591CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0591GraphCenterA.qJetBox,
   E8TAxisProd0591GraphCenterB.qJetBox,
   E8TAxisProd0591GraphCenterC.qJetBox,
   E8TAxisProd0591GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0591GraphWholeA.qJetBox,
   E8TAxisProd0591GraphWholeB.qJetBox,
   E8TAxisProd0591GraphWholeC.qJetBox,
   E8TAxisProd0591GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12267617334126469820068046688276556297194845908, 12267617334126469820068046688276631672627886152⟩
  | 0, 2 => ⟨39509723461768555203308965813788325466995507633, 39509723461768555203308965813788595775216678400⟩
  | 1, 1 => ⟨39682784685392179420534718679852930060420941619, 39682784685392179420534718679853407064358832499⟩
  | 0, 3 => ⟨86742755926867882085296377135174142976519998541, 86742755926867882085296377135175001579590864451⟩
  | 1, 2 => ⟨117734870517717850541447927698786066592163680634, 117734870517717850541447927698787574778459291417⟩
  | 2, 1 => ⟨118186140519142499877991605455627558620962530950, 118186140519142499877991605455630263348842670336⟩
  | 0, 4 => ⟨157316336743776438990526918604636174355713029785, 157316336743776438990526918604639018967634478108⟩
  | 1, 3 => ⟨237825962883434007289870900237125046243364282025, 237825962883434007289870900237130132621208381890⟩
  | 2, 2 => ⟨318576820838889850158673284968385144649278664822, 318576820838889850158673284968394407581708828459⟩
  | 3, 1 => ⟨319626728983145236211475118381593319497542075198, 319626728983145236211475118381610346656513566989⟩
  | 0, 5 => ⟨-510859812858363691336125030005801444282852540447143, 514009415114252121744896590867863014134521743162028⟩
  | 1, 4 => ⟨-994636877361411329525427952590882182520757788947270, 999334421293730933237757009885434932229930152561654⟩
  | 2, 3 => ⟨-1938983491315290043309380669261952333356862224896084, 1945708569274767282964602234747277006891448793415453⟩
  | 3, 2 => ⟨-3782805728463746440004241094645388028437807058271850, 3791603253473470756333479990602112872178101466881605⟩
  | 4, 1 => ⟨-7383876098545062006781177254367720468615718616775006, 7392866133987513593864027311632778048621989872850856⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0591Geometry.ds, E8TAxisProd0591Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 11474646851230267937465623416883200995681029882 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0591CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0592CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0592CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0592GraphCenterA.qJetBox,
   E8TAxisProd0592GraphCenterB.qJetBox,
   E8TAxisProd0592GraphCenterC.qJetBox,
   E8TAxisProd0592GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0592GraphWholeA.qJetBox,
   E8TAxisProd0592GraphWholeB.qJetBox,
   E8TAxisProd0592GraphWholeC.qJetBox,
   E8TAxisProd0592GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨11049014492785802237796609630667251938053478206, 11049014492785802237796609630667321101185245352⟩
  | 0, 2 => ⟨35774137664211306910812522483816383620285250960, 35774137664211306910812522483816628892288860179⟩
  | 1, 1 => ⟨36037946294364405047800150576021503156960624294, 36037946294364405047800150576021934336004279358⟩
  | 0, 3 => ⟨79101588864432973445551014575665532019252596501, 79101588864432973445551014575666308398177832748⟩
  | 1, 2 => ⟨107588548256547394153782357401450547053694179192, 107588548256547394153782357401451906573061669918⟩
  | 2, 1 => ⟨108283094176550507207941365246200374712407535979, 108283094176550507207941365246202807819588894525⟩
  | 0, 4 => ⟨144608608658119953539162474144099969849363075004, 144608608658119953539162474144102535721963748712⟩
  | 1, 3 => ⟨219133521471699643462343815023654901090465450289, 219133521471699643462343815023659478034737147696⟩
  | 2, 2 => ⟨294034628870980790830118587719666004709338669704, 294034628870980790830118587719674326524347387511⟩
  | 3, 1 => ⟨295666403029770970033309176593680164030365839523, 295666403029770970033309176593695440166599733357⟩
  | 0, 5 => ⟨-446357393233001241639311792903426966542807497322938, 449166254174498902246022012370142244284768495583581⟩
  | 1, 4 => ⟨-868311536070634609548513609674575996135736330468502, 872493675086271607786458376160253270392551327153201⟩
  | 2, 3 => ⟨-1691377530625682808692330263325922272673937889465038, 1697357817846753024436108697749646532015681912269605⟩
  | 3, 2 => ⟨-3297211391888172741412775561133100323545427048159952, 3305029756225617922058073099110513681420655581401678⟩
  | 4, 1 => ⟨-6431128944033584293125881961688999453530656209141358, 6439119665662956299594400795578269246796641926404156⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0592Geometry.ds, E8TAxisProd0592Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10330056592589738627228586709849386876063413706 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0592CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0593CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0593CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0593GraphCenterA.qJetBox,
   E8TAxisProd0593GraphCenterB.qJetBox,
   E8TAxisProd0593GraphCenterC.qJetBox,
   E8TAxisProd0593GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0593GraphWholeA.qJetBox,
   E8TAxisProd0593GraphWholeB.qJetBox,
   E8TAxisProd0593GraphWholeC.qJetBox,
   E8TAxisProd0593GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨9821586874444809372411429394396566060006425560, 9821586874444809372411429394396629189670632824⟩
  | 0, 2 => ⟨32092117229662558494411241829006672607454782805, 32092117229662558494411241829006893812963789328⟩
  | 1, 1 => ⟨32331993802440190600972502419575119187396053142, 32331993802440190600972502419575506472771143517⟩
  | 0, 3 => ⟨71566195812519334055844998778434489329743686746, 71566195812519334055844998778435187181137021292⟩
  | 1, 2 => ⟨97472130278604155723662644748170428313023382692, 97472130278604155723662644748171646307236081262⟩
  | 2, 1 => ⟨98110154093349764045325337829397476249758145527, 98110154093349764045325337829399651390472744672⟩
  | 0, 4 => ⟨132006425494979399091470309248593194583438644648, 132006425494979399091470309248595496156238870622⟩
  | 1, 3 => ⟨200469572741434175715152422428991311989255080185, 200469572741434175715152422428995407328995373499⟩
  | 2, 2 => ⟨269283296113062687656171987629839081012938174589, 269283296113062687656171987629846514971632013228⟩
  | 3, 1 => ⟨270798405470950677978488751711480677178279069622, 270798405470950677978488751711494304276520567869⟩
  | 0, 5 => ⟨-385366013011899706971580849975781222127958333416059, 387852846855269089964728957488720541833523817134359⟩
  | 1, 4 => ⟨-748947002088331147571313010354238994363763204731378, 752643114147082891638506704189796898405575287820715⟩
  | 2, 3 => ⟨-1457572612898356403547592864424453709774535440426548, 1462851962863663100534166850153837945943670785518274⟩
  | 3, 2 => ⟨-2838984306841793169291082838769707022156617950660082, 2845882599696342316592004114840989802785221793719584⟩
  | 4, 1 => ⟨-5532663290285092487848630906723182083973564084464760, 5539715502082655467362052542315979024042995706138605⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0593Geometry.ds, E8TAxisProd0593Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 9177497272433651516639585856399293522931627381 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0593CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0594CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0594CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0594GraphCenterA.qJetBox,
   E8TAxisProd0594GraphCenterB.qJetBox,
   E8TAxisProd0594GraphCenterC.qJetBox,
   E8TAxisProd0594GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0594GraphWholeA.qJetBox,
   E8TAxisProd0594GraphWholeB.qJetBox,
   E8TAxisProd0594GraphWholeC.qJetBox,
   E8TAxisProd0594GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨11004358571772141756084384036792027693619408748, 11004358571772141756084384036792096717667115706⟩
  | 0, 2 => ⟨35675373578674880615465981624471472125666876418, 35675373578674880615465981624471716859099023912⟩
  | 1, 1 => ⟨35903631688412878269126397045107910602395747720, 35903631688412878269126397045108340816042978471⟩
  | 0, 3 => ⟨78921007912744433358886901696484464294902416349, 78921007912744433358886901696485238956335568085⟩
  | 1, 2 => ⟨107314916178856506268341866629093624909352694757, 107314916178856506268341866629094981376178442185⟩
  | 2, 1 => ⟨107915972341212379251411006757485424239624354800, 107915972341212379251411006757487851817266915522⟩
  | 0, 4 => ⟨144320997947256317089876320070499693326904278630, 144320997947256317089876320070502253420906039247⟩
  | 1, 3 => ⟨218677939236417689091956851892875216201721922876, 218677939236417689091956851892879782771057506202⟩
  | 2, 2 => ⟨293360517106112740598792182535400445135636815690, 293360517106112740598792182535408747957026685493⟩
  | 3, 1 => ⟨294772903462914293250127482513053957363767553511, 294772903462914293250127482513069198367572127341⟩
  | 0, 5 => ⟨-445063642466308481087340869470508685162034081351985, 447866046810727905049714360128647191953231936498931⟩
  | 1, 4 => ⟨-865780103524749814274155004139737233555014619328002, 869952600160425238025139659700535132669052575392410⟩
  | 2, 3 => ⟨-1686418332143749972224846404857170784114557979625811, 1692384898018133021640074254658787074731670868578556⟩
  | 3, 2 => ⟨-3287488242462955915619751160984221644082954572899790, 3295288823996171592870116791724154122641679297464502⟩
  | 4, 1 => ⟨-6412054088435756471185465474374016563391018047926262, 6420026654906439951296854440076572798922804411658073⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0594Geometry.ds, E8TAxisProd0594Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10288028153898563814105191940073255926360419566 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0594CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0595CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0595CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0595GraphCenterA.qJetBox,
   E8TAxisProd0595GraphCenterB.qJetBox,
   E8TAxisProd0595GraphCenterC.qJetBox,
   E8TAxisProd0595GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0595GraphWholeA.qJetBox,
   E8TAxisProd0595GraphWholeB.qJetBox,
   E8TAxisProd0595GraphWholeC.qJetBox,
   E8TAxisProd0595GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨9781527596048939189210030775939574454944141354, 9781527596048939189210030775939637458197395361⟩
  | 0, 2 => ⟨32002762545895329750869816416035426039237137031, 32002762545895329750869816416035646758926709629⟩
  | 1, 1 => ⟨32210310146834116375422786913243954038926610513, 32210310146834116375422786913244340456083990337⟩
  | 0, 3 => ⟨71401353407944012418919867203903174178925019670, 71401353407944012418919867203903870482584449536⟩
  | 1, 2 => ⟨97221806340723818884295182885452387097451329409, 97221806340723818884295182885453602347127071793⟩
  | 2, 1 => ⟨97773939862409385596800973744554628475764626230, 97773939862409385596800973744556798652217960514⟩
  | 0, 4 => ⟨131741499575384743240810335265444389273298935015, 131741499575384743240810335265446685633382052371⟩
  | 1, 3 => ⟨200048854596598024531332443119843869960196806501, 200048854596598024531332443119847955955787032660⟩
  | 2, 2 => ⟨268659668355941059742539352013075436548522094887, 268659668355941059742539352013082853416449861679⟩
  | 3, 1 => ⟨269971063268521100581894341415414490611124951223, 269971063268521100581894341415428086121031712914⟩
  | 0, 5 => ⟨-384224949314124206258739494322241905393647285364387, 386706008932534805211455736471364277499166085281146⟩
  | 1, 4 => ⟨-746715786242001980875958378378165683167873793924987, 750403277663337294252316455283574455437717578608937⟩
  | 2, 3 => ⟨-1453204258278612627111400856333657288782980995750119, 1458471337059089371790178101231887531688083618111406⟩
  | 3, 2 => ⟨-2830424740932789401860363675243656309512500636056160, 2837307110835854992365348019629609941128838304673596⟩
  | 4, 1 => ⟨-5515881146070703345738843908799783103592255593983747, 5522917043277587861166982733789028863745707713227994⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0595Geometry.ds, E8TAxisProd0595Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 9139816619333738246712788990399596442043335394 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0595CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0596CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0596CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0596GraphCenterA.qJetBox,
   E8TAxisProd0596GraphCenterB.qJetBox,
   E8TAxisProd0596GraphCenterC.qJetBox,
   E8TAxisProd0596GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0596GraphWholeA.qJetBox,
   E8TAxisProd0596GraphWholeB.qJetBox,
   E8TAxisProd0596GraphWholeC.qJetBox,
   E8TAxisProd0596GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8720961449892551693605670520892479542605527319, 8720961449892551693605670520892537213027720644⟩
  | 0, 2 => ⟨28758075120660608076105195349604489686904691438, 28758075120660608076105195349604689253336122188⟩
  | 1, 1 => ⟨28975977218216831195600948878952542379968276323, 28975977218216831195600948878952890287585152120⟩
  | 0, 3 => ⟨64676035818091096238261740134605152335500107132, 64676035818091096238261740134605779598656638333⟩
  | 1, 2 => ⟨88211782701679923504630772668980848787951082030, 88211782701679923504630772668981939780616529064⟩
  | 2, 1 => ⟨88797339691906961935026434526086972228403042876, 88797339691906961935026434526088916202746666468⟩
  | 0, 4 => ⟨120372374568358789078388748277914375800944735743, 120372374568358789078388748277916439637259289465⟩
  | 1, 3 => ⟨183208510102370915554636176343528719672273435042, 183208510102370915554636176343532382082335598257⟩
  | 2, 2 => ⟨246371190434409028235003667686525164473521109905, 246371190434409028235003667686531800825947792261⟩
  | 3, 1 => ⟨247777186808762820407992393040585840404367224434, 247777186808762820407992393040597987244517656301⟩
  | 0, 5 => ⟨-331619099471764391839565883667810835838397900098112, 333817857820901142572398406085397895009811641393659⟩
  | 1, 4 => ⟨-643835186540654277840463573060277380469018938448498, 647096934282556547967552951736269226278195713231748⟩
  | 2, 3 => ⟨-1251828223294562716223027743654473585718647884190017, 1256481579956000818317474894977851001397630426217617⟩
  | 3, 2 => ⟨-2436031166218367336753247774595340179214460775011478, 2442108113011541912442766605699644895125759383697345⟩
  | 4, 1 => ⟨-4743125095893483346641742727344185638633771828733089, 4749339689250973753437932997112273697726662121747211⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0596Geometry.ds, E8TAxisProd0596Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 8144576226919919603385433903013839126273523767 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0596CertifiedArithmetic

end


