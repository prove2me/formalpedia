-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0351CertifiedArithmetic__11
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0351CertifiedArithmetic__11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:28:32.885133+00:00
-- url     : https://prove2.me/theorems/42c95921-ea8a-4b84-86a4-bae7eb0fb2c2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0351CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0352CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0351CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0352CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0353CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0354CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0355CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0356CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0357CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0358CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0359CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0360CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0361CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0351CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0352CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0353CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0354CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0355CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0356CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0357CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0358CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0359CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0360CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0361CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0351CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0352CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0353CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0354CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0355CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0356CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0357CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0358CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0359CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0360CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0361CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0351CertifiedArithmetic (+10 modules: GeneralCK/Certificates/E8TAxisProd0352CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0353CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0354CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0355CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0356CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0357CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0358CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0359CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0360CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0361CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0342GraphCenterA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0344GraphCenterB__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0347GraphCenterC__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0347GraphCenterD__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0350GraphWholeA__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0351GraphWholeB__6
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0346GraphWholeC__6
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0346GraphWholeD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0345Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0352GraphCenterA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0352GraphCenterB__5
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0352GraphWholeC__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0354GraphCenterC__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0354GraphCenterD__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0357GraphCenterB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0357GraphWholeA__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0357GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0357GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0361GraphWholeC__10

-- ===== source module GeneralCK.Certificates.E8TAxisProd0351CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0351CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0351GraphCenterA.qJetBox,
   E8TAxisProd0351GraphCenterB.qJetBox,
   E8TAxisProd0351GraphCenterC.qJetBox,
   E8TAxisProd0351GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0351GraphWholeA.qJetBox,
   E8TAxisProd0351GraphWholeB.qJetBox,
   E8TAxisProd0351GraphWholeC.qJetBox,
   E8TAxisProd0351GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨69302438773390143074291424333255830165461358982, 69302438773390143074291424333256188576695847739⟩
  | 0, 2 => ⟨193664731272657857577775971838114654429182754366, 193664731272657857577775971838116137718308685240⟩
  | 1, 1 => ⟨194362856964070128055427246035114066923723094368, 194362856964070128055427246035116805536181819547⟩
  | 0, 3 => ⟨373187979720208577453012486313307370770867413994, 373187979720208577453012486313312380502308068793⟩
  | 1, 2 => ⟨498093624778434928001989343549407254592762909483, 498093624778434928001989343549416411236656429833⟩
  | 2, 1 => ⟨499682079297317391683391347397732951507397346833, 499682079297317391683391347397749869341007935339⟩
  | 0, 4 => ⟨600821208724089614375533411847735286547240339481, 600821208724089614375533411847753137256925206887⟩
  | 1, 3 => ⟨884142916895385116684260091089412649157931060806, 884142916895385116684260091089445600592367353389⟩
  | 2, 2 => ⟨1168197974458160352363188512343364478016157443533, 1168197974458160352363188512343425940915504601445⟩
  | 3, 1 => ⟨1171523414529131209114953194500487830846388566858, 1171523414529131209114953194500603282443406662089⟩
  | 0, 5 => ⟨-3497018226359793903577464003791998295108642383393953, 3513595793646577110135519718795793937747801805224840⟩
  | 1, 4 => ⟨-6873840581084100194064719804803397257977391479754665, 6898813189719508625368779463290892538599590729218700⟩
  | 2, 3 => ⟨-13523607185387827425264783271558412577753425883126441, 13559567265561503463085874591683454422229171429021373⟩
  | 3, 2 => ⟨-26623374175516681859393611811021402181802723516634066, 26670509337547873384412574127586379821953777313748105⟩
  | 4, 1 => ⟨-52439762487681109927816872953557445388399109825702658, 52487757254955302625193976231978436309318737083427060⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0351Geometry.ds, E8TAxisProd0351Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 65356810563622077047179842846962488404791246018 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0351CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0352CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0352CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0352GraphCenterA.qJetBox,
   E8TAxisProd0352GraphCenterB.qJetBox,
   E8TAxisProd0352GraphCenterC.qJetBox,
   E8TAxisProd0352GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0352GraphWholeA.qJetBox,
   E8TAxisProd0352GraphWholeB.qJetBox,
   E8TAxisProd0352GraphWholeC.qJetBox,
   E8TAxisProd0352GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨63295592602844999974089618962720855673866902602, 63295592602844999974089618962721181608114206883⟩
  | 0, 2 => ⟨177788506730326318454874822473863060598888021302, 177788506730326318454874822473864401041257595539⟩
  | 1, 1 => ⟨178865016920014231843130050475748109416220501873, 178865016920014231843130050475750579338624777366⟩
  | 0, 3 => ⟨344710396783182762079767857090769619559507177637, 344710396783182762079767857090774130964892339524⟩
  | 1, 2 => ⟨460771070924266791171735538835442594743919607358, 460771070924266791171735538835450825018396423970⟩
  | 2, 1 => ⟨463235968625357427732517209345172551913187831155, 463235968625357427732517209345187734699870018179⟩
  | 0, 4 => ⟨557885954523784583583729770897459440794095291418, 557885954523784583583729770897475439607051468839⟩
  | 1, 3 => ⟨822255185391754764275241483936382642430573590460, 822255185391754764275241483936412129256268247507⟩
  | 2, 2 => ⟨1087768221844809628321814655165705474297188320007, 1087768221844809628321814655165760405065757011973⟩
  | 3, 1 => ⟨1092947250529975503107580703092840537674079669447, 1092947250529975503107580703092943597956610184746⟩
  | 0, 5 => ⟨-3177502496520985826983253223310399614793843828160029, 3192848537852947884085127359258176737485887968305247⟩
  | 1, 4 => ⟨-6243337431331306388608488702841427343613613136498573, 6266468040400317864522627972582808798644770457753107⟩
  | 2, 3 => ⟨-12278396691050538958948343377694978864301594543562878, 12311727395585562651801295621195371269301269971562318⟩
  | 3, 2 => ⟨-24162622382467058108197229165669814238186244821846298, 24206358275402293353226090681033050090330456106203561⟩
  | 4, 1 => ⟨-47574308233438891965493731670911234781617762330112453, 47618973289308059438165594363762746071050824491020490⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0352Geometry.ds, E8TAxisProd0352Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 59667434213277085180449443167438045494556796641 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0352CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0353CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0353CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0353GraphCenterA.qJetBox,
   E8TAxisProd0353GraphCenterB.qJetBox,
   E8TAxisProd0353GraphCenterC.qJetBox,
   E8TAxisProd0353GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0353GraphWholeA.qJetBox,
   E8TAxisProd0353GraphWholeB.qJetBox,
   E8TAxisProd0353GraphWholeC.qJetBox,
   E8TAxisProd0353GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨57158473752959091864530556017735307207538764528, 57158473752959091864530556017735601874931615191⟩
  | 0, 2 => ⟨161914116619417332458255325473107117198713579282, 161914116619417332458255325473108320733844915751⟩
  | 1, 1 => ⟨162905310537430001084911575740088960997080554863, 162905310537430001084911575740091173927199487162⟩
  | 0, 3 => ⟨316290761912719980255407962910985919533058570048, 316290761912719980255407962910989954934957412101⟩
  | 1, 2 => ⟨423161187132396867398352209880387638224070076720, 423161187132396867398352209880394985429294697038⟩
  | 2, 1 => ⟨425446468033744115191363498125877060288411177635, 425446468033744115191363498125890592007861790824⟩
  | 0, 4 => ⟨515013220613494654820838401544146492606232083210, 515013220613494654820838401544160729842941648271⟩
  | 1, 3 => ⟨760121586737436849651170247549311811090375826811, 760121586737436849651170247549338008290943943658⟩
  | 2, 2 => ⟨1006296547243833151177495350435102217565449751950, 1006296547243833151177495350435150955505050988561⟩
  | 3, 1 => ⟨1011117822918686161091284635860829758599761104382, 1011117822918686161091284635860921087697321315583⟩
  | 0, 5 => ⟨-2860326425478926761805370587181955514938387028392955, 2874410158772949200769633286581130847444324573350340⟩
  | 1, 4 => ⟨-5617690924438237537134696187074771589643831723013682, 5638924259957395502312999115192756325214124566974788⟩
  | 2, 3 => ⟨-11043251755956280063310747985818880819987497377369786, 11073855207778155938481748555315961559781316073052581⟩
  | 3, 2 => ⟨-21722708183449982060878458094881596998815521849434573, 21762871412587117385193136897506308150244925409867898⟩
  | 4, 1 => ⟨-42751959730569137708229570108342036625914603082840014, 42792980851702373664200794883997182895200993054197218⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0353Geometry.ds, E8TAxisProd0353Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 53856107859481806920711157840862907445794695966 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0353CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0354CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0354CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0354GraphCenterA.qJetBox,
   E8TAxisProd0354GraphCenterB.qJetBox,
   E8TAxisProd0354GraphCenterC.qJetBox,
   E8TAxisProd0354GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0354GraphWholeA.qJetBox,
   E8TAxisProd0354GraphWholeB.qJetBox,
   E8TAxisProd0354GraphWholeC.qJetBox,
   E8TAxisProd0354GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨63073626092908014142418211218101278276103900031, 63073626092908014142418211218101603529673136949⟩
  | 0, 2 => ⟨177358054320575800191304936069799222623159671838, 177358054320575800191304936069800560128922657485⟩
  | 1, 1 => ⟨178289695065408743364783377268924438980156279292, 178289695065408743364783377268926903449760918190⟩
  | 0, 3 => ⟨344013668469372620885076938107621701139102588311, 344013668469372620885076938107626202458211472177⟩
  | 1, 2 => ⟨459744218557398704024032599960763725974996937307, 459744218557398704024032599960771937726018941015⟩
  | 2, 1 => ⟨461877658557877488829968909523775522695698226843, 461877658557877488829968909523790671101035288933⟩
  | 0, 4 => ⟨556879626195453075340991248377956989978888643384, 556879626195453075340991248377972951465507837962⟩
  | 1, 3 => ⟨820709043478058625411885743466721737917092475543, 820709043478058625411885743466751155755362444900⟩
  | 2, 2 => ⟨1085528553368486742997499565854234238713105565481, 1085528553368486742997499565854289040559431091688⟩
  | 3, 1 => ⟨1090011460050915341556570719908687517803358595377, 1090011460050915341556570719908790335350553960824⟩
  | 0, 5 => ⟨-3170825824121561889400881552611564285135726228388100, 3186140042194349904042035067211623753667692259707491⟩
  | 1, 4 => ⟨-6230185544182132036107686578343726200361307733734042, 6253266670310855458616516093237949759066382149279960⟩
  | 2, 3 => ⟨-12252462789279188798279542945459176582054743401568703, 12285718067588467700728482443309890204126722390361493⟩
  | 3, 2 => ⟨-24111446568357014069572251389164263749821333550970924, 24155071276329342632643480642884965164327094699930133⟩
  | 4, 1 => ⟨-47473264364072428430728365245507368391545216309690081, 47517775929780229038317228177493229044853038672320244⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0354Geometry.ds, E8TAxisProd0354Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 59456779967853510999538670692415520801951321371 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0354CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0355CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0355CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0355GraphCenterA.qJetBox,
   E8TAxisProd0355GraphCenterB.qJetBox,
   E8TAxisProd0355GraphCenterC.qJetBox,
   E8TAxisProd0355GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0355GraphWholeA.qJetBox,
   E8TAxisProd0355GraphWholeB.qJetBox,
   E8TAxisProd0355GraphWholeC.qJetBox,
   E8TAxisProd0355GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨56956328041770980793458920474123565193434244116, 56956328041770980793458920474123859246121143246⟩
  | 0, 2 => ⟨161519155278088364073434955848775849989260241960, 161519155278088364073434955848777050884404773508⟩
  | 1, 1 => ⟨162376952524624321658074485622393151939193317023, 162376952524624321658074485622395359974868137780⟩
  | 0, 3 => ⟨315647578546034005354171433206116658260135810833, 315647578546034005354171433206120684624895003511⟩
  | 1, 2 => ⟨422211932332080826833643036823161811033618228140, 422211932332080826833643036823169141666801889217⟩
  | 2, 1 => ⟨424189898177452321644116023737902541514681515109, 424189898177452321644116023737916042511190901969⟩
  | 0, 4 => ⟨514080425031692693746680318807412660602967302976, 514080425031692693746680318807426864542628512675⟩
  | 1, 3 => ⟨758686504796411373912050587988239361634751607200, 758686504796411373912050587988265497374546831995⟩
  | 2, 2 => ⟨1004215843764257206591666850662342046887485778159, 1004215843764257206591666850662390670084995302611⟩
  | 3, 1 => ⟨1008389081110185445195178571812091612977534630211, 1008389081110185445195178571812182726231559476324⟩
  | 0, 5 => ⟨-2854131532166921735996098521144980876095773495137045, 2868185772567560670305394230473747303732161609953801⟩
  | 1, 4 => ⟨-5605490713331241826870343584540683752279195900721273, 5626678239006964797473097577859815531676984670603788⟩
  | 2, 3 => ⟨-11019199961894035878890257799976220438445467992866346, 11049733732457265070375110517149823162769068932966870⟩
  | 3, 2 => ⟨-21675257668455090365538665679886434274180865138759470, 21715318592374995183321595755240588526366427507656716⟩
  | 4, 1 => ⟨-42658294231891763128535636456656549135689004331513326, 42699175259131831357228631850187876183440164967171861⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0355Geometry.ds, E8TAxisProd0355Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 53664356401475916550693441518494843240128175521 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0355CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0356CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0356CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0356GraphCenterA.qJetBox,
   E8TAxisProd0356GraphCenterB.qJetBox,
   E8TAxisProd0356GraphCenterC.qJetBox,
   E8TAxisProd0356GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0356GraphWholeA.qJetBox,
   E8TAxisProd0356GraphWholeB.qJetBox,
   E8TAxisProd0356GraphWholeC.qJetBox,
   E8TAxisProd0356GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨51571125796315512009865022007523942189625925917, 51571125796315512009865022007524208704374877723⟩
  | 0, 2 => ⟨147339981132408514209626998288797205080345573945, 147339981132408514209626998288798285799829899312⟩
  | 1, 1 => ⟨148252088118171425371421743281127663903786207478, 148252088118171425371421743281129646605722882482⟩
  | 0, 3 => ⟨290023789741382862844379565694098475337512001654, 290023789741382862844379565694102084861997109676⟩
  | 1, 2 => ⟨388374636599370321108733600934723453500132795995, 388374636599370321108733600934730011735641302061⟩
  | 2, 1 => ⟨390492710905167191928480541246526245219458579570, 390492710905167191928480541246538303696490295732⟩
  | 0, 4 => ⟨475223822779487809932419273343881537215802282238, 475223822779487809932419273343894205073738661261⟩
  | 1, 3 => ⟨702402051877766937997737528453670689127670866004, 702402051877766937997737528453693959039336398757⟩
  | 2, 2 => ⟨930574977657990414197529616541680696371319281854, 930574977657990414197529616541723929359319930922⟩
  | 3, 1 => ⟨935063063861890401029183608778608224583591058725, 935063063861890401029183608778689136131848375372⟩
  | 0, 5 => ⟨-2566987484374907333880883007275102494472869166524873, 2579888981425026974587894786524745698173006161902376⟩
  | 1, 4 => ⟨-5039281565041626854027107023722059630773147167109130, 5058736212178624471636708344519919587477329345429264⟩
  | 2, 3 => ⟨-9901803924137883083763387838528472055876611124645582, 9929848569283202845778291366327326987635109838456893⟩
  | 3, 2 => ⟨-19468779032472144118537433124752317703455154912341775, 19505588530977639694889283267394678584307537473171161⟩
  | 4, 1 => ⟨-38299008263982933805532491814327103474957482608101592, 38336607634028138134374838446533072565924891730728578⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0356Geometry.ds, E8TAxisProd0356Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 48568046710260656597419392564114153776749801399 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0356CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0357CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0357CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0357GraphCenterA.qJetBox,
   E8TAxisProd0357GraphCenterB.qJetBox,
   E8TAxisProd0357GraphCenterC.qJetBox,
   E8TAxisProd0357GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0357GraphWholeA.qJetBox,
   E8TAxisProd0357GraphWholeB.qJetBox,
   E8TAxisProd0357GraphWholeC.qJetBox,
   E8TAxisProd0357GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨46488384270478932710182850009442219330123802075, 46488384270478932710182850009442460489837644954⟩
  | 0, 2 => ⟨133968262781083900346242689927436794937878574480, 133968262781083900346242689927437765475666678286⟩
  | 1, 1 => ⟨134807081678674785620401572711369154886371544783, 134807081678674785620401572711370931332229306049⟩
  | 0, 3 => ⟨265756409968560604567978295918884432484856115798, 265756409968560604567978295918887660986017032167⟩
  | 1, 2 => ⟨356212003171246525419064191710409068737154460306, 356212003171246525419064191710414922115164327592⟩
  | 2, 1 => ⟨358174428689460896023654541096195852477655273178, 358174428689460896023654541096206596500423535853⟩
  | 0, 4 => ⟨438303278745484660189856184431305771562277824628, 438303278745484660189856184431317041408307471293⟩
  | 1, 3 => ⟨648790709716392284867623581170970214969559720684, 648790709716392284867623581170990880361835530555⟩
  | 2, 2 => ⟨860205883789518003042205655725551787290810540797, 860205883789518003042205655725590127563270036906⟩
  | 3, 1 => ⟨864383672671836000260255826423287120861443669531, 864383672671836000260255826423358783054403834796⟩
  | 0, 5 => ⟨-2298387433612242771228552704110628332638871909119982, 2310203029887202338403157217374633389249181428790700⟩
  | 1, 4 => ⟨-4509848658802818047321076126239050253873257152470572, 4527669934164632088178181235720647225096576933116282⟩
  | 2, 3 => ⟨-8857398729828199305656683300955101014308178894219008, 8883094497149732082801305043406762882454056503968277⟩
  | 3, 2 => ⟨-17407254844415112909044981190298482766386988515566558, 17440987903058650078518506819437921539618245704340512⟩
  | 4, 1 => ⟨-34227745347250814949982420286031972721179059368040452, 34262211977976894380927474547132270982014558969197021⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0357Geometry.ds, E8TAxisProd0357Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 43759890527968755948416353655119584536636870137 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0357CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0358CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0358CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0358GraphCenterA.qJetBox,
   E8TAxisProd0358GraphCenterB.qJetBox,
   E8TAxisProd0358GraphCenterC.qJetBox,
   E8TAxisProd0358GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0358GraphWholeA.qJetBox,
   E8TAxisProd0358GraphWholeB.qJetBox,
   E8TAxisProd0358GraphWholeC.qJetBox,
   E8TAxisProd0358GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨51387177246360862704959630154932943616235019361, 51387177246360862704959630154933209575678025807⟩
  | 0, 2 => ⟨146977822438643913889440116579773709007107607191, 146977822438643913889440116579774787353012909784⟩
  | 1, 1 => ⟨147767168227069009783031151424799459340111753540, 147767168227069009783031151424801437648598538388⟩
  | 0, 3 => ⟨289430300366315695715137480540302694568519818056, 289430300366315695715137480540306295995804941906⟩
  | 1, 2 => ⟨387497466610010843999234602957156065562723813567, 387497466610010843999234602957162608972700202659⟩
  | 2, 1 => ⟨389330700509070979014008389574914782152082096532, 389330700509070979014008389574926813177499110058⟩
  | 0, 4 => ⟨474359417919703381854245873326091467105929923245, 474359417919703381854245873326104105263468038522⟩
  | 1, 3 => ⟨701070313338242967506217739784062947164994185039, 701070313338242967506217739784086162328142749188⟩
  | 2, 2 => ⟨928642233840315025182510137650244707750614117812, 928642233840315025182510137650287838632472725073⟩
  | 3, 1 => ⟨932527064243616885861670287113555638115513308588, 932527064243616885861670287113636357766178527004⟩
  | 0, 5 => ⟨-2561286269453287275958564308205412217909799553696668, 2574160460799722622284193041220738341760276816368248⟩
  | 1, 4 => ⟨-5028057213896141884046695437541012023503515268669579, 5047469471018108500100695859612350805775038150428175⟩
  | 2, 3 => ⟨-9879683181982324366444386830904582899844172341073712, 9907663447392403088351277235134489150086185290853648⟩
  | 3, 2 => ⟨-19425152606393452471748826777646484527907529843857617, 19461867901184804143814464476268238155956813503142397⟩
  | 4, 1 => ⟨-38212920159282130862040912898311837598415596764064983, 38250391456908263698692093378717300849773517105210588⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0358Geometry.ds, E8TAxisProd0358Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 48393639752777494092481169058519429083721811426 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0358CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0359CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0359CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0359GraphCenterA.qJetBox,
   E8TAxisProd0359GraphCenterB.qJetBox,
   E8TAxisProd0359GraphCenterC.qJetBox,
   E8TAxisProd0359GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0359GraphWholeA.qJetBox,
   E8TAxisProd0359GraphWholeB.qJetBox,
   E8TAxisProd0359GraphWholeC.qJetBox,
   E8TAxisProd0359GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨46321131421586220142324622717262342483088598165, 46321131421586220142324622717262583140991967155⟩
  | 0, 2 => ⟨133636409484427840144620612837157238288549262099, 133636409484427840144620612837158206692063170146⟩
  | 1, 1 => ⟨134362323220544939906037801071852592430588914807, 134362323220544939906037801071854364932569597912⟩
  | 0, 3 => ⟨265209031516793413240544045757197149891016020418, 265209031516793413240544045757200371137127657510⟩
  | 1, 2 => ⟨355401787251632278117183223560199279493461922565, 355401787251632278117183223560205119609092211751⟩
  | 2, 1 => ⟨357100293574854802715537733087654851790964379976, 357100293574854802715537733087665571287315718750⟩
  | 0, 4 => ⟨437502467553915827401648655232486676541939145969, 437502467553915827401648655232497919898807950468⟩
  | 1, 3 => ⟨647555117055732447265513387324939529196694232367, 647555117055732447265513387324960145827838153419⟩
  | 2, 2 => ⟨858410837040620969922982414008331964555779346234, 858410837040620969922982414008370213984644287821⟩
  | 3, 1 => ⟨862027075983331762597110149431225039372139242042, 862027075983331762597110149431296530995300928307⟩
  | 0, 5 => ⟨-2293327918681185049543067513401772290071976690731903, 2305119617008935338657374741786073882466419850623542⟩
  | 1, 4 => ⟨-4499891516350081628930015013793614946710439030426520, 4517675782674405223697573098898407833135935496459000⟩
  | 2, 3 => ⟨-8837782368417692313584730000408562120051578319802218, 8863422006186150156744172763185468547915811867192010⟩
  | 3, 2 => ⟨-17368580569113020880045462981216661450289397879000252, 17402231452737337226669006016427651250928765397713227⟩
  | 4, 1 => ⟨-34151453954685699715412866599047184890529592604176238, 34185808409685464689937369032862396559866694680449273⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0359Geometry.ds, E8TAxisProd0359Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 43601377841591261586104701680567818321314913777 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0359CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0360CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0360CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0360GraphCenterA.qJetBox,
   E8TAxisProd0360GraphCenterB.qJetBox,
   E8TAxisProd0360GraphCenterC.qJetBox,
   E8TAxisProd0360GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0360GraphWholeA.qJetBox,
   E8TAxisProd0360GraphWholeB.qJetBox,
   E8TAxisProd0360GraphWholeC.qJetBox,
   E8TAxisProd0360GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨62852197104491666125797425957123558960713238426, 62852197104491666125797425957123883535016260696⟩
  | 0, 2 => ⟨176928472035458719590877137289970200653349592830, 176928472035458719590877137289971535228817071948⟩
  | 1, 1 => ⟨177715655569028632203068978745438512694465569838, 177715655569028632203068978745440971723014501236⟩
  | 0, 3 => ⟨343318197021670848225165076738748898841815815011, 343318197021670848225165076738753390096912389528⟩
  | 1, 2 => ⟨458719297211754481218794252485382381733748455766, 458719297211754481218794252485390575002247339702⟩
  | 2, 1 => ⟨460522145575210385549402894833273243724355204200, 460522145575210385549402894833288357824377579566⟩
  | 0, 4 => ⟨555874968323113909822056366923927521959462643811, 555874968323113909822056366923943446205257291599⟩
  | 1, 3 => ⟨819165550725762428464131699128592815221921880719, 819165550725762428464131699128622164230771935098⟩
  | 2, 2 => ⟨1083292885034485219120207407105343649684393826593, 1083292885034485219120207407105398322903617064380⟩
  | 3, 1 => ⟨1087081394225415654765076008201376064914674923711, 1087081394225415654765076008201478640282057247016⟩
  | 0, 5 => ⟨-3164159487528335567758187918675851531822726133120877, 3179441943162372610088179034763915474793804504835181⟩
  | 1, 4 => ⟨-6217054010558706709088932718931503067179364610668684, 6240085751865959560051347887446922492450402190717759⟩
  | 2, 3 => ⟨-12226569026856259033827756392759668829351931623882466, 12259749037213110128192413251228996470898233075112414⟩
  | 3, 2 => ⟨-24060349991127039152922958482553189189440342570498968, 24103863770077452324840385009026742944457917711411000⟩
  | 4, 1 => ⟨-47372377024788844284663859929538226042203917232122564, 47416735515579511739089209318407898887238860606952247⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0360Geometry.ds, E8TAxisProd0360Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 59246638447261919427983519337499887408411927441 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0360CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0361CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0361CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0361GraphCenterA.qJetBox,
   E8TAxisProd0361GraphCenterB.qJetBox,
   E8TAxisProd0361GraphCenterC.qJetBox,
   E8TAxisProd0361GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0361GraphWholeA.qJetBox,
   E8TAxisProd0361GraphWholeB.qJetBox,
   E8TAxisProd0361GraphWholeC.qJetBox,
   E8TAxisProd0361GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨56754675530076043704215706278337243877464015066, 56754675530076043704215706278337537316718678794⟩
  | 0, 2 => ⟨161124997187625654871184199379578390940724696933, 161124997187625654871184199379579589201559063041⟩
  | 1, 1 => ⟨161849779959803244324446697174966826447893759397, 161849779959803244324446697174969029599675828316⟩
  | 0, 3 => ⟨315005560203269804940291119969651571292745030808, 315005560203269804940291119969655588640332724617⟩
  | 1, 2 => ⟨421264469843661157080742545775541614778509220206, 421264469843661157080742545775548928876320884697⟩
  | 2, 1 => ⟨422935926873275372776540809020051556748542160612, 422935926873275372776540809020065027090164171240⟩
  | 0, 4 => ⟨513149181940264894739135807594633072175926408178, 513149181940264894739135807594647242894946825775⟩
  | 1, 3 => ⟨757253887042816733566721178616500287199860006252, 757253887042816733566721178616526361619913246593⟩
  | 2, 2 => ⟨1002138862824438735746372445117292889728147254693, 1002138862824438735746372445117341398446793292407⟩
  | 3, 1 => ⟨1005665668012440532365385362802323424943274128241, 1005665668012440532365385362802414322848889270277⟩
  | 0, 5 => ⟨-2847946597355840989335944862303480288445094602195948, 2861971402501078683457873455709589126698662407323359⟩
  | 1, 4 => ⟨-5593310115801194299379398100839667761292130269891066, 5614451924894433393412705993501625746563903100309324⟩
  | 2, 3 => ⟨-10995186851923700188437035071962056181219553371718276, 11025651092180993264065292912161531536699780316523762⟩
  | 3, 2 => ⟨-21627883523047523346390257590606586603099696480569415, 21667842386764844731294117481023543977966693244015718⟩
  | 4, 1 => ⟨-42564779606614867165832729606370373909305392851181683, 42605520939036894958810086669503894823163531135100335⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0361Geometry.ds, E8TAxisProd0361Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 53473075189891763750796083709181013327021459447 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0361CertifiedArithmetic

end


