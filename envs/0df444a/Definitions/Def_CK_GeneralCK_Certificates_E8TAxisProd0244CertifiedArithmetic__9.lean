-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0244CertifiedArithmetic__9
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0244CertifiedArithmetic__9
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T20:15:30.00733+00:00
-- url     : https://prove2.me/theorems/9c658c43-a728-4268-952b-a6bece9df987
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0244CertifiedArithmetic (+8 modules: GeneralCK.Certificates.E8TAxisProd0245CertifiedArithmetic, GeneralCK.Certificates.E8TAx…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0244CertifiedArithmetic (+8 modules: GeneralCK.Certificates.E8TAxisProd0245CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0246CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0247CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0248CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0249CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0250CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0251CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0252CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0244CertifiedArithmetic (+8 modules: GeneralCK.Certificates.E8TAxisProd0245CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0246CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0247CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0248CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0249CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0250CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0251CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0252CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0244CertifiedArithmetic (+8 modules: GeneralCK.Certificates.E8TAxisProd0245CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0246CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0247CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0248CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0249CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0250CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0251CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0252CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0244CertifiedArithmetic (+8 modules: GeneralCK/Certificates/E8TAxisProd0245CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0246CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0247CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0248CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0249CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0250CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0251CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0252CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0241GraphCenterA__4
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0242GraphCenterB__5
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0238GraphCenterC__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0241GraphCenterD__6
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0242GraphWholeA__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0238GraphWholeB__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0242GraphWholeC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0238GraphWholeD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0234Geometry__23
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0245GraphCenterA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0245GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0246GraphCenterC__6
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0246GraphWholeD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0247GraphCenterB__5
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0247GraphCenterD__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0249GraphWholeA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0252GraphCenterB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0252GraphCenterC__9

-- ===== source module GeneralCK.Certificates.E8TAxisProd0244CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0244CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0244GraphCenterA.qJetBox,
   E8TAxisProd0244GraphCenterB.qJetBox,
   E8TAxisProd0244GraphCenterC.qJetBox,
   E8TAxisProd0244GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0244GraphWholeA.qJetBox,
   E8TAxisProd0244GraphWholeB.qJetBox,
   E8TAxisProd0244GraphWholeC.qJetBox,
   E8TAxisProd0244GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨78492856264956759157174817439518933527115608092, 78492856264956759157174817439519336150073153179⟩
  | 0, 2 => ⟨215918679207779276476458217207505455830365392482, 215918679207779276476458217207507133679931884323⟩
  | 1, 1 => ⟨217873523850459926030584866341154125680643292660, 217873523850459926030584866341157229948282343295⟩
  | 0, 3 => ⟨411958505175036348466820056051774129703057410038, 411958505175036348466820056051779818316574786168⟩
  | 1, 2 => ⟨550157067203012318233045483977480298018355793527, 550157067203012318233045483977490715861526668413⟩
  | 2, 1 => ⟨554573174282740196667446280587530566316181454405, 554573174282740196667446280587549845740566005494⟩
  | 0, 4 => ⟨658518184695479747539966720772294390910963463539, 658518184695479747539966720772314774515807297985⟩
  | 1, 3 => ⟨968305274994001309229434948440474827895663450971, 968305274994001309229434948440512513781329263218⟩
  | 2, 2 => ⟨1280119755503084431543719676512165170208077878860, 1280119755503084431543719676512235555391771477454⟩
  | 3, 1 => ⟨1289327851373777396162326419766911436954217265763, 1289327851373777396162326419767043809704330615285⟩
  | 0, 5 => ⟨-3916931660140600143320389490411685768092187422912700, 3935147815215408486874422457575616395637129235887340⟩
  | 1, 4 => ⟨-7702444888285080889844563076167842642399998981281933, 7729883104084079365249108054053220309546382953698413⟩
  | 2, 3 => ⟨-15160113440806879339663632588476015556554498296606934, 15199640006330137395383006543881830840709974988171433⟩
  | 3, 2 => ⟨-29857604681006875693852940343173743712751302046409375, 29909499713773248399313810071867819248692175797333758⟩
  | 4, 1 => ⟨-58835079151309050489003054253087015760442868525594898, 58888239802013823794713402394133427877379511753457797⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0244Geometry.ds, E8TAxisProd0244Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 74071471182897406928530694957496178110861362784 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0244CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0245CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0245CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0245GraphCenterA.qJetBox,
   E8TAxisProd0245GraphCenterB.qJetBox,
   E8TAxisProd0245GraphCenterC.qJetBox,
   E8TAxisProd0245GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0245GraphWholeA.qJetBox,
   E8TAxisProd0245GraphWholeB.qJetBox,
   E8TAxisProd0245GraphWholeC.qJetBox,
   E8TAxisProd0245GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨71011358569942056572542781984559194841711240117, 71011358569942056572542781984559558541740181122⟩
  | 0, 2 => ⟨196953223110445328923937108000093797801721983579, 196953223110445328923937108000095304008651824959⟩
  | 1, 1 => ⟨198755170851325181500643737379388647508046722624, 198755170851325181500643737379391428738663553141⟩
  | 0, 3 => ⟨378478395723973589208217143852582605973783087705, 378478395723973589208217143852587694681670966894⟩
  | 1, 2 => ⟨505880866029664763773456230476681688363682755643, 505880866029664763773456230476690990256631621035⟩
  | 2, 1 => ⟨509977609367977028903471153586659662162763951915, 509977609367977028903471153586676849903407628144⟩
  | 0, 4 => ⟨608431443181397064237937471116327539247036650545, 608431443181397064237937471116345683512222786274⟩
  | 1, 3 => ⟨895821249769408959690219030999699241121098017441, 895821249769408959690219030999732735790481240797⟩
  | 2, 2 => ⟨1185101226549750555142925274698230663286872543872, 1185101226549750555142925274698293142356580509855⟩
  | 3, 1 => ⟨1193673925903480076479713039702602455009357683379, 1193673925903480076479713039702719821525953889550⟩
  | 0, 5 => ⟨-3547451080727945985829236765680803632558773870060815, 3564266013225156240540885013650274239896820796446840⟩
  | 1, 4 => ⟨-6973203028331905499835882163876300834904175831021131, 6998544839018629069819312436573230675009844547392913⟩
  | 2, 3 => ⟨-13719576587005117599576020086595675480899835321004138, 13756100258707454577625238762877372749527242703179752⟩
  | 3, 2 => ⟨-27010164007652936274895785408737341956153878274788232, 27058133137848800280152289349147014125764999290013928⟩
  | 4, 1 => ⟨-53203620912669188055038693066155536433172114707589391, 53252777151141542345709544404889599398797052582857316⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0245Geometry.ds, E8TAxisProd0245Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 66979413372924068900173503507016027089340587262 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0245CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0246CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0246CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0246GraphCenterA.qJetBox,
   E8TAxisProd0246GraphCenterB.qJetBox,
   E8TAxisProd0246GraphCenterC.qJetBox,
   E8TAxisProd0246GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0246GraphWholeA.qJetBox,
   E8TAxisProd0246GraphWholeB.qJetBox,
   E8TAxisProd0246GraphWholeC.qJetBox,
   E8TAxisProd0246GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨78223279544263734387255500918790456209133813893, 78223279544263734387255500918790857989707740530⟩
  | 0, 2 => ⟨215404245236724971953429472760061958089759942869, 215404245236724971953429472760063632273171513213⟩
  | 1, 1 => ⟨217186583534451756771733567556305901262646285646, 217186583534451756771733567556308998702846083122⟩
  | 0, 3 => ⟨411136093944343186299034044365725846068598111962, 411136093944343186299034044365731522005438293014⟩
  | 1, 2 => ⟨548947814649923974841859737974793148650927823696, 548947814649923974841859737974803543147325292286⟩
  | 2, 1 => ⟨552974657809915820773581433966920235642584149177, 552974657809915820773581433966939471634405124506⟩
  | 0, 4 => ⟨657340108683017056658018762777846542650139723205, 657340108683017056658018762777866878920959079268⟩
  | 1, 3 => ⟨966499323557914120079444002025186142048035175784, 966499323557914120079444002025223740234179411948⟩
  | 2, 2 => ⟨1277507376154078019657054036775730970906072030298, 1277507376154078019657054036775801191884842972934⟩
  | 3, 1 => ⟨1285904316971062792172312370516799907731418641607, 1285904316971062792172312370516931970782386451345⟩
  | 0, 5 => ⟨-3909131297909978875388646327040709712336386345392243, 3927311423027119547253956666436125771750048098104077⟩
  | 1, 4 => ⟨-7687073610364185590531701093350977021624388120567841, 7714455827286313797351261639057050088989595905918214⟩
  | 2, 3 => ⟨-15129790744801517588920021844228356391383928773890043, 15169231800103986255188662295877010638354814516439170⟩
  | 3, 2 => ⟨-29797742858331198889125101177464174303662606118385787, 29849511042111635518230400390689508345283021565283418⟩
  | 4, 1 => ⟨-58716833396512755474320291485636987241176556210536862, 58769816159100105189328197067713339593221712335825085⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0246Geometry.ds, E8TAxisProd0246Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 73815386445987353097008095851204899826594661918 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0246CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0247CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0247CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0247GraphCenterA.qJetBox,
   E8TAxisProd0247GraphCenterB.qJetBox,
   E8TAxisProd0247GraphCenterC.qJetBox,
   E8TAxisProd0247GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0247GraphWholeA.qJetBox,
   E8TAxisProd0247GraphWholeB.qJetBox,
   E8TAxisProd0247GraphWholeC.qJetBox,
   E8TAxisProd0247GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨70765462529332507927358681750814092711132457311, 70765462529332507927358681750814455650900060094⟩
  | 0, 2 => ⟨196480600168209880645545182157787745153129673407, 196480600168209880645545182157789248064928938848⟩
  | 1, 1 => ⟨198123519192258163619420371911806537107071680036, 198123519192258163619420371911809312209964693330⟩
  | 0, 3 => ⟨377718539474869346541896914422202424004226776529, 377718539474869346541896914422207501354903808722⟩
  | 1, 2 => ⟨504762137833225800844298767649263258317115681115, 504762137833225800844298767649272539322418693344⟩
  | 2, 1 => ⟨508497750594085564580491751215072981972720085834, 508497750594085564580491751215090130899078454374⟩
  | 0, 4 => ⟨607338856931980065893317603945767086303326263561, 607338856931980065893317603945785188343381826486⟩
  | 1, 3 => ⟨894144342515682482747325999524252538249827704299, 894144342515682482747325999524285954780359804734⟩
  | 2, 2 => ⟨1182673533315935645956191350774710593166458600392, 1182673533315935645956191350774772926071015840204⟩
  | 3, 1 => ⟨1190491044857471446620385285889019700086634073901, 1190491044857471446620385285889136791163718005350⟩
  | 0, 5 => ⟨-3540213982569105925755187019204113967902041106574740, 3556994844406458303786654662164508974793275788961507⟩
  | 1, 4 => ⟨-6958944620134140336543575592040498207899712747285738, 6984233410108001461121265100169564794351730165387894⟩
  | 2, 3 => ⟨-13691455223622348093425541789580514813063101172102071, 13727897926498318969024970569623516639811898825013071⟩
  | 3, 2 => ⟨-26954660142407639715690300914700348823788621701514918, 27002509399515140340452742952297064973046814553599926⟩
  | 4, 1 => ⟨-53094008071071379262736816888227564148833990280397954, 53142997195316727210880293590089259149406106196513344⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0247Geometry.ds, E8TAxisProd0247Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 66745929025750449775617300410072032508980006483 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0247CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0248CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0248CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0248GraphCenterA.qJetBox,
   E8TAxisProd0248GraphCenterB.qJetBox,
   E8TAxisProd0248GraphCenterC.qJetBox,
   E8TAxisProd0248GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0248GraphWholeA.qJetBox,
   E8TAxisProd0248GraphWholeB.qJetBox,
   E8TAxisProd0248GraphWholeC.qJetBox,
   E8TAxisProd0248GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨95022093652498680144256655254787542249788323494, 95022093652498680144256655254788034157016082965⟩
  | 0, 2 => ⟨257728116226541556087571963458272375115026011314, 257728116226541556087571963458274448673207292351⟩
  | 1, 1 => ⟨259620521955744261732634765969655437798801960916, 259620521955744261732634765969659288362751217692⟩
  | 0, 3 => ⟨485309096703058625536542749767150415498440739386, 485309096703058625536542749767157492520916829540⟩
  | 1, 2 => ⟨646783055596239974288326262543592954509341846304, 646783055596239974288326262543605960688845347378⟩
  | 2, 1 => ⟨651007904771503994192330910420519256606601590718, 651007904771503994192330910420543397033797342078⟩
  | 0, 4 => ⟨767788106479539831690961845209239013326052623716, 767788106479539831690961845209264611239710233388⟩
  | 1, 3 => ⟨1126021204726131277728865443269741928662289505151, 1126021204726131277728865443269789391884280919712⟩
  | 2, 2 => ⟨1486176843944902235041524527829524333287449122073, 1486176843944902235041524527829613192289613069669⟩
  | 3, 1 => ⟨1494929926241846403396591577502534824463131252231, 1494929926241846403396591577502702316911602782139⟩
  | 0, 5 => ⟨-4714966176734900972896552297444348453276442490253694, 4736139689667796574092322470408526201401073292403132⟩
  | 1, 4 => ⟨-9278165421740193526700746165704459592849654573088947, 9310006785580542033507297675981984255267390552607670⟩
  | 2, 3 => ⟨-18274123346604377962498657550344898951323219701996617, 18319925372116161895228219944501974221487017484132857⟩
  | 3, 2 => ⟨-36015704819964088092586970240537213874247764736269483, 36075750000459548222388568174925100119689865629620459⟩
  | 4, 1 => ⟨-71019842188869352451388197967669582956386463510553445, 71081182211630255111189684810180731901175296282324378⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0248Geometry.ds, E8TAxisProd0248Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 89750759835748299694831455399353726331245936425 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0248CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0249CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0249CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0249GraphCenterA.qJetBox,
   E8TAxisProd0249GraphCenterB.qJetBox,
   E8TAxisProd0249GraphCenterC.qJetBox,
   E8TAxisProd0249GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0249GraphWholeA.qJetBox,
   E8TAxisProd0249GraphWholeB.qJetBox,
   E8TAxisProd0249GraphWholeC.qJetBox,
   E8TAxisProd0249GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨86101024175638365357933633944222293715519853246, 86101024175638365357933633944222737733326458994⟩
  | 0, 2 => ⟨235420057784219920530644273409959184267283523691, 235420057784219920530644273409961045344775154154⟩
  | 1, 1 => ⟨237166153167288878391936974148259478087023182473, 237166153167288878391936974148262927781376316459⟩
  | 0, 3 => ⟨446363350560136767065147952331240131891206272758, 446363350560136767065147952331246462763270937952⟩
  | 1, 2 => ⟨595364559071150754930720442056107591593585133046, 595364559071150754930720442056119206239647299996⟩
  | 2, 1 => ⟨599285811629328705237593943193657251064331055832, 599285811629328705237593943193678777136466481914⟩
  | 0, 4 => ⟨709916115509977777768186922679973678041298028319, 709916115509977777768186922679996468814066642838⟩
  | 1, 3 => ⟨1042411801812377393168844350721539260697587613874, 1042411801812377393168844350721581458767687594848⟩
  | 2, 2 => ⟨1376699635093375699284577870510094575899606043544, 1376699635093375699284577870510173483760382971176⟩
  | 3, 1 => ⟨1384849470341670992745796696315826568028639422155, 1384849470341670992745796696315975137172004070554⟩
  | 0, 5 => ⟨-4295253063609779523646605041404761565483588927736808, 4314869145127688931417396701511690479985378878386156⟩
  | 1, 4 => ⟨-8449380893076334007874944316635034631475746940125390, 8478904100729482096860608393056954486288472898002579⟩
  | 2, 3 => ⟨-16636100238525754110087359477824620942820967706605203, 16678596046229851813423092374029662730898760090564260⟩
  | 3, 2 => ⟨-32776126585590210402447556680419633562399896397922132, 32831865019708379742634553381518320960216037476749424⟩
  | 4, 1 => ⟨-64609170412422529774266441826781727972753212315162731, 64666139523069090014513871702710383138125371548354920⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0249Geometry.ds, E8TAxisProd0249Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 81286040413032874951788872677397474405731163178 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0249CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0250CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0250CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0250GraphCenterA.qJetBox,
   E8TAxisProd0250GraphCenterB.qJetBox,
   E8TAxisProd0250GraphCenterC.qJetBox,
   E8TAxisProd0250GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0250GraphWholeA.qJetBox,
   E8TAxisProd0250GraphWholeB.qJetBox,
   E8TAxisProd0250GraphWholeC.qJetBox,
   E8TAxisProd0250GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨94700312405127343827896967157937259269321340427, 94700312405127343827896967157937750145733766187⟩
  | 0, 2 => ⟨257122079334740162554916166622299016955378006619, 257122079334740162554916166622301085993209275207⟩
  | 1, 1 => ⟨258812922296783217248199349756224738922523840644, 258812922296783217248199349756228581045523956568⟩
  | 0, 3 => ⟨484350214367025152711063667675747308388715265182, 484350214367025152711063667675754369687824614086⟩
  | 1, 2 => ⟨645376833382341144959484253019336014310580934031, 645376833382341144959484253019348991455759256922⟩
  | 2, 1 => ⟨649152067352018786582796803541279464621149015023, 649152067352018786582796803541303550919200751914⟩
  | 0, 4 => ⟨766424004723072610850010668843852693838669394504, 766424004723072610850010668843878232569447876577⟩
  | 1, 3 => ⟨1123934928264837353496673814555260969867634001338, 1123934928264837353496673814555308323183637875247⟩
  | 2, 2 => ⟨1483163918099134587091407026563076768979889315797, 1483163918099134587091407026563165421823992050681⟩
  | 3, 1 => ⟨1490985902224231652573007656283555594959482440687, 1490985902224231652573007656283722697942430451603⟩
  | 0, 5 => ⟨-4706088536322110794735830261886444144364867363550737, 4727221334396300347030590425727688152728198298981743⟩
  | 1, 4 => ⟨-9260666457480079224610680465492936811835062083377018, 9292444839063140765414245969598990072415784003260446⟩
  | 2, 3 => ⟨-18239592664788489545911433719609996649030088872599047, 18285298846308516778417319094559240810068168746441417⟩
  | 3, 2 => ⟨-35947512916537769007128949872877571762636238415910470, 36007416121361236353137604223866839579690953009706998⟩
  | 4, 1 => ⟨-70885094293270861116278594220970891535933152805805664, 70946234819171688395283224881603425332885611592516078⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0250Geometry.ds, E8TAxisProd0250Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 89444817198544312649859576427391308416508326108 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0250CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0251CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0251CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0251GraphCenterA.qJetBox,
   E8TAxisProd0251GraphCenterB.qJetBox,
   E8TAxisProd0251GraphCenterC.qJetBox,
   E8TAxisProd0251GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0251GraphWholeA.qJetBox,
   E8TAxisProd0251GraphWholeB.qJetBox,
   E8TAxisProd0251GraphWholeC.qJetBox,
   E8TAxisProd0251GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨85807097593786287986552432842907660620511185146, 85807097593786287986552432842908103708542056320⟩
  | 0, 2 => ⟨234862657888226743153932506217183597832471222454, 234862657888226743153932506217185454848031785185⟩
  | 1, 1 => ⟨236422761347783927992654542510926964307758931423, 236422761347783927992654542510930406427241119492⟩
  | 0, 3 => ⟨445476746726919222401622721052076866870117308886, 445476746726919222401622721052083183655401341443⟩
  | 1, 2 => ⟨594062755873804327317384397758084129914782732510, 594062755873804327317384397758095718582309355807⟩
  | 2, 1 => ⟨597566688060239694446133485142727932720414067946, 597566688060239694446133485142749410411538890438⟩
  | 0, 4 => ⟨708650365190629466193634523210355626186462174226, 708650365190629466193634523210378364150565767662⟩
  | 1, 3 => ⟨1040473863959695790572327002167954513190397929857, 1040473863959695790572327002167996613302815448147⟩
  | 2, 2 => ⟨1373898905146726111378376640865139473336867523080, 1373898905146726111378376640865218197616312861868⟩
  | 3, 1 => ⟨1381181805257811161072485803740955572556595955985, 1381181805257811161072485803741103795166756210381⟩
  | 0, 5 => ⟨-4286933350808278532547315475943043779303625486916513, 4306511065129682555432153618389078327691523025236939⟩
  | 1, 4 => ⟨-8432983761713710844459921237111018559648033220364220, 8462447483077575874100807132908882498021872405292244⟩
  | 2, 3 => ⟨-16603748524177079044233189277765155995419445549463547, 16646153643590850132395493421593547014416003652180246⟩
  | 3, 2 => ⟨-32712247890719944502824945080451885355104025865506753, 32767851850206676086274093521353377503058593650203603⟩
  | 4, 1 => ⟨-64482966701904683045422544729014021173794202460737660, 64539746923582661318972863058277635846027284203947458⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0251Geometry.ds, E8TAxisProd0251Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 81006704921499678830172245496529855275502695034 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0251CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0252CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0252CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0252GraphCenterA.qJetBox,
   E8TAxisProd0252GraphCenterB.qJetBox,
   E8TAxisProd0252GraphCenterC.qJetBox,
   E8TAxisProd0252GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0252GraphWholeA.qJetBox,
   E8TAxisProd0252GraphWholeB.qJetBox,
   E8TAxisProd0252GraphWholeC.qJetBox,
   E8TAxisProd0252GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨77954345223909083517835136632037507174630856588, 77954345223909083517835136632037908114571940618⟩
  | 0, 2 => ⟨214890838359843627117135103885510125399951744075, 214890838359843627117135103885511795925080149408⟩
  | 1, 1 => ⟨216501153374037585647181144637989933417254977102, 216501153374037585647181144637993024044694917771⟩
  | 0, 3 => ⟨410315154093272865148400647573724802619260409171, 410315154093272865148400647573730465907354377707⟩
  | 1, 2 => ⟨547740817611113023892010763388000189729785094924, 547740817611113023892010763388010560930870445333⟩
  | 2, 1 => ⟨551379403906111667342754929818147626853125720425, 551379403906111667342754929818166819508128185487⟩
  | 0, 4 => ⟨656163976804948358339864385767773737116848399001, 656163976804948358339864385767794026161738189884⟩
  | 1, 3 => ⟨964696451332888076130368318987451296894262052578, 964696451332888076130368318987488807581020203467⟩
  | 2, 2 => ⟨1274899643789465105317222663177616638577098330085, 1274899643789465105317222663177686695725342650954⟩
  | 3, 1 => ⟨1282487432388794159430758566767817006091670874638, 1282487432388794159430758566767948760149081736462⟩
  | 0, 5 => ⟨-3901342311489481780840863220232847485969898273668177, 3919486466247391755098281775936689042146997729597803⟩
  | 1, 4 => ⟨-7671724729572794675097410803267456233781212226044477, 7699051039763573297127757182888382410852664315621012⟩
  | 2, 3 => ⟨-15099512211680826609389507987008217966094597140656144, 15138867900043114066124919481611216934033438180261080⟩
  | 3, 2 => ⟨-29737968203827459704620302513084621830661885901103270, 29789609763225563857493297733188291924315727284790748⟩
  | 4, 1 => ⟨-58598759818561267876307124847129409516351652109682283, 58651565048391897466807053519645705060087815412055398⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0252Geometry.ds, E8TAxisProd0252Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 73559914968985830229473321020142158361029753408 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0252CertifiedArithmetic

end


