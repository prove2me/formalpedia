-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0212CertifiedArithmetic__8
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0212CertifiedArithmetic__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T16:27:13.155079+00:00
-- url     : https://prove2.me/theorems/0d89d64f-1759-457e-91df-38a397627812
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0212CertifiedArithmetic (+7 modules: GeneralCK.Certificates.E8TAxisProd0213CertifiedArithmetic, GeneralCK.Certificates.E8TAx…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0212CertifiedArithmetic (+7 modules: GeneralCK.Certificates.E8TAxisProd0213CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0214CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0215CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0216CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0217CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0218CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0219CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0212CertifiedArithmetic (+7 modules: GeneralCK.Certificates.E8TAxisProd0213CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0214CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0215CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0216CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0217CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0218CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0219CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0212CertifiedArithmetic (+7 modules: GeneralCK.Certificates.E8TAxisProd0213CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0214CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0215CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0216CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0217CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0218CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0219CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0212CertifiedArithmetic (+7 modules: GeneralCK/Certificates/E8TAxisProd0213CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0214CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0215CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0216CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0217CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0218CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0219CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0211GraphCenterA__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0212GraphCenterB__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0212GraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0210GraphCenterD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0210GraphWholeA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0209GraphWholeB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0212GraphWholeC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0208GraphWholeD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0201Geometry__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0216Geometry__18
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0218GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0219GraphWholeB__11

-- ===== source module GeneralCK.Certificates.E8TAxisProd0212CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0212CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0212GraphCenterA.qJetBox,
   E8TAxisProd0212GraphCenterB.qJetBox,
   E8TAxisProd0212GraphCenterC.qJetBox,
   E8TAxisProd0212GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0212GraphWholeA.qJetBox,
   E8TAxisProd0212GraphWholeB.qJetBox,
   E8TAxisProd0212GraphWholeC.qJetBox,
   E8TAxisProd0212GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨79577612886035198236621616484404622692407464245, 79577612886035198236621616484405028702480930426⟩
  | 0, 2 => ⟨217986722894272228034513630216435295210565032755, 217986722894272228034513630216436987803808108975⟩
  | 1, 1 => ⟨220636443178757864539025526505664649940037312231, 220636443178757864539025526505667781664858594301⟩
  | 0, 3 => ⟨415262912590144167198307651053211351413050597713, 415262912590144167198307651053217091013821936901⟩
  | 1, 2 => ⟨555016709691875897126064028940303325302843697249, 555016709691875897126064028940313837049991009008⟩
  | 2, 1 => ⟨560999982279444079566522069007804191957012605489, 560999982279444079566522069007823646073312420394⟩
  | 0, 4 => ⟨663249989469979861968536697999672420320048419070, 663249989469979861968536697999692994346865259017⟩
  | 1, 3 => ⟨975559971103040679659779027209980509451907197015, 975559971103040679659779027210018548146113191750⟩
  | 2, 2 => ⟨1290615896788502269278997800842084847447585225738, 1290615896788502269278997800842155893211905578993⟩
  | 3, 1 => ⟨1303088718526342641314314962741352311923155186208, 1303088718526342641314314962741485930557637729740⟩
  | 0, 5 => ⟨-3948247258354144046391124513236137920732150896210426, 3966608158342912343392382079995190559552916213699020⟩
  | 1, 4 => ⟨-7764154736471914533072361777944610709029715587964226, 7791817880826592270291747420199987053736238638901844⟩
  | 2, 3 => ⟨-15281847360901758846094441257728468057282635302643322, 15321717401791828563720549708724657859648845873986951⟩
  | 3, 2 => ⟨-30097926628190238508798239200633094087729876791866614, 30150331303002758721678382771415776754507587361311478⟩
  | 4, 1 => ⟨-59309789814192039394961949321664958401151258582245005, 59363665565524750688528333982970060265937917903426716⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0212Geometry.ds, E8TAxisProd0212Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 75101967378871908253984675871736829011589652532 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0212CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0213CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0213CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0213GraphCenterA.qJetBox,
   E8TAxisProd0213GraphCenterB.qJetBox,
   E8TAxisProd0213GraphCenterC.qJetBox,
   E8TAxisProd0213GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0213GraphWholeA.qJetBox,
   E8TAxisProd0213GraphWholeB.qJetBox,
   E8TAxisProd0213GraphWholeC.qJetBox,
   E8TAxisProd0213GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨72000868363907172658543800767455883813198191547, 72000868363907172658543800767456250570124740786⟩
  | 0, 2 => ⟨198853238737171618909928832996208143948094497109, 198853238737171618909928832996209663406632936531⟩
  | 1, 1 => ⟨201295800967352990326385060882672133445481387025, 201295800967352990326385060882674939319415036045⟩
  | 0, 3 => ⟨381531512030200329515007742920216130119869081377, 381531512030200329515007742920221264508163467916⟩
  | 1, 2 => ⟨510376794024707800643428100298740884627451468221, 510376794024707800643428100298750270533971792361⟩
  | 2, 1 => ⟨515927471963241734186958336737568468505054103539, 515927471963241734186958336737585812363524520571⟩
  | 0, 4 => ⟨612819922531704329926668796525505936197702579531, 612819922531704329926668796525524250333565975648⟩
  | 1, 3 => ⟨902557626572209651502959860729118118452078227584, 902557626572209651502959860729151927471257769013⟩
  | 2, 2 => ⟨1194855405774342828045090590006845168232045250868, 1194855405774342828045090590006908235316589060166⟩
  | 3, 1 => ⟨1206467586161380630207591340850780637771705199756, 1206467586161380630207591340850899112363643031897⟩
  | 0, 5 => ⟨-3576507748186353817660386971640807190329487700885489, 3593459609713888224178886258890763477874423524922944⟩
  | 1, 4 => ⟨-7030449845502568637050912620729678017926974877598422, 7056004724867513371611713076933698954587861169691659⟩
  | 2, 3 => ⟨-13832482413885741547751047275609584159890747909208060, 13869331508224527002728407908663412411579559663075436⟩
  | 3, 2 => ⟨-27233009215221085654187105956872524920518306334353293, 27281460307467385388403286309167205442057183884846993⟩
  | 4, 1 => ⟨-53643711238818839040460736390887569072898180088210174, 53693539903165323738578389035572703221418377628599108⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0213Geometry.ds, E8TAxisProd0213Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 67919005588130159532799628200075695371961049464 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0213CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0214CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0214CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0214GraphCenterA.qJetBox,
   E8TAxisProd0214GraphCenterB.qJetBox,
   E8TAxisProd0214GraphCenterC.qJetBox,
   E8TAxisProd0214GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0214GraphWholeA.qJetBox,
   E8TAxisProd0214GraphWholeB.qJetBox,
   E8TAxisProd0214GraphWholeC.qJetBox,
   E8TAxisProd0214GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨79305453690762684860629874583891717190817096558, 79305453690762684860629874583892122351466976859⟩
  | 0, 2 => ⟨217468162108637869731702200509293431116413178982, 217468162108637869731702200509295120011844548728⟩
  | 1, 1 => ⟨219943433974148359525157962712537954363953521864, 219943433974148359525157962712541079202302166681⟩
  | 0, 3 => ⟨414434591483620979905639760821041386322715685692, 414434591483620979905639760821047113134467877982⟩
  | 1, 2 => ⟨553798396499445272421686980184095036990337709448, 553798396499445272421686980184105525183730868307⟩
  | 2, 1 => ⟨559388357298846919498075748880549834651315465881, 559388357298846919498075748880569244949965128345⟩
  | 0, 4 => ⟨662064107219332983291510549910358067477332826726, 662064107219332983291510549910378593735281156131⟩
  | 1, 3 => ⟨973741653677664329419329884944515834949189222364, 973741653677664329419329884944553785138779611514⟩
  | 2, 2 => ⟨1287984852449773188741129263423225185791034935524, 1287984852449773188741129263423296065844355798354⟩
  | 3, 1 => ⟨1299638469127254263357694763607817306243926334110, 1299638469127254263357694763607950612340949416510⟩
  | 0, 5 => ⟨-3940401103529108205800856357771213653435465620869929, 3958725727817376157306872957279293749408099499918860⟩
  | 1, 4 => ⟨-7748693299542975295462827451049684743782319715179527, 7776300072593682461615357142420497637482364649966378⟩
  | 2, 3 => ⟨-15251346885428499727857259853755239340416258285845996, 15291130840862232689265041752642883975535067920093502⟩
  | 3, 2 => ⟨-30037713900589957000164492957333347767923311937638215, 30089990826160702602240836534569654495931780226943305⟩
  | 4, 1 => ⟨-59190850932265339468842758647617471189626487140370032, 59244547374590252168907465152178752827067573011790777⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0214Geometry.ds, E8TAxisProd0214Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 74843417279074743662709244964634271424461228019 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0214CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0215CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0215CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0215GraphCenterA.qJetBox,
   E8TAxisProd0215GraphCenterB.qJetBox,
   E8TAxisProd0215GraphCenterC.qJetBox,
   E8TAxisProd0215GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0215GraphWholeA.qJetBox,
   E8TAxisProd0215GraphWholeB.qJetBox,
   E8TAxisProd0215GraphWholeC.qJetBox,
   E8TAxisProd0215GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨71752599687583379968672829283106956056812278275, 71752599687583379968672829283107322047129933065⟩
  | 0, 2 => ⟨198376802826161717472403213551427894277078451748, 198376802826161717472403213551429410412021213803⟩
  | 1, 1 => ⟨200658534658088395401336209312712340820670152956, 200658534658088395401336209312715140513854522154⟩
  | 0, 3 => ⟨380766174720119427034331706070546205164616088991, 380766174720119427034331706070551328094963276079⟩
  | 1, 2 => ⟨509249652551869138559727239492934489519529506320, 509249652551869138559727239492943854353004795366⟩
  | 2, 1 => ⟨514435431328900057919865432356498189213224626192, 514435431328900057919865432356515493912757467221⟩
  | 0, 4 => ⟨611720076993554981973872488832820071386712961967, 611720076993554981973872488832838342908942004363⟩
  | 1, 3 => ⟨900869211015132913863027474969578701786742001797, 900869211015132913863027474969612431948498382783⟩
  | 2, 2 => ⟨1192410335614962706059776860071948073181293189723, 1192410335614962706059776860072010992757472975797⟩
  | 3, 1 => ⟨1203259829046450527912128071147692000807213412812, 1203259829046450527912128071147810197429866797281⟩
  | 0, 5 => ⟨-3569227321674243679411835080030169311143939749332724, 3586144858575929537845585689016456594424235194715432⟩
  | 1, 4 => ⟨-7016106126864684440501798309800108479962890170963346, 7041607592723975076482185617141922612467681457718762⟩
  | 2, 3 => ⟨-13804192829175775809038573838798735490315827767134040, 13840960335535431734876039078190852608976426425193124⟩
  | 3, 2 => ⟨-27177173310350883181561062203180459860021589757209981, 27225503541402360799216770590868220577723793782777341⟩
  | 4, 1 => ⟨-53533442536858204570089313209179226877025719424139423, 53583102499234142334851403197664007328475328403916789⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0215Geometry.ds, E8TAxisProd0215Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 67683257027020991157896205211378489831281612338 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0215CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0216CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0216CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0216GraphCenterA.qJetBox,
   E8TAxisProd0216GraphCenterB.qJetBox,
   E8TAxisProd0216GraphCenterC.qJetBox,
   E8TAxisProd0216GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0216GraphWholeA.qJetBox,
   E8TAxisProd0216GraphWholeB.qJetBox,
   E8TAxisProd0216GraphWholeC.qJetBox,
   E8TAxisProd0216GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨96316816621405288202755683976495164456612692832, 96316816621405288202755683976495660508654475356⟩
  | 0, 2 => ⟨260164281852527941447089765836621496664885741716, 260164281852527941447089765836623588401873650241⟩
  | 1, 1 => ⟨262868547358801389884041085619384513904498212342, 262868547358801389884041085619388398414256064348⟩
  | 0, 3 => ⟨489161719414333882780875470794637477266166332702, 489161719414333882780875470794644617529518332887⟩
  | 1, 2 => ⟨652434089484403177182210479617737159546969331880, 652434089484403177182210479617750282505162011534⟩
  | 2, 1 => ⟨658469016428616197071872680336764738283013626950, 658469016428616197071872680336789096421971857725⟩
  | 0, 4 => ⟨773266977524598843611164762161042444872526625025, 773266977524598843611164762161068280871416153810⟩
  | 1, 3 => ⟨1134401840086364399180195006950956456673625641621, 1134401840086364399180195006951004362030733480549⟩
  | 2, 2 => ⟨1498282131542423463170072179259820516065503716795, 1498282131542423463170072179259910204404297003923⟩
  | 3, 1 => ⟨1510782677855385189302083924807194735493640743723, 1510782677855385189302083924807363794680902024223⟩
  | 0, 5 => ⟨-4750598595553503077499540802165984726018848171682454, 4771935610607046700759363422001311147813831638011104⟩
  | 1, 4 => ⟨-9348401070533853164210363775601716337864470104993885, 9380495298643783611990403824812538908769201703201314⟩
  | 2, 3 => ⟨-18412718711336864005928756089052991386676904561968408, 18458905493817318183058735505580481926711127713095902⟩
  | 3, 2 => ⟨-36289405021290376028620695649040901120252789415168755, 36350020158640539855865478074088334677631560319347130⟩
  | 4, 1 => ⟨-71560675339103248688460434799536240445499316919751498, 71622816400546607747138036718968300167982251482947445⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0216Geometry.ds, E8TAxisProd0216Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 90981789056448915310145443269437398774371155722 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0216CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0217CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0217CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0217GraphCenterA.qJetBox,
   E8TAxisProd0217GraphCenterB.qJetBox,
   E8TAxisProd0217GraphCenterC.qJetBox,
   E8TAxisProd0217GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0217GraphWholeA.qJetBox,
   E8TAxisProd0217GraphWholeB.qJetBox,
   E8TAxisProd0217GraphWholeC.qJetBox,
   E8TAxisProd0217GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨87283718822786882628035337556427373574637809400, 87283718822786882628035337556427821330970047278⟩
  | 0, 2 => ⟨237660769636509203512585984734793752930441029923, 237660769636509203512585984734795630343214897325⟩
  | 1, 1 => ⟨240156038491755138775350580505539536370720583749, 240156038491755138775350580505543016528004471599⟩
  | 0, 3 => ⟨449925626937806507386195723038924989063611778897, 449925626937806507386195723038931376594291007080⟩
  | 1, 2 => ⟨600596058070032020422141580070118283025132574546, 600596058070032020422141580070130002159838301843⟩
  | 2, 1 => ⟨606197408542364007114951906940602581810309394849, 606197408542364007114951906940624302476208438924⟩
  | 0, 4 => ⟨715000017580335743229708342231808247900836049204, 715000017580335743229708342231831251117942746763⟩
  | 1, 3 => ⟨1050196633037853998485193896746054724133301532565, 1050196633037853998485193896746097316275996883031⟩
  | 2, 2 => ⟨1387952460159660323565174026206919079528813405311, 1387952460159660323565174026206998725911838319482⟩
  | 3, 1 => ⟨1399591533345462659252330020289906695879392227013, 1399591533345462659252330020290056659069984651188⟩
  | 0, 5 => ⟨-4328649690525787521233031754356587259226704521960779, 4348419874533353104965288280182773559205461627925116⟩
  | 1, 4 => ⟨-8515201238728883212317813391435088180329426941499381, 8544963331261420912940601232940474772453468079686711⟩
  | 2, 3 => ⟨-16765964113489093621803654266919989138631943741867661, 16808824094730104750129697292424029599965340414699585⟩
  | 3, 2 => ⟨-33032543283024014130241704291835375305639952483038473, 33088821789975001655694534487073859380453564610138803⟩
  | 4, 1 => ⟨-65115766517065716840882479518078894930305663171028469, 65173494531435852052296073712366905777051329385804299⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0217Geometry.ds, E8TAxisProd0217Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 82410056209078063234599250525428460324518105671 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0217CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0218CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0218CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0218GraphCenterA.qJetBox,
   E8TAxisProd0218GraphCenterB.qJetBox,
   E8TAxisProd0218GraphCenterC.qJetBox,
   E8TAxisProd0218GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0218GraphWholeA.qJetBox,
   E8TAxisProd0218GraphWholeB.qJetBox,
   E8TAxisProd0218GraphWholeC.qJetBox,
   E8TAxisProd0218GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨95991993175080207558644353549068252340129757687, 95991993175080207558644353549068747352726054131⟩
  | 0, 2 => ⟨259553433460362792306815287788274011318169684698, 259553433460362792306815287788276098495802995526⟩
  | 1, 1 => ⟨262053890451146126749666993153760433893603781335, 262053890451146126749666993153764309889529498582⟩
  | 0, 3 => ⟨488195994111180906515855857984452859306471944012, 488195994111180906515855857984459983707340270383⟩
  | 1, 2 => ⟨651017400368066510942819146614911459458316437610, 651017400368066510942819146614924553125346272905⟩
  | 2, 1 => ⟨656598060810390928813456893207216813347365846310, 656598060810390928813456893207241116878581256177⟩
  | 0, 4 => ⟨771893883342029146555219083903419739002750584412, 771893883342029146555219083903445515276660090677⟩
  | 1, 3 => ⟨1132301340558620968057994851852111306482288827442, 1132301340558620968057994851852159100927805140617⟩
  | 2, 2 => ⟨1495247754367004360937041414193661692863818164042, 1495247754367004360937041414193751173160671667551⟩
  | 3, 1 => ⟨1506807965121788362461159497380402956966738939953, 1506807965121788362461159497380571623133801651836⟩
  | 0, 5 => ⟨-4741672191252972770876676671680131723946942283768353, 4762968233448091236704889050833896258117460340307320⟩
  | 1, 4 => ⟨-9330806148884264150974341944639498956783636857589731, 9362837020397658811313545363986427631338756671331402⟩
  | 2, 3 => ⟨-18377998895200264299978522108791141474573647452019541, 18424089281513823682598516482712401261185458312359471⟩
  | 3, 2 => ⟨-36220839927743470602713614171091738734573185853581119, 36281312268435141354573023506189162811340666364899269⟩
  | 4, 1 => ⟨-71425190512844571473495158747261334441639815669576671, 71487130858620724655261539538190098253246450187235091⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0218Geometry.ds, E8TAxisProd0218Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 90672940067226678427876136232947023538105840612 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0218CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0219CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0219CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0219GraphCenterA.qJetBox,
   E8TAxisProd0219GraphCenterB.qJetBox,
   E8TAxisProd0219GraphCenterC.qJetBox,
   E8TAxisProd0219GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0219GraphWholeA.qJetBox,
   E8TAxisProd0219GraphWholeB.qJetBox,
   E8TAxisProd0219GraphWholeC.qJetBox,
   E8TAxisProd0219GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨86986994132493628861365172570572825479163385976, 86986994132493628861365172570573272297942640792⟩
  | 0, 2 => ⟨237098920864662781144806650290806039596710634451, 237098920864662781144806650290807912912492550683⟩
  | 1, 1 => ⟨239406113376951060887567912103181570700525577590, 239406113376951060887567912103185043217489542844⟩
  | 0, 3 => ⟨449032673457499119209431115127626928994622616769, 449032673457499119209431115127633302313786882432⟩
  | 1, 2 => ⟨599284532112368408903848547683017433810728585646, 599284532112368408903848547683029126736845305685⟩
  | 2, 1 => ⟨604464231431993609904716942689230255367399061322, 604464231431993609904716942689251927223929619170⟩
  | 0, 4 => ⟨713725900583967070145881686639613094161531817374, 713725900583967070145881686639636044085552484479⟩
  | 1, 3 => ⟨1048245452746104649044956248973215848728129801567, 1048245452746104649044956248973258342015380001865⟩
  | 2, 2 => ⟨1385131751623281347981928410692647217157258127253, 1385131751623281347981928410692726678278285190963⟩
  | 3, 1 => ⟨1395895282447926959629071328613772518192964441834, 1395895282447926959629071328613922131681020619400⟩
  | 0, 5 => ⟨-4320282846993750832961098256967888646601899596968472, 4340014409425884132895350975111413787208971284529267⟩
  | 1, 4 => ⟨-8498711339677640872154106872263639895815673859376059, 8528413569769110943726751399515476454105686714022824⟩
  | 2, 3 => ⟨-16733429514828879517579529741205194971342262730682999, 16776198239778207349198460669781706710823326685700909⟩
  | 3, 2 => ⟨-32968303669799472432891237969133185363802176849655258, 33024446832904810152272946415716199763923425401547172⟩
  | 4, 1 => ⟨-64988850005425885784222401375115448964113280015119106, 65046387793007078032078165147612228306160890544693661⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0219Geometry.ds, E8TAxisProd0219Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 82128048520215550456721811708162933814269180510 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0219CertifiedArithmetic

end


