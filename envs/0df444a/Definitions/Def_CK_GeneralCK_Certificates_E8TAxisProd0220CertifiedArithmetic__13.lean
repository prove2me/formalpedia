-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0220CertifiedArithmetic__13
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0220CertifiedArithmetic__13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T13:48:34.467058+00:00
-- url     : https://prove2.me/theorems/afb117f6-a589-44c2-bcf6-89cd0a785374
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0220CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0221CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0220CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0221CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0222CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0223CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0224CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0225CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0226CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0227CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0228CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0229CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0230CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0231CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0232CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0220CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0221CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0222CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0223CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0224CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0225CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0226CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0227CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0228CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0229CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0230CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0231CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0232CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0220CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0221CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0222CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0223CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0224CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0225CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0226CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0227CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0228CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0229CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0230CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0231CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0232CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0220CertifiedArithmetic (+12 modules: GeneralCK/Certificates/E8TAxisProd0221CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0222CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0223CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0224CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0225CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0226CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0227CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0228CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0229CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0230CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0231CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0232CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0220GraphCenterA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0212GraphCenterB__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0212GraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0210GraphCenterD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0220GraphWholeA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0219GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0212GraphWholeC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0218GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0216Geometry__18
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0221GraphCenterB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0221GraphCenterD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0223GraphCenterC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0226GraphWholeC__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0230GraphCenterA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0230GraphWholeB__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0231GraphCenterD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0231GraphWholeA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0231GraphWholeD__7

-- ===== source module GeneralCK.Certificates.E8TAxisProd0220CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0220CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0220GraphCenterA.qJetBox,
   E8TAxisProd0220GraphCenterB.qJetBox,
   E8TAxisProd0220GraphCenterC.qJetBox,
   E8TAxisProd0220GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0220GraphWholeA.qJetBox,
   E8TAxisProd0220GraphWholeB.qJetBox,
   E8TAxisProd0220GraphWholeC.qJetBox,
   E8TAxisProd0220GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨79033942049732220085428520897927919551015959262, 79033942049732220085428520897928323864007790871⟩
  | 0, 2 => ⟨216950635798425732084161990163931376942415758571, 216950635798425732084161990163933062147975155842⟩
  | 1, 1 => ⟨219251946241276226268819995553101167731453942780, 219251946241276226268819995553104285698135803134⟩
  | 0, 3 => ⟨413607751507086374218513457945856493708944062692, 413607751507086374218513457945862207759855574203⟩
  | 1, 2 => ⟨552582354266480383682815915069595412202280613014, 552582354266480383682815915069605876893835648315⟩
  | 2, 1 => ⟨557780018199224478936115495763387915434610789707, 557780018199224478936115495763407282012198821255⟩
  | 0, 4 => ⟨660880180991528492957131310413106098127014977728, 660880180991528492957131310413126576725176583187⟩
  | 1, 3 => ⟨971926435135775092484630732947517381410175952964, 971926435135775092484630732947555243297109121467⟩
  | 2, 2 => ⟨1285358485939840020438812333839573139577559792867, 1285358485939840020438812333839643854297678124600⟩
  | 3, 1 => ⟨1296194915871231844177063382432223371178727867062, 1296194915871231844177063382432356365450271103700⟩
  | 0, 5 => ⟨-3932566553380925318906149117085096763199738744220362, 3950854962057294815013243831369274778922174497675616⟩
  | 1, 4 => ⟨-7733254713572616096804885133149708409220540540434491, 7760805208889039837836674338645433533108036144299453⟩
  | 2, 3 => ⟨-15220891473174106364746214562306511498827471465504100, 15260589488800245328796635434474019465410866141707834⟩
  | 3, 2 => ⟨-29977590127838912587389683871035266314805242622950056, 30029739531679791625261703350063921984607215931114339⟩
  | 4, 1 => ⟨-59072087773550122726782727367726401079715973308485523, 59125605264617280004548161110016648747134938956685785⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0220Geometry.ds, E8TAxisProd0220Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 74585485364627719672861724837889573190311789760 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0220CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0221CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0221CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0221GraphCenterA.qJetBox,
   E8TAxisProd0221GraphCenterB.qJetBox,
   E8TAxisProd0221GraphCenterC.qJetBox,
   E8TAxisProd0221GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0221GraphWholeA.qJetBox,
   E8TAxisProd0221GraphWholeB.qJetBox,
   E8TAxisProd0221GraphWholeC.qJetBox,
   E8TAxisProd0221GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨71504925958586450693778073506765451479423747369, 71504925958586450693778073506765816704724390881⟩
  | 0, 2 => ⟨197901322728008965425395016415964887254086917168, 197901322728008965425395016415966400072573231593⟩
  | 1, 1 => ⟨200022675957341528550005562057996893842960255248, 200022675957341528550005562057999687368694373062⟩
  | 0, 3 => ⟨380002211079806140732458501960996200305208160422, 380002211079806140732458501961001311802875626433⟩
  | 1, 2 => ⟨508124619795515750177379476242478660571030013598, 508124619795515750177379476242488004377963148347⟩
  | 2, 1 => ⟨512946444309602699140688170425945640579307538749, 512946444309602699140688170425962906206349627081⟩
  | 0, 4 => ⟨610622050440256412616468759372963943045469697553, 610622050440256412616468759372982172051521927753⟩
  | 1, 3 => ⟨899183679428404703340010771580991874208609795131, 899183679428404703340010771581025525693197967594⟩
  | 2, 2 => ⟨1189969620499858575394611766350733374664766970409, 1189969620499858575394611766350796147069527007542⟩
  | 3, 1 => ⟨1200058307186898569532027808675179950214392478057, 1200058307186898569532027808675297869502347436771⟩
  | 0, 5 => ⟨-3561957741226683690975773444517827723779709539492821, 3578841015053168343945401095211526908050331961903941⟩
  | 1, 4 => ⟨-7001783763404318300471741972499732007025440885834166, 7027231913345927540933850253549089494731468712016209⟩
  | 2, 3 => ⟨-13775945353798589968394212403458930748882280755285648, 13812631427130781780971017545347185444666876377332995⟩
  | 3, 2 => ⟨-27121420521145902698471299364882895628890891969322784, 27169630138199591239075343460433594772688024674635195⟩
  | 4, 1 => ⟨-53423338007363627813607304062865166766610386958157581, 53472829664821919445317092744439592760217131089058134⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0221Geometry.ds, E8TAxisProd0221Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 67448076232922393202435706950776107249456949381 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0221CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0222CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0222CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0222GraphCenterA.qJetBox,
   E8TAxisProd0222GraphCenterB.qJetBox,
   E8TAxisProd0222GraphCenterC.qJetBox,
   E8TAxisProd0222GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0222GraphWholeA.qJetBox,
   E8TAxisProd0222GraphWholeB.qJetBox,
   E8TAxisProd0222GraphWholeC.qJetBox,
   E8TAxisProd0222GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨78763076671006022455064687947583637444651516907, 78763076671006022455064687947584040911747134868⟩
  | 0, 2 => ⟨216434142113750696351996232452697195654939581594, 216434142113750696351996232452698877178549690453⟩
  | 1, 1 => ⟨218561977143861851281979033336043228304488390205, 218561977143861851281979033336046339414277601853⟩
  | 0, 3 => ⟨412782390217373643409802933387604659762988382433, 412782390217373643409802933387610361081175601235⟩
  | 1, 2 => ⟨551368579122458197662409574867986198531991945718, 551368579122458197662409574867996639773510823066⟩
  | 2, 1 => ⟨556174959138122470890635205169351699175791501691, 556174959138122470890635205169371022128694861085⟩
  | 0, 4 => ⟨659698207808297578803014746041364469028667750495, 659698207808297578803014746041384900075876856007⟩
  | 1, 3 => ⟨970114310548455203266745722078460280288632595531, 970114310548455203266745722078498054074409650064⟩
  | 2, 2 => ⟨1282736789529936343698304023421643194615165322188, 1282736789529936343698304023421713744379024960424⟩
  | 3, 1 => ⟨1292758047150018651322191809890598085294194776016, 1292758047150018651322191809890730768450634614642⟩
  | 0, 5 => ⟨-3924743408894141700394560229717788770640884423921087, 3942995661023456598867650445684503429495295024968159⟩
  | 1, 4 => ⟨-7717838582958128194743968612987072575678240335574523, 7745332892472820684575439613226770363379308269528118⟩
  | 2, 3 => ⟨-15190480337620907765225376471800832571459267358301760, 15230092556596366582437352247273672328405883338851719⟩
  | 3, 2 => ⟨-29917553746084505279089690426892806485944583303451124, 29969575852263834910026159503419011662594876369023782⟩
  | 4, 1 => ⟨-58953497228457371237304337892248993933082175489729517, 59006836122152619710548247999311216197687674985949652⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0222Geometry.ds, E8TAxisProd0222Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 74328170411209064260883154998315879677451917428 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0222CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0223CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0223CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0223GraphCenterA.qJetBox,
   E8TAxisProd0223GraphCenterB.qJetBox,
   E8TAxisProd0223GraphCenterC.qJetBox,
   E8TAxisProd0223GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0223GraphWholeA.qJetBox,
   E8TAxisProd0223GraphWholeB.qJetBox,
   E8TAxisProd0223GraphWholeC.qJetBox,
   E8TAxisProd0223GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨71257845983222901011746964324609508174369452511, 71257845983222901011746964324609872636241633784⟩
  | 0, 2 => ⟨197426796727046511565540237639793607366632088155, 197426796727046511565540237639795116875785859668⟩
  | 1, 1 => ⟨199388222231468686443151133575315131669505925594, 199388222231468686443151133575317919041060337692⟩
  | 0, 3 => ⟨379239618837265842629679035817876791464219771921, 379239618837265842629679035817881891554419319192⟩
  | 1, 2 => ⟨507001692153560921207990386525128174424134014587, 507001692153560921207990386525137497250925668795⟩
  | 2, 1 => ⟨511460505466055424150510013938545322530466535806, 511460505466055424150510013938562549171275246841⟩
  | 0, 4 => ⟨609525840094149355955386725210365710932877126349, 609525840094149355955386725210383897519988685860⟩
  | 1, 3 => ⟨897501027211194490648984785748184917138219570869, 897501027211194490648984785748218490125485908429⟩
  | 2, 2 => ⟨1187533253213091622720150065180895382305735634894, 1187533253213091622720150065180958007875258419613⟩
  | 3, 1 => ⟨1196863009745801713117153134414480298183615700717, 1196863009745801713117153134414597940770027462287⟩
  | 0, 5 => ⟨-3554698997379856813040512450899395661466501546342347, 3571548069614967625444074649721853206028901368711536⟩
  | 1, 4 => ⟨-6987482736694070944188264644765744403626183397213199, 7012877668221289756035376406027843915332897630908191⟩
  | 2, 3 => ⟨-13747739951740297355363705429494608394520312530413799, 13784344746889402558386988658325004503919288900281466⟩
  | 3, 2 => ⟨-27065750777078253300535909526474295842451948404566415, 27113840027218014900643694793856099009261496264581804⟩
  | 4, 1 => ⟨-53313397512043825086955029868088996477145270791903580, 53362721261560438603288241489116938028732988605802225⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0223Geometry.ds, E8TAxisProd0223Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 67213462062111561996011918152248302882864215017 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0223CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0224CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0224CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0224GraphCenterA.qJetBox,
   E8TAxisProd0224GraphCenterB.qJetBox,
   E8TAxisProd0224GraphCenterC.qJetBox,
   E8TAxisProd0224GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0224GraphWholeA.qJetBox,
   E8TAxisProd0224GraphWholeB.qJetBox,
   E8TAxisProd0224GraphWholeC.qJetBox,
   E8TAxisProd0224GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨65090806507595419715982185059922052670747421731, 65090806507595419715982185059922384101602371306⟩
  | 0, 2 => ⟨181263639731708822643619532177155768745950194458, 181263639731708822643619532177157132910005983308⟩
  | 1, 1 => ⟨183514047426975664092496461525665254026094327555, 183514047426975664092496461525667767996712412501⟩
  | 0, 3 => ⟨350329721909336918446225052211460797578385898504, 350329721909336918446225052211465390481407793663⟩
  | 1, 2 => ⟨469055805434558542544478568245019367761832476002, 469055805434558542544478568245027747708353446782⟩
  | 2, 1 => ⟨474203746493295905977062649966902860065802731604, 474203746493295905977062649966918320660467811289⟩
  | 0, 4 => ⟨565997026162881316346234726899096840467817809308, 565997026162881316346234726899113140993398780385⟩
  | 1, 3 => ⟨834720201821926729303965934712185550847690786634, 834720201821926729303965934712215595304248619088⟩
  | 2, 2 => ⟨1105830376591690248252036410572022000408713365794, 1105830376591690248252036410572077973260969334473⟩
  | 3, 1 => ⟨1116640865494459290428652090228821672249183501726, 1116640865494459290428652090228926694564637192928⟩
  | 0, 5 => ⟨-3231289368789587750610599966712460798701193947663257, 3246891889094580798222596263003530104355432002808057⟩
  | 1, 4 => ⟨-6349287554677764384740633721968370929717973753785394, 6372817391382666883987969144702999248701308032944058⟩
  | 2, 3 => ⟨-12487317188472755249205456017351830138803674498367596, 12521256932723294375789144962702914457244538611209860⟩
  | 3, 2 => ⟨-24574889760998123913502251673596143838182658004568946, 24619524321543618227177823340398941748887824364629990⟩
  | 4, 1 => ⟨-48388310615370863921171129656233943110484896236494220, 48434218588872726469325489593568743073001138381811683⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0224Geometry.ds, E8TAxisProd0224Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 61371251798648515723987660819019921182740912794 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0224CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0225CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0225CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0225GraphCenterA.qJetBox,
   E8TAxisProd0225GraphCenterB.qJetBox,
   E8TAxisProd0225GraphCenterC.qJetBox,
   E8TAxisProd0225GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0225GraphWholeA.qJetBox,
   E8TAxisProd0225GraphWholeB.qJetBox,
   E8TAxisProd0225GraphWholeC.qJetBox,
   E8TAxisProd0225GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨58793515604807520048986160485634015699692836791, 58793515604807520048986160485634315330908223320⟩
  | 0, 2 => ⟨165102899791583461274699653870363271194071662433, 165102899791583461274699653870364496054926208687⟩
  | 1, 1 => ⟨167175120656675472198913699761861816358962962863, 167175120656675472198913699761864068827210381435⟩
  | 0, 3 => ⟨321478403389673017371640604832466564323286365548, 321478403389673017371640604832470672746470067073⟩
  | 1, 2 => ⟨430820119732192948877026793127762781816617376502, 430820119732192948877026793127770262927989928387⟩
  | 2, 1 => ⟨435593135244130083483992660548172063404238805556, 435593135244130083483992660548185843375183840517⟩
  | 0, 4 => ⟨522531762652177921901969980154195329337481375193, 522531762652177921901969980154209835722252438681⟩
  | 1, 3 => ⟨771691430098299738793287270700197470935607618762, 771691430098299738793287270700224164938157697487⟩
  | 2, 2 => ⟨1023076934764427281051964943376365587957742397123, 1023076934764427281051964943376415253382330136756⟩
  | 3, 1 => ⟨1033140713997799660007773745964408788139064955568, 1033140713997799660007773745964501861944598391632⟩
  | 0, 5 => ⟨-2910245471280513103565745356762979787554001130270386, 2924566938799872086588665434048294432155234477499651⟩
  | 1, 4 => ⟨-5716001000441285313224101224172342505772602751757605, 5737604011639187595788105455563440417349958723457402⟩
  | 2, 3 => ⟨-11237063013650120210809407747318283808353453565020968, 11268229286128747556973371152712909995123561766477863⟩
  | 3, 2 => ⟨-22105069975820420797971807704532264341624848621391232, 22146060445290707495554714318430117072042336403691791⟩
  | 4, 1 => ⟨-43506731578576583380958653508136359973148139265430341, 43548887869419165229518732004424191587710576153873221⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0225Geometry.ds, E8TAxisProd0225Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 55407164243526544304631308582887901938922940580 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0225CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0226CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0226CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0226GraphCenterA.qJetBox,
   E8TAxisProd0226GraphCenterB.qJetBox,
   E8TAxisProd0226GraphCenterC.qJetBox,
   E8TAxisProd0226GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0226GraphWholeA.qJetBox,
   E8TAxisProd0226GraphWholeB.qJetBox,
   E8TAxisProd0226GraphWholeC.qJetBox,
   E8TAxisProd0226GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨64864500468865233343300691454359640419920894381, 64864500468865233343300691454359971158695899171⟩
  | 0, 2 => ⟨180826169498819740976156595081109362292078672698, 180826169498819740976156595081110723468548228535⟩
  | 1, 1 => ⟨182928379386965103699495805581512826694993992144, 182928379386965103699495805581515335117949275370⟩
  | 0, 3 => ⟨349622863168315925665415837791786926632317338264, 349622863168315925665415837791791509269171804663⟩
  | 1, 2 => ⟨468013385142475133680162840638992079414614044552, 468013385142475133680162840639000440506963028975⟩
  | 2, 1 => ⟨472822878889156025898728407433289288676503478291, 472822878889156025898728407433304714275534309207⟩
  | 0, 4 => ⟨564977241533205189250289555911028361646873268096, 564977241533205189250289555911044624154964020311⟩
  | 1, 3 => ⟨833152713092429738115131405471564262501447778368, 833152713092429738115131405471594236693537338908⟩
  | 2, 2 => ⟨1103558466217365100130224654744535256353806517946, 1103558466217365100130224654744591097898459159884⟩
  | 3, 1 => ⟨1113658916368436193025617219843159785276084659629, 1113658916368436193025617219843264560366532584568⟩
  | 0, 5 => ⟨-3224529645953416368352044248750967261441076795128861, 3240099886403649413156442978225762566440486833682121⟩
  | 1, 4 => ⟨-6335972180192288837206732607965353267167972587249640, 6359451764229379454903652236259209252457849062018356⟩
  | 2, 3 => ⟨-12461060903465238120919271669347534709644416853488345, 12494923958239689077045401775460107026919277509322021⟩
  | 3, 2 => ⟨-24523077557188304344944250752448739175181755250808841, 24567598881946150534861880114921672289813041296548104⟩
  | 4, 1 => ⟨-48286009600899487370161508990024184041250892919891035, 48331760748053803848676137640445134586313226480895231⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0226Geometry.ds, E8TAxisProd0226Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 61156458056327974719942573478662747161221881356 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0226CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0227CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0227CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0227GraphCenterA.qJetBox,
   E8TAxisProd0227GraphCenterB.qJetBox,
   E8TAxisProd0227GraphCenterC.qJetBox,
   E8TAxisProd0227GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0227GraphWholeA.qJetBox,
   E8TAxisProd0227GraphWholeB.qJetBox,
   E8TAxisProd0227GraphWholeC.qJetBox,
   E8TAxisProd0227GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨58587387965052681352610722314378570225472464239, 58587387965052681352610722314378869231695707402⟩
  | 0, 2 => ⟨164701459769011164583592726440265044465573687631, 164701459769011164583592726440266266640586828619⟩
  | 1, 1 => ⟨166637198011887067571948644047444171035145135056, 166637198011887067571948644047446418523718536377⟩
  | 0, 3 => ⟨320825829663887742993208259944054704265354715717, 320825829663887742993208259944058803490057216350⟩
  | 1, 2 => ⟨429856415041467399143869432802484692151641442954, 429856415041467399143869432802492156394696271027⟩
  | 2, 1 => ⟨434315608661774137352147122069395526614258734710, 434315608661774137352147122069409275312416966838⟩
  | 0, 4 => ⟨521586460758808561697812753054278325050864267749, 521586460758808561697812753054292797521017349569⟩
  | 1, 3 => ⟨770236491409290976216418611685561602220849888139, 770236491409290976216418611685588233622758532121⟩
  | 2, 2 => ⟨1020966226289087037627964186294294129741299099151, 1020966226289087037627964186294343678296329671650⟩
  | 3, 1 => ⟨1030369005280030851496777199069123498382653192304, 1030369005280030851496777199069216352343042470025⟩
  | 0, 5 => ⟨-2903970546588791204414898805673660264406037060997390, 2918262089093319991992384264894740496173098202636356⟩
  | 1, 4 => ⟨-5703643220526741379980970002909254843517166304555119, 5725199690406955655259732820029267449783788455891626⟩
  | 2, 3 => ⟨-11212700474678851175978800840676321554413325996841940, 11243795860796113598883285032928879239206535268357060⟩
  | 3, 2 => ⟨-22057006000568454573353349223234549486845394914949281, 22097892200743500162761148735589782212417609068354607⟩
  | 4, 1 => ⟨-43411854166956395438720678734728136271533116094303178, 43453867155779614749762283886796541215407008766446542⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0227Geometry.ds, E8TAxisProd0227Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 55211616022584778533929185307955624305944921755 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0227CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0228CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0228CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0228GraphCenterA.qJetBox,
   E8TAxisProd0228GraphCenterB.qJetBox,
   E8TAxisProd0228GraphCenterC.qJetBox,
   E8TAxisProd0228GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0228GraphWholeA.qJetBox,
   E8TAxisProd0228GraphWholeB.qJetBox,
   E8TAxisProd0228GraphWholeC.qJetBox,
   E8TAxisProd0228GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨53059106290244813936483918221799129042533984981, 53059106290244813936483918221799400041399150726⟩
  | 0, 2 => ⟨150264095957401989439480565750735426237164488146, 150264095957401989439480565750736526130447249163⟩
  | 1, 1 => ⟨152171132918496291251371757971940607326509494154, 152171132918496291251371757971942625519811781289⟩
  | 0, 3 => ⟨294810787616720646146028019620311226924776098867, 294810787616720646146028019620314901876399825055⟩
  | 1, 2 => ⟨395452218164016961641392646007623935145152085989, 395452218164016961641392646007630613176285877180⟩
  | 2, 1 => ⟨399876211090686371889837050494371539324127670586, 399876211090686371889837050494383819623140489284⟩
  | 0, 4 => ⟨482191257569905006976100630646470751766146713729, 482191257569905006976100630646483659703798524905⟩
  | 1, 3 => ⟨713138902701468999951908999820602723024377695068, 713138902701468999951908999820626435490189626504⟩
  | 2, 2 => ⟨946162314676877146529840247992416410055948055721, 946162314676877146529840247992460468408335289077⟩
  | 3, 1 => ⟨955530647627963939555807650164973276393030323926, 955530647627963939555807650165055739127788743813⟩
  | 0, 5 => ⟨-2612939628574603811327133443258462588873867291459177, 2626061158508705789125403272910715057565438607895749⟩
  | 1, 4 => ⟨-5129750328953206230726530460865047457364056733692540, 5149546923970914770837373605793790607196061157694289⟩
  | 2, 3 => ⟨-10080098753948187999568748573181058044194004453719087, 10108663144312195483442605417537935820391215560268975⟩
  | 3, 2 => ⟨-19820413573808258957465800391230116794178637846414417, 19857984300646083481053165898015151502481417504555135⟩
  | 4, 1 => ⟨-38992894565859844375055394400730343748371371618717098, 39031530727966869535094390225659859192824221179299741⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0228Geometry.ds, E8TAxisProd0228Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 49978925409035973813913324867124722800912501847 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0228CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0229CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0229CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0229GraphCenterA.qJetBox,
   E8TAxisProd0229GraphCenterB.qJetBox,
   E8TAxisProd0229GraphCenterC.qJetBox,
   E8TAxisProd0229GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0229GraphWholeA.qJetBox,
   E8TAxisProd0229GraphWholeB.qJetBox,
   E8TAxisProd0229GraphWholeC.qJetBox,
   E8TAxisProd0229GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨47841428037212396101690349432142393383310114839, 47841428037212396101690349432142638595120812161⟩
  | 0, 2 => ⟨136647849267665152349819083771966834826727239826, 136647849267665152349819083771967822605313251483⟩
  | 1, 1 => ⟨138401806704313923942266294888351303490983840049, 138401806704313923942266294888353111796788109610⟩
  | 0, 3 => ⟨270171645604670393580572411549536188414769362260, 270171645604670393580572411549539475538963266334⟩
  | 1, 2 => ⟨362749605004401001422908533428191905638868684065, 362749605004401001422908533428197866183271763372⟩
  | 2, 1 => ⟨366848699331867251907717076366271228872540450985, 366848699331867251907717076366282171083962362782⟩
  | 0, 4 => ⟨444758250775672053997678946398257228997571398992, 444758250775672053997678946398268712973956951375⟩
  | 1, 3 => ⟨658752568039605229075583712522678779890341459817, 658752568039605229075583712522699839455351828365⟩
  | 2, 2 => ⟨874682902905095924252884060887902483610486096850, 874682902905095924252884060887941558242316054395⟩
  | 3, 1 => ⟨883403567562512103468426298334724375922156259386, 883403567562512103468426298334797416970963283811⟩
  | 0, 5 => ⟨-2339165074941897538988808135974389019059958212031431, 2351172776589701628616107133211070336641764916561713⟩
  | 1, 4 => ⟨-4590098903882295874488224655701030526085170299116157, 4608217973765490497086941922597910952449594718639695⟩
  | 2, 3 => ⟨-9015498533746800241910032099312333201580497384567362, 9041646280989549610850778650219502599414741638883371⟩
  | 3, 2 => ⟨-17718955402402254765468026301219256831128266920654742, 17753350801281784803965930797588602300503152071049610⟩
  | 4, 1 => ⟨-34842630396626026065863028092415880918224094508814904, 34878003007237443740734175823622610004167838937172067⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0229Geometry.ds, E8TAxisProd0229Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 45042303664974019497909354873581364453841633897 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0229CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0230CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0230CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0230GraphCenterA.qJetBox,
   E8TAxisProd0230GraphCenterB.qJetBox,
   E8TAxisProd0230GraphCenterC.qJetBox,
   E8TAxisProd0230GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0230GraphWholeA.qJetBox,
   E8TAxisProd0230GraphWholeB.qJetBox,
   E8TAxisProd0230GraphWholeC.qJetBox,
   E8TAxisProd0230GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨52871506334333913793386277858571536267845023311, 52871506334333913793386277858571806702121923209⟩
  | 0, 2 => ⟨149895958956574432907645632140896062977977334198, 149895958956574432907645632140897160456429704798⟩
  | 1, 1 => ⟨151677374433791877770139057543130511073257718415, 151677374433791877770139057543132524796526092350⟩
  | 0, 3 => ⟨294208596212544728469220084412035833367649292085, 294208596212544728469220084412039500077358378364⟩
  | 1, 2 => ⟨394561638655726704408458680061018346703453517184, 394561638655726704408458680061025009643624420321⟩
  | 2, 1 => ⟨398694733977021383673259362628476987103754942122, 398694733977021383673259362628489239458988003791⟩
  | 0, 4 => ⟨481315232692697758575625586013864067075703847214, 481315232692697758575625586013876944761148929644⟩
  | 1, 3 => ⟨711788697765025881966796198785876148977368797685, 711788697765025881966796198785899805677292287567⟩
  | 2, 2 => ⟨944201652714743288305966492721025098127892677919, 944201652714743288305966492721069052476831416875⟩
  | 3, 1 => ⟨952954658059138594031981435101663449787520232515, 952954658059138594031981435101745717058419832529⟩
  | 0, 5 => ⟨-2607162264807596967577698603791756538005615328707710, 2620256103800380942662500654855813682106931782989954⟩
  | 1, 4 => ⟨-5118376061499324649345303890774710516977100849474608, 5138129617764444262457609571084456616957105516285797⟩
  | 2, 3 => ⟨-10057682383739016689192238813225024742015095603625365, 10086181336440414310178430632725446021875947773884985⟩
  | 3, 2 => ⟨-19776203591192348188377442049805211606138842606920417, 19813678415696682591296764723222505744853679687103958⟩
  | 4, 1 => ⟨-38905653758583995023526958062974624616656524408092514, 38944159127163107893965212903691989507236943486666577⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0230Geometry.ds, E8TAxisProd0230Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 49801038319007863923065865581967193161949093318 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0230CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0231CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0231CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0231GraphCenterA.qJetBox,
   E8TAxisProd0231GraphCenterB.qJetBox,
   E8TAxisProd0231GraphCenterC.qJetBox,
   E8TAxisProd0231GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0231GraphWholeA.qJetBox,
   E8TAxisProd0231GraphWholeB.qJetBox,
   E8TAxisProd0231GraphWholeC.qJetBox,
   E8TAxisProd0231GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨47670829152513948581589869376483887378219313638, 47670829152513948581589869376484132079840685760⟩
  | 0, 2 => ⟨136310481966598986713734830727451082376519285665, 136310481966598986713734830727452067983714983714⟩
  | 1, 1 => ⟨137948884022121417620939139682545397063324887040, 137948884022121417620939139682547201356428936438⟩
  | 0, 3 => ⟨269616205185475039677833414849415135936151489053, 269616205185475039677833414849418415675486389349⟩
  | 1, 2 => ⟨361926947495714802281378189133690860862125083870, 361926947495714802281378189133696807906346657267⟩
  | 2, 1 => ⟨365756484180372290905803351668958026713585451568, 365756484180372290905803351668968943958055866076⟩
  | 0, 4 => ⟨443946646194661880936302177428435227691065867607, 443946646194661880936302177428446684684358891649⟩
  | 1, 3 => ⟨657499805874121231231861873124816808312159433370, 657499805874121231231861873124837818206266785260⟩
  | 2, 2 => ⟨872861884206022459182959039054073105615650080447, 872861884206022459182959039054112087708403677711⟩
  | 3, 1 => ⟨881009756546457278879421384098011622870852181548, 881009756546457278879421384098084490164743676730⟩
  | 0, 5 => ⟨-2334038509933558051577919162590321763105447460862927, 2346022079248328528023236652764635963848061781963338⟩
  | 1, 4 => ⟨-4580009832061869869427167290547432459584071386021512, 4598091493276466222477906391486166018254485084471869⟩
  | 2, 3 => ⟨-8995622137147908188677395098194820889536583338469699, 9021713093914797734811023585042170189385721378250246⟩
  | 3, 2 => ⟨-17679768048633236546732210359004064973584520620421754, 17714080173442515331594163389554710905385626692650706⟩
  | 4, 1 => ⟨-34765325923188104121104011959232240685920572951015651, 34800584461286253755338879634862034179093061532818178⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0231Geometry.ds, E8TAxisProd0231Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 44880602916532882881221015518117087909671466374 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0231CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0232CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0232CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0232GraphCenterA.qJetBox,
   E8TAxisProd0232GraphCenterB.qJetBox,
   E8TAxisProd0232GraphCenterC.qJetBox,
   E8TAxisProd0232GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0232GraphWholeA.qJetBox,
   E8TAxisProd0232GraphWholeB.qJetBox,
   E8TAxisProd0232GraphWholeC.qJetBox,
   E8TAxisProd0232GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨64638740716024590358899267709384559027189715286, 64638740716024590358899267709384889075320477443⟩
  | 0, 2 => ⟨180389582043090747461144914091626065013339111559, 180389582043090747461144914091627423208642902036⟩
  | 1, 1 => ⟨182344013148418142958930344093342777710770715488, 182344013148418142958930344093345280598010246068⟩
  | 0, 3 => ⟨348917278100887818823663981295218203804151376669, 348917278100887818823663981295222776197498833942⟩
  | 1, 2 => ⟨466972922533770685318955690915320487523186926105, 466972922533770685318955690915328829803022746509⟩
  | 2, 1 => ⟨471444848638694166956507712801945654748433969135, 471444848638694166956507712801961045429207925454⟩
  | 0, 4 => ⟨563959147982255828805828441634407377271816951757, 563959147982255828805828441634423601849501595303⟩
  | 1, 3 => ⟨831587907699421794801242317324822102520834096823, 831587907699421794801242317324852006609357925768⟩
  | 2, 2 => ⟨1101290609583367505020686334358275678389886085200, 1101290609583367505020686334358331388927475682652⟩
  | 3, 1 => ⟨1110682772361248383569706268071469714935575405915, 1110682772361248383569706268071574243366676077043⟩
  | 0, 5 => ⟨-3217780330698750586254200294444557140022686877638395, 3233318353551580228554723592647344060165390793076899⟩
  | 1, 4 => ⟨-6322677301324485525522000500209717559102414515990953, 6346106732561797142247141216190931546030417868125549⟩
  | 2, 3 => ⟨-12434845038587108931290174835316795012710643067952628, 12468631564279604276310265767708006079341445984530505⟩
  | 3, 2 => ⟨-24471345144094801549072050390837039169103658620620699, 24515753491560613185735378740736515318352208008416098⟩
  | 4, 1 => ⟨-48183866206877752662469661898651892811561824543538363, 48229460946079933693601941089236557397938404037076144⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0232Geometry.ds, E8TAxisProd0232Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 60942185433947641708211156766648096988506725643 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0232CertifiedArithmetic

end


