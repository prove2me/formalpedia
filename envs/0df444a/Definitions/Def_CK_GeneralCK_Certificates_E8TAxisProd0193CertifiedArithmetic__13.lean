-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0193CertifiedArithmetic__13
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0193CertifiedArithmetic__13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T13:53:47.670976+00:00
-- url     : https://prove2.me/theorems/4a29b36e-dcf1-449a-bda4-d0775968f587
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0193CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0194CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0193CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0194CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0195CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0196CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0197CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0198CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0199CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0200CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0201CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0202CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0203CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0204CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0205CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0193CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0194CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0195CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0196CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0197CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0198CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0199CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0200CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0201CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0202CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0203CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0204CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0205CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0193CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0194CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0195CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0196CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0197CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0198CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0199CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0200CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0201CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0202CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0203CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0204CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0205CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0193CertifiedArithmetic (+12 modules: GeneralCK/Certificates/E8TAxisProd0194CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0195CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0196CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0197CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0198CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0199CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0200CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0201CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0202CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0203CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0204CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0205CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0192GraphCenterA__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0188GraphCenterB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0182GraphCenterC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0181GraphCenterD__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0183GraphWholeA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0180GraphWholeB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0185GraphWholeC__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0181GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0181Geometry__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0194GraphWholeB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0194GraphWholeD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0195GraphCenterC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0197GraphCenterD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0197GraphWholeA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0199GraphCenterB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0199GraphWholeC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0201Geometry__15

-- ===== source module GeneralCK.Certificates.E8TAxisProd0193CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0193CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0193GraphCenterA.qJetBox,
   E8TAxisProd0193GraphCenterB.qJetBox,
   E8TAxisProd0193GraphCenterC.qJetBox,
   E8TAxisProd0193GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0193GraphWholeA.qJetBox,
   E8TAxisProd0193GraphWholeB.qJetBox,
   E8TAxisProd0193GraphWholeC.qJetBox,
   E8TAxisProd0193GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨242512535048132337473991007628242552250892513, 242512535048132337473991007628250603858464049⟩
  | 0, 2 => ⟨1075241119096391231117372900118801243081156637, 1075241119096391231117372900118820476546126571⟩
  | 1, 1 => ⟨1080217499394509926429384050967762537494240610, 1080217499394509926429384050967790635986032493⟩
  | 0, 3 => ⟨2977916314025528903247853362501280383979960620, 2977916314025528903247853362501330406009903037⟩
  | 1, 2 => ⟨4313468822569240789163859078607744437818525204, 4313468822569240789163859078607818474955546601⟩
  | 2, 1 => ⟨4330506794928338547701892528203871131411550801, 4330506794928338547701892528203991639649663481⟩
  | 0, 4 => ⟨6608131687218481801068620892196881603237621066, 6608131687218481801068620892197023686984659461⟩
  | 1, 3 => ⟨11164051165492308810153140172509933292156373351, 11164051165492308810153140172510151434623925429⟩
  | 2, 2 => ⟨15734387777485270512147352693132471393774713285, 15734387777485270512147352693132834826964785115⟩
  | 3, 1 => ⟨15788140133918565776440810200733794789362347758, 15788140133918565776440810200734418619282685096⟩
  | 0, 5 => ⟨-47046570150248338132473577734190361526538354762758, 47416148335734420378870825658956543002805668697790⟩
  | 1, 4 => ⟨-89138163112442819149695004838633767956422831364335, 89610041835365826674732101220274346837431869134523⟩
  | 2, 3 => ⟨-169500660927835517791219940543557186578341953162665, 170106848834087105637573876754348201970240928037093⟩
  | 3, 2 => ⟨-322796672158965232725087327811440066722382025601840, 323546532758982878836482118353812418094372100836211⟩
  | 4, 1 => ⟨-615027803257284532320296800911824080611660799639186, 615817868104497721241120775183388297985421965972210⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0193Geometry.ds, E8TAxisProd0193Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 178442915326946857451150144356078803129824963 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0193CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0194CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0194CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0194GraphCenterA.qJetBox,
   E8TAxisProd0194GraphCenterB.qJetBox,
   E8TAxisProd0194GraphCenterC.qJetBox,
   E8TAxisProd0194GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0194GraphWholeA.qJetBox,
   E8TAxisProd0194GraphWholeB.qJetBox,
   E8TAxisProd0194GraphWholeC.qJetBox,
   E8TAxisProd0194GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨182847004231315636643428142728230938491063541, 182847004231315636643428142728238184773615975⟩
  | 0, 2 => ⟨834328919973932120637399570130789947246401071, 834328919973932120637399570130806935660663077⟩
  | 1, 1 => ⟨838339218482429542431776045360625215053352691, 838339218482429542431776045360649665699454025⟩
  | 0, 3 => ⟨2350588120741026884867190033802173558831204650, 2350588120741026884867190033802216957600124541⟩
  | 1, 2 => ⟨3426985586358731188890673191972433853274828274, 3426985586358731188890673191972497078941382610⟩
  | 2, 1 => ⟨3440957202656434136655647247863266593102918093, 3440957202656434136655647247863368621056308061⟩
  | 0, 4 => ⟨5247308590035806919253546546055342235289079141, 5247308590035806919253546546055464013673312994⟩
  | 1, 3 => ⟨8983208882401089148383609305036025328167756805, 8983208882401089148383609305036209337684868085⟩
  | 2, 2 => ⟨12731289518226068239829049579499197188873150491, 12731289518226068239829049579499501037061705212⟩
  | 3, 1 => ⟨12775920859630603477016217598883770155365257867, 12775920859630603477016217598884288459082520594⟩
  | 0, 5 => ⟨-36759275686699903235759357165053237199104637172607, 37048534270230221379457247140762926477684093817211⟩
  | 1, 4 => ⟨-69363860159373380418109106360073731360907645694261, 69720070426049327924642109249571582447769239970090⟩
  | 2, 3 => ⟨-131420084840594002015649506928656907660102330665062, 131864086045209937479460106852981740945990206716408⟩
  | 3, 2 => ⟨-249400342972757875485654600735893941758258642837749, 249939781561622250731987467140591127271894630484796⟩
  | 4, 1 => ⟨-473512869751322443724965677017410895475772897446275, 474084853586674982781068701628026223670534981712894⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0194Geometry.ds, E8TAxisProd0194Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 133238632299260498474093791271414432729720567 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0194CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0195CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0195CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0195GraphCenterA.qJetBox,
   E8TAxisProd0195GraphCenterB.qJetBox,
   E8TAxisProd0195GraphCenterC.qJetBox,
   E8TAxisProd0195GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0195GraphWholeA.qJetBox,
   E8TAxisProd0195GraphWholeB.qJetBox,
   E8TAxisProd0195GraphWholeC.qJetBox,
   E8TAxisProd0195GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨136678227855352655309747745130810524009682979, 136678227855352655309747745130817060902227412⟩
  | 0, 2 => ⟨643323716955741207462318221775396244174557290, 643323716955741207462318221775411317177250696⟩
  | 1, 1 => ⟨646542747424886638392434399845599380833172292, 646542747424886638392434399845620753832936619⟩
  | 0, 3 => ⟨1846705838438761154220852218909948454525865523, 1846705838438761154220852218909986258317058461⟩
  | 1, 2 => ⟨2710827061603000349061257876781434398252543975, 2710827061603000349061257876781488586656082914⟩
  | 2, 1 => ⟨2722255864312075021301698211967914984043288370, 2722255864312075021301698211968001648911389766⟩
  | 0, 4 => ⟨4145716323503525159977206122183694332416671757, 4145716323503525159977206122183799157608263034⟩
  | 1, 3 => ⟨7201595387969456636973540181191075284161125358, 7201595387969456636973540181191231054320397181⟩
  | 2, 2 => ⟨10267757873175515463707261425690290683190183306, 10267757873175515463707261425690545494963148392⟩
  | 3, 1 => ⟨10304720995620531333054178432302758100431575848, 10304720995620531333054178432303189939018518324⟩
  | 0, 5 => ⟨-28870633900900465345416427731261250243037938832593, 29098482686309005340738431369934968009883992716701⟩
  | 1, 4 => ⟨-54238456300123434331896280874874632947900314612198, 54507204928138062177234467943781637045382309567140⟩
  | 2, 3 => ⟨-102361401052685157946117458170667805252565829741514, 102683689320431408011881649496842185236879445663712⟩
  | 3, 2 => ⟨-193524370943007884336992262967738631212353297176124, 193906541911973305084659917833323682571182724833677⟩
  | 4, 1 => ⟨-366035438489930856456153358600271792019058636051301, 366444477475510058028064305308735265550213867634123⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0195Geometry.ds, E8TAxisProd0195Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 98340446781584340834855093042142574863914764 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0195CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0196CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0196CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0196GraphCenterA.qJetBox,
   E8TAxisProd0196GraphCenterB.qJetBox,
   E8TAxisProd0196GraphCenterC.qJetBox,
   E8TAxisProd0196GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0196GraphWholeA.qJetBox,
   E8TAxisProd0196GraphWholeB.qJetBox,
   E8TAxisProd0196GraphWholeC.qJetBox,
   E8TAxisProd0196GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨103669706917887193343768940754188458598875379, 103669706917887193343768940754194404409369547⟩
  | 0, 2 => ⟨499831302553928277288848868596752136785655228, 499831302553928277288848868596765657369128125⟩
  | 1, 1 => ⟨505888527362998328872319635586959002105070634, 505888527362998328872319635586977895533391380⟩
  | 0, 3 => ⟨1459865135414405857987196329571776779040979395, 1459865135414405857987196329571810078222307144⟩
  | 1, 2 => ⟨2163081161028298698557721410513676879871809625, 2163081161028298698557721410513723842620475332⟩
  | 2, 1 => ⟨2185018898948411261395227925025655958233681973, 2185018898948411261395227925025730394896398773⟩
  | 0, 4 => ⟨3292692546542757314454336527342604355263229672, 3292692546542757314454336527342695718542161177⟩
  | 1, 3 => ⟨5815379148924486910385368121370777408672639261, 5815379148924486910385368121370910885868591325⟩
  | 2, 2 => ⟨8358456581390627996526623281981556278009897691, 8358456581390627996526623281981772564216849629⟩
  | 3, 1 => ⟨8430272660452127984832085355426200010814626352, 8430272660452127984832085355426564239354964710⟩
  | 0, 5 => ⟨-23074443995070919416435827722837970180937375091905, 23254660505203169836348936531689825466537630539247⟩
  | 1, 4 => ⟨-43156806665601334591779969278822951561072265662941, 43359284183542472672986871361888305760752134865310⟩
  | 2, 3 => ⟨-81129458470565855917732377761643815292338643591421, 81361399988229056256672382664904220498287763614052⟩
  | 3, 2 => ⟨-152809087131128019468356067049939341858573721630093, 153076436948706322294000902964660317707711800048954⟩
  | 4, 1 => ⟨-287937170158303392654565302839911363290483259956352, 288228427097136460203787383690545549639110034149389⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0196Geometry.ds, E8TAxisProd0196Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 73577355642863428797502625030578582586459718 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0196CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0197CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0197CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0197GraphCenterA.qJetBox,
   E8TAxisProd0197GraphCenterB.qJetBox,
   E8TAxisProd0197GraphCenterC.qJetBox,
   E8TAxisProd0197GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0197GraphWholeA.qJetBox,
   E8TAxisProd0197GraphWholeB.qJetBox,
   E8TAxisProd0197GraphWholeC.qJetBox,
   E8TAxisProd0197GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨75994353348717699223861824115124376601133575, 75994353348717699223861824115129757507951261⟩
  | 0, 2 => ⟨379826020759937627119403825426633603202203877, 379826020759937627119403825426645687557892966⟩
  | 1, 1 => ⟨384643831275085141359686288585586218741067536, 384643831275085141359686288585602856958632734⟩
  | 0, 3 => ⟨1134858458289897954899114938898261056275549598, 1134858458289897954899114938898290257607797431⟩
  | 1, 2 => ⟨1694385639825995367499074320450751372769822357, 1694385639825995367499074320450791867941182911⟩
  | 2, 1 => ⟨1712240208847407702807836471308765219774884292, 1712240208847407702807836471308828797310024476⟩
  | 0, 4 => ⟨2573722539438929675080818704881123171334071950, 2573722539438929675080818704881202655234672437⟩
  | 1, 3 => ⟨4626643297545541698331842017609238504252277748, 4626643297545541698331842017609352643264464227⟩
  | 2, 2 => ⟨6696777854445947206089054249662323122238388910, 6696777854445947206089054249662506283492710681⟩
  | 3, 1 => ⟨6756006845001572074425510800472263304851658056, 6756006845001572074425510800472569796432298858⟩
  | 0, 5 => ⟨-18387367571928276727134881010889041907276518393066, 18529277613130029287689663622884591954763853834971⟩
  | 1, 4 => ⟨-34220983622368711624569624493576580499845865511447, 34371004349550033880932405850739790593766258909990⟩
  | 2, 3 => ⟨-64050109837407298143580261435877186092153131962447, 64210934386585747328203215012983434993465020231450⟩
  | 3, 2 => ⟨-120129871747470714819811406993564451834129507302236, 120306267324802857541874541389843509287863319810279⟩
  | 4, 1 => ⟨-225388327285108390015110134678397578068628141488319, 225583778131825992820084917847179368784091169936816⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0197Geometry.ds, E8TAxisProd0197Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 52804132073305514801276670968955474884151686 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0197CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0198CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0198CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0198GraphCenterA.qJetBox,
   E8TAxisProd0198GraphCenterB.qJetBox,
   E8TAxisProd0198GraphCenterC.qJetBox,
   E8TAxisProd0198GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0198GraphWholeA.qJetBox,
   E8TAxisProd0198GraphWholeB.qJetBox,
   E8TAxisProd0198GraphWholeC.qJetBox,
   E8TAxisProd0198GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨102424682176592050031116861041146571842672430, 102424682176592050031116861041152498564043697⟩
  | 0, 2 => ⟨496191911365398961860244116978916932770714323, 496191911365398961860244116978930405919676989⟩
  | 1, 1 => ⟨500498964150564227832639965420259149585725330, 500498964150564227832639965420277974443254547⟩
  | 0, 3 => ⟨1451655012116679041837198328043006295304261834, 1451655012116679041837198328043039466373480873⟩
  | 1, 2 => ⟨2148582739651107610125574832792876369895653819, 2148582739651107610125574832792923143119066205⟩
  | 2, 1 => ⟨2164188554803813020845101409071966308337692919, 2164188554803813020845101409072040433242638642⟩
  | 0, 4 => ⟨3275420441693247004857960279698782115163656449, 3275420441693247004857960279698873110035159629⟩
  | 1, 3 => ⟨5783385378922335835840187169970287267100117898, 5783385378922335835840187169970420183967173209⟩
  | 2, 2 => ⟨8305865852217634117073414080421952579762102935, 8305865852217634117073414080422167919840158904⟩
  | 3, 1 => ⟨8356966651546626252254253679539702501966340144, 8356966651546626252254253679540065078028523150⟩
  | 0, 5 => ⟨-22940743827715971537456937495550281448851919477143, 23120124147081549950899564017725317200718684323626⟩
  | 1, 4 => ⟨-42900950498608179865298140728452356996030290892207, 43102279808781716165829743096545778575989206668462⟩
  | 2, 3 => ⟨-80637799783092105891199575580853711405788965851800, 80868072265644945944877397653664580396522509404086⟩
  | 3, 2 => ⟨-151862168246209028022561301608685617010002713679200, 152127100841914994721560062768619310673247001015470⟩
  | 4, 1 => ⟨-286111078971902320039451128088480760925604194157718, 286399257356169863825714526273260199940133844844289⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0198Geometry.ds, E8TAxisProd0198Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 72595364764534507807535426970152182104355978 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0198CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0199CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0199CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0199GraphCenterA.qJetBox,
   E8TAxisProd0199GraphCenterB.qJetBox,
   E8TAxisProd0199GraphCenterC.qJetBox,
   E8TAxisProd0199GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0199GraphWholeA.qJetBox,
   E8TAxisProd0199GraphWholeB.qJetBox,
   E8TAxisProd0199GraphWholeC.qJetBox,
   E8TAxisProd0199GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨75048328035941517794060031596921138732082584, 75048328035941517794060031596926502373386679⟩
  | 0, 2 => ⟨376996903350394683126537859980990004950908185, 376996903350394683126537859981002047543665771⟩
  | 1, 1 => ⟨380422298744509867396475534665739227287929883, 380422298744509867396475534665755806143165825⟩
  | 0, 3 => ⟨1128441120906003241922122738349529410675074240, 1128441120906003241922122738349558500727186589⟩
  | 1, 2 => ⟨1682851047291672213850969815046353000473267474, 1682851047291672213850969815046393333928112662⟩
  | 2, 1 => ⟨1695551533384772690520407713401704465556785805, 1695551533384772690520407713401767779594415516⟩
  | 0, 4 => ⟨2560158786459838337886164138709254215314558398, 2560158786459838337886164138709333389267239919⟩
  | 1, 3 => ⟨4601052909061224281168630633455556597375965709, 4601052909061224281168630633455670275376222925⟩
  | 2, 2 => ⟨6654201029672297139208073599664907196656101412, 6654201029672297139208073599665089587968869984⟩
  | 3, 1 => ⟨6696343902699207775473576334891437465559232169, 6696343902699207775473576334891742622348349434⟩
  | 0, 5 => ⟨-18282155430612599525563945232771429702014545719350, 18423526350010472604383813710403037927941293835782⟩
  | 1, 4 => ⟨-34020226198877203454465683401420303948284598167081, 34169558807977777181580024207597956538671245719787⟩
  | 2, 3 => ⟨-63665247125092668076838485610779676884382423083609, 63825110568335514200236140144873459042246574530435⟩
  | 3, 2 => ⟨-119390205829153533461753964102090381622630698707305, 119565248712069019268977349747387826513277903574189⟩
  | 4, 1 => ⟨-223964740659700160035142195682588058916223732212740, 224158631781628120414380735015980008994584104655697⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0199Geometry.ds, E8TAxisProd0199Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 52063991214687139536358394973718615076988994 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0199CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0200CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0200CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0200GraphCenterA.qJetBox,
   E8TAxisProd0200GraphCenterB.qJetBox,
   E8TAxisProd0200GraphCenterC.qJetBox,
   E8TAxisProd0200GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0200GraphWholeA.qJetBox,
   E8TAxisProd0200GraphWholeB.qJetBox,
   E8TAxisProd0200GraphWholeC.qJetBox,
   E8TAxisProd0200GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨55038150839966359049114457265347886668767006, 55038150839966359049114457265352761640774044⟩
  | 0, 2 => ⟨286081124312915296269914405198754607971460455, 286081124312915296269914405198765446273427663⟩
  | 1, 1 => ⟨289891573370903726113158944738319940096992990, 289891573370903726113158944738334646046206961⟩
  | 0, 3 => ⟨876792079325396787063924999494274336617480446, 876792079325396787063924999494300023172907133⟩
  | 1, 2 => ⟨1319510103910226119127867669604980275639809766, 1319510103910226119127867669605015293970813302⟩
  | 2, 1 => ⟨1334000067595937719016551429739714613341933499, 1334000067595937719016551429739769056011102280⟩
  | 0, 4 => ⟨1999982211993000187128070588993885817991030651, 1999982211993000187128070588993955357295374322⟩
  | 1, 3 => ⟨3665817004515797245917200248304931389104949683, 3665817004515797245917200248305029549615986463⟩
  | 2, 2 => ⟨5346190944866876870404490210268779712171760040, 5346190944866876870404490210268935709645197330⟩
  | 3, 1 => ⟨5394953650509457140987647668290649518993547555, 5394953650509457140987647668290908968599413292⟩
  | 0, 5 => ⟨-14727049108797348033119328857972553514175468248272, 14839653352571174026035980579358157697067133081522⟩
  | 1, 4 => ⟨-27265183519580102810009642925044936262933514331113, 27376126392017256556205303296164601084315789007744⟩
  | 2, 3 => ⟨-50794152315900153159022851219297172184810709574451, 50903038033167334721088845546043891134766671382185⟩
  | 3, 2 => ⟨-94838114449516469184572124241615584931164375167999, 94948788693519794884815857117926804739129220714339⟩
  | 4, 1 => ⟨-177117107987668032631244758683009070222611829780089, 177243045104466998366695686120559126405012537418434⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0200Geometry.ds, E8TAxisProd0200Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 37220676900040908278300147930330237524914185 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0200CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0201CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0201CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0201GraphCenterA.qJetBox,
   E8TAxisProd0201GraphCenterB.qJetBox,
   E8TAxisProd0201GraphCenterC.qJetBox,
   E8TAxisProd0201GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0201GraphWholeA.qJetBox,
   E8TAxisProd0201GraphWholeB.qJetBox,
   E8TAxisProd0201GraphWholeC.qJetBox,
   E8TAxisProd0201GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨39317817900344618505095053659928190648324136, 39317817900344618505095053659932610588266321⟩
  | 0, 2 => ⟨213302939108250217534509473143116583117768545, 213302939108250217534509473143126337086218786⟩
  | 1, 1 => ⟨216297087332253865731565337507725319955003745, 216297087332253865731565337507738366495638318⟩
  | 0, 3 => ⟨672744090524826292020899655882611815918914098, 672744090524826292020899655882634468223891922⟩
  | 1, 2 => ⟨1020786848546985661817826780070660011580324558, 1020786848546985661817826780070690361491658522⟩
  | 2, 1 => ⟨1032508860453723028545310141789328647900224761, 1032508860453723028545310141789375350596485509⟩
  | 0, 4 => ⟨1544398344594977435569763136005151823036331098, 1544398344594977435569763136005212849844728005⟩
  | 1, 3 => ⟨2891805276474516579307583116331080675329706894, 2891805276474516579307583116331165298845041622⟩
  | 2, 2 => ⟨4251501821837137766931959933889954614716333596, 4251501821837137766931959933890087717666547859⟩
  | 3, 1 => ⟨4291586231877642187168917406068738670026667037, 4291586231877642187168917406068958641575885611⟩
  | 0, 5 => ⟨-12151503244275646129312478987428750751140189913082, 12236721971197582155946795432855749303913988416279⟩
  | 1, 4 => ⟨-22387791216126011690680537258976971410823394898015, 22461989675634430653776211853141649416090971283247⟩
  | 2, 3 => ⟨-41523197546724076292302893353928185792391007048452, 41583023761707681128869788179237320112634934001541⟩
  | 3, 2 => ⟨-77187306309168991705396874606309524183312575562583, 77235897334686876763847285347573828771380058743242⟩
  | 4, 1 => ⟨-143492183786202713195662659282081685035098140767266, 143553107970905801926568606755856267799180684166644⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0201Geometry.ds, E8TAxisProd0201Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 25511423292182120685379359826835677926045832 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0201CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0202CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0202CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0202GraphCenterA.qJetBox,
   E8TAxisProd0202GraphCenterB.qJetBox,
   E8TAxisProd0202GraphCenterC.qJetBox,
   E8TAxisProd0202GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0202GraphWholeA.qJetBox,
   E8TAxisProd0202GraphWholeB.qJetBox,
   E8TAxisProd0202GraphWholeC.qJetBox,
   E8TAxisProd0202GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨54325682803039390707479221566116316997735735, 54325682803039390707479221566121176299099011⟩
  | 0, 2 => ⟨283895383030733042139965584459442566333302589, 283895383030733042139965584459453367753206423⟩
  | 1, 1 => ⟨286604232543995426451480847182516865525691262, 286604232543995426451480847182531519948899725⟩
  | 0, 3 => ⟨871805352094151901518651998603000970095196762, 871805352094151901518651998603026559178349959⟩
  | 1, 2 => ⟨1310371044577670418666090927698998688655159545, 1310371044577670418666090927699033567699891906⟩
  | 2, 1 => ⟨1320677570432639480775024809191796206839608294, 1320677570432639480775024809191850424487011723⟩
  | 0, 4 => ⟨1989408590798817448622295268913433909115319888, 1989408590798817448622295268913503179350492903⟩
  | 1, 3 => ⟨3645448288846001176591792057045776410203647033, 3645448288846001176591792057045874176755287603⟩
  | 2, 2 => ⟨5311838113319217563786200086373352712779465312, 5311838113319217563786200086373508056635597446⟩
  | 3, 1 => ⟨5346532838129556796785657409089401866583591755, 5346532838129556796785657409089660187479937249⟩
  | 0, 5 => ⟨-14643908141064791957387655802622462516287587032931, 14756182110512484835771585984046435238454058624132⟩
  | 1, 4 => ⟨-27107027871165315556612703453296773516868415765286, 27217602497022634565381156073907797720078796999339⟩
  | 2, 3 => ⟨-50491717371754251362795720722604338635467082458187, 50600130146171024984346439366108052823462230320639⟩
  | 3, 2 => ⟨-94258149392014957381983986491628047500208186159268, 94368197486475612139300914167049733702659768680252⟩
  | 4, 1 => ⟨-176003186064146032634241879617090542531783940243523, 176128576390763853518700217004682043966434480192519⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0202Geometry.ds, E8TAxisProd0202Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 36668897684142332849853504938701347568354558 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0202CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0203CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0203CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0203GraphCenterA.qJetBox,
   E8TAxisProd0203GraphCenterB.qJetBox,
   E8TAxisProd0203GraphCenterC.qJetBox,
   E8TAxisProd0203GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0203GraphWholeA.qJetBox,
   E8TAxisProd0203GraphWholeB.qJetBox,
   E8TAxisProd0203GraphWholeC.qJetBox,
   E8TAxisProd0203GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨38786658861318226300823284535842590847082088, 38786658861318226300823284535846996515491168⟩
  | 0, 2 => ⟨211625896597723365309143107329857431658083563, 211625896597723365309143107329867152957161389⟩
  | 1, 1 => ⟨213754140276841497502961361420914437471623911, 213754140276841497502961361420927439169098358⟩
  | 0, 3 => ⟨668893325094607285073112123127607788383637577, 668893325094607285073112123127630355016591784⟩
  | 1, 2 => ⟨1013577517091176512297861895150816586443120810, 1013577517091176512297861895150846816063628978⟩
  | 2, 1 => ⟨1021914669787171066169181403241253873436679359, 1021914669787171066169181403241300383552974271⟩
  | 0, 4 => ⟨1536221066190857619469574433170943183410211496, 1536221066190857619469574433171003976029899539⟩
  | 1, 3 => ⟨2875674129628234911607182280912967669670059992, 2875674129628234911607182280913051955965104351⟩
  | 2, 2 => ⟨4223876072563477253827727252459918319371152413, 4223876072563477253827727252460050866773782839⟩
  | 3, 1 => ⟨4252395360030928279457864090833131532611132050, 4252395360030928279457864090833350548718620019⟩
  | 0, 5 => ⟨-12090174108805835709569609090126808634603851887321, 12175132898329919022314796837580635554333830185885⟩
  | 1, 4 => ⟨-22271426827155132935568282909551792166476046589578, 22345357280944310328810316995215613653482746786846⟩
  | 2, 3 => ⟨-41300972232645871364619651131354828425314486931884, 41360482555030575286341455189651171114417667161573⟩
  | 3, 2 => ⟨-76761400418018444510240037540457705524276139096532, 76809638412529451622695589106199112259775019485740⟩
  | 4, 1 => ⟨-142674220789962780061868035984365158629107754847570, 142735117780105515970883615475920741839479269289149⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0203Geometry.ds, E8TAxisProd0203Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 25102801988868345582485079585067579397790590 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0203CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0204CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0204CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0204GraphCenterA.qJetBox,
   E8TAxisProd0204GraphCenterB.qJetBox,
   E8TAxisProd0204GraphCenterC.qJetBox,
   E8TAxisProd0204GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0204GraphWholeA.qJetBox,
   E8TAxisProd0204GraphWholeB.qJetBox,
   E8TAxisProd0204GraphWholeC.qJetBox,
   E8TAxisProd0204GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨101188730301556360395476088795439128986167311, 101188730301556360395476088795445036675917674⟩
  | 0, 2 => ⟨492572991599372210665016299099677522927122938, 492572991599372210665016299099690948814395985⟩
  | 1, 1 => ⟨495145547182253584785301562682003409511688742, 495145547182253584785301562682022166059824516⟩
  | 0, 3 => ⟨1443487961618746604231148291211845519974577387, 1443487961618746604231148291211878563418238444⟩
  | 1, 2 => ⟨2134164097325332031309248211621269249498979311, 2134164097325332031309248211621315833944637122⟩
  | 2, 1 => ⟨2143489334670978658340665206565699185159176967, 2143489334670978658340665206565772999569855805⟩
  | 0, 4 => ⟨3258234241529876081805109469568141615992749072, 3258234241529876081805109469568232243965222936⟩
  | 1, 3 => ⟨5751555779055511289268453480179908420431787655, 5751555779055511289268453480180040779340557510⟩
  | 2, 2 => ⟨8253557142855387029925825969803144304645686534, 8253557142855387029925825969803358702671624013⟩
  | 3, 1 => ⟨8284100217247117132290203296037706850018478451, 8284100217247117132290203296038067780844108851⟩
  | 0, 5 => ⟨-22807813897755546412154015818405255712345643095675, 22987087789946768823703338367860613574356281528430⟩
  | 1, 4 => ⟨-42646584032763053307268583798009772389695295090904, 42847644206655075060806177219376619145352913358786⟩
  | 2, 3 => ⟨-80149031282173438431129856544660059082515389366202, 80378522292120533845498969835406894931669213255710⟩
  | 3, 2 => ⟨-150920866934849337455752753364270042441019159525054, 151183995376029167578985323260016339688949861439711⟩
  | 4, 1 => ⟨-284295919013494246827055708358860053572465976028055, 284581077458397324673690481192657978442144301564190⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0204Geometry.ds, E8TAxisProd0204Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 71620744229855466862931715874063456632491073 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0204CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0205CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0205CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0205GraphCenterA.qJetBox,
   E8TAxisProd0205GraphCenterB.qJetBox,
   E8TAxisProd0205GraphCenterC.qJetBox,
   E8TAxisProd0205GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0205GraphWholeA.qJetBox,
   E8TAxisProd0205GraphWholeB.qJetBox,
   E8TAxisProd0205GraphWholeC.qJetBox,
   E8TAxisProd0205GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨74109355497787578932317529752998936141597148, 74109355497787578932317529753004282568308084⟩
  | 0, 2 => ⟨374183786968868581739880090066533738806013604, 374183786968868581739880090066545739786460397⟩
  | 1, 1 => ⟨376229522863760505401955143660176311316934029, 376229522863760505401955143660192831034009098⟩
  | 0, 3 => ⟨1122057607395230003651162329193932439238405039, 1122057607395230003651162329193961418424859670⟩
  | 1, 2 => ⟨1671380264649803756915075996889240548354018498, 1671380264649803756915075996889280720717933363⟩
  | 2, 1 => ⟨1678969011606047237397764147889698924637064093, 1678969011606047237397764147889761976225300040⟩
  | 0, 4 => ⟨2546663388368793684765654676123091008012349065, 2546663388368793684765654676123169873235066475⟩
  | 1, 3 => ⟨4575595277732090891992091621344626693467626172, 4575595277732090891992091621344739912315082880⟩
  | 2, 2 => ⟨6611854716666583539421518392419213986321890381, 6611854716666583539421518392419395610838180876⟩
  | 3, 1 => ⟨6637042679324982451105079001886158521091017593, 6637042679324982451105079001886462348606631268⟩
  | 0, 5 => ⟨-18177543195878547335866116354754191789547356858781, 18318950878603761255734987205725090314434476214255⟩
  | 1, 4 => ⟨-33820626608764623930549744582256241491158334659467, 33969964313219132694352209135516019224213199291322⟩
  | 2, 3 => ⟨-63282626872570269264497325853654054970382975608208, 63442228028516748848254123457723108540562457132203⟩
  | 3, 2 => ⟨-118654891910779463878590920992456996290394388306105, 118829062076609559970648398229346727955129339209984⟩
  | 4, 1 => ⟨-222549610709281248613402405240222763806585268632941, 222741980393202114168827429834204916680121318910715⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0205Geometry.ds, E8TAxisProd0205Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 51329558727197614137719751361658389110682836 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0205CertifiedArithmetic

end


