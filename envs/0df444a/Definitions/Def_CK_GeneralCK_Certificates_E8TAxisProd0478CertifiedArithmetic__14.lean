-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0478CertifiedArithmetic__14
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0478CertifiedArithmetic__14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:51:48.319044+00:00
-- url     : https://prove2.me/theorems/6dedea67-1cf9-4136-81fc-3cf1044a6fcf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0478CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0479CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0478CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0479CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0480CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0481CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0482CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0483CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0484CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0485CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0486CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0487CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0488CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0489CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0490CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0491CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0478CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0479CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0480CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0481CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0482CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0483CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0484CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0485CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0486CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0487CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0488CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0489CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0490CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0491CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0478CertifiedArithmetic (+13 modules: GeneralCK.Certificates.E8TAxisProd0479CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0480CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0481CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0482CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0483CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0484CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0485CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0486CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0487CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0488CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0489CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0490CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0491CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0478CertifiedArithmetic (+13 modules: GeneralCK/Certificates/E8TAxisProd0479CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0480CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0481CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0482CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0483CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0484CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0485CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0486CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0487CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0488CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0489CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0490CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0491CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0470GraphCenterA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0476GraphCenterB__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0476GraphCenterC__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0469GraphCenterD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0478GraphWholeA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0476GraphWholeB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0471GraphWholeC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0477GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0471Geometry__23
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0479GraphCenterD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0482GraphWholeC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0483GraphCenterA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0484GraphCenterB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0486GraphCenterC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0489GraphWholeA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0489GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0490GraphCenterD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0490GraphWholeD__15

-- ===== source module GeneralCK.Certificates.E8TAxisProd0478CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0478CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0478GraphCenterA.qJetBox,
   E8TAxisProd0478GraphCenterB.qJetBox,
   E8TAxisProd0478GraphCenterC.qJetBox,
   E8TAxisProd0478GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0478GraphWholeA.qJetBox,
   E8TAxisProd0478GraphWholeB.qJetBox,
   E8TAxisProd0478GraphWholeC.qJetBox,
   E8TAxisProd0478GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8901967533621552169107537944146481651144321746, 8901967533621552169107537944146539899829688634⟩
  | 0, 2 => ⟨29164659329931505214554166341383931208739146240, 29164659329931505214554166341384132980791566621⟩
  | 1, 1 => ⟨29530891830312784308302707754048608549489881748, 29530891830312784308302707754048960386672112797⟩
  | 0, 3 => ⟨65432187968562018418190582702704214959700291620, 65432187968562018418190582702704849236945032650⟩
  | 1, 2 => ⟨89362926426909128918743173665751335162497088284, 89362926426909128918743173665752438566904739111⟩
  | 2, 1 => ⟨90346205359902946642061703308303259522949308550, 90346205359902946642061703308305225917087167185⟩
  | 0, 4 => ⟨121598123164263513960959014203257804587428218705, 121598123164263513960959014203259892018205475322⟩
  | 1, 3 => ⟨185160440072768359723469064682543481738427296096, 185160440072768359723469064682547186417166632364⟩
  | 2, 2 => ⟨249270384074757868880264383068119389206335599908, 249270384074757868880264383068126102842687509640⟩
  | 3, 1 => ⟨251629057644735529527462248616564896497776433333, 251629057644735529527462248616577186115051416561⟩
  | 0, 5 => ⟨-336677463336987998275194420477832812654527760379019, 338902090818998595917458636836825608191873533152609⟩
  | 1, 4 => ⟨-653719527488141368338243756234795080449170243580178, 657019964553640559994538756147754194167184675899598⟩
  | 2, 3 => ⟨-1271167969686963176534406519638611856755487218413411, 1275876463995258532357290638878095649750406806293934⟩
  | 3, 2 => ⟨-2473903403362589715380268483185883170158752711218762, 2480051994860598942800739461014601240409558954211233⟩
  | 4, 1 => ⟨-4817334115250340167889119143820901505353246537938770, 4823622379281901859439273832182956680586141657168491⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0478Geometry.ds, E8TAxisProd0478Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 8314743716374313547574113115191731521530317132 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0478CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0479CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0479CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0479GraphCenterA.qJetBox,
   E8TAxisProd0479GraphCenterB.qJetBox,
   E8TAxisProd0479GraphCenterC.qJetBox,
   E8TAxisProd0479GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0479GraphWholeA.qJetBox,
   E8TAxisProd0479GraphWholeB.qJetBox,
   E8TAxisProd0479GraphWholeC.qJetBox,
   E8TAxisProd0479GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7897138581782387324557799952767796622429942184, 7897138581782387324557799952767849877307544195⟩
  | 0, 2 => ⟨26109445861396902649907909569139410742352180147, 26109445861396902649907909569139592842346836395⟩
  | 1, 1 => ⟨26441827442962596475671867390667635002456265668, 26441827442962596475671867390667951120670045034⟩
  | 0, 3 => ⟨59071183119562259519978409541599687995245776775, 59071183119562259519978409541600258120390749376⟩
  | 1, 2 => ⟨80794608982278701537487003608967721280868094529, 80794608982278701537487003608968709471531040582⟩
  | 2, 1 => ⟨81696232240474015083454382929556622493701309210, 81696232240474015083454382929558379479300742395⟩
  | 0, 4 => ⟨110767064641527853541369094409769665374557449030, 110767064641527853541369094409771536482270460103⟩
  | 1, 3 => ⟨169055584598346364324099601525777325460162591050, 169055584598346364324099601525780636675857311996⟩
  | 2, 2 => ⟨227853930072869159999169545895932781786204094063, 227853930072869159999169545895938771223703180348⟩
  | 3, 1 => ⟨230041464637980956878952211857092232008859241723, 230041464637980956878952211857103178856543922138⟩
  | 0, 5 => ⟨-288828150587667302595693757049268461169685880162181, 290792878007404031807555100916422659036164174604011⟩
  | 1, 4 => ⟨-560205517021120023973974192506659317406560169212363, 563114492691636170124686178142556266954135910716840⟩
  | 2, 3 => ⟨-1088246516309800573291564718231844226131640681900538, 1092391331868204002320480695188257116673958277245801⟩
  | 3, 2 => ⟨-2115885292172614819589454351520852832116520825210951, 2121294745593272897778604226700532375842926199678807⟩
  | 4, 1 => ⟨-4116304299587056583344505903206135991046021298284068, 4121838998972935808870538385038953084270031848454319⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0479Geometry.ds, E8TAxisProd0479Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7372118898984243489634191667114979389162432258 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0479CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0480CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0480CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0480GraphCenterA.qJetBox,
   E8TAxisProd0480GraphCenterB.qJetBox,
   E8TAxisProd0480GraphCenterC.qJetBox,
   E8TAxisProd0480GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0480GraphWholeA.qJetBox,
   E8TAxisProd0480GraphWholeB.qJetBox,
   E8TAxisProd0480GraphWholeC.qJetBox,
   E8TAxisProd0480GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17783012170161592318278595498916585611347213852, 17783012170161592318278595498916686844663539766⟩
  | 0, 2 => ⟨55247528537051780754279941181919028892370117001, 55247528537051780754279941181919404912768839856⟩
  | 1, 1 => ⟨55837425985555478576528347722629717939970972503, 55837425985555478576528347722630388986155176580⟩
  | 0, 3 => ⟨117834068262459840789520528702875180425949708827, 117834068262459840789520528702876390507822831121⟩
  | 1, 2 => ⟨159616470100151275649626296966688122762322410313, 159616470100151275649626296966690268637764397164⟩
  | 2, 1 => ⟨161107854210214178099659568485938900220264789319, 161107854210214178099659568485942774145846425299⟩
  | 0, 4 => ⟨207817332447985669393971643508173097986727350494, 207817332447985669393971643508177162546513573519⟩
  | 1, 3 => ⟨312485489604113966194263461732034678559735283892, 312485489604113966194263461732042001290195523705⟩
  | 2, 2 => ⟨417919706895961389334330643361767412460870995823, 417919706895961389334330643361780819231278929178⟩
  | 3, 1 => ⟨421289091666987289690037265650432676630079074211, 421289091666987289690037265650457436522433133394⟩
  | 0, 5 => ⟨-783658979576207075276121725248839614156476433890214, 788251141712030575136928340974500076033902479812725⟩
  | 1, 4 => ⟨-1529576564407403324748725083114172835940624249508903, 1536461249086219038856996662765292644498450398394462⟩
  | 2, 3 => ⟨-2988850496624616978097642381578812726613967267108861, 2998740787111396500580604348377712455267240639536388⟩
  | 3, 2 => ⟨-5844471898950651104870187789075352869472138909931650, 5857435805278150580128310391964345925461818116089363⟩
  | 4, 1 => ⟨-11434354721977036255874309394669031784965809579916384, 11447614481544292639306902217544549661337431493361711⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0480Geometry.ds, E8TAxisProd0480Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16663517948588966684752408613099624799789204226 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0480CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0481CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0481CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0481GraphCenterA.qJetBox,
   E8TAxisProd0481GraphCenterB.qJetBox,
   E8TAxisProd0481GraphCenterC.qJetBox,
   E8TAxisProd0481GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0481GraphWholeA.qJetBox,
   E8TAxisProd0481GraphWholeB.qJetBox,
   E8TAxisProd0481GraphWholeC.qJetBox,
   E8TAxisProd0481GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨15877198801484557720497569134591656074818525547, 15877198801484557720497569134591748196723927674⟩
  | 0, 2 => ⟨49773769793195178692868491489601379725080302283, 49773769793195178692868491489601718223027651569⟩
  | 1, 1 => ⟨50312194720427963862438203814708215614011272223, 50312194720427963862438203814708817599033934555⟩
  | 0, 3 => ⟨107069314913547821719105210940690057244115609465, 107069314913547821719105210940691142174339288758⟩
  | 1, 2 => ⟨145212584477849444107960049958587680715439384086, 145212584477849444107960049958589598988467249161⟩
  | 2, 1 => ⟨146587171829863122579418046867688738196860604714, 146587171829863122579418046867692194053338054367⟩
  | 0, 4 => ⟨190443671153711012529980662887091203264748975622, 190443671153711012529980662887094832054326513876⟩
  | 1, 3 => ⟨286920066808354806855033461874522442514106093845, 286920066808354806855033461874528964846756004011⟩
  | 2, 2 => ⟨384111180655457011334571801639582384763425535846, 384111180655457011334571801639594306264184932950⟩
  | 3, 1 => ⟨387244508951606442347267129960393743374266805711, 387244508951606442347267129960415727958910210100⟩
  | 0, 5 => ⟨-686723556571392775159854477430284431712877422147909, 690800737360740463879779635984737547805078263822546⟩
  | 1, 4 => ⟨-1339381752632623766080175580170744805243152838881366, 1345484453016262963639361244458630955641138718934664⟩
  | 2, 3 => ⟨-2615362925301923194422156235610437634739581001835893, 2624119979937158982578713994294034506211600639260690⟩
  | 3, 2 => ⟨-5110623016014046102569893406758185671522357929357379, 5122093566548936694419996212331570064148597632380978⟩
  | 4, 1 => ⟨-9991767137204748918868373516213129901748664865415275, 10003495369095909424374429112416859062089066277870760⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0481Geometry.ds, E8TAxisProd0481Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 14869680830127601767270316267003516028697690584 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0481CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0482CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0482CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0482GraphCenterA.qJetBox,
   E8TAxisProd0482GraphCenterB.qJetBox,
   E8TAxisProd0482GraphCenterC.qJetBox,
   E8TAxisProd0482GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0482GraphWholeA.qJetBox,
   E8TAxisProd0482GraphWholeB.qJetBox,
   E8TAxisProd0482GraphWholeC.qJetBox,
   E8TAxisProd0482GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17714044749739789897726952222232232571657158061, 17714044749739789897726952222232333598464585157⟩
  | 0, 2 => ⟨55100398204852429577013033155842798847178082546, 55100398204852429577013033155843174038660698955⟩
  | 1, 1 => ⟨55638149363746331770293316374121248474462486004, 55638149363746331770293316374121918017343602132⟩
  | 0, 3 => ⟨117574546550535156019125536130520461323507636117, 117574546550535156019125536130521668695844080355⟩
  | 1, 2 => ⟨159226255515013040690856331856890361529740820838, 159226255515013040690856331856892502537675434009⟩
  | 2, 1 => ⟨160586031354322494057081832909516405369081498110, 160586031354322494057081832909520270410200475920⟩
  | 0, 4 => ⟨207417521070961308310788580776624199800201324354, 207417521070961308310788580776628254931520658004⟩
  | 1, 3 => ⟨311858031032671328711704070384334118113990881787, 311858031032671328711704070384341423749911306538⟩
  | 2, 2 => ⟨416997143880319306600847560830210736090077614811, 416997143880319306600847560830224111357799271328⟩
  | 3, 1 => ⟨420069658853845208505039229330420095416716453502, 420069658853845208505039229330444796716036016675⟩
  | 0, 5 => ⟨-781607956437275545114895928834452185369996758195206, 786189562624283908502018635369406529780435237013865⟩
  | 1, 4 => ⟨-1525554346656105876767074380794735594621795801911108, 1532423033887295229662060535500477221734455299295013⟩
  | 2, 3 => ⟨-2980953556095419933012634040697331036404852469349442, 2990820693395549892059651640289790992838513162499442⟩
  | 3, 2 => ⟨-5828955539765033362197514240518750708681335538564826, 5841888653391995210952043339739373647269366003363757⟩
  | 4, 1 => ⟨-11403849334984608602510893359158581608218605924030553, 11417075592463447509111266974010243067602854827438236⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0482Geometry.ds, E8TAxisProd0482Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16598455486241297745763903018431794967223724185 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0482CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0483CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0483CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0483GraphCenterA.qJetBox,
   E8TAxisProd0483GraphCenterB.qJetBox,
   E8TAxisProd0483GraphCenterC.qJetBox,
   E8TAxisProd0483GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0483GraphWholeA.qJetBox,
   E8TAxisProd0483GraphWholeB.qJetBox,
   E8TAxisProd0483GraphWholeC.qJetBox,
   E8TAxisProd0483GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨15815065175182014170560576702526255302317769968, 15815065175182014170560576702526347236896038241⟩
  | 0, 2 => ⟨49640081837498018115587407879796514672742928321, 49640081837498018115587407879796852424031207183⟩
  | 1, 1 => ⟨50130902994857063228854297910119894349792501916, 50130902994857063228854297910120494984138123787⟩
  | 0, 3 => ⟨106831491107407380990966110133376916472354279826, 106831491107407380990966110133377998969174181877⟩
  | 1, 2 => ⟨144854297402683047381397977546903820966058409555, 144854297402683047381397977546905734877106829165⟩
  | 2, 1 => ⟨146107567439853726748716672348151336995326830942, 146107567439853726748716672348154784902220193772⟩
  | 0, 4 => ⟨190074524745205829176086285985711455900651311269, 190074524745205829176086285985715076248808656640⟩
  | 1, 3 => ⟨286339424741239495777922074958601757856258291283, 286339424741239495777922074958608264910761448431⟩
  | 2, 2 => ⟨383256105054815233574532713961057021595912264264, 383256105054815233574532713961068914974381569431⟩
  | 3, 1 => ⟨386113349325672189827118307923434337371991021412, 386113349325672189827118307923456269703808080516⟩
  | 0, 5 => ⟨-684875541432546976563129943186051061533967088939417, 688943338114908608986353489934635478358787363441272⟩
  | 1, 4 => ⟨-1335759394576453985381599608308462787506405394236792, 1341847920293445691161355172028839331987848524429199⟩
  | 2, 3 => ⟨-2608254384003449973003155542728820184499839347387265, 2616991016717402768708700888098952321291623258897711⟩
  | 3, 2 => ⟨-5096662269122750494693367097858826729682105377027221, 5108105866530682727818306277833498104315396599941629⟩
  | 4, 1 => ⟨-9964332951783752487566236656009691534268989990073592, 9976032406653654656160686269395685064444488585201496⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0483Geometry.ds, E8TAxisProd0483Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 14811098994919990684490914054773076385475175615 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0483CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0484CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0484CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0484GraphCenterA.qJetBox,
   E8TAxisProd0484GraphCenterB.qJetBox,
   E8TAxisProd0484GraphCenterC.qJetBox,
   E8TAxisProd0484GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0484GraphWholeA.qJetBox,
   E8TAxisProd0484GraphWholeB.qJetBox,
   E8TAxisProd0484GraphWholeC.qJetBox,
   E8TAxisProd0484GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨14160830151768531183409426129433184098816853908, 14160830151768531183409426129433267988533753221⟩
  | 0, 2 => ⟨44796356011937280299230121627598280221080137884, 44796356011937280299230121627598585016336455159⟩
  | 1, 1 => ⟨45287356814611145980778663831171534715136564963, 45287356814611145980778663831172074792650162690⟩
  | 0, 3 => ⟨97189239799330916066869133456827234937432561536, 97189239799330916066869133456828207706387036307⟩
  | 1, 2 => ⟨131979106244532590876099664357176201262356792312, 131979106244532590876099664357177915930184527967⟩
  | 2, 1 => ⟨133245094152125394357797128197095292029117471230, 133245094152125394357797128197098374482570446275⟩
  | 0, 4 => ⟨174369532089838879316762713956360482958414138618, 174369532089838879316762713956363722450523312361⟩
  | 1, 3 => ⟨263228953686319484849367642103449409957209247750, 263228953686319484849367642103455218262622555332⟩
  | 2, 2 => ⟨352755075342238619980817379711670785699661553470, 352755075342238619980817379711681383806983288235⟩
  | 3, 1 => ⟨355668063378391454670970283220774433038809845091, 355668063378391454670970283220793947683044908989⟩
  | 0, 5 => ⟨-599399793194835033641039169095103160174318302393763, 603015108767556008776855634116246348265828664199156⟩
  | 1, 4 => ⟨-1168140925738125024419291939542611924560392963272405, 1173543143356477600293226874659652417328386258424757⟩
  | 2, 3 => ⟨-2279282278946494134319006586706434100069873240930130, 2287025181802512692883569634890432724311034299202176⟩
  | 3, 2 => ⟨-4450643777360423081398150882229678739583420075652538, 4460778914489715638397488903308362149498292343350402⟩
  | 4, 1 => ⟨-8695130008223350891161639230315159313382649087260157, 8705490020464178677023475527200891574303641189836773⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0484Geometry.ds, E8TAxisProd0484Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 13255099932547287592450207042647933770208720339 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0484CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0485CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0485CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0485GraphCenterA.qJetBox,
   E8TAxisProd0485GraphCenterB.qJetBox,
   E8TAxisProd0485GraphCenterC.qJetBox,
   E8TAxisProd0485GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0485GraphWholeA.qJetBox,
   E8TAxisProd0485GraphWholeB.qJetBox,
   E8TAxisProd0485GraphWholeC.qJetBox,
   E8TAxisProd0485GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12616665661336618222789607981352625047588762579, 12616665661336618222789607981352701496954665806⟩
  | 0, 2 => ⟨40274772677089688388801911074675066653298712952, 40274772677089688388801911074675341176242709862⟩
  | 1, 1 => ⟨40722113058285137172708683543006956265571671758, 40722113058285137172708683543007440851538498785⟩
  | 0, 3 => ⟨88128826992361028467308962168755648300754781524, 88128826992361028467308962168756520548764174022⟩
  | 1, 2 => ⟨119830942543039626322386072190089918799209993026, 119830942543039626322386072190091451332618930500⟩
  | 2, 1 => ⟨120995984376049638764402865343967817421426312398, 120995984376049638764402865343970566379598429290⟩
  | 0, 4 => ⟨159504350227651081647066609358328154766444086958, 159504350227651081647066609358331046373962745960⟩
  | 1, 3 => ⟨241283420574228864733332359978268364974083145519, 241283420574228864733332359978273536105711927686⟩
  | 2, 2 => ⟨323684248433082059323150860913471042862365611215, 323684248433082059323150860913480461430379322653⟩
  | 3, 1 => ⟨326391466382747347656897023599224405707253960200, 326391466382747347656897023599241721448799598623⟩
  | 0, 5 => ⟨-521134562377866315640769540337479736809716723339178, 524335820541893088655069815191410034413669065804318⟩
  | 1, 4 => ⟨-1014754566944754915062717689562646555906675390852761, 1019529551551559167063060132855113794530286784290075⟩
  | 2, 3 => ⟨-1978420327235150739751294573787193008213945553632622, 1985255960759648454620380173529132619684535673024486⟩
  | 3, 2 => ⟨-3860175323145624720866628944355691494198998178543111, 3869116609048483698760506991327726401833182112642395⟩
  | 4, 1 => ⟨-7535754015239784841080022909008103591767288579268836, 7544891793870270031862854754410427512817120208541803⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0485Geometry.ds, E8TAxisProd0485Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 11803348635363729140215008360142726703375841351 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0485CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0486CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0486CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0486GraphCenterA.qJetBox,
   E8TAxisProd0486GraphCenterB.qJetBox,
   E8TAxisProd0486GraphCenterC.qJetBox,
   E8TAxisProd0486GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0486GraphWholeA.qJetBox,
   E8TAxisProd0486GraphWholeB.qJetBox,
   E8TAxisProd0486GraphWholeC.qJetBox,
   E8TAxisProd0486GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨14104910579114025150264078781622910180981010664, 14104910579114025150264078781622993900693796569⟩
  | 0, 2 => ⟨44675005599631996444120131964100417645932255511, 44675005599631996444120131964100721768552969495⟩
  | 1, 1 => ⟨45122588439495629535974054375467720638635880850, 45122588439495629535974054375468259502628315125⟩
  | 0, 3 => ⟨96971490860848031824101424304977057201620849496, 96971490860848031824101424304978027785672988757⟩
  | 1, 2 => ⟨131650405834502637099058173484169358284836887755, 131650405834502637099058173484171069044746081094⟩
  | 2, 1 => ⟨132804645604978197259689942322261367102775895539, 132804645604978197259689942322264442445151525725⟩
  | 0, 4 => ⟨174028867795356965607819188336275088569364570959, 174028867795356965607819188336278320510279115056⟩
  | 1, 3 => ⟨262691861457525340449193347602682444762439367194, 262691861457525340449193347602688239423976776707⟩
  | 2, 2 => ⟨351962843551371725246243208092971857834392845823, 351962843551371725246243208092982430856095829635⟩
  | 3, 1 => ⟨354619147806671768115974865788499365944788522998, 354619147806671768115974865788518834025194702712⟩
  | 0, 5 => ⟨-597742877619642560547717346372078924717432377021721, 601349849924118630444961762664675854678474972722020⟩
  | 1, 4 => ⟨-1164894845048554117050695562706925131926468887517673, 1170284498882503333437977505272285790316953626998564⟩
  | 2, 3 => ⟨-2272915370758002667950147474976734136654030796914933, 2280640248975949679513287775842064175377501510027330⟩
  | 3, 2 => ⟨-4438145807755130594762715477213848744043613822247715, 4448257325880527540835104970014148333344451654900114⟩
  | 4, 1 => ⟨-8670582592254824541778628267331528732864795333681912, 8680917841213421539226643393357089655505044884378461⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0486Geometry.ds, E8TAxisProd0486Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 13202407326139831340872567629167947641622603942 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0486CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0487CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0487CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0487GraphCenterA.qJetBox,
   E8TAxisProd0487GraphCenterB.qJetBox,
   E8TAxisProd0487GraphCenterC.qJetBox,
   E8TAxisProd0487GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0487GraphWholeA.qJetBox,
   E8TAxisProd0487GraphWholeB.qJetBox,
   E8TAxisProd0487GraphWholeC.qJetBox,
   E8TAxisProd0487GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12566390994239938530900293251703509510818726838, 12566390994239938530900293251703585805828881563⟩
  | 0, 2 => ⟨40164736174262315123882502477907482903283757098, 40164736174262315123882502477907756820210947550⟩
  | 1, 1 => ⟨40572512753404960051556876244785122416805394948, 40572512753404960051556876244785605912507041753⟩
  | 0, 3 => ⟨87929642991388755191297119888753534699569673310, 87929642991388755191297119888754404985362839661⟩
  | 1, 2 => ⟨119529648718013662317685361938723036485750696924, 119529648718013662317685361938724565517758582816⟩
  | 2, 1 => ⟨120591837766755176868144038220939425012298992014, 120591837766755176868144038220942167609408686175⟩
  | 0, 4 => ⟨159190142440966292244830316264333333807599281342, 159190142440966292244830316264336218655594880671⟩
  | 1, 3 => ⟨240786847254622572386879764378469634579222109762, 240786847254622572386879764378474793520231600670⟩
  | 2, 2 => ⟨322950552975680561315369227360467050267945322804, 322950552975680561315369227360476446449738687021⟩
  | 3, 1 => ⟨325419202920764310931642039933559587611333177177, 325419202920764310931642039933576861843272573911⟩
  | 0, 5 => ⟨-519656309165345781740614932885826926550241901688521, 522850151984680401044756867206451567990329446828725⟩
  | 1, 4 => ⟨-1011860141280236457844306278594236898148219841502560, 1016623992237801961486232144333688766780496815478441⟩
  | 2, 3 => ⟨-1972746244608377896116112506315260924221547396311971, 1979565969459175427754841797778958638177802736096533⟩
  | 3, 2 => ⟨-3849043294101081953319499446165687454416095144297559, 3857963876958621372637362697806986940188580339266111⟩
  | 4, 1 => ⟨-7513901100267256297630675740230201587275266906973307, 7523017558866751366175151678249790058296734565049558⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0487Geometry.ds, E8TAxisProd0487Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 11756002491464711617834044901140580532162929087 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0487CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0488CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0488CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0488GraphCenterA.qJetBox,
   E8TAxisProd0488GraphCenterB.qJetBox,
   E8TAxisProd0488GraphCenterC.qJetBox,
   E8TAxisProd0488GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0488GraphWholeA.qJetBox,
   E8TAxisProd0488GraphWholeB.qJetBox,
   E8TAxisProd0488GraphWholeC.qJetBox,
   E8TAxisProd0488GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17645261039611990296624607568106175408295554457, 17645261039611990296624607568106276229015683170⟩
  | 0, 2 => ⟨54953591962619086996150667142731671321759874722, 54953591962619086996150667142732045686111946995⟩
  | 1, 1 => ⟨55439360020254630303661631217060567147758952773, 55439360020254630303661631217061235190602827093⟩
  | 0, 3 => ⟨117315524173909724668308202157776729363570678954, 117315524173909724668308202157777934032325201095⟩
  | 1, 2 => ⟨158836824561907847524750518997110918436717269899, 158836824561907847524750518997113054587894013213⟩
  | 2, 1 => ⟨160065360647731615012028952450382383066636647947, 160065360647731615012028952450386239242991939245⟩
  | 0, 4 => ⟨207018395788500096056319799391317606157303331420, 207018395788500096056319799391321651881463696900⟩
  | 1, 3 => ⟨311231678049522855208879186246160715422472291523, 311231678049522855208879186246168004002531218735⟩
  | 2, 2 => ⟨416076267541069216717121461752760608672103222270, 416076267541069216717121461752773952508468393073⟩
  | 3, 1 => ⟨418852656177892268258514833680255911954367762013, 418852656177892268258514833680280554793487168810⟩
  | 0, 5 => ⟨-779561208605647084457430808023344488761419228155926, 784132284586764005317571421941671677307727574399873⟩
  | 1, 4 => ⟨-1521540533827345030468636536139418014599673800771660, 1528393263885451626089954067220806333702314853778031⟩
  | 2, 3 => ⟨-2973073161009751647077007249680206211237895390647397, 2982917206691859024401992445243754957641395530346507⟩
  | 3, 2 => ⟨-5813471780419625249864690785408740860448489190748302, 5826374191828776715614590295496770735666126366040742⟩
  | 4, 1 => ⟨-11373408223353678090907692734205973170740911040010650, 11386601102245217778907884888318147856949333129035664⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0488Geometry.ds, E8TAxisProd0488Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16533567278410936219642749728029760677706821214 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0488CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0489CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0489CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0489GraphCenterA.qJetBox,
   E8TAxisProd0489GraphCenterB.qJetBox,
   E8TAxisProd0489GraphCenterC.qJetBox,
   E8TAxisProd0489GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0489GraphWholeA.qJetBox,
   E8TAxisProd0489GraphWholeB.qJetBox,
   E8TAxisProd0489GraphWholeC.qJetBox,
   E8TAxisProd0489GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨15753098473144356592962602198562167964761934730, 15753098473144356592962602198562259712394826502⟩
  | 0, 2 => ⟨49506690873328576934709248758353960364749076224, 49506690873328576934709248758354297370988171525⟩
  | 1, 1 => ⟨49950058674771026491356338282816081772730759114, 49950058674771026491356338282816681059338654960⟩
  | 0, 3 => ⟨106594128336708757640641821484018784835437649364, 106594128336708757640641821484019864904208492494⟩
  | 1, 2 => ⟨144496735488138056976035527234029494111059632357, 144496735488138056976035527234031403669779008893⟩
  | 2, 1 => ⟨145629030913537653174605494819626274478677213882, 145629030913537653174605494819629714453651580660⟩
  | 0, 4 => ⟨189706014279268236895424906157523967190243907934, 189706014279268236895424906157527579116089401358⟩
  | 1, 3 => ⟨285759809534104629091341648163185301524382275783, 285759809534104629091341648163191793335376479663⟩
  | 2, 2 => ⟨382402598306554532749216394686606457547813640878, 382402598306554532749216394686618322867814104420⟩
  | 3, 1 => ⟨384984452334217222068660517768709609767460876040, 384984452334217222068660517768731489965217134668⟩
  | 0, 5 => ⟨-683031543312450484878816580367558351663933445219931, 687089978518447257022155352279032686891007753367755⟩
  | 1, 4 => ⟨-1332144932137262430155213069190072815528561446073133, 1338219318295258549792690907203854531022796075570894⟩
  | 2, 3 => ⟨-2601161382140579797026746932024024520736349589429345, 2609877646025254896501375182030827921932025470936484⟩
  | 3, 2 => ⟨-5082732132625430631519107481363313331564441419501864, 5094148853715682420266558783105159798618212269572764⟩
  | 4, 1 => ⟨-9936959104060430953254024682806056801802039465708608, 9948629883927590267428931354243903090885741126532036⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0489Geometry.ds, E8TAxisProd0489Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 14752675394487521815388149486982170118476074950 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0489CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0490CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0490CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0490GraphCenterA.qJetBox,
   E8TAxisProd0490GraphCenterB.qJetBox,
   E8TAxisProd0490GraphCenterC.qJetBox,
   E8TAxisProd0490GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0490GraphWholeA.qJetBox,
   E8TAxisProd0490GraphWholeB.qJetBox,
   E8TAxisProd0490GraphWholeC.qJetBox,
   E8TAxisProd0490GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17576660635055618456891020710256498858024476020, 17576660635055618456891020710256599473078038733⟩
  | 0, 2 => ⟨54807109186718358111851359228331952749137511580, 54807109186718358111851359228332326288140795109⟩
  | 1, 1 => ⟨55241056976403602469850256250570803786326733953, 55241056976403602469850256250571470332392244779⟩
  | 0, 3 => ⟨117057000275642566372534722096607316635654790964, 117057000275642566372534722096608518606769145167⟩
  | 1, 2 => ⟨158448175859981203114160231141954390189629275729, 158448175859981203114160231141956521494774198016⟩
  | 2, 1 => ⟨159545839983871089420157222840812378211950106803, 159545839983871089420157222840816225543197750062⟩
  | 0, 4 => ⟨206619955517305707021783036480381951297244836864, 206619955517305707021783036480385987635506426415⟩
  | 1, 3 => ⟨310606428845741945208132870662441192239827268871, 310606428845741945208132870662448463802616605539⟩
  | 2, 2 => ⟨415157075038931151773200731332456137353226204069, 415157075038931151773200731332469449829405740819⟩
  | 3, 1 => ⟨417638079389605331724681356277292964706729808639, 417638079389605331724681356277317549218188112062⟩
  | 0, 5 => ⟨-777518730503063743484517197525749370765269872780015, 782079302455405283126780052284388855782107128882073⟩
  | 1, 4 => ⟨-1517535114878315650562069067405752843864285312193673, 1524371928120139577565568075584459906799827329522314⟩
  | 2, 3 => ⟨-2965209289598556353930559982943382397109484832956680, 2975030305029667106671207573562817905187334491556033⟩
  | 3, 2 => ⟨-5798020578667487751701322757790890669123849225592706, 5810892377369663273256529037909991916676378711438374⟩
  | 4, 1 => ⟨-11343031302529033416419364868093503052351782040562585, 11356190925776905746515493228896242435238623835407264⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0490Geometry.ds, E8TAxisProd0490Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16468852939107357702030917188619539736184102202 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0490CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0491CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0491CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0491GraphCenterA.qJetBox,
   E8TAxisProd0491GraphCenterB.qJetBox,
   E8TAxisProd0491GraphCenterC.qJetBox,
   E8TAxisProd0491GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0491GraphWholeA.qJetBox,
   E8TAxisProd0491GraphWholeB.qJetBox,
   E8TAxisProd0491GraphWholeC.qJetBox,
   E8TAxisProd0491GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨15691298324492152346603788767568992387557845272, 15691298324492152346603788767569083948626332914⟩
  | 0, 2 => ⟨49373596324889121331289445472705185458422865748, 49373596324889121331289445472705521721219231076⟩
  | 1, 1 => ⟨49769660854520873924068601938301359044495740079, 49769660854520873924068601938301956986298949196⟩
  | 0, 3 => ⟨106357225807151693566262517738409963628623540804, 106357225807151693566262517738411041274688348866⟩
  | 1, 2 => ⟨144139897451688945910004675769470018546965051841, 144139897451688945910004675769471923762984720423⟩
  | 2, 1 => ⟨145151560291496964751661216833133044711739699277, 145151560291496964751661216833136476772421632616⟩
  | 0, 4 => ⟨189338138751419763507991025043056006587831568938, 189338138751419763507991025043059610110430756345⟩
  | 1, 3 => ⟨285181219508273701956211293744824480065269176216, 285181219508273701956211293744830956667314848086⟩
  | 2, 2 => ⟨381550657775341120149555883593829163777339336816, 381550657775341120149555883593841001102549997272⟩
  | 3, 1 => ⟨383857814033766450177775801084572678859484316135, 383857814033766450177775801084594507041681273267⟩
  | 0, 5 => ⟨-681191556720316567706695354683176877125421646266583, 685240653321394650122468250749147804723806256127045⟩
  | 1, 4 => ⟨-1328538354191860093371450546625829838540259885838700, 1334598635883510428247389505711030851195520379789245⟩
  | 2, 3 => ⟨-2594083897616721550768593491181521320227461823709689, 2602779845546177091706295446604985393376061702168706⟩
  | 3, 2 => ⟨-5068832563660584725913739912716706582421284966791999, 5080222484184439575679325565121795954952564394425761⟩
  | 4, 1 => ⟨-9909645507932891762054921146895743402618478144181551, 9921287714384153326435959414167466620054650513706423⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0491Geometry.ds, E8TAxisProd0491Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 14694409675322114488133960607368730124756807589 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0491CertifiedArithmetic

end


