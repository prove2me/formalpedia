-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000RCertifiedArithmetic__11
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0000RCertifiedArithmetic__11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T14:29:09.618499+00:00
-- url     : https://prove2.me/theorems/f0e6d97c-7b43-433f-b734-64712619e1be
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0000RCertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0023RCertifiedArithmetic, GeneralCK.Certificates.E8…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0000RCertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0023RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0024RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0028RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0073RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0074RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0079RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0080RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0087RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0088RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0093RCertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0000RCertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0023RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0024RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0028RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0073RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0074RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0079RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0080RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0087RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0088RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0093RCertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0000RCertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0023RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0024RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0028RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0073RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0074RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0079RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0080RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0087RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0088RCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0093RCertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0000RCertifiedArithmetic (+10 modules: GeneralCK/Certificates/E8TAxisProd0023RCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0024RCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0028RCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0073RCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0074RCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0079RCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0080RCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0087RCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0088RCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0093RCertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000RGraphCenterA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000RGraphCenterB__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000RGraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000RGraphCenterD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000RGraphWholeA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000RGraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000RGraphWholeC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000RGraphWholeD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000RGeometry__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0088RGraphCenterB__2

-- ===== source module GeneralCK.Certificates.E8TAxisProd0000RCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0000RCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0000RGraphCenterA.qJetBox,
   E8TAxisProd0000RGraphCenterB.qJetBox,
   E8TAxisProd0000RGraphCenterC.qJetBox,
   E8TAxisProd0000RGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0000RGraphWholeA.qJetBox,
   E8TAxisProd0000RGraphWholeB.qJetBox,
   E8TAxisProd0000RGraphWholeC.qJetBox,
   E8TAxisProd0000RGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨369963124682839412446207436954852287361, 369963124682839412446207437685360805606⟩
  | 0, 2 => ⟨13911391885679069398026867667591073566797, 13911391885679069398026867670465316731661⟩
  | 1, 1 => ⟨16972747601081805136686276390841884730700, 16972747601081805136686276394373176723508⟩
  | 0, 3 => ⟨285581748835538451475123150743903705390092, 285581748835538451475123150747791409364655⟩
  | 1, 2 => ⟨531877189578079695235139330673410472050141, 531877189578079695235139330677622375139548⟩
  | 2, 1 => ⟨620500792790920231549418923704017048056208, 620500792790920231549418923708964517568984⟩
  | 0, 4 => ⟨2607132765060793440890506570657353696413761, 2607132765060793440890506570669727463034488⟩
  | 1, 3 => ⟨8503051741524598630357164719036899379500430, 8503051741524598630357164719050183155525269⟩
  | 2, 2 => ⟨15249562655851950438326103221263776216156443, 15249562655851950438326103221280070342242321⟩
  | 3, 1 => ⟨16966471924230240094473810536455691398550304, 16966471924230240094473810536479653903464176⟩
  | 0, 5 => ⟨-69524556854628300116382235619161426620742711503, 69502699038970323658840711131459925661113570064⟩
  | 1, 4 => ⟨-87460489275783180148103618531762054828492852666, 87142420110754284970284413723380898482292256323⟩
  | 2, 3 => ⟨-127135440019531782989901442225573103318689105253, 126596812882699371457842221357225054240636336835⟩
  | 3, 2 => ⟨-198246333927990746813731520344167876969827259863, 197607341501960275130838144731507197969791974908⟩
  | 4, 1 => ⟨-306340233422495317540155232721779739999269039700, 306184238918805851727842781383793923931463076783⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0000RGeometry.ds, E8TAxisProd0000RGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 210087860829291867431293357920022579334 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0000RCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0023RCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0023RCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0023RGraphCenterA.qJetBox,
   E8TAxisProd0023RGraphCenterB.qJetBox,
   E8TAxisProd0023RGraphCenterC.qJetBox,
   E8TAxisProd0023RGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0023RGraphWholeA.qJetBox,
   E8TAxisProd0023RGraphWholeB.qJetBox,
   E8TAxisProd0023RGraphWholeC.qJetBox,
   E8TAxisProd0023RGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨737256808254318255674385956749942394483, 737256808254318255674385957519673001851⟩
  | 0, 2 => ⟨24993971003639002627376132545961039940432, 24993971003639002627376132548882567125987⟩
  | 1, 1 => ⟨29376160816055141111242719358431175535662, 29376160816055141111242719362013493795262⟩
  | 0, 3 => ⟨453781713605309238362815701566639510836780, 453781713605309238362815701570664082254750⟩
  | 1, 2 => ⟨825177577347170249834804655873746050521742, 825177577347170249834804655878111923679437⟩
  | 2, 1 => ⟨934662134690094535597019787967339042771503, 934662134690094535597019787972517804598444⟩
  | 0, 4 => ⟨3649083221406889882597592841183257014545448, 3649083221406889882597592841195922142973753⟩
  | 1, 3 => ⟨11605893129143307339210804952102960024840760, 11605893129143307339210804952116591639547078⟩
  | 2, 2 => ⟨20469026200469398052143492593114496866970615, 20469026200469398052143492593131325410256112⟩
  | 3, 1 => ⟨22304185017808694599577461692736807489445011, 22304185017808694599577461692761608683889165⟩
  | 0, 5 => ⟨-50610820280527041316835704218087758706531790674, 50516248895452461520481302444659759025628411131⟩
  | 1, 4 => ⟨-73961608640484377453443641918191498401554313339, 73493237499364259893599291035289603625733321340⟩
  | 2, 3 => ⟨-115134769948769800951554629110067375030788762750, 114305724212250455856880505349557492559422715472⟩
  | 3, 2 => ⟨-182976993188928388196075127433262726706964423839, 181849801142190513649329052886392839383796698870⟩
  | 4, 1 => ⟨-287447700039779997354820037074165713914046234914, 286515642791511239804773597025634563395306547386⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0023RGeometry.ds, E8TAxisProd0023RGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 541332942101661313296613786419100133149 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0023RCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0024RCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0024RCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0024RGraphCenterA.qJetBox,
   E8TAxisProd0024RGraphCenterB.qJetBox,
   E8TAxisProd0024RGraphCenterC.qJetBox,
   E8TAxisProd0024RGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0024RGraphWholeA.qJetBox,
   E8TAxisProd0024RGraphWholeB.qJetBox,
   E8TAxisProd0024RGraphWholeC.qJetBox,
   E8TAxisProd0024RGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨676180449552995016586922641388761330487, 676180449552995016586922642153478720786⟩
  | 0, 2 => ⟨23870914072922480912573564299996324430678, 23870914072922480912573564302911025894203⟩
  | 1, 1 => ⟨27349312691200696370466531691706349881563, 27349312691200696370466531695281263821558⟩
  | 0, 3 => ⟨444666231547715883404294580445747889149882, 444666231547715883404294580449752729305061⟩
  | 1, 2 => ⟨796369923021898812290306441736327678690055, 796369923021898812290306441740672368943066⟩
  | 2, 1 => ⟨884113041958526809115001462312179104932398, 884113041958526809115001462317330126090124⟩
  | 0, 4 => ⟨3643321827279152662648593339820937879979703, 3643321827279152662648593339833560757421315⟩
  | 1, 3 => ⟨11440291876168236341341552745657530627157674, 11440291876168236341341552745671116953943523⟩
  | 2, 2 => ⟨19970935654591565550807760431805978769825489, 19970935654591565550807760431822743964825595⟩
  | 3, 1 => ⟨21456152428980741626938454612156734923805713, 21456152428980741626938454612181435139914885⟩
  | 0, 5 => ⟨-50475161892020925905120523154136783609085061631, 50382971334881503041182687899015015824857638573⟩
  | 1, 4 => ⟨-73744159940382250549514938185875626290445941533, 73284423416373783128067129169370207590309519191⟩
  | 2, 3 => ⟨-114757189249056128453907554883548383418899882161, 113939091381292498787117200776968600773848859079⟩
  | 3, 2 => ⟨-182301190885538911359567834667849161616310628683, 181180316865766479636930789585454592385934050076⟩
  | 4, 1 => ⟨-286215430159101212608071479694817880985489049338, 285275916472521610584901250474786405662916028520⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0024RGeometry.ds, E8TAxisProd0024RGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 491957402976364409096167917944129167622 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0024RCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0028RCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0028RCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0028RGraphCenterA.qJetBox,
   E8TAxisProd0028RGraphCenterB.qJetBox,
   E8TAxisProd0028RGraphCenterC.qJetBox,
   E8TAxisProd0028RGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0028RGraphWholeA.qJetBox,
   E8TAxisProd0028RGraphWholeB.qJetBox,
   E8TAxisProd0028RGraphWholeC.qJetBox,
   E8TAxisProd0028RGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨617883262224892318567911299322464263849, 617883262224892318567911300082178322726⟩
  | 0, 2 => ⟨22770627964219376683282319869870408654992, 22770627964219376683282319872778311593487⟩
  | 1, 1 => ⟨25393966581530424252590613679888642223783, 25393966581530424252590613683456180822840⟩
  | 0, 3 => ⟨435565007520193528551729583261394757776115, 435565007520193528551729583265379920510316⟩
  | 1, 2 => ⟨767975812433197986989022845536970093835945, 767975812433197986989022845541293658852391⟩
  | 2, 1 => ⟨834804024694550577659617665474203364205863, 834804024694550577659617665479326727924693⟩
  | 0, 4 => ⟨3637676771719742405804525648617554110230273, 3637676771719742405804525648630134896879287⟩
  | 1, 3 => ⟨11275057263279857796724149082112368204496504, 11275057263279857796724149082125909413796428⟩
  | 2, 2 => ⟨19476963180119589478857503483304039290524590, 19476963180119589478857503483320741384846002⟩
  | 3, 1 => ⟨20619490595362121146066498913662165559357394, 20619490595362121146066498913686765202284680⟩
  | 0, 5 => ⟨-50340389941244043036485449761993142817169186126, 50250680175970048664592765205667105584273987231⟩
  | 1, 4 => ⟨-73527517122777269623819176685876393178981833418, 73076463101262655527313318818849876601850324113⟩
  | 2, 3 => ⟨-114380664422581552487027632550116271587971963541, 113573517537838661468554454592029901871973519806⟩
  | 3, 2 => ⟨-181627293366793516480115830779731412290302535185, 180512703906357071740798522041624074679162906304⟩
  | 4, 1 => ⟨-284986688600032043568979047451511310506569341957, 284039627434831151659794618598864499352072630765⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0028RGeometry.ds, E8TAxisProd0028RGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 444980972519640813744912802697173738679 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0028RCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0073RCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0073RCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0073RGraphCenterA.qJetBox,
   E8TAxisProd0073RGraphCenterB.qJetBox,
   E8TAxisProd0073RGraphCenterC.qJetBox,
   E8TAxisProd0073RGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0073RGraphWholeA.qJetBox,
   E8TAxisProd0073RGraphWholeB.qJetBox,
   E8TAxisProd0073RGraphWholeC.qJetBox,
   E8TAxisProd0073RGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2499178570950341234862965637093716669026698, 2499178570950341234862965637096002480709401⟩
  | 0, 2 => ⟨20017987026215324734026309749547533954215457, 20017987026215324734026309749552797401367530⟩
  | 1, 1 => ⟨20986834929291904964229155353395396874845718, 20986834929291904964229155353401905694000130⟩
  | 0, 3 => ⟨86489180350525946806208739064723714422224819, 86489180350525946806208739064734098441987973⟩
  | 1, 2 => ⟨140795243673911182506935547921265837487239262, 140795243673911182506935547921278223208975447⟩
  | 2, 1 => ⟨146102342403105313621589599918160348161524948, 146102342403105313621589599918177880702794663⟩
  | 0, 4 => ⟨220083657490717253561365689071359493883307803, 220083657490717253561365689071387379830475035⟩
  | 1, 3 => ⟨505606776656992851024950427966027756319938234, 505606776656992851024950427966061761512043172⟩
  | 2, 2 => ⟨799838232014158455144235308901220404122670107, 799838232014158455144235308901269467117868698⟩
  | 3, 1 => ⟨822271309337393599359120868673922502023359875, 822271309337393599359120868673999809553159522⟩
  | 0, 5 => ⟨-628243374874913542518926652434234071873356392412, 635133163798653505957128645436028358273121182093⟩
  | 1, 4 => ⟨-1061028030702096245105153861086552378533382797742, 1061932346873496943799839660125218408838636721706⟩
  | 2, 3 => ⟨-1832873221206964444773578442769978347441986349650, 1826443432467464068424525832647658282632791438227⟩
  | 3, 2 => ⟨-3184974616007403449545734018795958958504153731645, 3171584772391589788953045171470617912242125702424⟩
  | 4, 1 => ⟨-5521136499438751220370133619598783738379476002841, 5509014569136900685242785591771576658275993541646⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0073RGeometry.ds, E8TAxisProd0073RGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2108510137259429536260122967948645584062809 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0073RCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0074RCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0074RCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0074RGraphCenterA.qJetBox,
   E8TAxisProd0074RGraphCenterB.qJetBox,
   E8TAxisProd0074RGraphCenterC.qJetBox,
   E8TAxisProd0074RGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0074RGraphWholeA.qJetBox,
   E8TAxisProd0074RGraphWholeB.qJetBox,
   E8TAxisProd0074RGraphWholeC.qJetBox,
   E8TAxisProd0074RGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2449403309647378146000766550456577331264854, 2449403309647378146000766550458854832422468⟩
  | 0, 2 => ⟨19802450703501040553877106380384983079543320, 19802450703501040553877106380390230896255429⟩
  | 1, 1 => ⟨20636423799021566313370642996955552374387663, 20636423799021566313370642996962042162457408⟩
  | 0, 3 => ⟨85940330448863584172687206247268361225054784, 85940330448863584172687206247278705246470667⟩
  | 1, 2 => ⟨139534875808241958248199190181331455236670387, 139534875808241958248199190181343791663332134⟩
  | 2, 1 => ⟨144110170686387159273790538923062517502874281, 144110170686387159273790538923079976848474497⟩
  | 0, 4 => ⟨218997349904517689714024005129707276273050984, 218997349904517689714024005129735061664263527⟩
  | 1, 3 => ⟨502690137141786805239198791564081250608210640, 502690137141786805239198791564115128814164944⟩
  | 2, 2 => ⟨793904623261443758217914264735789384793585264, 793904623261443758217914264735838250625235003⟩
  | 3, 1 => ⟨813265984860248101860211583195552444605351783, 813265984860248101860211583195629423440275784⟩
  | 0, 5 => ⟨-625745011572541659091660666344901910761584222894, 632638892945115194505134537189004482479467081280⟩
  | 1, 4 => ⟨-1056585719513572345552008452663973920353683038019, 1057533308343624885968290357722384492973984472314⟩
  | 2, 3 => ⟨-1824778604510288167510504517797703651787871537716, 1818451105604637989170302930676134475283323229558⟩
  | 3, 2 => ⟨-3170038032178548774647831544935191736288830239350, 3156844393486242162719661210163534112756191048452⟩
  | 4, 1 => ⟨-5493370221837068277481330683666848902042357738968, 5481609618714451167245236632020563699123462594562⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0074RGeometry.ds, E8TAxisProd0074RGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2064835990846182304508327025055489533877607 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0074RCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0079RCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0079RCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0079RGraphCenterA.qJetBox,
   E8TAxisProd0079RGraphCenterB.qJetBox,
   E8TAxisProd0079RGraphCenterC.qJetBox,
   E8TAxisProd0079RGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0079RGraphWholeA.qJetBox,
   E8TAxisProd0079RGraphWholeB.qJetBox,
   E8TAxisProd0079RGraphWholeC.qJetBox,
   E8TAxisProd0079RGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2400165176819945356492286541689298459091451, 2400165176819945356492286541691567669954193⟩
  | 0, 2 => ⟨19588283117610172903032510045400296853662283, 19588283117610172903032510045405529093641296⟩
  | 1, 1 => ⟨20289154490277998359310744271129680440051463, 20289154490277998359310744271136151264230833⟩
  | 0, 3 => ⟨85394188182579800511437369761530299704814977, 85394188182579800511437369761540603858058476⟩
  | 1, 2 => ⟨138281779916781360625515145271445547158553912, 138281779916781360625515145271457834457619285⟩
  | 2, 1 => ⟨142132791952931628570940156690232302938088950, 142132791952931628570940156690249689350625200⟩
  | 0, 4 => ⟨217917544432078396941886782935471731435951426, 217917544432078396941886782935499416643612575⟩
  | 1, 3 => ⟨499789183345184660722394516859879160774384642, 499789183345184660722394516859912912477478057⟩
  | 2, 2 => ⟨788003815178588612880199909930532180537135601, 788003815178588612880199909930580849972247495⟩
  | 3, 1 => ⟨804318536131706328240825931930660073400085483, 804318536131706328240825931930736724842076970⟩
  | 0, 5 => ⟨-623256118330867588626143245632078513700764428655, 630230439126644481521579341064960353945887916838⟩
  | 1, 4 => ⟨-1052160372477496584094319080355283328718579247587, 1053242828699127316470653217316738886224251403198⟩
  | 2, 3 => ⟨-1816715250714622825647889519132668704002389222753, 1810581585791061288844063006998824066667682872276⟩
  | 3, 2 => ⟨-3155159919136782406699317691718242443027906361446, 3142223362657704630354798187824895815332309284701⟩
  | 4, 1 => ⟨-5465714204446486456686664116862125944810743935560, 5454314453939399612811156473386495854932850759597⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0079RGeometry.ds, E8TAxisProd0079RGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2021645855255962136479126219370739957655498 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0079RCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0080RCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0080RCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0080RGraphCenterA.qJetBox,
   E8TAxisProd0080RGraphCenterB.qJetBox,
   E8TAxisProd0080RGraphCenterC.qJetBox,
   E8TAxisProd0080RGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0080RGraphWholeA.qJetBox,
   E8TAxisProd0080RGraphWholeB.qJetBox,
   E8TAxisProd0080RGraphWholeC.qJetBox,
   E8TAxisProd0080RGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2351460759070430850977235967467059655648912, 2351460759070430850977235967469320596383612⟩
  | 0, 2 => ⟨19375477519743700089504184797058285456270213, 19375477519743700089504184797063502173049235⟩
  | 1, 1 => ⟨19945008872056500133362425711008901310849311, 19945008872056500133362425711015353238105403⟩
  | 0, 3 => ⟨84850737331989957528770288075380214833815015, 84850737331989957528770288075390479248566174⟩
  | 1, 2 => ⟨137035916889650703637873988455021516049215204, 137035916889650703637873988455033754387515749⟩
  | 2, 1 => ⟨140170124427379418160469858959474861217350688, 140170124427379418160469858959492174958410194⟩
  | 0, 4 => ⟨216844212620990110743105431919600449854934648, 216844212620990110743105431919628035250030693⟩
  | 1, 3 => ⟨496903831800451132626119029046375406357261011, 496903831800451132626119029046409032038897505⟩
  | 2, 2 => ⟨782135626863440887338627852812559923045219709, 782135626863440887338627852812608396847776666⟩
  | 3, 1 => ⟨795428637803638989088164650495960439932042507, 795428637803638989088164650496036765277866850⟩
  | 0, 5 => ⟨-620776592644599716632399466256540185591061661631, 627831072892091463319380657103014747409386149609⟩
  | 1, 4 => ⟨-1047751872914971850291324865875498247915295964818, 1048968800892525288656412130357997924167914026636⟩
  | 2, 3 => ⟨-1808683002303456126584965706188645844848695123608, 1802742704629993542727880359245753799898484793735⟩
  | 3, 2 => ⟨-3140340021416692881087264641264846921839641625956, 3127660080187524662674543918993338283903246170476⟩
  | 4, 1 => ⟨-5438167999598132938816449945965838939405533435770, 5427128622393916904822940854524779289273259508507⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0080RGeometry.ds, E8TAxisProd0080RGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1978936621624598027559484057802480634884814 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0080RCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0087RCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0087RCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0087RGraphCenterA.qJetBox,
   E8TAxisProd0087RGraphCenterB.qJetBox,
   E8TAxisProd0087RGraphCenterC.qJetBox,
   E8TAxisProd0087RGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0087RGraphWholeA.qJetBox,
   E8TAxisProd0087RGraphWholeB.qJetBox,
   E8TAxisProd0087RGraphWholeC.qJetBox,
   E8TAxisProd0087RGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2303286659822607641696304231892050737414786, 2303286659822607641696304231894303428125085⟩
  | 0, 2 => ⟨19164027201563069324830449568594251360727489, 19164027201563069324830449568599452607666543⟩
  | 1, 1 => ⟨19603968910866655331128588968320356385365749, 19603968910866655331128588968326789482439346⟩
  | 0, 3 => ⟨84309961748335202863020274464154878025739572, 84309961748335202863020274464165102831185651⟩
  | 1, 2 => ⟨135797247825132553386077016813639428311194161, 135797247825132553386077016813651617854917594⟩
  | 2, 1 => ⟨138222086785502548846915849309845960387371622, 138222086785502548846915849309863201717527635⟩
  | 0, 4 => ⟨215777326182926422977890216788957988906712131, 215777326182926422977890216788985474858819375⟩
  | 1, 3 => ⟨494033999444983402023562390842625240473209060, 494033999444983402023562390842658740612916750⟩
  | 2, 2 => ⟨776299878312343652141052952318152687977280348, 776299878312343652141052952318200966908253713⟩
  | 3, 1 => ⟨786595966234656827606381150466312260978366933, 786595966234656827606381150466388261519640711⟩
  | 0, 5 => ⟨-618307083681854541680209951282967894670893416361, 625441674470221692635892216866900332408179668872⟩
  | 1, 4 => ⟨-1043360466872305840718264572094574135237229388047, 1044711705274416696494008911514705472771676130920⟩
  | 2, 3 => ⟨-1800681802618088859683762716403486952296604712641, 1794934634640014791542053225875656603780545584909⟩
  | 3, 2 => ⟨-3125578132832499209183172240796856814899807292131, 3113154505821560309368582472702347270782119983985⟩
  | 4, 1 => ⟨-5410731163056479116820667136429358469608561902107, 5400051674653966892951953611685370041706336123745⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0087RGeometry.ds, E8TAxisProd0087RGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1936705195738521703830596995556550406779000 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0087RCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0088RCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0088RCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0088RGraphCenterA.qJetBox,
   E8TAxisProd0088RGraphCenterB.qJetBox,
   E8TAxisProd0088RGraphCenterC.qJetBox,
   E8TAxisProd0088RGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0088RGraphWholeA.qJetBox,
   E8TAxisProd0088RGraphWholeB.qJetBox,
   E8TAxisProd0088RGraphWholeC.qJetBox,
   E8TAxisProd0088RGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2255639499220703812431532292768680900873512, 2255639499220703812431532292770925361600089⟩
  | 0, 2 => ⟨18953925495013394350732431094844976257055526, 18953925495013394350732431094850162087342247⟩
  | 1, 1 => ⟨19266016670213189995781943742182334596584268, 19266016670213189995781943742188748929990757⟩
  | 0, 3 => ⟨83771845353373063530061012996613389433047212, 83771845353373063530061012996623574757884540⟩
  | 1, 2 => ⟨134565734028662916527151337717511834125531235, 134565734028662916527151337717523975040223891⟩
  | 2, 1 => ⟨136288598151963742319375554027273525203310663, 136288598151963742319375554027290694382126364⟩
  | 0, 4 => ⟨214716856993003858977103825492500626514570769, 214716856993003858977103825492528013391860298⟩
  | 1, 3 => ⟨491179603618296838705094129082148416352037933, 491179603618296838705094129082181791427474669⟩
  | 2, 2 => ⟨770496390415646704202679587055510991119229394, 770496390415646704202679587055559075936587185⟩
  | 3, 1 => ⟨777820199481691882092863141531130407350232225, 777820199481691882092863141531206084373436492⟩
  | 0, 5 => ⟨-615847141050887740722948142422393317100364036527, 623062084774653943807976574388678527015032736098⟩
  | 1, 4 => ⟨-1038985879879271024075896085232223119911232359395, 1040471345368757101058332708546192993128803246314⟩
  | 2, 3 => ⟨-1792711447724476254690674217303884212581845600167, 1787157098208144298443006080504195482664341687249⟩
  | 3, 2 => ⟨-3110873985866806663486074410077520989882767989677, 3098706304598383338933502913236447608093080112722⟩
  | 4, 1 => ⟨-5383403252431603041431063109136761465802737257778, 5373083163186679131820368987419131077005126580678⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0088RGeometry.ds, E8TAxisProd0088RGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1894948498540349743802015562361140324149593 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0088RCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0093RCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0093RCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0093RGraphCenterA.qJetBox,
   E8TAxisProd0093RGraphCenterB.qJetBox,
   E8TAxisProd0093RGraphCenterC.qJetBox,
   E8TAxisProd0093RGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0093RGraphWholeA.qJetBox,
   E8TAxisProd0093RGraphWholeB.qJetBox,
   E8TAxisProd0093RGraphWholeC.qJetBox,
   E8TAxisProd0093RGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2208515914028913290648895110315295632511644, 2208515914028913290648895110317531883232393⟩
  | 0, 2 => ⟨18745165772147674585809434510569124196574841, 18745165772147674585809434510574294663225129⟩
  | 1, 1 => ⟨18931134310079343444447389945226166485752905, 18931134310079343444447389945232562121783135⟩
  | 0, 3 => ⟨83236372138969635082394273813511119491857427, 83236372138969635082394273813521265464293263⟩
  | 1, 2 => ⟨133341337011828453799505047974317746528615065, 133341337011828453799505047974329838979184450⟩
  | 2, 1 => ⟨134369578098086994272407746326458993523580545, 134369578098086994272407746326476090809613134⟩
  | 0, 4 => ⟨213662777089145228301495363690588735105246121, 213662777089145228301495363690616023274490753⟩
  | 1, 3 => ⟨488340562060019216188483605583462563808925471, 488340562060019216188483605583495814295888704⟩
  | 2, 2 => ⟨764724984953237914607900624286650317406325043, 764724984953237914607900624286698208865048391⟩
  | 3, 1 => ⟨769101017291617435404640133160151467699783970, 769101017291617435404640133160226822486292935⟩
  | 0, 5 => ⟨-613396381421748857137153259903983616770550530588, 620691398654280147624610913514398411207820223719⟩
  | 1, 4 => ⟨-1034627903524659448828535720016717313615373488894, 1036247208317546295894851634563331211417224267565⟩
  | 2, 3 => ⟨-1784771806644148191907323268428294269359482554158, 1779409818411012494216955845456409686796916267989⟩
  | 3, 2 => ⟨-3096227343418121932185189106387984328810557342408, 3084315140144059247477114479260596957407786656062⟩
  | 4, 1 => ⟨-5356183827144524598610862230971377278589670344490, 5346222642323870728055077949955385367075385542085⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0093RGeometry.ds, E8TAxisProd0093RGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1853663465941290203790927805769989416536637 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0093RCertifiedArithmetic

end


