-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0362CertifiedArithmetic__12
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0362CertifiedArithmetic__12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T20:06:53.602735+00:00
-- url     : https://prove2.me/theorems/af5c7371-dd39-47d6-aa63-6048601aac3f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0362CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0363CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0362CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0363CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0364CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0365CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0366CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0367CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0368CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0369CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0370CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0371CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0372CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0373CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0362CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0363CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0364CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0365CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0366CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0367CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0368CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0369CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0370CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0371CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0372CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0373CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0362CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0363CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0364CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0365CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0366CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0367CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0368CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0369CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0370CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0371CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0372CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0373CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0362CertifiedArithmetic (+11 modules: GeneralCK/Certificates/E8TAxisProd0363CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0364CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0365CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0366CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0367CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0368CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0369CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0370CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0371CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0372CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0373CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0362GraphCenterA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0357GraphCenterB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0362GraphCenterC__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0354GraphCenterD__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0357GraphWholeA__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0357GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0361GraphWholeC__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0357GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0345Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0363GraphCenterD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0365GraphWholeA__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0367GraphCenterB__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0368GraphWholeB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0369Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0370GraphWholeD__6
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0371GraphCenterD__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0371GraphWholeC__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0372GraphCenterA__5
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0372GraphCenterC__10

-- ===== source module GeneralCK.Certificates.E8TAxisProd0362CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0362CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0362GraphCenterA.qJetBox,
   E8TAxisProd0362GraphCenterB.qJetBox,
   E8TAxisProd0362GraphCenterC.qJetBox,
   E8TAxisProd0362GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0362GraphWholeA.qJetBox,
   E8TAxisProd0362GraphWholeB.qJetBox,
   E8TAxisProd0362GraphWholeC.qJetBox,
   E8TAxisProd0362GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨62631304550921547214660513660647767635794456265, 62631304550921547214660513660648091532240163979⟩
  | 0, 2 => ⟨176499758305196817539845877319132116124942022423, 176499758305196817539845877319133447776411537304⟩
  | 1, 1 => ⟨177142896019165920324818133287310937153779630981, 177142896019165920324818133287313390752991640845⟩
  | 0, 3 => ⟨342623980353609023135060099289181664819011888148, 342623980353609023135060099289186146032311058643⟩
  | 1, 2 => ⟨457696303578535359778767631487476785743299598114, 457696303578535359778767631487484960570117067473⟩
  | 2, 1 => ⟨459169424681337791280025519003999309933644377855, 459169424681337791280025519004014389804215803961⟩
  | 0, 4 => ⟨554871978344843272524328151460007168105702802338, 554871978344843272524328151460023055195990884316⟩
  | 1, 3 => ⟨817624702891125368040003350475743519820611975551, 817624702891125368040003350475772800157688357387⟩
  | 2, 2 => ⟨1081061210189186593513054070635389317708241679446, 1081061210189186593513054070635443862594835439321⟩
  | 3, 1 => ⟨1084157043067489501163351030672929802384341837168, 1084157043067489501163351030673032136126179007849⟩
  | 0, 5 => ⟨-3157503475825878863347607203335711278733095966796487, 3172754230396943057931939546302774028541240224707240⟩
  | 1, 4 => ⟨-6203942810537539880584522794890061926235397287879447, 6226925265563555431375110478129323530739394056694067⟩
  | 2, 3 => ⟨-12200715366628907651353328574988640459584315207811537, 12233820267538634931427285723239694813657220459793875⟩
  | 3, 2 => ⟨-24009332580194181246862900257012028571971732001293385, 24052735686040543202665443532607510105886502788437841⟩
  | 4, 1 => ⟨-47271646079287828243295277457616972778225757129933401, 47315851910017377282705746726904012930731058710770925⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0362Geometry.ds, E8TAxisProd0362Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 59037008610636430340164777950106806542209887304 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0362CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0363CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0363CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0363GraphCenterA.qJetBox,
   E8TAxisProd0363GraphCenterB.qJetBox,
   E8TAxisProd0363GraphCenterC.qJetBox,
   E8TAxisProd0363GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0363GraphWholeA.qJetBox,
   E8TAxisProd0363GraphWholeB.qJetBox,
   E8TAxisProd0363GraphWholeC.qJetBox,
   E8TAxisProd0363GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨56553515214720367538221848261144087428602062530, 56553515214720367538221848261144380255695546391⟩
  | 0, 2 => ⟨160731640892961563466852513943785180312436915303, 160731640892961563466852513943786375944625580351⟩
  | 1, 1 => ⟨161323790604501013513337746663193561589429815778, 161323790604501013513337746663195759867847905142⟩
  | 0, 3 => ⟨314364704945307691452954243312890837067052190012, 314364704945307691452954243312894845417392518479⟩
  | 1, 2 => ⟨420318796589378956180074197139511349844714852810, 420318796589378956180074197139518647443742829205⟩
  | 2, 1 => ⟨421684549471920240337207336801569011278255840937, 421684549471920240337207336801582451032895016961⟩
  | 0, 4 => ⟨512219488950510516002415663767850012440622256108, 512219488950510516002415663767864150015235509725⟩
  | 1, 3 => ⟨755823729517005310972219388343613283183437778427, 755823729517005310972219388343639296424459560027⟩
  | 2, 2 => ⟨1000065598215301453340771663093282261840221975802, 1000065598215301453340771663093330656342636172740⟩
  | 3, 1 => ⟨1002947574308186331390236163064554871503870432482, 1002947574308186331390236163064645554555082118164⟩
  | 0, 5 => ⟨-2841771610227864837038176580607438485603141095537890, 2855767038286098537290704624188962370773659082359386⟩
  | 1, 4 => ⟨-5581149112010785662262117829163439141156318871833969, 5602245298182827240799424062138763573120597548095285⟩
  | 2, 3 => ⟨-10971212388909739842778835458575983490589978749683248, 11001607250027162201327379188887652847165333371365988⟩
  | 3, 2 => ⟨-21580585676465664825345764610754942072157094103071720, 21620442724950403241508862255442967414492227276313706⟩
  | 4, 1 => ⟨-42471415717810846346656655069711852445620375767377493, 42512017754065616113606343007802782958376950755731079⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0363Geometry.ds, E8TAxisProd0363Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 53282263264143035814591842320455821215741006015 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0363CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0364CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0364CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0364GraphCenterA.qJetBox,
   E8TAxisProd0364GraphCenterB.qJetBox,
   E8TAxisProd0364GraphCenterC.qJetBox,
   E8TAxisProd0364GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0364GraphWholeA.qJetBox,
   E8TAxisProd0364GraphWholeB.qJetBox,
   E8TAxisProd0364GraphWholeC.qJetBox,
   E8TAxisProd0364GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨51203680931391109229375835086527212377064493834, 51203680931391109229375835086527477782350977338⟩
  | 0, 2 => ⟨146616404931657630277712957190868775790826947182, 146616404931657630277712957190869851768260016766⟩
  | 1, 1 => ⟨147283343758629570133901509795919524535681859461, 147283343758629570133901509795921498460199773097⟩
  | 0, 3 => ⟨288837890595568632933143780623363741267331804580, 288837890595568632933143780623367334615327239726⟩
  | 1, 2 => ⟨386621959861192885016879801642560987203846245428, 386621959861192885016879801642567515821141632942⟩
  | 2, 1 => ⟨388171103877413566288896019743509917104704772290, 388171103877413566288896019743521920739421452785⟩
  | 0, 4 => ⟨473496455495952664467299735645778234171046818039, 473496455495952664467299735645790842696457329406⟩
  | 1, 3 => ⟨699740866395289615208866857204361904616474425830, 699740866395289615208866857204385065156979419803⟩
  | 2, 2 => ⟨926712953589749782973611627495114935052504961874, 926712953589749782973611627495157964062969459068⟩
  | 3, 1 => ⟨929996024050928118566472612467197093291108432884, 929996024050928118566472612467277621485435265292⟩
  | 0, 5 => ⟨-2555594528281659932397085439333707020729735042847119, 2568441465499938963441897145405955831323069440607454⟩
  | 1, 4 => ⟨-5016851520628774975402477344626713937575902534926630, 5036221470413057093766712521182080788301770538185315⟩
  | 2, 3 => ⟨-9857599235859195194975317469550829283016060961227985, 9885515253701617047954317952990376371938367546646936⟩
  | 3, 2 => ⟨-19381598814880908468073318622597525383591587267415609, 19418220117032775011727712946253745415807427340033808⟩
  | 4, 1 => ⟨-38126975532195197545940047618911962431933657053691181, 38164319094088080112831369190172367777478447724042396⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0364Geometry.ds, E8TAxisProd0364Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 48219663800056811143559901228730212442004767668 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0364CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0365CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0365CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0365GraphCenterA.qJetBox,
   E8TAxisProd0365GraphCenterB.qJetBox,
   E8TAxisProd0365GraphCenterC.qJetBox,
   E8TAxisProd0365GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0365GraphWholeA.qJetBox,
   E8TAxisProd0365GraphWholeB.qJetBox,
   E8TAxisProd0365GraphWholeC.qJetBox,
   E8TAxisProd0365GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨46154292961935483849694897918186698954869098464, 46154292961935483849694897918186939111999552389⟩
  | 0, 2 => ⟨133305239785551785123164001483224967013736138367, 133305239785551785123164001483225933287570720700⟩
  | 1, 1 => ⟨133918576567562917208513719476670753256402459009, 133918576567562917208513719476672521823026298198⟩
  | 0, 3 => ⟨264662653241428797726399205367256809358633713071, 264662653241428797726399205367260023365761631371⟩
  | 1, 2 => ⟨354593114490852167195587113134463376189849445096, 354593114490852167195587113134469203072531614912⟩
  | 2, 1 => ⟨356028400254334999603905531600184712262173347269, 356028400254334999603905531600195407286631509945⟩
  | 0, 4 => ⟨436702996155283876841652430365005054979294818833, 436702996155283876841652430365016271907998689358⟩
  | 1, 3 => ⟨646321655007307844656848976797319841049067124851, 646321655007307844656848976797340409031411497057⟩
  | 2, 2 => ⟨856619012350429515504162124580557931682517227514, 856619012350429515504162124580596090477107720832⟩
  | 3, 1 => ⟨859675094425174089913470601499755143817556506059, 859675094425174089913470601499826465264100228526⟩
  | 0, 5 => ⟨-2288276745462298182541555716305086387161604535763725, 2300044579062562230155275379282047385444237331893922⟩
  | 1, 4 => ⟨-4489950793698538081088599044693642962020066230659478, 4507698103614386777130394478705176716983380972548889⟩
  | 2, 3 => ⟨-8818198374210349063454588558525538743575624187240976, 8843781967104399397558134673705244047069636354745860⟩
  | 3, 2 => ⟨-17329970158782234113498173355134488457452882971548603, 17363539007541318791780203153838767020644285929417200⟩
  | 4, 1 => ⟨-34075288666508972062127288057208826126887551760628163, 34109531186956874185630802672887653209872398407028168⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0365Geometry.ds, E8TAxisProd0365Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 43443259963577683385798348135219114107630673486 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0365CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0366CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0366CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0366GraphCenterA.qJetBox,
   E8TAxisProd0366GraphCenterB.qJetBox,
   E8TAxisProd0366GraphCenterC.qJetBox,
   E8TAxisProd0366GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0366GraphWholeA.qJetBox,
   E8TAxisProd0366GraphWholeB.qJetBox,
   E8TAxisProd0366GraphWholeC.qJetBox,
   E8TAxisProd0366GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨51020635925765750200612090115493203959698422654, 51020635925765750200612090115493468811975407647⟩
  | 0, 2 => ⟨146255727263070586332122038729247503415407992637, 146255727263070586332122038729248577029464669302⟩
  | 1, 1 => ⟨146800612635591777126626044189902890274016984025, 146800612635591777126626044189904859824026751318⟩
  | 0, 3 => ⟨288246558627488624472606676243511043682687311778, 288246558627488624472606676243514628969263860576⟩
  | 1, 2 => ⟨385748113490729776279441937012835597815829378857, 385748113490729776279441937012842111673222587112⟩
  | 2, 1 => ⟨387013916684357300818191826455397948266326809660, 387013916684357300818191826455409924571123789327⟩
  | 0, 4 => ⟨472634933281559027448227254256347309400650279958, 472634933281559027448227254256359888362048275788⟩
  | 1, 3 => ⟨698413707355342656533188927014823566777472824703, 698413707355342656533188927014846672820921373715⟩
  | 2, 2 => ⟨924787131113811856866340269418235836307867469309, 924787131113811856866340269418278763681153086096⟩
  | 3, 1 => ⟨927469934593346283539650314439979523488059996821, 927469934593346283539650314440059860666303140245⟩
  | 0, 5 => ⟨-2549912250246122077246946339585389311637819221593255, 2562731985399985639972228125958528390302385186595247⟩
  | 1, 4 => ⟨-5005664465706779338026582330780489719991691794889093, 5024992191174091384944197279641343911864344704238050⟩
  | 2, 3 => ⟨-9835552049095632407354541371268330425141427035665432, 9863403951659911903254878277289769965880082844377751⟩
  | 3, 2 => ⟨-19338117587897940030565114367866873287594846844806367, 19374645108272676890216268786939938216381622362900378⟩
  | 4, 1 => ⟨-38041174246994143597083692652332621365888148668908774, 38078390409086778192350157191053032668508759617893153⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0366Geometry.ds, E8TAxisProd0366Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 48046117966002936767171761027389615000937592800 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0366CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0367CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0367CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0367GraphCenterA.qJetBox,
   E8TAxisProd0367GraphCenterB.qJetBox,
   E8TAxisProd0367GraphCenterC.qJetBox,
   E8TAxisProd0367GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0367GraphWholeA.qJetBox,
   E8TAxisProd0367GraphWholeB.qJetBox,
   E8TAxisProd0367GraphWholeC.qJetBox,
   E8TAxisProd0367GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨45987868037810450678755056317570493429672978770, 45987868037810450678755056317570733087065914633⟩
  | 0, 2 => ⟨132974752435281404731173634458288686196808884412, 132974752435281404731173634458289650345549161772⟩
  | 1, 1 => ⟨133475839792443818394913258889757662579265816253, 133475839792443818394913258889759427219034809565⟩
  | 0, 3 => ⟨264117273469022788784724789113159436004493451091, 264117273469022788784724789113162642788667772798⟩
  | 1, 2 => ⟨353785982227794083765836481047667167740708939110, 353785982227794083765836481047672981419809644686⟩
  | 2, 1 => ⟨354958744703705196152134499651919240739143896930, 354958744703705196152134499651929911346112834845⟩
  | 0, 4 => ⟨435904862474542667719894563338645629302443772895, 435904862474542667719894563338656819863839476315⟩
  | 1, 3 => ⟨645090320126872572871606237040267855233222640242, 645090320126872572871606237040288374678844025261⟩
  | 2, 2 => ⟨854830404316996321790037713321415906215081808780, 854830404316996321790037713321453974584242337756⟩
  | 3, 1 => ⟨857327719894543044481123240052696272090124212559, 857327719894543044481123240052767423752339012735⟩
  | 0, 5 => ⟨-2283233904596537010848603450865567030689783760490537, 2294977907289903452106093214635994018166801243943957⟩
  | 1, 4 => ⟨-4480026473711935207534145691080645117879200733705392, 4497736880427529423226061438109666679285034837859848⟩
  | 2, 3 => ⟨-8798646715158268470288732813260498172539366176027298, 8824174348440937151547816759944541232956670438811458⟩
  | 3, 2 => ⟨-17291423552390428729149273139748384284977857791720460, 17324910507105155031245278802331734612912623592297454⟩
  | 4, 1 => ⟨-33999249364656784694027023521576194718434810633547686, 34033380192621709090951789765764408123696943582793502⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0367Geometry.ds, E8TAxisProd0367Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 43285536076858080252098131140672954564796971161 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0367CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0368CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0368CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0368GraphCenterA.qJetBox,
   E8TAxisProd0368GraphCenterB.qJetBox,
   E8TAxisProd0368GraphCenterC.qJetBox,
   E8TAxisProd0368GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0368GraphWholeA.qJetBox,
   E8TAxisProd0368GraphWholeB.qJetBox,
   E8TAxisProd0368GraphWholeC.qJetBox,
   E8TAxisProd0368GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨93102728257748036475599588569752168540202013069, 93102728257748036475599588569752654294640965078⟩
  | 0, 2 => ⟨254109815436895901316026505953697406510027767153, 254109815436895901316026505953699453091175109844⟩
  | 1, 1 => ⟨254801201231126127802147377885474288358930178707, 254801201231126127802147377885478088548257620333⟩
  | 0, 3 => ⟨479581302709418519557702055786253032482814234551, 479581302709418519557702055786260015682388555093⟩
  | 1, 2 => ⟨638384718416441887327199470636261810187915718655, 638384718416441887327199470636274643116528922549⟩
  | 2, 1 => ⟨639929189284316441497408878360840100931568370840, 639929189284316441497408878360863918363638565633⟩
  | 0, 4 => ⟨759637022040858997664758305521779714461059049869, 759637022040858997664758305521804959292724972044⟩
  | 1, 3 => ⟨1113556559647080155215115523887224188145398435009, 1113556559647080155215115523887270995669921441859⟩
  | 2, 2 => ⟨1468179225603894022543107884510715051052914476196, 1468179225603894022543107884510802680110437462454⟩
  | 3, 1 => ⟨1471380105335067557772351755968168910776486565265, 1471380105335067557772351755968334079647445049677⟩
  | 0, 5 => ⟨-4661882863559100179018546847600523444180973894477550, 4682812776195146956956079150146013331948085717492645⟩
  | 1, 4 => ⟨-9173530486672881773254252624887200972015464495616600, 9204995204515708672289988812172343372021646583874033⟩
  | 2, 3 => ⟨-18067646341783846689905663571209456998220164225578228, 18112875310122211733880684152132277403175208486057002⟩
  | 3, 2 => ⟨-35607948493492716230931730617840426338231865238379838, 35667144873221184422799544084892463017162372355505944⟩
  | 4, 1 => ⟨-70214109621248550378593822382707537258331545222606771, 70274257285403480884659745870699488976569024983403603⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0368Geometry.ds, E8TAxisProd0368Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 87925920226829097559111554294436069766927550244 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0368CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0369CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0369CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0369GraphCenterA.qJetBox,
   E8TAxisProd0369GraphCenterB.qJetBox,
   E8TAxisProd0369GraphCenterC.qJetBox,
   E8TAxisProd0369GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0369GraphWholeA.qJetBox,
   E8TAxisProd0369GraphWholeB.qJetBox,
   E8TAxisProd0369GraphWholeC.qJetBox,
   E8TAxisProd0369GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨84347877928857725380415601709901310979559908025, 84347877928857725380415601709901749447642852558⟩
  | 0, 2 => ⟨232092227964409228386784300354348518361113144211, 232092227964409228386784300354350355197417490076⟩
  | 1, 1 => ⟨232730127982474334369965797101016724075457339136, 232730127982474334369965797101020128564009067228⟩
  | 0, 3 => ⟨441067388845028985082720536273845165931040335601, 441067388845028985082720536273851412746238467335⟩
  | 1, 2 => ⟨587589963025926701831154339091841022615980390337, 587589963025926701831154339091852482246290036894⟩
  | 2, 1 => ⟨589023413160525387698980999110096408204979655110, 589023413160525387698980999110117645583956251712⟩
  | 0, 4 => ⟨702352806281760764396536543818740987296762092856, 702352806281760764396536543818763463018382351120⟩
  | 1, 3 => ⟨1030833532453788118108694671528738621616261346648, 1030833532453788118108694671528780235277781956800⟩
  | 2, 2 => ⟨1359969702796712964593658508335733383816032608201, 1359969702796712964593658508335811196437002490885⟩
  | 3, 1 => ⟨1362949967383829796399950760187157777895962424457, 1362949967383829796399950760187304279622971750210⟩
  | 0, 5 => ⟨-4245511562407806362826073759525999937044440313156297, 4264898600545152409285606410693003027108081395501470⟩
  | 1, 4 => ⟨-8351345509848404235775557013803504266216128422762215, 8380513651477803121396178785397991164861347134661090⟩
  | 2, 3 => ⟨-16442674333122495098445923246372310643945575990802655, 16484628817729993452321738760783816160504199703859593⟩
  | 3, 2 => ⟨-32394204540818265577435627077348870267919113507610264, 32449140280258252784812353718934874620454910293715884⟩
  | 4, 1 => ⟨-63854613980102392394123949283871668706316675689844444, 63910455959725384550390197072921773577056810488013814⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0369Geometry.ds, E8TAxisProd0369Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 79619971830081196645141513730377266267821713537 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0369CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0370CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0370CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0370GraphCenterA.qJetBox,
   E8TAxisProd0370GraphCenterB.qJetBox,
   E8TAxisProd0370GraphCenterC.qJetBox,
   E8TAxisProd0370GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0370GraphWholeA.qJetBox,
   E8TAxisProd0370GraphWholeB.qJetBox,
   E8TAxisProd0370GraphWholeC.qJetBox,
   E8TAxisProd0370GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨92785465414176957583688613285660286427686195743, 92785465414176957583688613285660771164119660420⟩
  | 0, 2 => ⟨253510931923039293178876181876265065895457792141, 253510931923039293178876181876267108014136327859⟩
  | 1, 1 => ⟨254004089761150117062099795885764953655255207120, 254004089761150117062099795885768745511792038311⟩
  | 0, 3 => ⟨478632600860104390398678725614164116726827162142, 478632600860104390398678725614171084409423407624⟩
  | 1, 2 => ⟨636994063776428774190351955215637578585591927581, 636994063776428774190351955215650382860927166911⟩
  | 2, 1 => ⟨638095828936405307014119679842357222485815944966, 638095828936405307014119679842380986498822830700⟩
  | 0, 4 => ⟨758286307025192563525410623319064793545935508528, 758286307025192563525410623319089979998708262383⟩
  | 1, 3 => ⟨1111491449537646012094140951294705543853067729502, 1111491449537646012094140951294752242963049583645⟩
  | 2, 2 => ⟨1465198213166621947312773567669927942243858619423, 1465198213166621947312773567670015367937457685894⟩
  | 3, 1 => ⟨1467481718582233608259123736427747148281739854124, 1467481718582233608259123736427911932959593765062⟩
  | 0, 5 => ⟨-4653078142029926368669031835113558491071301724043579, 4673967654643629212347803850877981611535046571955158⟩
  | 1, 4 => ⟨-9156174915856707297334556038272965043347367162007127, 9187577174095986183498868342601328052950048235486611⟩
  | 2, 3 => ⟨-18033398224054582677987511150997555831985106157777464, 18078532163972589324118459918728561284035621194460815⟩
  | 3, 2 => ⟨-35540314096950272329219384190244939415683631119564622, 35599369734041673986461145390248274550069572038097726⟩
  | 4, 1 => ⟨-70080462607465758242698903083002159979359322964793700, 70140412632063674351322681035575180325745170346276328⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0370Geometry.ds, E8TAxisProd0370Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 87624294073339041321077401190972923664072464450 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0370CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0371CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0371CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0371GraphCenterA.qJetBox,
   E8TAxisProd0371GraphCenterB.qJetBox,
   E8TAxisProd0371GraphCenterC.qJetBox,
   E8TAxisProd0371GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0371GraphWholeA.qJetBox,
   E8TAxisProd0371GraphWholeB.qJetBox,
   E8TAxisProd0371GraphWholeC.qJetBox,
   E8TAxisProd0371GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨84058106999271322118361521151294369196809389254, 84058106999271322118361521151294806746660603413⟩
  | 0, 2 => ⟨231541442114969316418085568611552597594913038458, 231541442114969316418085568611554430421315453475⟩
  | 1, 1 => ⟨231996445367636936801288594047645458893282386049, 231996445367636936801288594047648855904089864300⟩
  | 0, 3 => ⟨440190231362017179123312768695017396470521213937, 440190231362017179123312768695023629383989629561⟩
  | 1, 2 => ⟨586302620345407456536319908897877151496240082558, 586302620345407456536319908897888585489323047226⟩
  | 2, 1 => ⟨587325183425622735568170718740001071590628791915, 587325183425622735568170718740022261224131811229⟩
  | 0, 4 => ⟨701099510931677334589298596325793351677431544322, 701099510931677334589298596325815775308820886189⟩
  | 1, 3 => ⟨1028915301176566699442626525228648061822896397184, 1028915301176566699442626525228689578858223107709⟩
  | 2, 2 => ⟨1357198694568845065905407906573840680522922716600, 1357198694568845065905407906573918312055266960184⟩
  | 3, 1 => ⟨1359324811389602224061474601181590091075021567153, 1359324811389602224061474601181736250969627430693⟩
  | 0, 5 => ⟨-4237262443897636570536076934458397611853531079953180, 4256611601324659800694888223537373504531263503365115⟩
  | 1, 4 => ⟨-8335087167161316459040229658792990625153051016927398, 8364196566437496331477577604407498713946407657849916⟩
  | 2, 3 => ⟨-16410596070473127681633910944696946263163602592360197, 16452460977125993189672946384704892787569250053626896⟩
  | 3, 2 => ⟨-32330865331685792619076893239879743913613955591189698, 32385668238054764276615661563609249851444230892892056⟩
  | 4, 1 => ⟨-63729475527643478121460360637986531257858916000307776, 63785131068422287348869784825433124244134273253531517⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0371Geometry.ds, E8TAxisProd0371Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 79344604839695110986241310684549668778272280580 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0371CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0372CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0372CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0372GraphCenterA.qJetBox,
   E8TAxisProd0372GraphCenterB.qJetBox,
   E8TAxisProd0372GraphCenterC.qJetBox,
   E8TAxisProd0372GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0372GraphWholeA.qJetBox,
   E8TAxisProd0372GraphWholeB.qJetBox,
   E8TAxisProd0372GraphWholeC.qJetBox,
   E8TAxisProd0372GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨76354158037086945538696292064199828468833164057, 76354158037086945538696292064200224401538476603⟩
  | 0, 2 => ⟨211831863376683937780609520889625791673051578359, 211831863376683937780609520889627440412843929888⟩
  | 1, 1 => ⟨212420128263496104354031635595828205030186047225, 212420128263496104354031635595831255087578114383⟩
  | 0, 3 => ⟨405420278231911608204299703684671282118886601871, 405420278231911608204299703684676870097617952602⟩
  | 1, 2 => ⟨540545986232789815747758027768716269622932432369, 540545986232789815747758027768726502126518421138⟩
  | 2, 1 => ⟨541876070083550294805204516264115600655624894030, 541876070083550294805204516264134535288651563227⟩
  | 0, 4 => ⟨649147846779736854180382155040615519323460440998, 649147846779736854180382155040635527269067091826⟩
  | 1, 3 => ⟨953943607509719826034178335686097206290969379029, 953943607509719826034178335686134196158951942443⟩
  | 2, 2 => ⟨1259350406917455009136175766827200146599571277343, 1259350406917455009136175766827269228579761579425⟩
  | 3, 1 => ⟨1262125126459087727223184630896152089806956461742, 1262125126459087727223184630896282004631664346102⟩
  | 0, 5 => ⟨-3854846963352840310522754785473919784083191776505461, 3872776317983108162354235989561481955583101004578504⟩
  | 1, 4 => ⟨-7580100847330175020364348197179495241966122844956838, 7607093513572282149318076010907919792317642387468423⟩
  | 2, 3 => ⟨-14918766393510957804464889896191971564536227314010544, 14957612821644465906200573874254181560785541682212066⟩
  | 3, 2 => ⟨-29381146710084963492264819146802319893043163549773006, 29432033203677114217076315306234124647691181896521994⟩
  | 4, 1 => ⟨-57893925927115040040992277600660784565008800366326533, 57945673449777316251159419907649920659455285598425198⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0372Geometry.ds, E8TAxisProd0372Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 72039895879269928683296853714951117282349550049 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0372CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0373CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0373CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0373GraphCenterA.qJetBox,
   E8TAxisProd0373GraphCenterB.qJetBox,
   E8TAxisProd0373GraphCenterC.qJetBox,
   E8TAxisProd0373GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0373GraphWholeA.qJetBox,
   E8TAxisProd0373GraphWholeB.qJetBox,
   E8TAxisProd0373GraphWholeC.qJetBox,
   E8TAxisProd0373GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨69060649216916590039545970228478711614990091145, 69060649216916590039545970228479069276944189877⟩
  | 0, 2 => ⟨193198715408213273965030035909608824396562970180, 193198715408213273965030035909610304439787337225⟩
  | 1, 1 => ⟨193740930238070477358084375620717689239334760519, 193740930238070477358084375620720421815777080823⟩
  | 0, 3 => ⟨372437628388792160996414826634008752383463640339, 372437628388792160996414826634013750931857492739⟩
  | 1, 2 => ⟨496989482017619698643534149010577115858009406030, 496989482017619698643534149010586251934805306189⟩
  | 2, 1 => ⟨498223330749893876265359186670821395370810139458, 498223330749893876265359186670838274986047073346⟩
  | 0, 4 => ⟨599741219877029810306480362700964116109783479502, 599741219877029810306480362700981925265772607713⟩
  | 1, 3 => ⟨882485973074968079252538205952581855154805776376, 882485973074968079252538205952614729692303667988⟩
  | 2, 2 => ⟨1165800414723470025843820458947535040221484760438, 1165800414723470025843820458947596359277239745012⟩
  | 3, 1 => ⟨1168383652029322476992884771136423855839953064776, 1168383652029322476992884771136539036369968201781⟩
  | 0, 5 => ⟨-3489856655129023339892517315418550053660489065527261, 3506400528848951155982196362536698714410414029353988⟩
  | 1, 4 => ⟨-6859730812285190631248461857140080635585311856313727, 6884651047278772510402394016081374753994098985125333⟩
  | 2, 3 => ⟨-13495778879624540225111723042455122346185317205584814, 13531659053258545273514421412704746652226027941822682⟩
  | 3, 2 => ⟨-26568448747609248001560487797856074739036499370007842, 26615465750506797900713284458737308333632472549833898⟩
  | 4, 1 => ⟨-52331292215580952364068449130813867123684224098122245, 52379122643930201566191986959865600838965429625390094⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0373Geometry.ds, E8TAxisProd0373Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 65127244872783507861158485041985510741204291761 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0373CertifiedArithmetic

end


