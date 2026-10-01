-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0423CertifiedArithmetic__11
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0423CertifiedArithmetic__11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:55:58.387768+00:00
-- url     : https://prove2.me/theorems/19e42d0e-b147-43bb-bb81-0a1ef155583c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0423CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0424CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0423CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0424CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0425CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0426CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0427CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0428CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0429CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0430CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0431CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0432CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0433CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0423CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0424CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0425CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0426CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0427CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0428CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0429CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0430CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0431CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0432CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0433CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0423CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0424CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0425CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0426CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0427CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0428CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0429CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0430CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0431CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0432CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0433CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0423CertifiedArithmetic (+10 modules: GeneralCK/Certificates/E8TAxisProd0424CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0425CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0426CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0427CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0428CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0429CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0430CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0431CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0432CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0433CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0416GraphCenterA__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0418GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0422GraphCenterC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0413GraphCenterD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0413GraphWholeA__18
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0419GraphWholeB__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0416GraphWholeC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0418GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0419Geometry__26
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0429GraphWholeC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0430GraphCenterD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0431GraphWholeA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0431GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0433GraphCenterA__12

-- ===== source module GeneralCK.Certificates.E8TAxisProd0423CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0423CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0423GraphCenterA.qJetBox,
   E8TAxisProd0423GraphCenterB.qJetBox,
   E8TAxisProd0423GraphCenterC.qJetBox,
   E8TAxisProd0423GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0423GraphWholeA.qJetBox,
   E8TAxisProd0423GraphWholeB.qJetBox,
   E8TAxisProd0423GraphWholeC.qJetBox,
   E8TAxisProd0423GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨19365931403562796313790455740094158684526338840, 19365931403562796313790455740094268421172454504⟩
  | 0, 2 => ⟨60136359422298484896381259218911680768133762477, 60136359422298484896381259218912092163697894311⟩
  | 1, 1 => ⟨60386278181975821239885400465879067101116970965, 60386278181975821239885400465879803548658841190⟩
  | 0, 3 => ⟨127583888012962822316341443698629125092002091209, 127583888012962822316341443698630453815099848185⟩
  | 1, 2 => ⟨172327225296976201436467315774709476389261749992, 172327225296976201436467315774711838867997409451⟩
  | 2, 1 => ⟨172953773814731840878526954725873586545367245232, 172953773814731840878526954725877859391516130217⟩
  | 0, 4 => ⟨223573822321868895709623459281433685268153718982, 223573822321868895709623459281438164102722702410⟩
  | 1, 3 => ⟨335344353310823630594884932776430242087594408803, 335344353310823630594884932776438328483258556877⟩
  | 2, 2 => ⟨447433445481129757518027028351484930509242180908, 447433445481129757518027028351499757771493394041⟩
  | 3, 1 => ⟨448838473532862186261491515739930501379408134817, 448838473532862186261491515739957920736985624762⟩
  | 0, 5 => ⟨-874959573402391118937491493621550188652353655955093, 880043035520720401868034175340902118279460711915745⟩
  | 1, 4 => ⟨-1708827064201889606149025616308048124692902909186905, 1716458830109340182496927574238535422939236513768148⟩
  | 2, 3 => ⟨-3341048891749372088918600141790564832447085186396043, 3352022628236135404587558273092762894085918631244391⟩
  | 3, 2 => ⟨-6536871311466471549259338333523053031759766262058920, 6551260383523982598683363957423517795158972653298132⟩
  | 4, 1 => ⟨-12796197637712977181323605161308218817622639024641574, 12810901070727172696724464643799763790400784383698514⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0423Geometry.ds, E8TAxisProd0423Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 18153205451986679816032550142045074258176380313 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0423CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0424CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0424CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0424GraphCenterA.qJetBox,
   E8TAxisProd0424GraphCenterB.qJetBox,
   E8TAxisProd0424GraphCenterC.qJetBox,
   E8TAxisProd0424GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0424GraphWholeA.qJetBox,
   E8TAxisProd0424GraphWholeB.qJetBox,
   E8TAxisProd0424GraphWholeC.qJetBox,
   E8TAxisProd0424GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨41262983156550928099475134859928538235140641685, 41262983156550928099475134859928754744657610899⟩
  | 0, 2 => ⟨120496347170805898121827937896660659197516728741, 120496347170805898121827937896661523229602108697⟩
  | 1, 1 => ⟨120853998544099249707161887952888864125293291348, 120853998544099249707161887952890441672600949779⟩
  | 0, 3 => ⟨241333317372235279511628528423322295862137315538, 241333317372235279511628528423325157562636481335⟩
  | 1, 2 => ⟨323504104145546672111876371777105269251372524864, 323504104145546672111876371777110445662633023136⟩
  | 2, 1 => ⟨324347762555059036942648176495189105407504615502, 324347762555059036942648176495198589413480581829⟩
  | 0, 4 => ⟨401092260514445073161117271218127488880472571781, 401092260514445073161117271218137419372034319771⟩
  | 1, 3 => ⟨594429624437221682061739170846251204107137636491, 594429624437221682061739170846269379467044418069⟩
  | 2, 2 => ⟨788168886755790310517842871280228918067715228967, 788168886755790310517842871280262588514028368349⟩
  | 3, 1 => ⟨789974636273477877659781689901444310253178471104, 789974636273477877659781689901507157891587021382⟩
  | 0, 5 => ⟨-2039825791108423153276274229807337450676783431467590, 2050577368135246154319277040642708579046754898118778⟩
  | 1, 4 => ⟨-4000459748507516351036145306497981208045162848923304, 4016679346154369202229071461703102513069616759899161⟩
  | 2, 3 => ⟨-7853011733197352710700290317841063267629375392104812, 7876397760588849164821236554874257418976460720069036⟩
  | 3, 2 => ⟨-15425630562847647601198645361103074066528098454280830, 15456314168256290744606589029244480753545613241516182⟩
  | 4, 1 => ⟨-30316032635578645859505257333009603339015741750364361, 30347307535509012155904834417095112275035093081462502⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0424Geometry.ds, E8TAxisProd0424Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 38817777962211123630321419796637026056164140022 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0424CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0425CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0425CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0425GraphCenterA.qJetBox,
   E8TAxisProd0425GraphCenterB.qJetBox,
   E8TAxisProd0425GraphCenterC.qJetBox,
   E8TAxisProd0425GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0425GraphWholeA.qJetBox,
   E8TAxisProd0425GraphWholeB.qJetBox,
   E8TAxisProd0425GraphWholeC.qJetBox,
   E8TAxisProd0425GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨37123249278020106854290433398494837212601833574, 37123249278020106854290433398495033313018426153⟩
  | 0, 2 => ⟨109366166390720898456912230751915950659944651170, 109366166390720898456912230751916726767708591409⟩
  | 1, 1 => ⟨109694637477238581257558823197686219494016182030, 109694637477238581257558823197687632938973455141⟩
  | 0, 3 => ⟨220805954594305427004926424244248081051974846656, 220805954594305427004926424244250640848906796578⟩
  | 1, 2 => ⟨296275644312121550372364803678418231502053543780, 296275644312121550372364803678422851174761448798⟩
  | 2, 1 => ⟨297056680735321620684389933803626597356167536846, 297056680735321620684389933803635046092262676578⟩
  | 0, 4 => ⟨369542188306282654480457858910149383342200443292, 369542188306282654480457858910158219382911492162⟩
  | 1, 3 => ⟨548530430351603452161748533081808305530249111770, 548530430351603452161748533081824447434138262804⟩
  | 2, 2 => ⟨727893599526229307149373596546090943788840093971, 727893599526229307149373596546120803477268017224⟩
  | 3, 1 => ⟨729574381734508238190556901121257402465965338453, 729574381734508238190556901121313062745708734356⟩
  | 0, 5 => ⟨-1820033873691023480656503990493549948923966868700866, 1829833828837212523527749171618025471274959880899263⟩
  | 1, 4 => ⟨-3567562092639369818681727673132315956158193665559695, 3582350080483294157200540437168873145177503268741743⟩
  | 2, 3 => ⟨-6999694676835329492806080113498568786923207457381871, 7021023311479741674259535978036137938712423223343721⟩
  | 3, 2 => ⟨-13742592769130909749092306851175952812841133994488596, 13770586627115193679734538988916154867852152703960008⟩
  | 4, 1 => ⟨-26994831975909097531947417562195626810421449347298745, 27023380233035288298318514386439592851276357135186847⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0425Geometry.ds, E8TAxisProd0425Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 34905784679667544013102564959268525132519689131 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0425CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0426CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0426CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0426GraphCenterA.qJetBox,
   E8TAxisProd0426GraphCenterB.qJetBox,
   E8TAxisProd0426GraphCenterC.qJetBox,
   E8TAxisProd0426GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0426GraphWholeA.qJetBox,
   E8TAxisProd0426GraphWholeB.qJetBox,
   E8TAxisProd0426GraphWholeC.qJetBox,
   E8TAxisProd0426GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨41112551133737716058185340258564649516529584657, 41112551133737716058185340258564865576161456833⟩
  | 0, 2 => ⟨120194993685482738281436897873500501082767581367, 120194993685482738281436897873501363212052572187⟩
  | 1, 1 => ⟨120450082515512652398324109345646995357773781236, 120450082515512652398324109345648569395206620393⟩
  | 0, 3 => ⟨240832412629479709977508735975941960986695885320, 240832412629479709977508735975944816244172401377⟩
  | 1, 2 => ⟨322761778729429436319384989417674784649770026275, 322761778729429436319384989417679949302843122800⟩
  | 2, 1 => ⟨323363586105955613627145512651218769611336477718, 323363586105955613627145512651228231901133538562⟩
  | 0, 4 => ⟨400355534117985235485853792598983927463254327174, 400355534117985235485853792598993834548169562085⟩
  | 1, 3 => ⟨593291369565962316270487942103146511185512068088, 593291369565962316270487942103164643520864918018⟩
  | 2, 2 => ⟨786513928365533792631831200000399711238849019921, 786513928365533792631831200000433301616185005076⟩
  | 3, 1 => ⟨787802141880688948075135254681583968397445671445, 787802141880688948075135254681646665842627227005⟩
  | 0, 5 => ⟨-2035188886631475940896537062119217528177385386556077, 2045917914437012627674409740271853265549638052403177⟩
  | 1, 4 => ⟨-3991336683628378924045807682643623157684513276059974, 4007521350070510378234513030918495549088336723498275⟩
  | 2, 3 => ⟨-7835043435983784276837521345359810589046958386528260, 7858376594478097834338862584125472406800507477796355⟩
  | 3, 2 => ⟨-15390215364170564934262410056302400178692440163317306, 15420822059950252494388865942411351538472187647090042⟩
  | 4, 1 => ⟨-30246190222951123722466117585862292433634247184787483, 30277361734979953420558557467072283518288170473609577⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0426Geometry.ds, E8TAxisProd0426Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 38675287589273566018771872435836644607662072899 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0426CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0427CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0427CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0427GraphCenterA.qJetBox,
   E8TAxisProd0427GraphCenterB.qJetBox,
   E8TAxisProd0427GraphCenterC.qJetBox,
   E8TAxisProd0427GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0427GraphWholeA.qJetBox,
   E8TAxisProd0427GraphWholeB.qJetBox,
   E8TAxisProd0427GraphWholeC.qJetBox,
   E8TAxisProd0427GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨36986713954445591594947180338576288556882103812, 36986713954445591594947180338576484250472809877⟩
  | 0, 2 => ⟨109090447474599104754930529565637791363277824081, 109090447474599104754930529565638565759758684105⟩
  | 1, 1 => ⟨109324721186223640318320330389587336894515632749, 109324721186223640318320330389588747188639207003⟩
  | 0, 3 => ⟨220344453311552197255645917336571618352356381435, 220344453311552197255645917336574172384160672235⟩
  | 1, 2 => ⟨295590641235248442920269171450998640434814333019, 295590641235248442920269171451003249605973721698⟩
  | 2, 1 => ⟨296147774385667114162523221230542935287352441141, 296147774385667114162523221230551364656428642391⟩
  | 0, 4 => ⟨368860055535440608609862614948190986380644630191, 368860055535440608609862614948199801639948085125⟩
  | 1, 3 => ⟨547474797672414954309406115980411198080805745379, 547474797672414954309406115980427301853256152483⟩
  | 2, 2 => ⟨726357021714488927941006171923824449663798575658, 726357021714488927941006171923854238484582805200⟩
  | 3, 1 => ⟨727556083285159751104648973162899290036767573447, 727556083285159751104648973162954817540343688581⟩
  | 0, 5 => ⟨-1815787205415806592716914826081974360391413246291694, 1825565972713886090782985752440917635893606994991269⟩
  | 1, 4 => ⟨-3559209721069599970575540576229260275241114081838016, 3573964913202715620814228529719507563883364538282415⟩
  | 2, 3 => ⟨-6983250034656484839941396465445851332310210904091854, 7004529198445837225171706189729412333848032823291466⟩
  | 3, 2 => ⟨-13710192041962197259280891237888826749703252362558057, 13738114511960599375565837483646178734312865559255921⟩
  | 4, 1 => ⟨-26930957002162734824289224051590453947050825873144549, 26959411045875481590908222106076827106896295066347142⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0427Geometry.ds, E8TAxisProd0427Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 34776523252873182472383954676695552110519199324 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0427CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0428CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0428CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0428GraphCenterA.qJetBox,
   E8TAxisProd0428GraphCenterB.qJetBox,
   E8TAxisProd0428GraphCenterC.qJetBox,
   E8TAxisProd0428GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0428GraphWholeA.qJetBox,
   E8TAxisProd0428GraphWholeB.qJetBox,
   E8TAxisProd0428GraphWholeC.qJetBox,
   E8TAxisProd0428GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨33367390422417830317127674651029283371444967426, 33367390422417830317127674651029461076349484685⟩
  | 0, 2 => ⟨99176523724663961786908111365618140870749380517, 99176523724663961786908111365618838091730182364⟩
  | 1, 1 => ⟨99477986184383518414562537809952082276515146533, 99477986184383518414562537809953348714809333940⟩
  | 0, 3 => ⟨201868330799411493346322026792163767850165946269, 201868330799411493346322026792166057684004730556⟩
  | 1, 2 => ⟨271135470819234928727026758669785647405724984786, 271135470819234928727026758669789770040142416660⟩
  | 2, 1 => ⟨271858220244495214333815284153320611800540817788, 271858220244495214333815284153328137617318555492⟩
  | 0, 4 => ⟨340285241624591499552954790702446596699090623257, 340285241624591499552954790702454459266822669215⟩
  | 1, 3 => ⟨505917663609327627460169777897538009420173192564, 505917663609327627460169777897552345102978288657⟩
  | 2, 2 => ⟨671899884778755435477844430770980821738589812953, 671899884778755435477844430771007300569237354941⟩
  | 3, 1 => ⟨673464279487858228268467790934814122912835218184, 673464279487858228268467790934863413974412345367⟩
  | 0, 5 => ⟨-1618409732657029681243238344802433172023449596946541, 1627294369411371135368026359968448780766666054987988⟩
  | 1, 4 => ⟨-3170611755210770070166154455009061512432003593648032, 3184018776182984240348853771268458750879287935425350⟩
  | 2, 3 => ⟨-6217566587267883139509198761618049610437120431018965, 6236906061168551144928442592960396393570972274591466⟩
  | 3, 2 => ⟨-12200628853040899988123967740758801225677485965608544, 12226018000344832825564820365279634616224290875094809⟩
  | 4, 1 => ⟨-23953353847635258323812787899224899276725823606102082, 23979257978874408607822362217218375024686564289198473⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0428Geometry.ds, E8TAxisProd0428Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 31358470112266016832030344517921814650095676338 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0428CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0429CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0429CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0429GraphCenterA.qJetBox,
   E8TAxisProd0429GraphCenterB.qJetBox,
   E8TAxisProd0429GraphCenterC.qJetBox,
   E8TAxisProd0429GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0429GraphWholeA.qJetBox,
   E8TAxisProd0429GraphWholeB.qJetBox,
   E8TAxisProd0429GraphWholeC.qJetBox,
   E8TAxisProd0429GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨29962846673130927614122022866316174878594242069, 29962846673130927614122022866316335998374169289⟩
  | 0, 2 => ⟨89855071093829503175845035327854415377512070966, 89855071093829503175845035327855042295443082460⟩
  | 1, 1 => ⟨90131546207239125195401304464971253928015972445, 90131546207239125195401304464972389632056495094⟩
  | 0, 3 => ⟨184406502260644907955423603324753842632915971389, 184406502260644907955423603324755895313450334097⟩
  | 1, 2 => ⟨247935118740716725074071306338703725487166776544, 247935118740716725074071306338707412609782886648⟩
  | 2, 1 => ⟨248603618719609645908284975349893580453950516321, 248603618719609645908284975349900299412668490481⟩
  | 0, 4 => ⟨313160672394175308381260852119483394664331449551, 313160672394175308381260852119490418269446461130⟩
  | 1, 3 => ⟨466362422567715356906455186526943557485308332683, 466362422567715356906455186526956340426928451529⟩
  | 2, 2 => ⟨619890555197624059894734990343336082348166603882, 619890555197624059894734990343359660709939589721⟩
  | 3, 1 => ⟨621346542062442332459267690547942976340572968109, 621346542062442332459267690547986812754982856500⟩
  | 0, 5 => ⟨-1433646857156381721025641722322413585886456890082813, 1441656998503769226480182943237468390851385766133147⟩
  | 1, 4 => ⟨-2807002462932261389489755210578522265726359710515360, 2819086623298011136952135134322037696130119064008098⟩
  | 2, 3 => ⟨-5501423420958189027914666264954342420419686482775774, 5518853452940963911672220711232473301925379867800703⟩
  | 3, 2 => ⟨-10789340549102178288780321241917715517951179381621904, 10812225694924053626468127135049230355505061607473240⟩
  | 4, 1 => ⟨-21170809616533475782745106331700978297954869816409378, 21194168608539488361351323399415300038559339403732594⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0429Geometry.ds, E8TAxisProd0429Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 28144744960236689560304933307442966567473017074 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0429CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0430CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0430CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0430GraphCenterA.qJetBox,
   E8TAxisProd0430GraphCenterB.qJetBox,
   E8TAxisProd0430GraphCenterC.qJetBox,
   E8TAxisProd0430GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0430GraphWholeA.qJetBox,
   E8TAxisProd0430GraphWholeB.qJetBox,
   E8TAxisProd0430GraphWholeC.qJetBox,
   E8TAxisProd0430GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨33243577366676911536002483992908044202600261907, 33243577366676911536002483992908221539486868049⟩
  | 0, 2 => ⟨98924453994513022353734327911038893756511013796, 98924453994513022353734327911039589447654954553⟩
  | 1, 1 => ⟨99139461839027933370818092381557025522879434062, 99139461839027933370818092381558289151315677936⟩
  | 0, 3 => ⟨201443368983918878433205160331460873145853655382, 201443368983918878433205160331463157898349759758⟩
  | 1, 2 => ⟨270503685666105046447606934118788029394882571298, 270503685666105046447606934118792142799649494136⟩
  | 2, 1 => ⟨271019237182242499624614752958199189938467597574, 271019237182242499624614752958206698771982656360⟩
  | 0, 4 => ⟨339653840825845482947589092998709089632078999687, 339653840825845482947589092998716934208974137119⟩
  | 1, 3 => ⟨504938864824359048470778005527454018263334313928, 504938864824359048470778005527468321033402474905⟩
  | 2, 2 => ⟨670473444245235317215891191223642148982236428600, 670473444245235317215891191223668566777992169833⟩
  | 3, 1 => ⟨671589474612190244564452790080775034866523875617, 671589474612190244564452790080824211778654710298⟩
  | 0, 5 => ⟨-1614520085022271495284357709531512059860889648042455, 1623384957105507509670129134972108572557142702148392⟩
  | 1, 4 => ⟨-3162963978865990385438811142274262305459069226693475, 3176340492039830947443361277167750946903229228565842⟩
  | 2, 3 => ⟨-6202513959448114150677399725599240490031658719648782, 6221807686011797193366879406975651866122811745848466⟩
  | 3, 2 => ⟨-12170980282081296699039762122851217708556311948429104, 12196304196541186923749196114483017230223907451290030⟩
  | 4, 1 => ⟨-23894923399275814254011166264369857185381404702384595, 23920743635475516682198989024999078081055288988651343⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0430Geometry.ds, E8TAxisProd0430Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 31241314649615285766359489179336723866650169421 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0430CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0431CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0431CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0431GraphCenterA.qJetBox,
   E8TAxisProd0431GraphCenterB.qJetBox,
   E8TAxisProd0431GraphCenterC.qJetBox,
   E8TAxisProd0431GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0431GraphWholeA.qJetBox,
   E8TAxisProd0431GraphWholeB.qJetBox,
   E8TAxisProd0431GraphWholeC.qJetBox,
   E8TAxisProd0431GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨29850671799950780594220492525183989171384974433, 29850671799950780594220492525184149958132280633⟩
  | 0, 2 => ⟨89624807470562205614528678831508237054678054652, 89624807470562205614528678831508862595480444424⟩
  | 1, 1 => ⟨89821991418062866273998264066657408994886994161, 89821991418062866273998264066658542174459439219⟩
  | 0, 3 => ⟨184015416688950859386896613376442463997290524616, 184015416688950859386896613376444512115391537112⟩
  | 1, 2 => ⟨247352732973393841409093648126877808909222648898, 247352732973393841409093648126881487758988979332⟩
  | 2, 1 => ⟨247829583260026616115335755952168480676393765836, 247829583260026616115335755952175184432096549685⟩
  | 0, 4 => ⟨312576407153893216604879959351679456042185903114, 312576407153893216604879959351686463541007915288⟩
  | 1, 3 => ⟨465455068462486990759749428554661204153067588711, 465455068462486990759749428554673957670933422462⟩
  | 2, 2 => ⟨618566579421108583661332434726249728329383227068, 618566579421108583661332434726273252181389954208⟩
  | 3, 1 => ⟨619605271124123838356503265774668820589872021803, 619605271124123838356503265774712555149321493006⟩
  | 0, 5 => ⟨-1430098960857989270167019267813331482673540582795126, 1438091061455882189155259170317133670116973876741047⟩
  | 1, 4 => ⟨-2800029058753826587627085351219628356398648623684290, 2812085379033965521596960398230818334696500564235213⟩
  | 2, 3 => ⟨-5487702878365817466977929706536744564850657622021006, 5505091378859168616621111372078963373801350539266400⟩
  | 3, 2 => ⟨-10762325152378381397676355891297962681793938471676846, 10785151856802867490673693950836830869335149185457025⟩
  | 4, 1 => ⟨-21117587241199419409139833875355695864577206643224810, 21140873430156537726594447438273354883453221386297500⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0431Geometry.ds, E8TAxisProd0431Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 28038658009920377547235818438888660502059797960 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0431CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0432CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0432CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0432GraphCenterA.qJetBox,
   E8TAxisProd0432GraphCenterB.qJetBox,
   E8TAxisProd0432GraphCenterC.qJetBox,
   E8TAxisProd0432GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0432GraphWholeA.qJetBox,
   E8TAxisProd0432GraphWholeB.qJetBox,
   E8TAxisProd0432GraphWholeC.qJetBox,
   E8TAxisProd0432GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨40962495411689046815665621477788055086534103195, 40962495411689046815665621477788270697209963557⟩
  | 0, 2 => ⟨119894265755842624633410696536406681925827639970, 119894265755842624633410696536407542156411821489⟩
  | 1, 1 => ⟨120047093504947212342021973812791608832698196084, 120047093504947212342021973812793179367848524787⟩
  | 0, 3 => ⟨240332428021782408549573967955439461199570526474, 240332428021782408549573967955442310028309318318⟩
  | 1, 2 => ⟨322020874901758336759628790166681067005137726703, 322020874901758336759628790166686219926160040079⟩
  | 2, 1 => ⟨322381476493799299369003723402799720555926940443, 322381476493799299369003723402809161177920334188⟩
  | 0, 4 => ⟨399620044100593013598547261474430025298658050630, 399620044100593013598547261474439909030928285849⟩
  | 1, 3 => ⟨592155082391092436811082256911012253045658553892, 592155082391092436811082256911030342455793380574⟩
  | 2, 2 => ⟨784861946805705732192204438302478947455139462147, 784861946805705732192204438302512457948446521267⟩
  | 3, 1 => ⟨785633911622266567714849517221770763691608123012, 785633911622266567714849517221833311290720840778⟩
  | 0, 5 => ⟨-2030559954758372646559480288332198615995218286140053, 2041267423932098371870499100094030064405022428814851⟩
  | 1, 4 => ⟨-3982229315787217878588408954944173112253807260711873, 3998380254386297921392242405097962857098879087873385⟩
  | 2, 3 => ⟨-7817106085834156008454665321981348300441001184091175, 7840387615500594822437973002460170828364949886188418⟩
  | 3, 2 => ⟨-15354861233733824214848116829367643386935299868461976, 15385391942160208004758656511234672507208034914393468⟩
  | 4, 1 => ⟨-30176468397835752668747151792911124513496850629802847, 30207536796834617241728218568211400389300611307053665⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0432Geometry.ds, E8TAxisProd0432Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 38533155551050701595821542435421918754929048449 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0432CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0433CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0433CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0433GraphCenterA.qJetBox,
   E8TAxisProd0433GraphCenterB.qJetBox,
   E8TAxisProd0433GraphCenterC.qJetBox,
   E8TAxisProd0433GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0433GraphWholeA.qJetBox,
   E8TAxisProd0433GraphWholeB.qJetBox,
   E8TAxisProd0433GraphWholeC.qJetBox,
   E8TAxisProd0433GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨36850522919190306409064894026919027403864941366, 36850522919190306409064894026919222691468934872⟩
  | 0, 2 => ⟨108815304902463528324919376993916856141632045749, 108815304902463528324919376993917628830519597779⟩
  | 1, 1 => ⟨108955660324818171101914326031436199309150074817, 108955660324818171101914326031437606459264337567⟩
  | 0, 3 => ⟨219883803977248740940999763689305279632923828915, 219883803977248740940999763689307827912377508849⟩
  | 1, 2 => ⟨294906956555993043750066515214472131201869817605, 294906956555993043750066515214476729894821085089⟩
  | 2, 1 => ⟨295240787027524123163224787169677940551637109304, 295240787027524123163224787169686350596840873276⟩
  | 0, 4 => ⟨368179070488084407045595706432861004206471909721, 368179070488084407045595706432869798732168931794⟩
  | 1, 3 => ⟨546420993667301155842093594526794177422532858904, 546420993667301155842093594526810243151313256728⟩
  | 2, 2 => ⟨724823212330053807159576052554192406868662078537, 724823212330053807159576052554222124984984884092⟩
  | 3, 1 => ⟨725541752145404920672237516376227141090172897189, 725541752145404920672237516376282536123516704531⟩
  | 0, 5 => ⟨-1811548103051222206140781211457754802372734717465729, 1821307300204404274309861928242132094917891652858638⟩
  | 1, 4 => ⟨-3550872244242040761436803681574316524784223463087654, 3565596599483939545389691461532823051070931992491545⟩
  | 2, 3 => ⟨-6966834753967930701471330132467463979503344003301235, 6988066449388605492713325561316417815310130909968296⟩
  | 3, 2 => ⟨-13677849245848652078907412332575469999212115012412235, 13705701776347001485644708195662815822813704235403861⟩
  | 4, 1 => ⟨-26867196403727517621661766701472778634538061860099238, 26895556561366278069751144845585685792296868726546295⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0433Geometry.ds, E8TAxisProd0433Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 34647589519168351375463321221076012334208598544 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0433CertifiedArithmetic

end


