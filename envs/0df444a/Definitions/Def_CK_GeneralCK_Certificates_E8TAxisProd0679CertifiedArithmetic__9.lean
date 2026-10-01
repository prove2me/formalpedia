-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0679CertifiedArithmetic__9
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0679CertifiedArithmetic__9
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T17:48:54.059647+00:00
-- url     : https://prove2.me/theorems/0cbc1911-fe56-4a73-b389-9f4ab863a395
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0679CertifiedArithmetic (+8 modules: GeneralCK.Certificates.E8TAxisProd0680CertifiedArithmetic, GeneralCK.Certificates.E8TAx…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0679CertifiedArithmetic (+8 modules: GeneralCK.Certificates.E8TAxisProd0680CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0681CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0682CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0683CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0684CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0685CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0686CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0687CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0679CertifiedArithmetic (+8 modules: GeneralCK.Certificates.E8TAxisProd0680CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0681CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0682CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0683CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0684CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0685CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0686CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0687CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0679CertifiedArithmetic (+8 modules: GeneralCK.Certificates.E8TAxisProd0680CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0681CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0682CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0683CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0684CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0685CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0686CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0687CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0679CertifiedArithmetic (+8 modules: GeneralCK/Certificates/E8TAxisProd0680CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0681CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0682CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0683CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0684CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0685CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0686CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0687CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0674GraphCenterA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0677GraphCenterB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0668GraphCenterC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0667GraphCenterD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0677GraphWholeA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0668GraphWholeB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0678GraphWholeC__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0678GraphWholeD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0659Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0680GraphCenterD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0681GraphWholeB__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0683GraphCenterC__5
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0683Geometry__5
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0686GraphCenterA__2

-- ===== source module GeneralCK.Certificates.E8TAxisProd0679CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0679CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0679GraphCenterA.qJetBox,
   E8TAxisProd0679GraphCenterB.qJetBox,
   E8TAxisProd0679GraphCenterC.qJetBox,
   E8TAxisProd0679GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0679GraphWholeA.qJetBox,
   E8TAxisProd0679GraphWholeB.qJetBox,
   E8TAxisProd0679GraphWholeC.qJetBox,
   E8TAxisProd0679GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3596158201347853994917146868974846227392762852, 3596158201347853994917146868974877349028838988⟩
  | 0, 2 => ⟨12746652703155367575263321007364703310876311036, 12746652703155367575263321007364800592054202838⟩
  | 1, 1 => ⟨12782368999759620906304593307746349647032239488, 12782368999759620906304593307746513185785244012⟩
  | 0, 3 => ⟨30428995828800087188726536007799049723593679966, 30428995828800087188726536007799344342159806703⟩
  | 1, 2 => ⟨41909783472686937597203330768149401553835748108, 41909783472686937597203330768149898664893479386⟩
  | 2, 1 => ⟨42012922724275885822271898152479549067146859086, 42012922724275885822271898152480418524542451697⟩
  | 0, 4 => ⟨60319931790667798035692373026473596139726692375, 60319931790667798035692373026474537547141092927⟩
  | 1, 3 => ⟨93394889195086714504960324250253362341244412266, 93394889195086714504960324250254991934905953599⟩
  | 2, 2 => ⟨126534267417380426257682095300359112829862922647, 126534267417380426257682095300362019830391257104⟩
  | 3, 1 => ⟨126803872843125687460780293707683076698549681270, 126803872843125687460780293707688329823646137385⟩
  | 0, 5 => ⟨-105249076877674779464561171773112257158795058758951, 106169190833687399879498316163054340058574776913432⟩
  | 1, 4 => ⟨-202417605078222568634197331767056423664337417641892, 203755295788596457786336465095748798396263682483767⟩
  | 2, 3 => ⟨-390234539374379109859466819224361465944593638018296, 392118742930286632345628083256181659105079630494589⟩
  | 3, 2 => ⟨-753280340953990782551838550802668399006928554108739, 755725351828585854836449295417508230354995741984856⟩
  | 4, 1 => ⟨-1455148492302014638240060879406410504603557467199541, 1457654548379726426117702806249518878087417769169606⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0679Geometry.ds, E8TAxisProd0679Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3344312699596977733100455409121580653724241618 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0679CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0680CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0680CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0680GraphCenterA.qJetBox,
   E8TAxisProd0680GraphCenterB.qJetBox,
   E8TAxisProd0680GraphCenterC.qJetBox,
   E8TAxisProd0680GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0680GraphWholeA.qJetBox,
   E8TAxisProd0680GraphWholeB.qJetBox,
   E8TAxisProd0680GraphWholeC.qJetBox,
   E8TAxisProd0680GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3177135222071078534053595452266398759642642359, 3177135222071078534053595452266427467171990690⟩
  | 0, 2 => ⟨11353708752738747068003151482907273071368227531, 11353708752738747068003151482907361401194210188⟩
  | 1, 1 => ⟨11398841767664230835451320334952854488194417196, 11398841767664230835451320334953002083579989693⟩
  | 0, 3 => ⟨27302358512500815155144220717351634846217256943, 27302358512500815155144220717351900501344517714⟩
  | 1, 2 => ⟨37684276099433280363474685617974647270530444410, 37684276099433280363474685617975093178583718538⟩
  | 2, 1 => ⟨37815865679580286628889154424147854330708517122, 37815865679580286628889154424148631867595901643⟩
  | 0, 4 => ⟨54555845834898440549058808661655325639610152577, 54555845834898440549058808661656169529683855213⟩
  | 1, 3 => ⟨84724021731646526003688241258406228875522169311, 84724021731646526003688241258407683123616430446⟩
  | 2, 2 => ⟨114975735017381842870387881069041135533987869750, 114975735017381842870387881069043722718946880920⟩
  | 3, 1 => ⟨115323872024847575108566120666621715279907741432, 115323872024847575108566120666626380506494337397⟩
  | 0, 5 => ⟨-89066765666669110887087775498124709624464063753395, 89881457221102149297790998829504638813089968027429⟩
  | 1, 4 => ⟨-171007768411845777929703584404803022622978645094426, 172187576591119826601462963135956535421279143925877⟩
  | 2, 3 => ⟨-329197368350597433686719036761453860887033464797117, 330855318366117766684568508130036422166567048031482⟩
  | 3, 2 => ⟨-634590486067749826663685896105632584607795635901866, 636740041100266370933326955375453613780332452183083⟩
  | 4, 1 => ⟨-1224249052699368276834237153722969857602604995231729, 1226455126270105388094859068120066962512318870619010⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0680Geometry.ds, E8TAxisProd0680Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2952836616719498412808460796270480765637931888 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0680CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0681CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0681CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0681GraphCenterA.qJetBox,
   E8TAxisProd0681GraphCenterB.qJetBox,
   E8TAxisProd0681GraphCenterC.qJetBox,
   E8TAxisProd0681GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0681GraphWholeA.qJetBox,
   E8TAxisProd0681GraphWholeB.qJetBox,
   E8TAxisProd0681GraphWholeC.qJetBox,
   E8TAxisProd0681GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2791038606549696571238342957097396723011671221, 2791038606549696571238342957097423181702798034⟩
  | 0, 2 => ⟨10071278416241068054393158666587785789906388358, 10071278416241068054393158666587865876867619514⟩
  | 1, 1 => ⟨10111901134121605742254032443518387990108945247, 10111901134121605742254032443518520961870762346⟩
  | 0, 3 => ⟨24406057280563592132061972151615467550920944195, 24406057280563592132061972151615706617658855486⟩
  | 1, 2 => ⟨33751046798071997957152139948358819025800345918, 33751046798071997957152139948359218078485162901⟩
  | 2, 1 => ⟨33870632118713271329009199762201545299482151076, 33870632118713271329009199762202238901819059490⟩
  | 0, 4 => ⟨49163875840600714646207196991958903875241817397, 49163875840600714646207196991959658411897826427⟩
  | 1, 3 => ⟨76580626939028665426068073779901845111737216592, 76580626939028665426068073779903139105978284508⟩
  | 2, 2 => ⟨104074559544729293361252447959558404618578924373, 104074559544729293361252447959560700021873612793⟩
  | 3, 1 => ⟨104394802187780559328032207161309514721092390825, 104394802187780559328032207161313644390558040690⟩
  | 0, 5 => ⟨-75266528301356752752360550156991620280057599512834, 75978877494162414389946959485673315825762977713687⟩
  | 1, 4 => ⟨-144250987051372032532017857614344899437785469267058, 145276630385253106020670591738702083292827107931946⟩
  | 2, 3 => ⟨-277253218250376018091069040889281975141009968125245, 278689035660580611639631321726577526372627965438294⟩
  | 3, 2 => ⟨-533675216430539697405953036608604661785343601422008, 535533349463626544010201041285554947383011120680636⟩
  | 4, 1 => ⟨-1028102023616192192773110775602388168511544709789173, 1030011023420513809892235891529114743548736442316182⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0681Geometry.ds, E8TAxisProd0681Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2592275702512271072450995005946954834134897895 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0681CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0682CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0682CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0682GraphCenterA.qJetBox,
   E8TAxisProd0682GraphCenterB.qJetBox,
   E8TAxisProd0682GraphCenterC.qJetBox,
   E8TAxisProd0682GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0682GraphWholeA.qJetBox,
   E8TAxisProd0682GraphWholeB.qJetBox,
   E8TAxisProd0682GraphWholeC.qJetBox,
   E8TAxisProd0682GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3162964398348467758087791284990188314758747694, 3162964398348467758087791284990216967721141115⟩
  | 0, 2 => ⟨11319623395030352696974880443013418293678570854, 11319623395030352696974880443013506431732011346⟩
  | 1, 1 => ⟨11351802562140765411864568129319892696501578964, 11351802562140765411864568129320039961191822873⟩
  | 0, 3 => ⟨27234238866775791254656280150224208964246158913, 27234238866775791254656280150224474021895711437⟩
  | 1, 2 => ⟨37578493550866575042077649286245033628907011854, 37578493550866575042077649286245478505940110811⟩
  | 2, 1 => ⟨37672330781555325638257772450368533707646652620, 37672330781555325638257772450369309410442300376⟩
  | 0, 4 => ⟨54435625769695464844277779112599763242998007526, 54435625769695464844277779112600605141591873647⟩
  | 1, 3 => ⟨84528120496050282742573771691154035194792728063, 84528120496050282742573771691155485944623014331⟩
  | 2, 2 => ⟨114680203303823253379612331698011014726843951066, 114680203303823253379612331698013595586386004773⟩
  | 3, 1 => ⟨114928514326738532332186011815127246506546905702, 114928514326738532332186011815131900151518697022⟩
  | 0, 5 => ⟨-88769571283990922434281746356136515675498015778322, 89583256919599434644916614801783413759972384209363⟩
  | 1, 4 => ⟨-170431439855108643963656349863646638647889118848929, 171609356274086009470997448254367979021134370868382⟩
  | 2, 3 => ⟨-328077527417153749486330677746666544970379677605953, 329732069862101662368129863233928155610495476681826⟩
  | 3, 2 => ⟨-632411969210046911564051543149046198441447149306366, 634555917634648967706789431460489892608242382507539⟩
  | 4, 1 => ⟨-1220007654649878328997521217023191445033725274359688, 1222206195410765922130303148874885616651102407232336⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0682Geometry.ds, E8TAxisProd0682Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2939576930043916518479521483617762405246334411 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0682CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0683CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0683CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0683GraphCenterA.qJetBox,
   E8TAxisProd0683GraphCenterB.qJetBox,
   E8TAxisProd0683GraphCenterC.qJetBox,
   E8TAxisProd0683GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0683GraphWholeA.qJetBox,
   E8TAxisProd0683GraphWholeB.qJetBox,
   E8TAxisProd0683GraphWholeC.qJetBox,
   E8TAxisProd0683GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2778468559766696774439686108574394713544768543, 2778468559766696774439686108574421122304426812⟩
  | 0, 2 => ⟨10040809225386954130256335829872111287669587881, 10040809225386954130256335829872191201280194799⟩
  | 1, 1 => ⟨10069772107593513559391981183821922846560869448, 10069772107593513559391981183822055520908845066⟩
  | 0, 3 => ⟨24344670900064341767769941326459017326574432220, 24344670900064341767769941326459255855359078775⟩
  | 1, 2 => ⟨33655432944443959090672073541532960867676353443, 33655432944443959090672073541533358995751561419⟩
  | 2, 1 => ⟨33740708151632331927765736515073052748447801235, 33740708151632331927765736515073744709806521870⟩
  | 0, 4 => ⟨49054368415622282073019643401811052780562738236, 49054368415622282073019643401811805529552788093⟩
  | 1, 3 => ⟨76401598600353693850704942675305915855999941519, 76401598600353693850704942675307206720391514442⟩
  | 2, 2 => ⟨103803882005393084691051305316122317156637892645, 103803882005393084691051305316124606911020341209⟩
  | 3, 1 => ⟨104032292068813873011426911203247067197094698614, 104032292068813873011426911203251186538479749634⟩
  | 0, 5 => ⟨-75012942757223589674051635858803000566856819939584, 75724544610386327871810456974162025001649489488648⟩
  | 1, 4 => ⟨-143759823963868192413935371174233005534462893729697, 144783972879916664259432089718079147960552832350542⟩
  | 2, 3 => ⟨-276299891783290935054516046901730534608424001442719, 277732886563107291911921608463934925272298281416983⟩
  | 3, 2 => ⟨-531822513364922996772324779420646115093680331749744, 533675838462642507189614023112876144025267094629593⟩
  | 4, 1 => ⟨-1024498490580473104403365451765568092220713088352886, 1026400879696087701705691170180233148631901048796622⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0683Geometry.ds, E8TAxisProd0683Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2580520978309021781744129647358379711548646891 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0683CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0684CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0684CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0684GraphCenterA.qJetBox,
   E8TAxisProd0684GraphCenterB.qJetBox,
   E8TAxisProd0684GraphCenterC.qJetBox,
   E8TAxisProd0684GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0684GraphWholeA.qJetBox,
   E8TAxisProd0684GraphWholeB.qJetBox,
   E8TAxisProd0684GraphWholeC.qJetBox,
   E8TAxisProd0684GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4065764772015333622640119227003461466406915958, 4065764772015333622640119227003495240203104298⟩
  | 0, 2 => ⟨14294820852680225734477284471618328725866333657, 14294820852680225734477284471618435938307632681⟩
  | 1, 1 => ⟨14318539491154865958901781085836386529151186632, 14318539491154865958901781085836567811585380263⟩
  | 0, 3 => ⟨33873177192930891076009859294783502901133352564, 33873177192930891076009859294783829716529753445⟩
  | 1, 2 => ⟨46557034078335377560165805879901130069779091007, 46557034078335377560165805879901684244881062739⟩
  | 2, 1 => ⟨46624864172338533557966737394382218300008294310, 46624864172338533557966737394383190394696037833⟩
  | 0, 4 => ⟨66601588559835908839445179650938283933264651782, 66601588559835908839445179650939333869855312095⟩
  | 1, 3 => ⟨102823549194384083942722545908929937943469006450, 102823549194384083942722545908931763065208193316⟩
  | 2, 2 => ⟨139087194841435370732158210300518279717246085232, 139087194841435370732158210300521543873734786556⟩
  | 3, 1 => ⟨139262373895044752930284405536352838961177698130, 139262373895044752930284405536358749522003331435⟩
  | 0, 5 => ⟨-124191821037854100777257855147516711318481109871235, 125230171644298064621609567214530189678109352387526⟩
  | 1, 4 => ⟨-239225896788476038274966858306608081915639543471117, 240740751572520965233979741241635944091147043508205⟩
  | 2, 3 => ⟨-461836375754613525163280880235374357283627930110846, 463974496831249597974345806670190820798734054868305⟩
  | 3, 2 => ⟨-892654390808364885794717048874445882968684088459566, 895430950312013403938555463787632377729998054392267⟩
  | 4, 1 => ⟨-1726559172778847860012854450579464970700463025954334, 1729401862958331026642033847170678464089166110288744⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0684Geometry.ds, E8TAxisProd0684Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3783270736370859504305425509139101248301405303 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0684CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0685CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0685CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0685GraphCenterA.qJetBox,
   E8TAxisProd0685GraphCenterB.qJetBox,
   E8TAxisProd0685GraphCenterC.qJetBox,
   E8TAxisProd0685GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0685GraphWholeA.qJetBox,
   E8TAxisProd0685GraphWholeB.qJetBox,
   E8TAxisProd0685GraphWholeC.qJetBox,
   E8TAxisProd0685GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3580248638497217074532371828379297550151072773, 3580248638497217074532371828379328612222182320⟩
  | 0, 2 => ⟨12708663549045720905044235056153466736866857310, 12708663549045720905044235056153563806278690264⟩
  | 1, 1 => ⟨12730054679511140042797533100127103459830600149, 12730054679511140042797533100127266631663678291⟩
  | 0, 3 => ⟨30353678149927292935151351539342386165348763366, 30353678149927292935151351539342680121812230015⟩
  | 1, 2 => ⟨41793173435001427365456127995916233100961431885, 41793173435001427365456127995916729065208790411⟩
  | 2, 1 => ⟨41854955946704439933377164468744345123123372164, 41854955946704439933377164468745212535972082827⟩
  | 0, 4 => ⟨60188395978954464144722260497968883685911033145, 60188395978954464144722260497969822881034109581⟩
  | 1, 3 => ⟨93181240612485087464858363832545690462499250566, 93181240612485087464858363832547316158101895096⟩
  | 2, 2 => ⟨126212685718628499041284314879311969084895011214, 126212685718628499041284314879314869025127682895⟩
  | 3, 1 => ⟨126374219333555926433553133700194925019097160237, 126374219333555926433553133700200165199712904578⟩
  | 0, 5 => ⟨-104894310196715770705750517586027263547015755842749, 105813635013059970197001053657669845361307374624647⟩
  | 1, 4 => ⟨-201728878093005876807476699823084760446604131904008, 203064933167257492459586194247185559727078904444794⟩
  | 2, 3 => ⟨-388895065884055662860845028223552271967846575260836, 390776103711653421564986349301577591467690842947050⟩
  | 3, 2 => ⟨-750672400025381615936669282037813613902732507529463, 753111927911229790488748234999492986474086182297749⟩
  | 4, 1 => ⟨-1450067133923099971741058263265003287734406759738196, 1452565576477538444532645873110545577060747353780568⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0685Geometry.ds, E8TAxisProd0685Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3329417904928073130769199986884772392034190999 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0685CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0686CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0686CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0686GraphCenterA.qJetBox,
   E8TAxisProd0686GraphCenterB.qJetBox,
   E8TAxisProd0686GraphCenterC.qJetBox,
   E8TAxisProd0686GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0686GraphWholeA.qJetBox,
   E8TAxisProd0686GraphWholeB.qJetBox,
   E8TAxisProd0686GraphWholeC.qJetBox,
   E8TAxisProd0686GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3148836128143634622576280594660332975297354991, 3148836128143634622576280594660361573799526838⟩
  | 0, 2 => ⟨11285623093017233833315426791323458575177308354, 11285623093017233833315426791323546521871951882⟩
  | 1, 1 => ⟨11304895431855940122883703938446958509533071797, 11304895431855940122883703938447105444258457798⟩
  | 0, 3 => ⟨27166269352043426686242457523563046040984199061, 27166269352043426686242457523563310502472924160⟩
  | 1, 2 => ⟨37472955637024968881211722810883282968072623118, 37472955637024968881211722810883726816390832002⟩
  | 2, 1 => ⟨37529164917832306553661456105806100740883381295, 37529164917832306553661456105806874613731153626⟩
  | 0, 4 => ⟨54315636184069069263170575918472283756732284230, 54315636184069069263170575918473123668340601336⟩
  | 1, 3 => ⟨84332606064130861791412798025509346840135697832, 84332606064130861791412798025510794099668917538⟩
  | 2, 2 => ⟨114385279962527731872974951678471504948111422967, 114385279962527731872974951678474079496724961082⟩
  | 3, 1 => ⟨114534051880470943591599739647255071826723465120, 114534051880470943591599739647259713916767304358⟩
  | 0, 5 => ⟨-88473300756539393349479534941697465529928383898573, 89286119097603199230488313225122211429579883825190⟩
  | 1, 4 => ⟨-169856914075965234437930376933495128919059046987599, 171033106922082071070176817767419894529053042737215⟩
  | 2, 3 => ⟨-326961210071440055106004152644046806553959913295290, 328612517149258589462529450898993595797318060157426⟩
  | 3, 2 => ⟨-630240346575811422347566931322841805886306675583279, 632378812192788322810027548328508165921823875827874⟩
  | 4, 1 => ⟨-1215779755817330925288265075384176576470302306176051, 1217970785234832492651970658414927566141048745325937⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0686Geometry.ds, E8TAxisProd0686Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2926357244128998168785798622008093730834661709 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0686CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0687CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0687CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0687GraphCenterA.qJetBox,
   E8TAxisProd0687GraphCenterB.qJetBox,
   E8TAxisProd0687GraphCenterC.qJetBox,
   E8TAxisProd0687GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0687GraphWholeA.qJetBox,
   E8TAxisProd0687GraphWholeB.qJetBox,
   E8TAxisProd0687GraphWholeC.qJetBox,
   E8TAxisProd0687GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2765936551549784495741928294202952697601596529, 2765936551549784495741928294202979056526951322⟩
  | 0, 2 => ⟨10010416682011167949924091437892798891010324877, 10010416682011167949924091437892878631644143739⟩
  | 1, 1 => ⟨10027762458609862797679830823361928788739484981, 10027762458609862797679830823362061166331330099⟩
  | 0, 3 => ⟨24283421270953864378503905106260945309531023736, 24283421270953864378503905106261183301550924403⟩
  | 1, 2 => ⟨33560042652360328538304218141334665511688285003, 33560042652360328538304218141335062717228836670⟩
  | 2, 1 => ⟨33611122178349695446135310176777875082781457239, 33611122178349695446135310176778565406886340844⟩
  | 0, 4 => ⟨48945073560272529231485804321777033648492751612, 48945073560272529231485804321777784613877250092⟩
  | 1, 3 => ⟨76222928367591838607804828860992755216023806754, 76222928367591838607804828860994042957749560188⟩
  | 2, 2 => ⟨103533769306327180417277447708619793384220960966, 103533769306327180417277447708622077502742755010⟩
  | 3, 1 => ⟨103670614786028794246127389047480498997512449194, 103670614786028794246127389047484608034840861630⟩
  | 0, 5 => ⟨-74760159805605141313728012822213791613230308232832, 75471014520248632787228130764807910033842129489503⟩
  | 1, 4 => ⟨-143270225657405376664035821783066485106730869493636, 144292882056093492117227343113556040588803910296077⟩
  | 2, 3 => ⟨-275349621291131746658727145823218633427770262387401, 276779798969539318234527310039398009396649751492115⟩
  | 3, 2 => ⟨-529975785072158423067731905280929102294591193852103, 531824314056127497136899050709858065053204753626031⟩
  | 4, 1 => ⟨-1020906647847080357245458888505087808012143524182653, 1022802445706231532880188942345915877435493625440808⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0687Geometry.ds, E8TAxisProd0687Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2568801987156669894169338661482072096633388524 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0687CertifiedArithmetic

end


