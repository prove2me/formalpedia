-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0016CertifiedArithmetic__12
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0016CertifiedArithmetic__12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T14:11:33.091903+00:00
-- url     : https://prove2.me/theorems/0ed02aa1-f583-4158-b997-c7e58f5e49bd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0016CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0017CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0016CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0017CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0018CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0019CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0020CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0021CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0022CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0025CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0026CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0027CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0029CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0030CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0016CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0017CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0018CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0019CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0020CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0021CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0022CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0025CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0026CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0027CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0029CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0030CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0016CertifiedArithmetic (+11 modules: GeneralCK.Certificates.E8TAxisProd0017CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0018CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0019CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0020CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0021CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0022CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0025CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0026CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0027CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0029CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0030CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0016CertifiedArithmetic (+11 modules: GeneralCK/Certificates/E8TAxisProd0017CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0018CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0019CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0020CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0021CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0022CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0025CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0026CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0027CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0029CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0030CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0001GraphCenterA__18
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0001GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0001GraphCenterC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0001GraphCenterD__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0001GraphWholeA__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0001GraphWholeB__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0001GraphWholeC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0001GraphWholeD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0001Geometry__22
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0017GraphCenterD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0017GraphWholeB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0018GraphCenterB__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0018GraphCenterC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0018GraphWholeA__4
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0018GraphWholeC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0018GraphWholeD__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0019GraphCenterA__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0022GraphWholeA__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0025Geometry__23
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0029GraphCenterA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0030GraphCenterD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0030GraphWholeD__17

-- ===== source module GeneralCK.Certificates.E8TAxisProd0016CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0016CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0016GraphCenterA.qJetBox,
   E8TAxisProd0016GraphCenterB.qJetBox,
   E8TAxisProd0016GraphCenterC.qJetBox,
   E8TAxisProd0016GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0016GraphWholeA.qJetBox,
   E8TAxisProd0016GraphWholeB.qJetBox,
   E8TAxisProd0016GraphWholeC.qJetBox,
   E8TAxisProd0016GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2605301935835484404371739566775161707968, 2605301935835484404371739567633609749494⟩
  | 0, 2 => ⟨68864232645163814160763884930025420192084, 68864232645163814160763884933058505344821⟩
  | 1, 1 => ⟨80808440828222929780000828406692714481911, 80808440828222929780000828410397342348485⟩
  | 0, 3 => ⟨976482824259508995530137044313980641613767, 976482824259508995530137044318324673699463⟩
  | 1, 2 => ⟨1771055789742066597204086974521319818145056, 1771055789742066597204086974526046153828540⟩
  | 2, 1 => ⟨2003700376858392829882836224838298790336148, 2003700376858392829882836224844010240156577⟩
  | 0, 4 => ⟨6212753374860078919965046887776561703466006, 6212753374860078919965046887789916058917105⟩
  | 1, 3 => ⟨19509947869425125394642451522905597502689170, 19509947869425125394642451522920048440446548⟩
  | 2, 2 => ⟨34303796897933398351042924370080215554383550, 34303796897933398351042924370098290877462052⟩
  | 3, 1 => ⟨37358482765887552666488711919495573902664097, 37358482765887552666488711919522342625239507⟩
  | 0, 5 => ⟨-135418445555630230588618310225155098028269071652, 134962418335987396216776640709950059708178704845⟩
  | 1, 4 => ⟨-203280043672090057614903759778728879965952219156, 201340427661382115616423355184377565150822314633⟩
  | 2, 3 => ⟨-322304528558004212258835788691667641097320835934, 318602925916393056189988218852861569963702285928⟩
  | 3, 2 => ⟨-518969526398845715972417554403687608575398517856, 513606181350338133359094159375870622386057792915⟩
  | 4, 1 => ⟨-825789205149236562586666395957857903880479392252, 820711382692730492228750493802943709384625483993⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0016Geometry.ds, E8TAxisProd0016Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1040049611528148367646550049487052253264 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0016CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0017CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0017CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0017GraphCenterA.qJetBox,
   E8TAxisProd0017GraphCenterB.qJetBox,
   E8TAxisProd0017GraphCenterC.qJetBox,
   E8TAxisProd0017GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0017GraphWholeA.qJetBox,
   E8TAxisProd0017GraphWholeB.qJetBox,
   E8TAxisProd0017GraphWholeC.qJetBox,
   E8TAxisProd0017GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3990364312223374837515888101422333614636, 3990364312223374837515888102317495197635⟩
  | 0, 2 => ⟨101757480048690319415706080728312980887253, 101757480048690319415706080731391445909862⟩
  | 1, 1 => ⟨113302843693379404618855436899442782730276, 113302843693379404618855436903198305226546⟩
  | 0, 3 => ⟨1350972135255928641224217285924004899586393, 1350972135255928641224217285928477861493716⟩
  | 1, 2 => ⟨2374058986504089910642895508963276726856644, 2374058986504089910642895508968153441464369⟩
  | 2, 1 => ⟨2577792573946141922402123860806233202604631, 2577792573946141922402123860812177680171414⟩
  | 0, 4 => ⟨7991871718145985434559759523094162307369000, 7991871718145985434559759523107798199722516⟩
  | 1, 3 => ⟨24306212585963394977157007552985487699611624, 24306212585963394977157007553000292513595748⟩
  | 2, 2 => ⟨41806588704915602796570085559082066638007076, 41806588704915602796570085559100698090221971⟩
  | 3, 1 => ⟨44237995011869438421909790679028442335830013, 44237995011869438421909790679056088080315728⟩
  | 0, 5 => ⟨-138162268305240629574358310691194578036845795111, 137663756662459945812496098433606941017038139967⟩
  | 1, 4 => ⟨-207732532333353847756719009417895680766122980423, 205604474291992341322722824185300058279552709824⟩
  | 2, 3 => ⟨-329967829546443948817239479488535395961314807593, 325892327669962185604912039639069502734182622586⟩
  | 3, 2 => ⟨-532246943245901465672215875779906095543794299720, 526322356234444902422091812904919444631237987273⟩
  | 4, 1 => ⟨-848720350091615239294895336136473110440022765938, 843131302463100122853731495552210000880203577443⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0017Geometry.ds, E8TAxisProd0017Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1982693090177056431813568043352849398689 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0017CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0018CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0018CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0018GraphCenterA.qJetBox,
   E8TAxisProd0018GraphCenterB.qJetBox,
   E8TAxisProd0018GraphCenterC.qJetBox,
   E8TAxisProd0018GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0018GraphWholeA.qJetBox,
   E8TAxisProd0018GraphWholeB.qJetBox,
   E8TAxisProd0018GraphWholeC.qJetBox,
   E8TAxisProd0018GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2273057505090012420402941173288753549542, 2273057505090012420402941174136858677590⟩
  | 0, 2 => ⟨64059374474334180913840977272174612081693, 64059374474334180913840977275193189041871⟩
  | 1, 1 => ⟨72195171841419223408420198818286566695044, 72195171841419223408420198821975361603610⟩
  | 0, 3 => ⟨945480972907139818597256604876038503726393, 945480972907139818597256604880341353609371⟩
  | 1, 2 => ⟨1674624166523991518676331304155883437434043, 1674624166523991518676331304160565253116412⟩
  | 2, 1 => ⟨1835475497022753463005216401999678344592350, 1835475497022753463005216402005330922354470⟩
  | 0, 4 => ⟨6188118728843404029560755104651306854142043, 6188118728843404029560755104664571653258762⟩
  | 1, 3 => ⟨19063113074150259723501885596671634008698947, 19063113074150259723501885596685987975466327⟩
  | 2, 2 => ⟨32989243250226146971155853274484215373790972, 32989243250226146971155853274502153843351007⟩
  | 3, 1 => ⟨35133320795949490711488138336617221508829830, 35133320795949490711488138336643771308039353⟩
  | 0, 5 => ⟨-134639276188995767253534162124144495747133061111, 134205133979646394750511447972708108838872743472⟩
  | 1, 4 => ⟨-201982078207109961216891192478197327810248519050, 200110527016767527980774213225069462410109731231⟩
  | 2, 3 => ⟨-320004103994835303790007967352359812887603418716, 316415855334649197611290919851534938353929971956⟩
  | 3, 2 => ⟨-514801843483494917559114718476143766846439371327, 509585079514783352636257939041867180683771500158⟩
  | 4, 1 => ⟨-818140907926580858942677115508408939857562713258, 813211738067495954810812177236463687990904816175⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0018Geometry.ds, E8TAxisProd0018Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 815021022732256150812183970832248767857 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0018CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0019CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0019CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0019GraphCenterA.qJetBox,
   E8TAxisProd0019GraphCenterB.qJetBox,
   E8TAxisProd0019GraphCenterC.qJetBox,
   E8TAxisProd0019GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0019GraphWholeA.qJetBox,
   E8TAxisProd0019GraphWholeB.qJetBox,
   E8TAxisProd0019GraphWholeC.qJetBox,
   E8TAxisProd0019GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1403677897334622912194321151401123750669, 1403677897334622912194321152212959542408⟩
  | 0, 2 => ⟨41208915633006696470680664012049229993809, 41208915633006696470680664015023781543265⟩
  | 1, 1 => ⟨49304827986706816555803053763715948408741, 49304827986706816555803053767356051618232⟩
  | 0, 3 => ⟨655075828026852783000006174576452999507299, 655075828026852783000006174580629998179868⟩
  | 1, 2 => ⟨1203472797086387685045033628651590691042259, 1203472797086387685045033628656127054370678⟩
  | 2, 1 => ⟨1382540463684297918259875695285292576226818, 1382540463684297918259875695290719982407790⟩
  | 0, 4 => ⟨4660453899254457613803119812095395118827067, 4660453899254457613803119812108387648070870⟩
  | 1, 3 => ⟨14886218053121934158164496217492430426219457, 14886218053121934158164496217506445472071771⟩
  | 2, 2 => ⟨26422137071750813258252107931178942976422004, 26422137071750813258252107931196349582318677⟩
  | 3, 1 => ⟨29084042417176350453016482831785308911686057, 29084042417176350453016482831811022226587573⟩
  | 0, 5 => ⟨-131972754196041984688810447521504124408296159687, 131580102816005463937648365113407132966654439354⟩
  | 1, 4 => ⟨-197667918231971277406345106730318083246293712976, 195978549069797016786392178537160155860631901169⟩
  | 2, 3 => ⟨-312592709238863026012774365755027257774045639117, 309365093343327904967117004618132534675288692185⟩
  | 3, 2 => ⟨-501988018254147062071164540409460156947012349810, 497312787983425902958593620217444704911164965836⟩
  | 4, 1 => ⟨-796066109182765270136249776581744002015368032023, 791631929306470493449253924369053811930633436868⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0019Geometry.ds, E8TAxisProd0019Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 263529458728066561982116535675129262621 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0019CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0020CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0020CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0020GraphCenterA.qJetBox,
   E8TAxisProd0020GraphCenterB.qJetBox,
   E8TAxisProd0020GraphCenterC.qJetBox,
   E8TAxisProd0020GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0020GraphWholeA.qJetBox,
   E8TAxisProd0020GraphWholeB.qJetBox,
   E8TAxisProd0020GraphWholeC.qJetBox,
   E8TAxisProd0020GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨721263032343315762417914580360034938745, 721263032343315762417914581128361941406⟩
  | 0, 2 => ⟨23394619170430597535431159853894678123704, 23394619170430597535431159856815883128686⟩
  | 1, 1 => ⟨29033465540951448555163782640067161508194, 29033465540951448555163782643649130590208⟩
  | 0, 3 => ⟨418299219943968218489829987109275642581408, 418299219943968218489829987113299343784684⟩
  | 1, 2 => ⟨787161533289482103972559106275854048551491, 787161533289482103972559106280216903450069⟩
  | 2, 1 => ⟨930899718578884091870009305560390687399380, 930899718578884091870009305565557246551618⟩
  | 0, 4 => ⟨3355979364358140538079021676094328369273056, 3355979364358140538079021676106991828278781⟩
  | 1, 3 => ⟨11004961987799973125571932880961905471569929, 11004961987799973125571932880975525081238007⟩
  | 2, 2 => ⟨19866981528451946613735095408577075768309309, 19866981528451946613735095408593874070494837⟩
  | 3, 1 => ⟨22322023250438845037362653178213812800337734, 22322023250438845037362653178238569171670037⟩
  | 0, 5 => ⟨-112419522341703435863843951569306254566839797842, 112073839147354341243957924268016991920094600130⟩
  | 1, 4 => ⟨-172068633296206755056137120036677866858849342332, 170664799942886815690414701039412210586413259204⟩
  | 2, 3 => ⟨-273917523993584424987847746214209516858976945654, 271256597975951450034284657286912859678071826108⟩
  | 3, 2 => ⟨-439750407645353127843961307868743991557225497913, 435897062620489088624391102208910879888236808184⟩
  | 4, 1 => ⟨-696400774733542399444316397741018276143038427802, 692638196016114739067555166516666552308292292419⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0020Geometry.ds, E8TAxisProd0020Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 55556497555614172408475471004153456426 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0020CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0021CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0021CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0021GraphCenterA.qJetBox,
   E8TAxisProd0021GraphCenterB.qJetBox,
   E8TAxisProd0021GraphCenterC.qJetBox,
   E8TAxisProd0021GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0021GraphWholeA.qJetBox,
   E8TAxisProd0021GraphWholeB.qJetBox,
   E8TAxisProd0021GraphWholeC.qJetBox,
   E8TAxisProd0021GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨664074933428208700555176579175580959635, 664074933428208700555176579938895559127⟩
  | 0, 2 => ⟨22359352996478394092103915673947933134757, 22359352996478394092103915676862313954037⟩
  | 1, 1 => ⟨27099786903032012709634636677100091582914, 27099786903032012709634636680674665345929⟩
  | 0, 3 => ⟨409915931907470685106472593303303559252303, 409915931907470685106472593307307532382309⟩
  | 1, 2 => ⟨759847464889817087142802283787324489849500, 759847464889817087142802283791666185797478⟩
  | 2, 1 => ⟨881839366582165945644699956291007251305256, 881839366582165945644699956296146123435640⟩
  | 0, 4 => ⟨3350668906748931582456298019522113510659339, 3350668906748931582456298019534734725352591⟩
  | 1, 3 => ⟨10846351078759725998322295381943233324384552, 10846351078759725998322295381956807720984506⟩
  | 2, 2 => ⟨19381983009096295216438338260105518989076743, 19381983009096295216438338260122254110347265⟩
  | 3, 1 => ⟨21486234874741532463916660583129313425826297, 21486234874741532463916660583153969115504894⟩
  | 0, 5 => ⟨-112101184955097723032618894330752766814775035407, 111764131435952504844507864933612937069516298870⟩
  | 1, 4 => ⟨-171529212427776160580935235951777289686820310586, 170154552380298650600430540313820831154821664548⟩
  | 2, 3 => ⟨-272959551155009794831654267921975179833022971745, 270347416784428391737125608762471088449990975228⟩
  | 3, 2 => ⟨-438013822568001777131753264823274019588485601896, 434222645633889156616056505004265769501106889785⟩
  | 4, 1 => ⟨-693212597269084641976577245573788640567748335934, 689512837530677282895190716369215304136623846283⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0021Geometry.ds, E8TAxisProd0021Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 21774746069930861703372097894491180572 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0021CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0022CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0022CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0022GraphCenterA.qJetBox,
   E8TAxisProd0022GraphCenterB.qJetBox,
   E8TAxisProd0022GraphCenterC.qJetBox,
   E8TAxisProd0022GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0022GraphWholeA.qJetBox,
   E8TAxisProd0022GraphWholeB.qJetBox,
   E8TAxisProd0022GraphWholeC.qJetBox,
   E8TAxisProd0022GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1205724761093225208472810205105780332967, 1205724761093225208472810205907444453243⟩
  | 0, 2 => ⟨37991722799982878217231244488421818589587, 37991722799982878217231244491382324321860⟩
  | 1, 1 => ⟨43471958017122504121235535095208042532379, 43471958017122504121235535098832871051593⟩
  | 0, 3 => ⟨631815054869394907561493876338578617518640, 631815054869394907561493876342715367118978⟩
  | 1, 2 => ⟨1129991539415418839341823447698505657519963, 1129991539415418839341823447702998684461197⟩
  | 2, 1 => ⟨1253273818004324033662028093444142474825977, 1253273818004324033662028093449512881649548⟩
  | 0, 4 => ⟨4643954245536761768460538528894696110294551, 4643954245536761768460538528907601819651888⟩
  | 1, 3 => ⟨14506598848847302219140524302607280156636779, 14506598848847302219140524302621201740349958⟩
  | 2, 2 => ⟨25287412334511658549788213764701407860059685, 25287412334511658549788213764718683215565735⟩
  | 3, 1 => ⟨27151906194729440401314044126089310951407707, 27151906194729440401314044126114814716048768⟩
  | 0, 5 => ⟨-131215334776982359586893929152526705143931525747, 130845407112923006073774388310656363875112449009⟩
  | 1, 4 => ⟨-196408144347487128333388515679036197367899379945, 194786271670399253777375929699725499572436754953⟩
  | 2, 3 => ⟨-310362639597373231670312643366974815697504087643, 307246105369841111484093721910173267838238629443⟩
  | 3, 2 => ⟨-497952172459314234613209295726880007270731214511, 493419471199204401789761101387052859183085534306⟩
  | 4, 1 => ⟨-788667495062681939389403978148164920202821295694, 784376716301304701114005674104048044591085907811⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0022Geometry.ds, E8TAxisProd0022Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 140284393974928527110962606430754148556 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0022CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0025CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0025CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0025GraphCenterA.qJetBox,
   E8TAxisProd0025GraphCenterB.qJetBox,
   E8TAxisProd0025GraphCenterC.qJetBox,
   E8TAxisProd0025GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0025GraphWholeA.qJetBox,
   E8TAxisProd0025GraphWholeB.qJetBox,
   E8TAxisProd0025GraphWholeC.qJetBox,
   E8TAxisProd0025GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3498297745624067003910947293292723001243, 3498297745624067003910947294177408212734⟩
  | 0, 2 => ⟨95102374555546004544330695978535332362523, 95102374555546004544330695981598931136688⟩
  | 1, 1 => ⟨101734224500673465212345275449521033749551, 101734224500673465212345275453260272489426⟩
  | 0, 3 => ⟨1311098493337950940873308742402715143071658, 1311098493337950940873308742407146190733531⟩
  | 1, 2 => ⟨2253818431239712248751207613532605194894755, 2253818431239712248751207613537436410342751⟩
  | 2, 1 => ⟨2372474223467396425331262109372693403828203, 2372474223467396425331262109378577425420505⟩
  | 0, 4 => ⟨7957754053472942302801816708880072321763828, 7957754053472942302801816708893616523130204⟩
  | 1, 3 => ⟨23790522707985171233246968659875049913346224, 23790522707985171233246968659889754857877372⟩
  | 2, 2 => ⟨40324033345246687680435381027017370548345725, 40324033345246687680435381027035860411493387⟩
  | 3, 1 => ⟨41759599977932560450825875919243866358465484, 41759599977932560450825875919271285213367297⟩
  | 0, 5 => ⟨-137365500953423233762500637741283214670873587060, 136889764679923412024324844594798018336205049226⟩
  | 1, 4 => ⟨-206403221660462319722154837720573192893687972515, 204345296728220115459795147987708233928473499919⟩
  | 2, 3 => ⟨-327609230739347059823528047007692155987003640164, 323650649693281060083135204938957989473694676843⟩
  | 3, 2 => ⟨-527969818452543138205973020914302465082007093153, 522197005927982788733826825036187609165021913155⟩
  | 4, 1 => ⟨-840864407836136539712563893380252892881978763740, 835430391556369453813336428080867307344289963621⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0025Geometry.ds, E8TAxisProd0025Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1632558688281025102338624859630106931790 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0025CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0026CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0026CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0026GraphCenterA.qJetBox,
   E8TAxisProd0026GraphCenterB.qJetBox,
   E8TAxisProd0026GraphCenterC.qJetBox,
   E8TAxisProd0026GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0026GraphWholeA.qJetBox,
   E8TAxisProd0026GraphWholeB.qJetBox,
   E8TAxisProd0026GraphWholeC.qJetBox,
   E8TAxisProd0026GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1964450351169984174710823325512821834015, 1964450351169984174710823326350625501056⟩
  | 0, 2 => ⟨59409220913517259315960089031023522085852, 59409220913517259315960089034027703808718⟩
  | 1, 1 => ⟨64058485768385628817333545767249656723013, 64058485768385628817333545770922740072401⟩
  | 0, 3 => ⟨914600323535420043577544978381245757366932, 914600323535420043577544978385507652843840⟩
  | 1, 2 => ⟨1580420589460172749188717283988702974255620, 1580420589460172749188717283993340517000120⟩
  | 2, 1 => ⟨1673777201661062003064398211879888235704005, 1673777201661062003064398211885482300148038⟩
  | 0, 4 => ⟨6164272147044087065960939923207573675952605, 6164272147044087065960939923220749591183107⟩
  | 1, 3 => ⟨18618720011878579885669964808147724101807440, 18618720011878579885669964808161981822203930⟩
  | 2, 2 => ⟨31693135295761951928833725303450789464130642, 31693135295761951928833725303468592139516846⟩
  | 3, 1 => ⟨32956959920880540101469326475576596481430657, 32956959920880540101469326475602929094290756⟩
  | 0, 5 => ⟨-133864544220325211124858423853468970124234408458, 133452232736086287937552120785908569425127350941⟩
  | 1, 4 => ⟨-200691775766765821358014478111374394398240737716, 198887935562039864734197931759408477261454360275⟩
  | 2, 3 => ⟨-317717672559537951146910451152782859296071673072, 314242068042087683631437750211500550642862530406⟩
  | 3, 2 => ⟨-510660219111895831875057148197383670389294525877, 505588914936370119583269682636967162914577554155⟩
  | 4, 1 => ⟨-810541738594024314385905858151095409471993007639, 805759654236592784317930426647566683015907949223⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0026Geometry.ds, E8TAxisProd0026Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 608399896120753611513658773724012737906 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0026CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0027CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0027CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0027GraphCenterA.qJetBox,
   E8TAxisProd0027GraphCenterB.qJetBox,
   E8TAxisProd0027GraphCenterC.qJetBox,
   E8TAxisProd0027GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0027GraphWholeA.qJetBox,
   E8TAxisProd0027GraphWholeB.qJetBox,
   E8TAxisProd0027GraphWholeC.qJetBox,
   E8TAxisProd0027GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1023567170007044367001388880513710523819, 1023567170007044367001388881305243359968⟩
  | 0, 2 => ⟨34890630057284475160778451059551132924792, 34890630057284475160778451062497703457187⟩
  | 1, 1 => ⟨38001756891574160498454530127239030733841, 38001756891574160498454530130848702857643⟩
  | 0, 3 => ⟨608635298220117420172649789712258643925917, 608635298220117420172649789716355365296745⟩
  | 1, 2 => ⟨1058403710340520288047383014475200671290928, 1058403710340520288047383014479650599657026⟩
  | 2, 1 => ⟨1129637549425248661046851429227271873471443, 1129637549425248661046851429232585625049420⟩
  | 0, 4 => ⟨4628047004764703007873488019369161872634528, 4628047004764703007873488019381981416766527⟩
  | 1, 3 => ⟨14128838605687746765784810332950866420918693, 14128838605687746765784810332964695242805009⟩
  | 2, 2 => ⟨24169962217462991842189136739631674651962447, 24169962217462991842189136739648819777224406⟩
  | 3, 1 => ⟨25266610137517085205362337386428813728799974, 25266610137517085205362337386454109613893327⟩
  | 0, 5 => ⟨-130462289104280617794202934792088930255204109637, 130114984222985660353530580769316349539977601435⟩
  | 1, 4 => ⟨-195155917457493301265286899428156068267216244854, 193601131827104273329163354039001127636957208460⟩
  | 2, 3 => ⟨-308146336697925080685516370986664296052273452876, 305140108553731976327303567440010895887322494998⟩
  | 3, 2 => ⟨-493941926492591135811361345756367738486091061185, 489550565018444220925358092763636038213314487300⟩
  | 4, 1 => ⟨-781317060679985323068927400164200756598120590439, 777168082274227569589050679890885339806557332228⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0027Geometry.ds, E8TAxisProd0027Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 28817779954658072892581687199443660045 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0027CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0029CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0029CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0029GraphCenterA.qJetBox,
   E8TAxisProd0029GraphCenterB.qJetBox,
   E8TAxisProd0029GraphCenterC.qJetBox,
   E8TAxisProd0029GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0029GraphWholeA.qJetBox,
   E8TAxisProd0029GraphWholeB.qJetBox,
   E8TAxisProd0029GraphWholeC.qJetBox,
   E8TAxisProd0029GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨562308363468455278984636126765603036023, 562308363468455278984636127520323617526⟩
  | 0, 2 => ⟨21693077395853164081310899441591449753179, 21693077395853164081310899444492581295808⟩
  | 1, 1 => ⟨23509089767976939234137553671884470139797, 23509089767976939234137553675444662303421⟩
  | 0, 3 => ⟨426477750867244548049353632470563663615796, 426477750867244548049353632474529202564948⟩
  | 1, 2 => ⟨739994335551303454963160368378968546469933, 739994335551303454963160368383271043697414⟩
  | 2, 1 => ⟨786724807512997855008312196043778973001964, 786724807512997855008312196048874762200573⟩
  | 0, 4 => ⟨3632147902511744984209342941359323515238426, 3632147902511744984209342941371862370772440⟩
  | 1, 3 => ⟨11110184035751450722448244969561620660779047, 11110184035751450722448244969575116922468456⟩
  | 2, 2 => ⟨18987092963853129333072650236497073574174489, 18987092963853129333072650236513712814607438⟩
  | 3, 1 => ⟨19794167659190053854188318598852736255398464, 19794167659190053854188318598877235728962029⟩
  | 0, 5 => ⟨-50206280547798190137714483483542925248089361372, 50119371873379146124902023513746545968386549106⟩
  | 1, 4 => ⟨-73311578750849036560303527624648291385718527817, 72869332332559839044973102432318108527986862651⟩
  | 2, 3 => ⟨-114005173215993147744775749485693124563582520413, 113208961264507572965585337997764213460597784779⟩
  | 3, 2 => ⟨-180955285840864974037556325240283020038747783444, 179846932263521941709820317325332117481694301942⟩
  | 4, 1 => ⟨-283761466740516073117778278958342369580305963346, 282806767680804504248744168109496090413533706114⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0029Geometry.ds, E8TAxisProd0029Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 400351772993422947735213486904429906094 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0029CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0030CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0030CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0030GraphCenterA.qJetBox,
   E8TAxisProd0030GraphCenterB.qJetBox,
   E8TAxisProd0030GraphCenterC.qJetBox,
   E8TAxisProd0030GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0030GraphWholeA.qJetBox,
   E8TAxisProd0030GraphWholeB.qJetBox,
   E8TAxisProd0030GraphWholeC.qJetBox,
   E8TAxisProd0030GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨373871256729014230436644481181123788712, 373871256729014230436644481913165396046⟩
  | 0, 2 => ⟨15545950778205259830100703239935769358262, 15545950778205259830100703242809454454688⟩
  | 1, 1 => ⟨16958344902809323327859748797617689536194, 16958344902809323327859748801148220351235⟩
  | 0, 3 => ⟨330647419431685317486559816728439868568601, 330647419431685317486559816732325750292788⟩
  | 1, 2 => ⟨575992589519055962441236537247074444992101, 575992589519055962441236537251287558396019⟩
  | 2, 1 => ⟨615472372337938149707485509285498806541050, 615472372337938149707485509290461463818600⟩
  | 0, 4 => ⟨3043008570803537111660378620165481532354306, 3043008570803537111660378620177851030976981⟩
  | 1, 3 => ⟨9359897467244654059826590783818983545981512, 9359897467244654059826590783832278814918932⟩
  | 2, 2 => ⟨16043086419632305292788603905871074302091896, 16043086419632305292788603905887406472226048⟩
  | 3, 1 => ⟨16782941771921595022877859531815467345093967, 16782941771921595022877859531839484672293181⟩
  | 0, 5 => ⟨-49632360413756806710218818685729184454598610615, 49536835800578111636909970078627172374712644040⟩
  | 1, 4 => ⟨-72408029505359818771419287755597784247471165827, 71976841426333419131657915951325362586708803471⟩
  | 2, 3 => ⟨-112460571783859147495708984640322812629119030157, 111690132802159815878804291273856351118095452238⟩
  | 3, 2 => ⟨-178274318871584010189997053138079302884003222606, 177195494634485532067531547161855778685559814436⟩
  | 4, 1 => ⟨-279086486426169057418046242738629007559593263581, 278113919741471360616432285625188037685166238733⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0030Geometry.ds, E8TAxisProd0030Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 253487430494316333814136046447617909223 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0030CertifiedArithmetic

end


