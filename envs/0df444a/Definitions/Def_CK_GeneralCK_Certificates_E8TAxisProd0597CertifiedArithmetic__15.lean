-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0597CertifiedArithmetic__15
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0597CertifiedArithmetic__15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T14:04:38.01085+00:00
-- url     : https://prove2.me/theorems/20c3c1c5-7676-4b85-b6f8-8e69dab6251a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0597CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0598CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0597CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0598CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0599CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0600CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0601CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0602CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0603CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0604CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0605CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0606CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0607CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0608CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0609CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0610CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0611CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0597CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0598CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0599CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0600CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0601CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0602CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0603CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0604CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0605CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0606CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0607CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0608CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0609CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0610CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0611CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0597CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0598CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0599CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0600CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0601CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0602CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0603CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0604CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0605CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0606CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0607CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0608CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0609CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0610CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0611CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0597CertifiedArithmetic (+14 modules: GeneralCK/Certificates/E8TAxisProd0598CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0599CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0600CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0601CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0602CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0603CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0604CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0605CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0606CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0607CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0608CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0609CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0610CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0611CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0593GraphCenterA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0585GraphCenterB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0583GraphCenterC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0592GraphCenterD__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0587GraphWholeA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0591GraphWholeB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0590GraphWholeC__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0587GraphWholeD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0592Geometry__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0599GraphCenterC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0600GraphCenterB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0601GraphWholeA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0602GraphWholeD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0602Geometry__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0606GraphCenterA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0606GraphCenterD__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0606GraphWholeB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0606GraphWholeC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0611GraphCenterC__11

-- ===== source module GeneralCK.Certificates.E8TAxisProd0597CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0597CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0597GraphCenterA.qJetBox,
   E8TAxisProd0597GraphCenterB.qJetBox,
   E8TAxisProd0597GraphCenterC.qJetBox,
   E8TAxisProd0597GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0597GraphWholeA.qJetBox,
   E8TAxisProd0597GraphWholeB.qJetBox,
   E8TAxisProd0597GraphWholeC.qJetBox,
   E8TAxisProd0597GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7735103783569308851937453851866445713335063917, 7735103783569308851937453851866498442070632387⟩
  | 0, 2 => ⟨25742407030211754039271683152621428567380521455, 25742407030211754039271683152621608677306086743⟩
  | 1, 1 => ⟨25940151257694593152745776550741999660358657013, 25940151257694593152745776550742312244830310655⟩
  | 0, 3 => ⟨58382417185142899312294321954521245196628834055, 58382417185142899312294321954521809002143024455⟩
  | 1, 2 => ⟨79743645367934964148618206390391326700962215400, 79743645367934964148618206390392303737129342632⟩
  | 2, 1 => ⟨80280529111443782544321252847462018241928599678, 80280529111443782544321252847463755111033662452⟩
  | 0, 4 => ⟨109639710878520904015567660678405412357937856800, 109639710878520904015567660678407262197312719239⟩
  | 1, 3 => ⟨167255520494463442743190485887528220630294163751, 167255520494463442743190485887531493815156788149⟩
  | 2, 2 => ⟨225175318080872203750871480338935474014846284954, 225175318080872203750871480338941393991270803469⟩
  | 3, 1 => ⟨226479222043443418271192259122871207558292784231, 226479222043443418271192259122882026193744379212⟩
  | 0, 5 => ⟨-284400598377797153206591398889832160770010491900285, 286342299052674079804058914220668208754085274545582⟩
  | 1, 4 => ⟨-551560286254969796662151190471593244413246605884813, 554434832360574469939476792551000951348531647918780⟩
  | 2, 3 => ⟨-1071343061249405089198061023995687669263821355523972, 1075438790887117823662311821656503054759495416386579⟩
  | 3, 2 => ⟨-2082806359887435594324957964080150089829930878345509, 2088151942883616279753538608073082601338048885643405⟩
  | 4, 1 => ⟨-4051530788423532105526160988716286160881865072083945, 4056999543191554434473054289800722347612392152121772⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0597Geometry.ds, E8TAxisProd0597Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7219874414602893131071673424030746420224048897 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0597CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0598CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0598CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0598GraphCenterA.qJetBox,
   E8TAxisProd0598GraphCenterB.qJetBox,
   E8TAxisProd0598GraphCenterC.qJetBox,
   E8TAxisProd0598GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0598GraphWholeA.qJetBox,
   E8TAxisProd0598GraphWholeB.qJetBox,
   E8TAxisProd0598GraphWholeC.qJetBox,
   E8TAxisProd0598GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8685064344980848191303518407529821260755861542, 8685064344980848191303518407529878816223746237⟩
  | 0, 2 => ⟨28677324053275082856820734951862848606607253436, 28677324053275082856820734951863047734754607865⟩
  | 1, 1 => ⟨28865855520332825988449044187071148693169428830, 28865855520332825988449044187071495819999820789⟩
  | 0, 3 => ⟨64525722800667163165005300630026597207292909656, 64525722800667163165005300630027223076702413325⟩
  | 1, 2 => ⟨87983014800264141993279292536233280148138569962, 87983014800264141993279292536234368674608856942⟩
  | 2, 1 => ⟨88489736168148822525049581415529316589442882174, 88489736168148822525049581415531256109146325943⟩
  | 0, 4 => ⟨120128525351019775596329770366264336295594501493, 120128525351019775596329770366266395443453768575⟩
  | 1, 3 => ⟨182820249911724694277476945626661109077721123180, 182820249911724694277476945626664763088618933210⟩
  | 2, 2 => ⟨245794629103190442733196125898898226012051776366, 245794629103190442733196125898904847007465848968⟩
  | 3, 1 => ⟨247011569109323953158082252082953608624844784325, 247011569109323953158082252082965727094025362344⟩
  | 0, 5 => ⟨-330615342583827912122170285198637867429928338438283, 332808941833038752883969830187420858745440968304581⟩
  | 1, 4 => ⟨-641873822120481932796362048879902672850822890201141, 645127869628561407519758113798130270418530097786390⟩
  | 2, 3 => ⟨-1247990712909328830716041559257246547956316169002712, 1252633104410053062513012900833560309336230121458735⟩
  | 3, 2 => ⟨-2428516557298417162660994762057865520671266716817445, 2434579257155429377569673246461830524637928945085081⟩
  | 4, 1 => ⟨-4728401008874705151829584617891057441209435116444817, 4734600951042367250987625045587860624324649963500080⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0598Geometry.ds, E8TAxisProd0598Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 8110830091472645015767941216223544947030251555 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0598CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0599CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0599CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0599GraphCenterA.qJetBox,
   E8TAxisProd0599GraphCenterB.qJetBox,
   E8TAxisProd0599GraphCenterC.qJetBox,
   E8TAxisProd0599GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0599GraphWholeA.qJetBox,
   E8TAxisProd0599GraphWholeB.qJetBox,
   E8TAxisProd0599GraphWholeC.qJetBox,
   E8TAxisProd0599GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7702971350373220583186041110133824864279106003, 7702971350373220583186041110133877488419901443⟩
  | 0, 2 => ⟨25669514606325800910530796556589395037099793289, 25669514606325800910530796556589574751576664707⟩
  | 1, 1 => ⟨25840602276078353037924539865090615689779474661, 25840602276078353037924539865090927572122443470⟩
  | 0, 3 => ⟨58245507754440258012470113164326302591238847180, 58245507754440258012470113164326865141020994761⟩
  | 1, 2 => ⟨79534799809220417550826226260884560560741483818, 79534799809220417550826226260885535380576417677⟩
  | 2, 1 => ⟨79999392988582880804934013023271088806332974974, 79999392988582880804934013023272821678551891229⟩
  | 0, 4 => ⟨109415444988851056520056521809539225352382779488, 109415444988851056520056521809541070965674368846⟩
  | 1, 3 => ⟨166897482854961850579565126975915026006680945536, 166897482854961850579565126975918291634782563556⟩
  | 2, 2 => ⟨224642647529714985601582532386807689540161669910, 224642647529714985601582532386813595714659277412⟩
  | 3, 1 => ⟨225771209482201561158047161696298057718422969379, 225771209482201561158047161696308850878300309361⟩
  | 0, 5 => ⟨-283522240686668606891198616538316659770241784148526, 285459348132516733935834115017685788918160404732789⟩
  | 1, 4 => ⟨-549845240978729131249920621221140412656309700333884, 552712934170978557920026828783798796058412605366151⟩
  | 2, 3 => ⟨-1067989844395064978856254930082357400816739835986249, 1072075812259150107175669420244247610745156757999122⟩
  | 3, 2 => ⟨-2076244557642883952435795846327011256785801794283502, 2081577439621816164072299949415015604927924911135827⟩
  | 4, 1 => ⟨-4038682235595909215071680209516603284987958096991314, 4044137875530301190318525949507782097953987299614368⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0599Geometry.ds, E8TAxisProd0599Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7189684755604733218641299043469549676775596032 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0599CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0600CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0600CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0600GraphCenterA.qJetBox,
   E8TAxisProd0600GraphCenterB.qJetBox,
   E8TAxisProd0600GraphCenterC.qJetBox,
   E8TAxisProd0600GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0600GraphWholeA.qJetBox,
   E8TAxisProd0600GraphWholeB.qJetBox,
   E8TAxisProd0600GraphWholeC.qJetBox,
   E8TAxisProd0600GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨10959825964880115623179596869814814254609628699, 10959825964880115623179596869814883139854956050⟩
  | 0, 2 => ⟨35576834994763244909630213667347858353299375107, 35576834994763244909630213667348102549315192281⟩
  | 1, 1 => ⟨35769658766847886239238464432216108182074609078, 35769658766847886239238464432216537432419258289⟩
  | 0, 3 => ⟨78740786159971219684655302520708584592553404191, 78740786159971219684655302520709357540185704484⟩
  | 1, 2 => ⟨107041853067727227560269773176194712353179250127, 107041853067727227560269773176196065774054942968⟩
  | 2, 1 => ⟨107549692360631237438899360489564990954167649918, 107549692360631237438899360489567413014255231498⟩
  | 0, 4 => ⟨144033890261102776157501360708334066558042382649, 144033890261102776157501360708336620885801546394⟩
  | 1, 3 => ⟨218223174751099992355639287550582980603564966782, 218223174751099992355639287550587536820111137374⟩
  | 2, 2 => ⟨292687660910931992983135869549470957869157857029, 292687660910931992983135869549479241737400495245⟩
  | 3, 1 => ⟨293881220721047553104315536905651823822006261440, 293881220721047553104315536905667029768188682624⟩
  | 0, 5 => ⟨-443773044961587501530913716707071104113728221390020, 446569005962908679469509314132733677415670148431642⟩
  | 1, 4 => ⟨-863254861915896800191721564697970111154307413351751, 867417736019230002847226036436512922786009748117072⟩
  | 2, 3 => ⟨-1681471304536622748004289335443515809140657349022997, 1687424177008373685394981982646049406480215166167139⟩
  | 3, 2 => ⟨-3277789041209018803119481232727503580156539792305588, 3285571875248743354276394593811572407295866563503726⟩
  | 4, 1 => ⟨-6393026385898425318907887588051602384997488535990928, 6400980831517675619206015832089252892474633889854906⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0600Geometry.ds, E8TAxisProd0600Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10246116384644213083430973886703146446231376957 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0600CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0601CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0601CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0601GraphCenterA.qJetBox,
   E8TAxisProd0601GraphCenterB.qJetBox,
   E8TAxisProd0601GraphCenterC.qJetBox,
   E8TAxisProd0601GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0601GraphWholeA.qJetBox,
   E8TAxisProd0601GraphWholeB.qJetBox,
   E8TAxisProd0601GraphWholeC.qJetBox,
   E8TAxisProd0601GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨9741579882310850421782079985681787123247074330, 9741579882310850421782079985681850000344783046⟩
  | 0, 2 => ⟨31913613708281881658262552167254138133651272472, 31913613708281881658262552167254358368564516276⟩
  | 1, 1 => ⟨32088939067662276276132680987020940974640660219, 32088939067662276276132680987021326525467233094⟩
  | 0, 3 => ⟨71236841869359705408126590970411826590578402653, 71236841869359705408126590970412521349838250438⟩
  | 1, 2 => ⟨96972007825546433141332095656870667308009406021, 96972007825546433141332095656871879819093043400⟩
  | 2, 1 => ⟨97438504435453826347868631172392854753522520685, 97438504435453826347868631172395019976512237156⟩
  | 0, 4 => ⟨131477039786626461692365767546837488257403305119, 131477039786626461692365767546839779415967615790⟩
  | 1, 3 => ⟨199628896210773265713326065598066853896955141104, 199628896210773265713326065598070930568448611310⟩
  | 2, 2 => ⟨268037209413531121040663712264328384401561560468, 268037209413531121040663712264335784215355535394⟩
  | 3, 1 => ⟨269145414678124159193938811500107310661458814468, 269145414678124159193938811500120874650724991651⟩
  | 0, 5 => ⟨-383086764129910471684569024696692746168574043144976, 385562061362314438644215641183880918427982565061998⟩
  | 1, 4 => ⟨-744490219573689254073003189457343599008339045126970, 748169108074492426405926761207038179019737165187536⟩
  | 2, 3 => ⟨-1448847004937747206773794166691597539172634216978312, 1454101837464309081538254957984913102174905712953359⟩
  | 3, 2 => ⟨-2821887009654308354217140717655378366114569160712049, 2828753488103059143892948963599318572546721937971243⟩
  | 4, 1 => ⟨-5499141975753103397266646311880248008758421261249368, 5506161588993680380014415707115426051262057343293084⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0601Geometry.ds, E8TAxisProd0601Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 9102241451809295901523732749000790978013460582 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0601CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0602CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0602CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0602GraphCenterA.qJetBox,
   E8TAxisProd0602GraphCenterB.qJetBox,
   E8TAxisProd0602GraphCenterC.qJetBox,
   E8TAxisProd0602GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0602GraphWholeA.qJetBox,
   E8TAxisProd0602GraphWholeB.qJetBox,
   E8TAxisProd0602GraphWholeC.qJetBox,
   E8TAxisProd0602GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨10915416390513153323097062449422193742115090871, 10915416390513153323097062449422262488839142279⟩
  | 0, 2 => ⟨35478521463870536742834864007010133307445882851, 35478521463870536742834864007010376967198056365⟩
  | 1, 1 => ⟨35636026819099747330003409704191400703229840530, 35636026819099747330003409704191828992361312791⟩
  | 0, 3 => ⟨78560922977829057260939222634164499890054150908, 78560922977829057260939222634165271127569026535⟩
  | 1, 2 => ⟨106769357901804255479891318393442309660954639422, 106769357901804255479891318393443660042458067800⟩
  | 2, 1 => ⟨107184252666652512240997854416868597086590262293, 107184252666652512240997854416871013641081497624⟩
  | 0, 4 => ⟨143747284805274136568689557248690314058029751167, 143747284805274136568689557248692862631877072838⟩
  | 1, 3 => ⟨217769226684654698393815379112136391951101425845, 217769226684654698393815379112140937836959512998⟩
  | 2, 2 => ⟨292016058193956226755481598417145914334674475252, 292016058193956226755481598417154179290159303049⟩
  | 3, 1 => ⟨292991351675719694097672190695952530720326321823, 292991351675719694097672190695967701683542997311⟩
  | 0, 5 => ⟨-442485594645139783410534770013495644749323172363503, 445275125821568049197831697239580171348007109992782⟩
  | 1, 4 => ⟨-860735799765860313374005478355421278307562628436579, 864889071392723835080605135035046374492129273399194⟩
  | 2, 3 => ⟨-1676536425786578921589270098322713584124233810799453, 1682475632930134495695837302714370605466038520590090⟩
  | 3, 2 => ⟨-3268113745406230206694298805907744392865840926169969, 3275878867294218325108840815464136376223817924141138⟩
  | 4, 1 => ⟨-6374045752805437517577548776677553211679651585952719, 6381982111784931090710733845021147727448660935428237⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0602Geometry.ds, E8TAxisProd0602Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10204321016936653246963730978036329670298205997 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0602CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0603CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0603CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0603GraphCenterA.qJetBox,
   E8TAxisProd0603GraphCenterB.qJetBox,
   E8TAxisProd0603GraphCenterC.qJetBox,
   E8TAxisProd0603GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0603GraphWholeA.qJetBox,
   E8TAxisProd0603GraphWholeB.qJetBox,
   E8TAxisProd0603GraphWholeC.qJetBox,
   E8TAxisProd0603GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨9701743476181188224404706946900060850886233340, 9701743476181188224404706946900123602083282312⟩
  | 0, 2 => ⟨31824670303603698469767999065123442957426578033, 31824670303603698469767999065123662708604389067⟩
  | 1, 1 => ⟨31967879908739531689521055169184164998907522713, 31967879908739531689521055169184549685286188119⟩
  | 0, 3 => ⟨71072660614562877905602968087955933407264625363, 71072660614562877905602968087956626625452157519⟩
  | 1, 2 => ⟨96722733784145097884953425595548459204036969098, 96722733784145097884953425595549668982460806197⟩
  | 2, 1 => ⟨97103846352678352860379563180518672882580167753, 97103846352678352860379563180520833162881193794⟩
  | 0, 4 => ⟨131213045392868274936876180509638554679029185657, 131213045392868274936876180509640840647249807297⟩
  | 1, 3 => ⟨199209696349304554982479801417672566808691184701, 199209696349304554982479801417676634176100089936⟩
  | 2, 2 => ⟨267415917344520420153717290530217406703710642677, 267415917344520420153717290530224789499928628772⟩
  | 3, 1 => ⟨268321456795255099208098056714262930046256262794, 268321456795255099208098056714276462582439406463⟩
  | 0, 5 => ⟨-381951451577446890032712066049187263201480232463568, 384420998514962448523284569265209602812035392303825⟩
  | 1, 4 => ⟨-742270290946008113385710533515370825828062517663485, 745940594444889599601542331489581670629060248017034⟩
  | 2, 3 => ⟨-1444500831481651048843416013135215008242527945354859, 1449743442818616042039567752218144031459300556497598⟩
  | 3, 2 => ⟨-2813371071459407631002877300314321919247615829499577, 2820221690000784479629771397648038021953912178613748⟩
  | 4, 1 => ⟨-5482445697980857522433917256579980538030104053235806, 5489449057827897544905146285899235629562645062908377⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0603Geometry.ds, E8TAxisProd0603Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 9064771525488852751652367990223535163361246363 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0603CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0604CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0604CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0604GraphCenterA.qJetBox,
   E8TAxisProd0604GraphCenterB.qJetBox,
   E8TAxisProd0604GraphCenterC.qJetBox,
   E8TAxisProd0604GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0604GraphWholeA.qJetBox,
   E8TAxisProd0604GraphWholeB.qJetBox,
   E8TAxisProd0604GraphWholeC.qJetBox,
   E8TAxisProd0604GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8649268061550674568309524085019682311824209001, 8649268061550674568309524085019739752569451565⟩
  | 0, 2 => ⟨28596760686766656276221869846899738766272059623, 28596760686766656276221869846899937457077366095⟩
  | 1, 1 => ⟨28756019479181224469626442784745222806980853910, 28756019479181224469626442784745569154725157777⟩
  | 0, 3 => ⟨64375714324752994938708267940564007007839813916, 64375714324752994938708267940564631486510903406⟩
  | 1, 2 => ⟨87754731782767420007405661763338376235365993085, 87754731782767420007405661763339462300999024110⟩
  | 2, 1 => ⟨88182852665713567913858903823063540924524514618, 88182852665713567913858903823065475999312654691⟩
  | 0, 4 => ⟨119885108039038561733860609312898415090868912752, 119885108039038561733860609312900469560369743470⟩
  | 1, 3 => ⟨182432695640799080588482799661189086024115294904, 182432695640799080588482799661192731653952151552⟩
  | 2, 2 => ⟨245219156017074135341195081302732313527579136531, 245219156017074135341195081302738919199080287837⟩
  | 3, 1 => ⟨246247530581208740921129913398475715365533284867, 246247530581208740921129913398487805524939289155⟩
  | 0, 5 => ⟨-329614206279420834093169362928566612598500006839608, 331802657047351355608978306857923571315249589428958⟩
  | 1, 4 => ⟨-639917598416314841415922506680733495485112981780840, 643163961581464736233930629348779119164324263139070⟩
  | 2, 3 => ⟨-1244163300231329337201553798899944111502816830812118, 1248794748939225786386774240425684280849675575517266⟩
  | 3, 2 => ⟨-2421021800526537723749448204871020959477779814870333, 2427070281731797196291824126577517282743562736674457⟩
  | 4, 1 => ⟨-4713715976946078973851781028278686594497688866497526, 4719901295501686657110351437377557166788427932053148⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0604Geometry.ds, E8TAxisProd0604Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 8077179221815430008306551107900291626194542716 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0604CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0605CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0605CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0605GraphCenterA.qJetBox,
   E8TAxisProd0605GraphCenterB.qJetBox,
   E8TAxisProd0605GraphCenterC.qJetBox,
   E8TAxisProd0605GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0605GraphWholeA.qJetBox,
   E8TAxisProd0605GraphWholeB.qJetBox,
   E8TAxisProd0605GraphWholeC.qJetBox,
   E8TAxisProd0605GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7670929925819467659566462786855698990048097551, 7670929925819467659566462786855751509804326357⟩
  | 0, 2 => ⟨25596793144124744775072595306401883343560295030, 25596793144124744775072595306402062663439284023⟩
  | 1, 1 => ⟨25741314071864478044408831990801152489015850422, 25741314071864478044408831990801463670762406415⟩
  | 0, 3 => ⟨58108878405944642044845449596957085266448381480, 58108878405944642044845449596957646563216358507⟩
  | 1, 2 => ⟨79326401387503968995493395934970854026295177693, 79326401387503968995493395934971826634629618542⟩
  | 2, 1 => ⟨79718922070386078915693218320356881818979674964, 79718922070386078915693218320358610703073350318⟩
  | 0, 4 => ⟨109191579241923051730181426634391089813986686490, 109191579241923051730181426634392931210345384688⟩
  | 1, 3 => ⟨166540101120133211470487653084179256010977435441, 166540101120133211470487653084182514098707610137⟩
  | 2, 2 => ⟨224110990338848009727547500995209906952306220545, 224110990338848009727547500995215799354829755268⟩
  | 3, 1 => ⟨225064669698696192522739613454586254192528508576, 225064669698696192522739613454597021932192817311⟩
  | 0, 5 => ⟨-282646249992701656682885554903121502109799527905143, 284578773703163837265676638950001098759901572591032⟩
  | 1, 4 => ⟨-548134836648703026892391890666605913485589394316399, 550995691133109615171972735261708163533572687136510⟩
  | 2, 3 => ⟨-1064645739159411209052104555385402691726270103579962, 1068721965245355876699446191284954874609874035309687⟩
  | 3, 2 => ⟨-2069700660340378712609530466314323347560548078711368, 2075020866592211693689121770860961257895142186065826⟩
  | 4, 1 => ⟨-4025868890380028564892078462075669263605877729305462, 4031311440155942349489047458206219894681786851619567⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0605Geometry.ds, E8TAxisProd0605Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7159581034393726169613385636811245183596053475 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0605CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0606CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0606CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0606GraphCenterA.qJetBox,
   E8TAxisProd0606GraphCenterB.qJetBox,
   E8TAxisProd0606GraphCenterC.qJetBox,
   E8TAxisProd0606GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0606GraphWholeA.qJetBox,
   E8TAxisProd0606GraphWholeB.qJetBox,
   E8TAxisProd0606GraphWholeC.qJetBox,
   E8TAxisProd0606GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8613572365213716967136709598402141099867660175, 8613572365213716967136709598402198426121453844⟩
  | 0, 2 => ⟨28516384640795689603376222629163925884430455315, 28516384640795689603376222629164124138833745427⟩
  | 1, 1 => ⟨28646468489208329157153689615488471140122131830, 28646468489208329157153689615488816710477130037⟩
  | 0, 3 => ⟨64226009850893047823521348405879903837955118674, 64226009850893047823521348405880526928890037309⟩
  | 1, 2 => ⟨87526932767506266815428767530247131107750079377, 87526932767506266815428767530248214717892439311⟩
  | 2, 1 => ⟨87876687825421897101053613605713024601453642662, 87876687825421897101053613605714955241030863855⟩
  | 0, 4 => ⟨119642121950736087532572235666753583748085249118, 119642121950736087532572235666755633549303620291⟩
  | 1, 3 => ⟨182045846144039697286338550201825098696185125498, 182045846144039697286338550201828735963027310019⟩
  | 2, 2 => ⟨244644769373233149360986485350714472997258641908, 244644769373233149360986485350721063377879207576⟩
  | 3, 1 => ⟨245485068525996882991090083627166331044542494283, 245485068525996882991090083627178392955245525110⟩
  | 0, 5 => ⟨-328615684890881050440371238059918320310254513269982, 330798998035792557053668805899928693464237555118058⟩
  | 1, 4 => ⟨-637966504678439478694643257264573513018202017012002, 641205199585009235324966633423964174573676842665974⟩
  | 2, 3 => ⟨-1240345964586675852454807285363124053539861016286353, 1244966493001969170477257400835049689529087767765759⟩
  | 3, 2 => ⟨-2413546855725335194087694576003856858522854654029047, 2419581146623383571932293429481350823691184119572063⟩
  | 4, 1 => ⟨-4699069921415387287565570840891031335538690298710468, 4705240643912883284798236111300776214522247375039784⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0606Geometry.ds, E8TAxisProd0606Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 8043623395277760616250322894270931033054475699 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0606CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0607CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0607CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0607GraphCenterA.qJetBox,
   E8TAxisProd0607GraphCenterB.qJetBox,
   E8TAxisProd0607GraphCenterC.qJetBox,
   E8TAxisProd0607GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0607GraphWholeA.qJetBox,
   E8TAxisProd0607GraphWholeB.qJetBox,
   E8TAxisProd0607GraphWholeC.qJetBox,
   E8TAxisProd0607GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7638979296424627980705878958158510791304974665, 7638979296424627980705878958158563206886414370⟩
  | 0, 2 => ⟨25524242293818273807500228475513093761372153376, 25524242293818273807500228475513272687502266195⟩
  | 1, 1 => ⟨25642286086643869038231982254244190666765617714, 25642286086643869038231982254244501149444771826⟩
  | 0, 3 => ⟨57972528639872522011560328112551651861486489807, 57972528639872522011560328112552211907952407030⟩
  | 1, 2 => ⟨79118449283569579511508894698448177986822139989, 79118449283569579511508894698449148388477564256⟩
  | 2, 1 => ⟨79439115091200434452380620381309678631246523384, 79439115091200434452380620381311403535957367920⟩
  | 0, 4 => ⟨108968113006053837455495597208861192905778281791, 108968113006053837455495597208863030094335515533⟩
  | 1, 3 => ⟨166183374226572199409192948347705149283484428613, 166183374226572199409192948347708399847199039512⟩
  | 2, 2 => ⟨223580344832855510553425257121511714898378199110, 223580344832855510553425257121517593558819386379⟩
  | 3, 1 => ⟨224359600183661390471820292765565063205827910343, 224359600183661390471820292765575805580528182480⟩
  | 0, 5 => ⟨-281772620900398333577766913639415762877700488868364, 283700570596223594670291777743203883189437862629745⟩
  | 1, 4 => ⟨-546429063020265619692010041142619101395601776116780, 549283093186880798647346866308844090947609014300076⟩
  | 2, 3 => ⟨-1061310725824798470790103559251285519960508871621390, 1065377230257481658240244592817216754772046977062708⟩
  | 3, 2 => ⟨-2063174629644006038948753137505974959874462691613567, 2068482185525341752055046136115347563038719397593708⟩
  | 4, 1 => ⟨-4013090677682407713063806446328529982274099940996498, 4018520161971223105726615956566243617736921610449713⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0607Geometry.ds, E8TAxisProd0607Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7129563048305156808324493525818377069112151014 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0607CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0608CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0608CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0608GraphCenterA.qJetBox,
   E8TAxisProd0608GraphCenterB.qJetBox,
   E8TAxisProd0608GraphCenterC.qJetBox,
   E8TAxisProd0608GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0608GraphWholeA.qJetBox,
   E8TAxisProd0608GraphWholeB.qJetBox,
   E8TAxisProd0608GraphWholeC.qJetBox,
   E8TAxisProd0608GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17236394085001326554895622718621127288622096509, 17236394085001326554895622718621226881623559640⟩
  | 0, 2 => ⟨54079525549863636422290657986343113300410383702, 54079525549863636422290657986343482739263380197⟩
  | 1, 1 => ⟨54256802118639543044412429711339799883318646865, 54256802118639543044412429711340458994132678908⟩
  | 0, 3 => ⟨115771828061356803856590976894491418499725874092, 115771828061356803856590976894492607071312612414⟩
  | 1, 2 => ⟨156516617946077752345080215364769948578421031592, 156516617946077752345080215364772055813480243973⟩
  | 2, 1 => ⟨156965413823462358991138694115991285180522949368, 156965413823462358991138694115995088579576814330⟩
  | 0, 4 => ⟨204637991524584221102953536716018995072424091726, 204637991524584221102953536716022984799055007671⟩
  | 1, 3 => ⟨307496676403181145047481274026988288622716080313, 307496676403181145047481274026995475675648601737⟩
  | 2, 2 => ⟨410586271037756986515790230350947838203975362494, 410586271037756986515790230350960994941874838502⟩
  | 3, 1 => ⟨411601435543002882664071242679243578214169695998, 411601435543002882664071242679267873065742619949⟩
  | 0, 5 => ⟨-767370350110414583624579764440259449998795744660651, 771878620704501189518896245216327325461354240947237⟩
  | 1, 4 => ⟨-1497633640509633690570805103414374681768817313882060, 1504391369491896949003297821666024478283408804340445⟩
  | 2, 3 => ⟨-2926137077942377915461717732924927810055127586232215, 2935843806617945035257102781783114209631911003464886⟩
  | 3, 2 => ⟨-5721251453866831124619340243693983092120937932541322, 5733971500962402344398313484915821890638702385926701⟩
  | 4, 1 => ⟨-11192106600342892399735351385928337302087223509329279, 11205101770217545743381170698062012529295464166606556⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0608Geometry.ds, E8TAxisProd0608Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16147875813014539369332374869679417619966616346 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0608CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0609CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0609CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0609GraphCenterA.qJetBox,
   E8TAxisProd0609GraphCenterB.qJetBox,
   E8TAxisProd0609GraphCenterC.qJetBox,
   E8TAxisProd0609GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0609GraphWholeA.qJetBox,
   E8TAxisProd0609GraphWholeB.qJetBox,
   E8TAxisProd0609GraphWholeC.qJetBox,
   E8TAxisProd0609GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨15384782951502338227627706742545657765532696082, 15384782951502338227627706742545748399466388185⟩
  | 0, 2 => ⟨48712549735079609996817265666464770802684336087, 48712549735079609996817265666465103372244203376⟩
  | 1, 1 => ⟨48874337665076775263580554146024809427313769939, 48874337665076775263580554146025400688870439496⟩
  | 0, 3 => ⟨105179589063706441565261213298609896448497399170, 105179589063706441565261213298610962061574221776⟩
  | 1, 2 => ⟨142366520699071631659382321051148524272589386462, 142366520699071631659382321051150407920425135423⟩
  | 2, 1 => ⟨142780127395891438427062583219455681095048465306, 142780127395891438427062583219459073850541508008⟩
  | 0, 4 => ⟨187508250128986318374562201245385403430553422075, 187508250128986318374562201245388965234737186576⟩
  | 1, 3 => ⟨282303588529983499163822481467983541904513721056, 282303588529983499163822481467989943003632059647⟩
  | 2, 2 => ⟨377314356443892824454658217012682460120386542751, 377314356443892824454658217012694158473002896560⟩
  | 3, 1 => ⟨378258365353183626933734194646989388149874636095, 378258365353183626933734194647010958122673751481⟩
  | 0, 5 => ⟨-672051749760870938174633971649397113080631573211394, 676054331187163848418530399928596920972413040739433⟩
  | 1, 4 => ⟨-1310623432613628973567676812380422162909349491931708, 1316613618445041756277749756763873505073840959574302⟩
  | 2, 3 => ⟨-2558928509567957965665696417695594544305921200807280, 2567523618512238019583111381176260530749912717055144⟩
  | 3, 2 => ⟨-4999791721164038145563377211046539225174957849541592, 5011048750845905015655003226744035015530352163489037⟩
  | 4, 1 => ⟨-9773978287903576042750360404037091082509934294664919, 9785479136127589235995811531720102679737386959419549⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0609Geometry.ds, E8TAxisProd0609Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 14405436973889716818023289610064816548267108152 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0609CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0610CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0610CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0610GraphCenterA.qJetBox,
   E8TAxisProd0610GraphCenterB.qJetBox,
   E8TAxisProd0610GraphCenterC.qJetBox,
   E8TAxisProd0610GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0610GraphWholeA.qJetBox,
   E8TAxisProd0610GraphWholeB.qJetBox,
   E8TAxisProd0610GraphWholeC.qJetBox,
   E8TAxisProd0610GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17168885058222849484333736498064468494994549370, 17168885058222849484333736498064567884835712894⟩
  | 0, 2 => ⟨53934970535477616896996583747922761468756284013, 53934970535477616896996583747923130092871533107⟩
  | 1, 1 => ⟨54061396416803772828705427489396892879873805102, 54061396416803772828705427489397550513317249057⟩
  | 0, 3 => ⟨115516277113117622717342695157957819065432451265, 115516277113117622717342695157959004974758092403⟩
  | 1, 2 => ⟨156132633879555988771959502372985198419206122179, 156132633879555988771959502372987300872100119778⟩
  | 2, 1 => ⟨156452749376180775694680525684821626218260526758, 156452749376180775694680525684825420889246610497⟩
  | 0, 4 => ⟨204243638659418227080614758673748120854778424463, 204243638659418227080614758673752101322200606294⟩
  | 1, 3 => ⟨306878012046661112232251144557650533370255311793, 306878012046661112232251144557657703635791107473⟩
  | 2, 2 => ⟨409677122195349379604800258252839066969465498513, 409677122195349379604800258252852192771011812172⟩
  | 3, 1 => ⟨410401325250965619478179705157761811640438098404, 410401325250965619478179705157786048953545234534⟩
  | 0, 5 => ⟨-765353406713099412245612655167974476577171673313016, 769851292300285547862020678224040762050693698186580⟩
  | 1, 4 => ⟨-1493678374469314471793129710469258588969573836302477, 1500420404525388229025593373326375947135874393281076⟩
  | 2, 3 => ⟨-2918371903494033354973431100434902028621988416015908, 2928055955391286992009524821690576987348161570335706⟩
  | 3, 2 => ⟨-5705994700184069883715366282335382039834757895212453, 5718684662407265256223825508248447142452851298338874⟩
  | 4, 1 => ⟨-11162113048048859255068881399622763369005594389521590, 11175075688405084184240058887308367368126826350315023⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0610Geometry.ds, E8TAxisProd0610Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16084196620792420841036923269331874346143413508 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0610CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0611CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0611CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0611GraphCenterA.qJetBox,
   E8TAxisProd0611GraphCenterB.qJetBox,
   E8TAxisProd0611GraphCenterC.qJetBox,
   E8TAxisProd0611GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0611GraphWholeA.qJetBox,
   E8TAxisProd0611GraphWholeB.qJetBox,
   E8TAxisProd0611GraphWholeC.qJetBox,
   E8TAxisProd0611GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨15323974374879247709876866754737656943997909711, 15323974374879247709876866754737747393636638481⟩
  | 0, 2 => ⟨48581221644715173802211857939276078660460607937, 48581221644715173802211857939276410496144777767⟩
  | 1, 1 => ⟨48696599914733651942273143019531376434341719290, 48696599914733651942273143019531966368560906934⟩
  | 0, 3 => ⟨104945431370827940276673179326606295028902346330, 104945431370827940276673179326607358251301112943⟩
  | 1, 2 => ⟨142013999115345400605541284409340173670420039523, 142013999115345400605541284409342053033320245653⟩
  | 2, 1 => ⟨142309011235665024634037268957789034918642990183, 142309011235665024634037268957792419865654560219⟩
  | 0, 4 => ⟨187144163217356669447484066022957073311830758290, 187144163217356669447484066022960626829810949917⟩
  | 1, 3 => ⟨281731114487665719016819629544795934411750240962, 281731114487665719016819629544802320514608065293⟩
  | 2, 2 => ⟨376471758117265005471354605693476659436443584527, 376471758117265005471354605693488330186967490169⟩
  | 3, 1 => ⟨377145196768100570070935045517793053069948534515, 377145196768100570070935045517814571759289449862⟩
  | 0, 5 => ⟨-670235744206264004472633095436124660215275655133598, 674229089045342311150694186032728682493543329042987⟩
  | 1, 4 => ⟨-1307063945757711790558742210599526868012626522865560, 1313040215411558067834394014994133932572903344926536⟩
  | 2, 3 => ⟨-2551943675256840641993242347995332192416785230707938, 2560518772309946397933941690345722259065273351494971⟩
  | 3, 2 => ⟨-4986074642706320232507500726015965817667954244364407, 4997305319854497983187428519867572295768213598994155⟩
  | 4, 1 => ⟨-9747024393341394426142390839285564495230138014077979, 9758497268739743858821107668863225158225373644551992⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0611Geometry.ds, E8TAxisProd0611Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 14348111157164932068910596266834498410484127376 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0611CertifiedArithmetic

end


