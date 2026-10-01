-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0652CertifiedArithmetic__13
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0652CertifiedArithmetic__13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T13:44:25.189908+00:00
-- url     : https://prove2.me/theorems/061cdc59-a780-4530-91e7-ac7dae7188d7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0652CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0653CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0652CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0653CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0654CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0655CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0656CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0657CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0658CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0659CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0660CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0661CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0662CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0663CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0664CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0652CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0653CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0654CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0655CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0656CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0657CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0658CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0659CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0660CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0661CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0662CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0663CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0664CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0652CertifiedArithmetic (+12 modules: GeneralCK.Certificates.E8TAxisProd0653CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0654CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0655CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0656CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0657CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0658CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0659CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0660CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0661CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0662CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0663CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0664CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0652CertifiedArithmetic (+12 modules: GeneralCK/Certificates/E8TAxisProd0653CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0654CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0655CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0656CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0657CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0658CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0659CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0660CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0661CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0662CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0663CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0664CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0644GraphCenterA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0652GraphCenterB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0648GraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0643GraphCenterD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0641GraphWholeA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0642GraphWholeB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0643GraphWholeC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0643GraphWholeD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0644Geometry__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0654GraphWholeC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0655GraphWholeA__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0655GraphWholeB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0656GraphWholeD__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0658GraphCenterD__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0659GraphCenterA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0659GraphCenterC__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0659Geometry__24
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0664GraphCenterB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0664GraphWholeA__13

-- ===== source module GeneralCK.Certificates.E8TAxisProd0652CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0652CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0652GraphCenterA.qJetBox,
   E8TAxisProd0652GraphCenterB.qJetBox,
   E8TAxisProd0652GraphCenterC.qJetBox,
   E8TAxisProd0652GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0652GraphWholeA.qJetBox,
   E8TAxisProd0652GraphWholeB.qJetBox,
   E8TAxisProd0652GraphWholeC.qJetBox,
   E8TAxisProd0652GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3234246184407139986613440852579747553012907431, 3234246184407139986613440852579776479881732127⟩
  | 0, 2 => ⟨11490904502817295023228288968529213740747665735, 11490904502817295023228288968529302841819066398⟩
  | 1, 1 => ⟨11588325473146659250179854588507623558238001239, 11588325473146659250179854588507772483741280140⟩
  | 0, 3 => ⟨27576344179065194940489036826561913811728313340, 27576344179065194940489036826562181869992212883⟩
  | 1, 2 => ⟨38109862331200740332578036713975572975660958154, 38109862331200740332578036713976023030947785779⟩
  | 2, 1 => ⟨38393710856254760781913526122272178995381469543, 38393710856254760781913526122272963910254299358⟩
  | 0, 4 => ⟨55039038413207969299390551428641436761775153513, 55039038413207969299390551428642288662903959116⟩
  | 1, 3 => ⟨85511507616896564336041579667912461060210080753, 85511507616896564336041579667913929381370042964⟩
  | 2, 2 => ⟨116163966241762587843807506078534090526551121343, 116163966241762587843807506078536703158679880982⟩
  | 3, 1 => ⟨116914286615931932095898120857461361188887048688, 116914286615931932095898120857466073009935686164⟩
  | 0, 5 => ⟨-90264836614106430012647907026611449837129718879371, 91088124104531698561513662058612618547428435553245⟩
  | 1, 4 => ⟨-173331212947942099582959497692119060194497314258882, 174524091683285784573052840877727567955679155235944⟩
  | 2, 3 => ⟨-333712165565616732687085985186867011119002010313200, 335389289046275587152860821275660156568413576268596⟩
  | 3, 2 => ⟨-643373881508524371387530552181878605990639000774396, 645549648976717362601072517482942350243262150730378⟩
  | 4, 1 => ⟨-1241350393654776233838774913537161831257416551313882, 1243586813986560914363160257337852155235288902812929⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0652Geometry.ds, E8TAxisProd0652Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3006277382982806488071658501169591741422540590 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0652CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0653CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0653CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0653GraphCenterA.qJetBox,
   E8TAxisProd0653GraphCenterB.qJetBox,
   E8TAxisProd0653GraphCenterC.qJetBox,
   E8TAxisProd0653GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0653GraphWholeA.qJetBox,
   E8TAxisProd0653GraphWholeB.qJetBox,
   E8TAxisProd0653GraphWholeC.qJetBox,
   E8TAxisProd0653GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2841701100881496239839539086406820305796136913, 2841701100881496239839539086406846965188716409⟩
  | 0, 2 => ⟨10193925081542333848099946786061788923504274882, 10193925081542333848099946786061869707622469653⟩
  | 1, 1 => ⟨10281616618728437464866382204310745643102926775, 10281616618728437464866382204310879811125819097⟩
  | 0, 3 => ⟨24652975641633081377540255613812958187076347292, 24652975641633081377540255613813199417564126790⟩
  | 1, 2 => ⟨34135746799524171987625001592969991071969463604, 34135746799524171987625001592970393843932637433⟩
  | 2, 1 => ⟨34393722076279000204332995573585553673276453225, 34393722076279000204332995573586253876932073139⟩
  | 0, 4 => ⟨49604038243609294017527414773286186544898499184, 49604038243609294017527414773286948272997940580⟩
  | 1, 3 => ⟨77300333420419373406251756821433867550099787787, 77300333420419373406251756821435174135885327669⟩
  | 2, 2 => ⟨105162937473945878811461161793503516690075459081, 105162937473945878811461161793505834820096211744⟩
  | 3, 1 => ⟨105853200446922368624773104510898000816852163447, 105853200446922368624773104510902172039910824008⟩
  | 0, 5 => ⟨-76288945786649098943240111506643866824140564100535, 77008813855688941053339005695170563591549717720510⟩
  | 1, 4 => ⟨-146231379194761016944090903015475259612242671635858, 147268450703760517949129632078234123379537488819203⟩
  | 2, 3 => ⟨-281097260896885940877669427188598969275833547071892, 282549855142646731334190405141945679445915606667273⟩
  | 3, 2 => ⟨-541146121794451837828168177903256267599579452655328, 543027226003804509020687291553810488055600041783745⟩
  | 4, 1 => ⟨-1042633735734364435222078601060602089519793509600998, 1044569373437211847210995160291533645118843283244498⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0653Geometry.ds, E8TAxisProd0653Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2639653740612516165654639741310770410313083364 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0653CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0654CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0654CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0654GraphCenterA.qJetBox,
   E8TAxisProd0654GraphCenterB.qJetBox,
   E8TAxisProd0654GraphCenterC.qJetBox,
   E8TAxisProd0654GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0654GraphWholeA.qJetBox,
   E8TAxisProd0654GraphWholeB.qJetBox,
   E8TAxisProd0654GraphWholeC.qJetBox,
   E8TAxisProd0654GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3219904079891019147234232899698974713723595739, 3219904079891019147234232899699003585596369387⟩
  | 0, 2 => ⟨11456477040278736253154318070571902784578717551, 11456477040278736253154318070571991692213691839⟩
  | 1, 1 => ⟨11540754899652062409283317523473770743955241744, 11540754899652062409283317523473919335825458285⟩
  | 0, 3 => ⟨27507621121324537290795958883000092493175746903, 27507621121324537290795958883000359948665901249⟩
  | 1, 2 => ⟨38003096396590637358689888509782153976447084942, 38003096396590637358689888509782602991442569635⟩
  | 2, 1 => ⟨38248692197015647047726906574676906563007707515, 38248692197015647047726906574677689627123365535⟩
  | 0, 4 => ⟨54917892667551524494030265452996780132780053669, 54917892667551524494030265452997630024355380739⟩
  | 1, 3 => ⟨85314052711216129608768897890901648222436940146, 85314052711216129608768897890903113013294846449⟩
  | 2, 2 => ⟨115865990711601873873058044084249163044917579036, 115865990711601873873058044084251769293366705817⟩
  | 3, 1 => ⟨116515332264556652312865600734948268682132023361, 116515332264556652312865600734952968814251011344⟩
  | 0, 5 => ⟨-89963919772116455551566020347672039765966689654494, 90785050610420406926284678242528749669249851832185⟩
  | 1, 4 => ⟨-172747622184089003654112437952838810285580611936239, 173937221266723656070218285112531008218050906512209⟩
  | 2, 3 => ⟨-332578131470979382475634052187544679684321750554016, 334250443470478569442480826316675118533936517963568⟩
  | 3, 2 => ⟨-641167594766512633368711012719037809986860884116522, 643336783434813917743850729192009490510645365576394⟩
  | 4, 1 => ⟨-1237054620232601063400438868178880201906975578666091, 1239283421461062949713925763531285350906196831601667⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0654Geometry.ds, E8TAxisProd0654Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2992856686207998775159580707788065189657300476 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0654CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0655CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0655CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0655GraphCenterA.qJetBox,
   E8TAxisProd0655GraphCenterB.qJetBox,
   E8TAxisProd0655GraphCenterC.qJetBox,
   E8TAxisProd0655GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0655GraphWholeA.qJetBox,
   E8TAxisProd0655GraphWholeB.qJetBox,
   E8TAxisProd0655GraphWholeC.qJetBox,
   E8TAxisProd0655GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2828977938528626929428085037312572395159928197, 2828977938528626929428085037312599004230413965⟩
  | 0, 2 => ⟨10163147586391329670037752730990547372973838765, 10163147586391329670037752730990627982238007877⟩
  | 1, 1 => ⟨10239007279094462381749320037001825439997990298, 10239007279094462381749320037001959307961889887⟩
  | 0, 3 => ⟨24591039591890732136284054330000377793373089921, 24591039591890732136284054330000618481127705482⟩
  | 1, 2 => ⟨34039234212083494421867514660969134812539539068, 34039234212083494421867514660969536651548072338⟩
  | 2, 1 => ⟨34262439055346532445927801319275130654088071188, 34262439055346532445927801319275829201786831318⟩
  | 0, 4 => ⟨49493677035527237252915298050608835824404390170, 49493677035527237252915298050609595748508436696⟩
  | 1, 3 => ⟨77119866622155865492439545553439240271581737649, 77119866622155865492439545553440543698628133168⟩
  | 2, 2 => ⟨104889990885431946571165583433639593557435885667, 104889990885431946571165583433641905986057291048⟩
  | 3, 1 => ⟨105487344267146769600473264594989216657763880070, 105487344267146769600473264594993377456130340851⟩
  | 0, 5 => ⟨-76032125560238261058894074456245147626267523663495, 76750095507636140329713461547421464995147621014181⟩
  | 1, 4 => ⟨-145733911154321328508300561880451240628720638436191, 146768100997106549861912524196990536889809203310635⟩
  | 2, 3 => ⟨-280131622007180878677415038745015820705701358926787, 281579991906624612704626324244548837473059148226919⟩
  | 3, 2 => ⟨-539269346853386325098529878736390964934435113005328, 541144675862515231459583128125586839242940966230232⟩
  | 4, 1 => ⟨-1038983102812556073673995120453056306497217178517072, 1040912051687900428658355997876266438811969807085083⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0655Geometry.ds, E8TAxisProd0655Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2627755177726307854425801687576231787391733941 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0655CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0656CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0656CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0656GraphCenterA.qJetBox,
   E8TAxisProd0656GraphCenterB.qJetBox,
   E8TAxisProd0656GraphCenterC.qJetBox,
   E8TAxisProd0656GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0656GraphWholeA.qJetBox,
   E8TAxisProd0656GraphWholeB.qJetBox,
   E8TAxisProd0656GraphWholeC.qJetBox,
   E8TAxisProd0656GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4137663681528234737168257280244521765799799587, 4137663681528234737168257280244555801170150970⟩
  | 0, 2 => ⟨14465021660597564828952228603833905862581775505, 14465021660597564828952228603834014015748564320⟩
  | 1, 1 => ⟨14552613845593619953929651368258248731032992103, 14552613845593619953929651368258431651023552293⟩
  | 0, 3 => ⟨34207627294531871403503697335395316794186838252, 34207627294531871403503697335395646560449335269⟩
  | 1, 2 => ⟨47073487135354789445530229446384201060017851669, 47073487135354789445530229446384760364628104211⟩
  | 2, 1 => ⟨47323808049957481532752419618490314609376810394, 47323808049957481532752419618491295868593446016⟩
  | 0, 4 => ⟨67179173655295463114252725088538012659495418155, 67179173655295463114252725088539072475954212882⟩
  | 1, 3 => ⟨103758875809560609703365597094841558700301600627, 103758875809560609703365597094843401280659003790⟩
  | 2, 2 => ⟨140492236686224952145487536864585636987277269604, 140492236686224952145487536864588932816433652978⟩
  | 3, 1 => ⟨141138166639704419044039960109347893564352985020, 141138166639704419044039960109353862269143981436⟩
  | 0, 5 => ⟨-125861235261765959063216909075557789336044748242005, 126906881357906304630918309373762622060968338934448⟩
  | 1, 4 => ⟨-242470551065364695941288565287973243881887961284190, 243997222125698436047851157744937637639930243771790⟩
  | 2, 3 => ⟨-468153329551645263902174210135612897644335966191572, 470310024396020452346602447271852844272712912584097⟩
  | 3, 2 => ⟨-904965557702349119155190596775766851458430577385809, 907769279203444319269052299916353216392744131089593⟩
  | 4, 1 => ⟨-1750569448965163340829556840204210925708863512197818, 1753445081678169067106524626127016309073753094217978⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0656Geometry.ds, E8TAxisProd0656Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3850624491187826319551911081079823783154330330 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0656CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0657CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0657CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0657GraphCenterA.qJetBox,
   E8TAxisProd0657GraphCenterB.qJetBox,
   E8TAxisProd0657GraphCenterC.qJetBox,
   E8TAxisProd0657GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0657GraphWholeA.qJetBox,
   E8TAxisProd0657GraphWholeB.qJetBox,
   E8TAxisProd0657GraphWholeC.qJetBox,
   E8TAxisProd0657GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3644172633886126222501506100348748011989960620, 3644172633886126222501506100348779313025683726⟩
  | 0, 2 => ⟨12861186489089856982812544067569895273620926052, 12861186489089856982812544067569993192848585756⟩
  | 1, 1 => ⟨12940188876483456071440767829376144119577910234, 12940188876483456071440767829376308763964768208⟩
  | 0, 3 => ⟨30655937569621891969410442474601994326892616486, 30655937569621891969410442474602290940532164342⟩
  | 1, 2 => ⟨42261219604599615832090626190122811955753953185, 42261219604599615832090626190123312522626500035⟩
  | 2, 1 => ⟨42489240651618829284629075922232326009747528103, 42489240651618829284629075922233201628475311359⟩
  | 0, 4 => ⟨60716038683371903357503180908105623903079346096, 60716038683371903357503180908106571977237970384⟩
  | 1, 3 => ⟨94038342158472391278098497891888736436751547071, 94038342158472391278098497891890377777634879781⟩
  | 2, 2 => ⟨127502944995664865574335680994557345848612178369, 127502944995664865574335680994560274126576976858⟩
  | 3, 1 => ⟨128098609160335024144808645233644302318677573590, 128098609160335024144808645233649594455161911214⟩
  | 0, 5 => ⟨-106320073240867103975004314109454717038092002976279, 107245746082335636529089293668784614426696544263820⟩
  | 1, 4 => ⟨-204496862429116431088216133969072248358186116475189, 205843295760707979723641788982830142297949767340391⟩
  | 2, 3 => ⟨-394278534990062026037050512128172141854986430412997, 396176084765930380447266792439612489234846955616408⟩
  | 3, 2 => ⟨-761154234268742830769595679573805947135542238340510, 763618286632993942819611531232068033394770491967771⟩
  | 4, 1 => ⟨-1470490663032127848397656210751859695533018201115665, 1473019605996885015406125753872328166099649799731364⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0657Geometry.ds, E8TAxisProd0657Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3389265842976156154813945931020856020710457054 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0657CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0658CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0658CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0658GraphCenterA.qJetBox,
   E8TAxisProd0658GraphCenterB.qJetBox,
   E8TAxisProd0658GraphCenterC.qJetBox,
   E8TAxisProd0658GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0658GraphWholeA.qJetBox,
   E8TAxisProd0658GraphWholeB.qJetBox,
   E8TAxisProd0658GraphWholeC.qJetBox,
   E8TAxisProd0658GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4119609107304881713527546841551815581272821874, 4119609107304881713527546841551849551055654512⟩
  | 0, 2 => ⟨14422314572482206009454393451411717582800905631, 14422314572482206009454393451411825500023815220⟩
  | 1, 1 => ⟨14493852987196869200412604663205602141287567067, 14493852987196869200412604663205784650534121036⟩
  | 0, 3 => ⟨34123743857202533906747754827209627986447039948, 34123743857202533906747754827209957012562459138⟩
  | 1, 2 => ⟨46943935155331127174112799578893680465606864758, 46943935155331127174112799578894238483564052402⟩
  | 2, 1 => ⟨47148413027002063658673713091269536797772188832, 47148413027002063658673713091270515758149361363⟩
  | 0, 4 => ⟨67034371278635660260217636304810000439358066049, 67034371278635660260217636304811057777582922291⟩
  | 1, 3 => ⟨103524367550594012131338831241079191059794480524, 103524367550594012131338831241081029260792484188⟩
  | 2, 2 => ⟨140139917866760258229304653405182276200392283070, 140139917866760258229304653405185564084596200397⟩
  | 3, 1 => ⟨140667666921643827361593667150402591608988284629, 140667666921643827361593667150408545728394233729⟩
  | 0, 5 => ⟨-125441956452582037280972349905390171240825221465029, 126485118401982514600080009345375342170274225003997⟩
  | 1, 4 => ⟨-241655625369172102099917092465937916181872852193125, 243178548245408166347939911513204552689479169959131⟩
  | 2, 3 => ⟨-466566727777119839505458641429580906925144595990105, 468717981040794725737845234761608468500111443505628⟩
  | 3, 2 => ⟨-901873339780027707788344440025345549046521611458580, 904669730565700787852688932520068986512708782725382⟩
  | 4, 1 => ⟨-1744538596505330384889262525583936017790172444951189, 1747405978673387240216803694151019904815072461463533⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0658Geometry.ds, E8TAxisProd0658Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3833710902188187111227644129396523770278030780 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0658CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0659CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0659CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0659GraphCenterA.qJetBox,
   E8TAxisProd0659GraphCenterB.qJetBox,
   E8TAxisProd0659GraphCenterC.qJetBox,
   E8TAxisProd0659GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0659GraphWholeA.qJetBox,
   E8TAxisProd0659GraphWholeB.qJetBox,
   E8TAxisProd0659GraphWholeC.qJetBox,
   E8TAxisProd0659GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3628120080972426237112393159821024846164558210, 3628120080972426237112393159821056087282703236⟩
  | 0, 2 => ⟨12822913967067267087353798708858630126228762625, 12822913967067267087353798708858727832313584909⟩
  | 1, 1 => ⟨12887435763440937000031499464471463517819082918, 12887435763440937000031499464471627792847223280⟩
  | 0, 3 => ⟨30580125226092262620840544710142184870359617757, 30580125226092262620840544710142480817510639938⟩
  | 1, 2 => ⟨42143806034861994764425650859995706456496357059, 42143806034861994764425650859996205868861154335⟩
  | 2, 1 => ⟨42330064257007511207715496714214198661013837577, 42330064257007511207715496714215072221339013688⟩
  | 0, 4 => ⟨60583752739083216563232779601009278593762443982, 60583752739083216563232779601010224440684026108⟩
  | 1, 3 => ⟨93823439277678033439073943769713722098787393594, 93823439277678033439073943769715359515070551285⟩
  | 2, 2 => ⟨127179395954726052305251945835498719575209014385, 127179395954726052305251945835501640744569466762⟩
  | 3, 1 => ⟨127666066092342335663229459731389748239524928751, 127666066092342335663229459731395027342493330884⟩
  | 0, 5 => ⟨-105961954833194635043884760453678996346121828744189, 106885408746690376398124427997469329502065720354230⟩
  | 1, 4 => ⟨-203801590872379237472264151387117479688587488434385, 205144669852148148509637827031385721745722792553393⟩
  | 2, 3 => ⟨-392926261870124765687582824221086180590029169703915, 394818920518977670958139555248360423327740016945359⟩
  | 3, 2 => ⟨-758521234683901916597591539885618727455661441260311, 760978640522693293889288092914466764019240570804995⟩
  | 4, 1 => ⟨-1465360211056429751972215028062675794530425552692517, 1467881517389337583362402040331380605841359240289933⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0659Geometry.ds, E8TAxisProd0659Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3374236556962578135612381562999596702506657012 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0659CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0660CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0660CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0660GraphCenterA.qJetBox,
   E8TAxisProd0660GraphCenterB.qJetBox,
   E8TAxisProd0660GraphCenterC.qJetBox,
   E8TAxisProd0660GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0660GraphWholeA.qJetBox,
   E8TAxisProd0660GraphWholeB.qJetBox,
   E8TAxisProd0660GraphWholeC.qJetBox,
   E8TAxisProd0660GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3205604956052599222267645249180197181385658804, 3205604956052599222267645249180225998369980754⟩
  | 0, 2 => ⟨11422135386977676969185558380028747533388323075, 11422135386977676969185558380028836248004181351⟩
  | 1, 1 => ⟨11493317629415528359762495841803483837209891640, 11493317629415528359762495841803632096183863676⟩
  | 0, 3 => ⟨27439049350735714646021120370782034874554548978, 27439049350735714646021120370782301728599256583⟩
  | 1, 2 => ⟨37896577037177841764576884003334367852689065847, 37896577037177841764576884003334815829718524865⟩
  | 2, 1 => ⟨38104045624264811564509499745606095924841616408, 38104045624264811564509499745606877142379997733⟩
  | 0, 4 => ⟨54796978907355770778099405865773782129858216094, 54796978907355770778099405865774630016412989904⟩
  | 1, 3 => ⟨85116987193226631155209497440372206107337845801, 85116987193226631155209497440373667375928854208⟩
  | 2, 2 => ⟨115568627687758785188390102957091313709065299297, 115568627687758785188390102957093913588446923806⟩
  | 3, 1 => ⟨116117279428011531952774295036283849790297988888, 116117279428011531952774295036288538260401380994⟩
  | 0, 5 => ⟨-89663937349551550257140828943569880327374903758064, 90482916606858636361735673018544119035655884087743⟩
  | 1, 4 => ⟨-172165854540739337701582208736689708270570557493020, 173352181963630451757334281746034963132411396930044⟩
  | 2, 3 => ⟨-331447660514602970655310804000570727775881304657658, 333115173107658052601477225531874210897928581723589⟩
  | 3, 2 => ⟨-638968279540460525344176497067882691337851451711292, 641130906540743796843847098972174528212978357092241⟩
  | 4, 1 => ⟨-1232772497600288623158960629666378581569720674674922, 1234993701361851217741845029577794411936508684602648⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0660Geometry.ds, E8TAxisProd0660Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2979476393658132617302587025765401853259165569 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0660CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0661CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0661CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0661GraphCenterA.qJetBox,
   E8TAxisProd0661GraphCenterB.qJetBox,
   E8TAxisProd0661GraphCenterC.qJetBox,
   E8TAxisProd0661GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0661GraphWholeA.qJetBox,
   E8TAxisProd0661GraphWholeB.qJetBox,
   E8TAxisProd0661GraphWholeC.qJetBox,
   E8TAxisProd0661GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2816293199693064963746188357105129212153726841, 2816293199693064963746188357105155771000070715⟩
  | 0, 2 => ⟨10132447425138554491384799142747013066772654534, 10132447425138554491384799142747093501559860258⟩
  | 1, 1 => ⟨10196518439299027381987147648533098741208003142, 10196518439299027381987147648533232309776349973⟩
  | 0, 3 => ⟨24529241359889098060897801542388878880373016492, 24529241359889098060897801542389119026593327453⟩
  | 1, 2 => ⟨33942946982751288906813450639429042674773244546, 33942946982751288906813450639429443582920197329⟩
  | 2, 1 => ⟨34131496862099473447619270836775523660707108599, 34131496862099473447619270836776220556205901337⟩
  | 0, 4 => ⟨49383529799857557898259110529454030698495303427, 49383529799857557898259110529454788822699521402⟩
  | 1, 3 => ⟨76939760345905401270442031131549040081269396917, 76939760345905401270442031131550340356822365867⟩
  | 2, 2 => ⟨104617613015237545400642512509407836669196993154, 104617613015237545400642512509410143409583055829⟩
  | 3, 1 => ⟨105122326814269621946540157836534426790400725570, 105122326814269621946540157836538577188305455117⟩
  | 0, 5 => ⟨-75776117409242234781279024008035693552631421253428, 76492193776211481199214139637661905438436910434231⟩
  | 1, 4 => ⟨-145238026134234965935889809671621763651171441083960, 146269341484696397906775294651424120871478893422816⟩
  | 2, 3 => ⟨-279169074526285021207626704581504185104655392379368, 280613230943783590804380899492445531552407634323536⟩
  | 3, 2 => ⟨-537398615889593258306444423607431944294611151795915, 539268185156859222672811471335207260104114369358954⟩
  | 4, 1 => ⟨-1035344295826367979187116647644967147689202709723109, 1037266575469386098851467103036794944611486450164603⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0661Geometry.ds, E8TAxisProd0661Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2615892711127822534999714878759658043800611327 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0661CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0662CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0662CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0662GraphCenterA.qJetBox,
   E8TAxisProd0662GraphCenterB.qJetBox,
   E8TAxisProd0662GraphCenterC.qJetBox,
   E8TAxisProd0662GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0662GraphWholeA.qJetBox,
   E8TAxisProd0662GraphWholeB.qJetBox,
   E8TAxisProd0662GraphWholeC.qJetBox,
   E8TAxisProd0662GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3191348705748450939339092585634309274343505269, 3191348705748450939339092585634338036546757685⟩
  | 0, 2 => ⟨11387879353986317745631087852014286962633117929, 11387879353986317745631087852014375484646276394⟩
  | 1, 1 => ⟨11446013354522100945931991312700500559859475201, 11446013354522100945931991312700648486672428702⟩
  | 0, 3 => ⟨27370628577552729827556709287257608602297814057, 27370628577552729827556709287257874856222509445⟩
  | 1, 2 => ⟨37790303766632463247721744794370464209127715367, 37790303766632463247721744794370911150511441954⟩
  | 2, 1 => ⟨37959770373016885047107770414293578257612675433, 37959770373016885047107770414294357632744638186⟩
  | 0, 4 => ⟨54676296755380413572220802536381425749464063533, 54676296755380413572220802536382271635521517658⟩
  | 1, 3 => ⟨84920310415526315333166382849135424382998795550, 84920310415526315333166382849136882137340947651⟩
  | 2, 2 => ⟨115271876134442448572352660119634979726398546671, 115271876134442448572352660119637573251293782668⟩
  | 3, 1 => ⟨115720126537075918170268266003512081923806781880, 115720126537075918170268266003516758758751661114⟩
  | 0, 5 => ⟨-89364886575368149876491391588545745208825193389086, 90181719466662400940982564144771008731763324836605⟩
  | 1, 4 => ⟨-171585904784322033793319219189417089473180652928462, 172768968652059805361863888596885003532654218142599⟩
  | 2, 3 => ⟨-330320742658390782859347248604287092936600281629816, 331983467990618168885879607123702147738067769853506⟩
  | 3, 2 => ⟨-636775916365334208181616981849770403738237055781022, 638931998852467443251006408785505150566732163176304⟩
  | 4, 1 => ⟨-1228503987733063693055516562966677921199544685985407, 1230717615623040665039509433257128121645741951710796⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0662Geometry.ds, E8TAxisProd0662Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2966136404148760240753782335697882891850261914 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0662CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0663CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0663CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0663GraphCenterA.qJetBox,
   E8TAxisProd0663GraphCenterB.qJetBox,
   E8TAxisProd0663GraphCenterC.qJetBox,
   E8TAxisProd0663GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0663GraphWholeA.qJetBox,
   E8TAxisProd0663GraphWholeB.qJetBox,
   E8TAxisProd0663GraphWholeC.qJetBox,
   E8TAxisProd0663GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨2803646787815038042609519970105883106956616677, 2803646787815038042609519970105909615676573197⟩
  | 0, 2 => ⟨10101824425678906822109913464684298387067125366, 10101824425678906822109913464684378647753620897⟩
  | 1, 1 => ⟨10154149817925997006563545518297659373099323817, 10154149817925997006563545518297792642934121075⟩
  | 0, 3 => ⟨24467580678382342725045633008578320001152400549, 24467580678382342725045633008578559607034672500⟩
  | 1, 2 => ⟨33846884661253454041525875540475740056233339759, 33846884661253454041525875540476140035607230931⟩
  | 2, 1 => ⟨34000894786247333911915787340948971837028022007, 34000894786247333911915787340949667084075578750⟩
  | 0, 4 => ⟨49273596185192939727055772425243489863350000365, 49273596185192939727055772425244246191741137759⟩
  | 1, 3 => ⟨76760013986348242692744230092213656715652720897, 76760013986348242692744230092214953846942421708⟩
  | 2, 2 => ⟨104345802891741272391736925081569359531478169620, 104345802891741272391736925081571660596764702954⟩
  | 3, 1 => ⟨104758146612397000834809739606845248895774238577, 104758146612397000834809739606849388917395921686⟩
  | 0, 5 => ⟨-75520918844331441046498029827429156551912659817423, 76235106307144822379555690802926624351451076814623⟩
  | 1, 4 => ⟨-144743719439810641333487212283768395576972273037125, 145772167576221093562973635180121984206333615811384⟩
  | 2, 3 => ⟨-278209609458312933158773355190490987870397974817252, 279649563324146300349648194912534225229666742043966⟩
  | 3, 2 => ⟨-535533911470874447016409976133887946889702161114994, 537397736475561734226418428853089243701920746357774⟩
  | 4, 1 => ⟨-1031717280742609971788242189687913639052979317885916, 1033632910709012542501882154253523292827963098046744⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0663Geometry.ds, E8TAxisProd0663Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2604066249701662746742164988662054674198564602 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0663CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0664CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0664CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0664GraphCenterA.qJetBox,
   E8TAxisProd0664GraphCenterB.qJetBox,
   E8TAxisProd0664GraphCenterC.qJetBox,
   E8TAxisProd0664GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0664GraphWholeA.qJetBox,
   E8TAxisProd0664GraphWholeB.qJetBox,
   E8TAxisProd0664GraphWholeC.qJetBox,
   E8TAxisProd0664GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6738575237439451895479822064579493291847450536, 6738575237439451895479822064579541165704068331⟩
  | 0, 2 => ⟨22755769831321446713965367018192209631575528789, 22755769831321446713965367018192370830857511703⟩
  | 1, 1 => ⟨22838857594432926042460301894603410154240143897, 22838857594432926042460301894603688551099428097⟩
  | 0, 3 => ⟨52143259614543387305281746940507063221844145577, 52143259614543387305281746940507565525357842967⟩
  | 1, 2 => ⟨71248802282442087097815966098459362068701553247, 71248802282442087097815966098460229029287688661⟩
  | 2, 1 => ⟨71476884192445434591790142700773176498697924728, 71476884192445434591790142700774713752393080872⟩
  | 0, 4 => ⟨98924339339336480804928535950649424941635288606, 98924339339336480804928535950651067280227279659⟩
  | 1, 3 => ⟨151206536484720092322868442578315624369464718775, 151206536484720092322868442578318521166125472120⟩
  | 2, 2 => ⟨203620043347464960247018092022876335071001103477, 203620043347464960247018092022881563461885489631⟩
  | 3, 1 => ⟨204180943987761724025687148544064400613305018256, 204180943987761724025687148544073938774034898224⟩
  | 0, 5 => ⟨-240069791026324060465503973145904393548136367681567, 241767997813402397687402441987421225196655242191451⟩
  | 1, 4 => ⟨-465002893406075264561909794361296103416733395776702, 467510335442099822627503135074923837274397317052403⟩
  | 2, 3 => ⟨-902176830155818100238909083323441326440730543576867, 905743784135596494257793678363516782271568112988911⟩
  | 3, 2 => ⟨-1751990192914960107710564367963352630504561500486564, 1756642214984093262977356699076683346361404398948307⟩
  | 4, 1 => ⟨-3404306097878220487791742518483543605663233565736007, 3409066796439015254372444818209101460841194440434118⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0664Geometry.ds, E8TAxisProd0664Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6285500730111869541361667572940295330434479223 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0664CertifiedArithmetic

end


