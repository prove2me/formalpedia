-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0271CertifiedArithmetic__19
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0271CertifiedArithmetic__19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:55:27.414013+00:00
-- url     : https://prove2.me/theorems/bc95a7a3-f7b6-4f97-a7ec-382c83a56001
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0271CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0272CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0271CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0272CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0273CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0274CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0275CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0276CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0277CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0278CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0279CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0280CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0281CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0282CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0283CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0284CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0285CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0286CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0287CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0288CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0289CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0271CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0272CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0273CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0274CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0275CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0276CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0277CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0278CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0279CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0280CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0281CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0282CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0283CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0284CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0285CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0286CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0287CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0288CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0289CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0271CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0272CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0273CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0274CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0275CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0276CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0277CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0278CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0279CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0280CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0281CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0282CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0283CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0284CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0285CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0286CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0287CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0288CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0289CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0271CertifiedArithmetic (+18 modules: GeneralCK/Certificates/E8TAxisProd0272CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0273CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0274CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0275CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0276CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0277CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0278CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0279CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0280CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0281CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0282CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0283CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0284CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0285CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0286CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0287CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0288CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0289CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0265GraphCenterA__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0264GraphCenterB__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0261GraphCenterC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0267GraphCenterD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0268GraphWholeA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0267GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0264GraphWholeC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0268GraphWholeD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0257Geometry__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0272GraphCenterB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0273GraphCenterA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0274GraphCenterC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0274Geometry__6
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0277GraphCenterD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0277GraphWholeC__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0278GraphWholeB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0280Geometry__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0282GraphWholeA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0285GraphWholeC__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0285GraphWholeD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0286GraphCenterA__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0289GraphCenterB__17

-- ===== source module GeneralCK.Certificates.E8TAxisProd0271CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0271CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0271GraphCenterA.qJetBox,
   E8TAxisProd0271GraphCenterB.qJetBox,
   E8TAxisProd0271GraphCenterC.qJetBox,
   E8TAxisProd0271GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0271GraphWholeA.qJetBox,
   E8TAxisProd0271GraphWholeB.qJetBox,
   E8TAxisProd0271GraphWholeC.qJetBox,
   E8TAxisProd0271GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨46656052363892670673801180492529755147492576538, 46656052363892670673801180492529996810056618675⟩
  | 0, 2 => ⟨134300800926787723115369120259353992416235086672, 134300800926787723115369120259354965092902127480⟩
  | 1, 1 => ⟨135252853872566435766850263212025955979894463487, 135252853872566435766850263212027736378167813713⟩
  | 0, 3 => ⟨266304790272769937509289065062358089477962051860, 266304790272769937509289065062361325250273324065⟩
  | 1, 2 => ⟨357023764915115515578696734290721741683891656862, 357023764915115515578696734290727608353777510083⟩
  | 2, 1 => ⟨359250809629107252824555603986484118041975663867, 359250809629107252824555603986494886645804663070⟩
  | 0, 4 => ⟨439105431807899322218134357371328710808527462645, 439105431807899322218134357371340007204853322540⟩
  | 1, 3 => ⟨650028436438638730223538094169902898557980044534, 650028436438638730223538094169923612823976452713⟩
  | 2, 2 => ⟨862004158007467660289928064805774516733406458006, 862004158007467660289928064805812948059257333269⟩
  | 3, 1 => ⟨866744892606667398195542924744529317927539988624, 866744892606667398195542924744601151084372666105⟩
  | 0, 5 => ⟨-2303455319663095392258304429218706613134061150736751, 2315294824258216487780716381985743271655233960793918⟩
  | 1, 4 => ⟨-4519822248488404250272445689248454503658809912340711, 4537680571995821123394721849693825879227646982373398⟩
  | 2, 3 => ⟨-8877047493913249393216020256538860665894609693007755, 8902799468772380255093995948266416587042518743803119⟩
  | 3, 2 => ⟨-17445993046871596930002168730671120556754649323427486, 17479808416984176104822660412325004342922077490671929⟩
  | 4, 1 => ⟨-34304162962038723488222059592686064127072102251049689, 34338742008778892195493213141957095810272303889687988⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0271Geometry.ds, E8TAxisProd0271Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 43918798841282791951279806267391020801396333597 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0271CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0272CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0272CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0272GraphCenterA.qJetBox,
   E8TAxisProd0272GraphCenterB.qJetBox,
   E8TAxisProd0272GraphCenterC.qJetBox,
   E8TAxisProd0272GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0272GraphWholeA.qJetBox,
   E8TAxisProd0272GraphWholeB.qJetBox,
   E8TAxisProd0272GraphWholeC.qJetBox,
   E8TAxisProd0272GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨43097805226014775537540048201828385211585167500, 43097805226014775537540048201828607192901221064⟩
  | 0, 2 => ⟨124161803294018790970125933691793713288853140385, 124161803294018790970125933691794600477534385273⟩
  | 1, 1 => ⟨125773948768033653583227694005992323716389298523, 125773948768033653583227694005993943980357899780⟩
  | 0, 3 => ⟨247416510227270728758696794609715446341816009922, 247416510227270728758696794609718386484381181771⟩
  | 1, 2 => ⟨332523793080807195623490302989696206157036375857, 332523793080807195623490302989701525726337541316⟩
  | 2, 1 => ⟨336320455120064429114387237944448568918692756289, 336320455120064429114387237944458317331127192785⟩
  | 0, 4 => ⟨410030118238662835697754064059142201842088842701, 410030118238662835697754064059152417470803548007⟩
  | 1, 3 => ⟨608243331424347290875734928401157126491020642703, 608243331424347290875734928401175825976918172349⟩
  | 2, 2 => ⟨808262412516601080915899635834433898136828791965, 808262412516601080915899635834468543991322409371⟩
  | 3, 1 => ⟨816379919190936631369003317422656596951445816629, 816379919190936631369003317422721274276319745501⟩
  | 0, 5 => ⟨-2096094267028666652689996581399013265987388537369802, 2107118519480394819908931214190948153017735055506242⟩
  | 1, 4 => ⟨-4111167499929876341120198566167948128761018932949852, 4127809967365968775989840270845573465296708243191053⟩
  | 2, 3 => ⟨-8071057405917186244422307831558071251063473644298236, 8095084253193990532127419463273147080238539463544542⟩
  | 3, 2 => ⟨-15855399578548729625390120801098154607143483498511520, 15887017217569462132527428330895572233404657585178358⟩
  | 4, 1 => ⟨-31163592336293824073610682131729818728783475263874085, 31196127738618608741178125185070786901236332611148883⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0272Geometry.ds, E8TAxisProd0272Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 40555886534005532947677638202375508000942661888 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0272CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0273CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0273CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0273GraphCenterA.qJetBox,
   E8TAxisProd0273GraphCenterB.qJetBox,
   E8TAxisProd0273GraphCenterC.qJetBox,
   E8TAxisProd0273GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0273GraphWholeA.qJetBox,
   E8TAxisProd0273GraphWholeB.qJetBox,
   E8TAxisProd0273GraphWholeC.qJetBox,
   E8TAxisProd0273GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨38788791467992256671671830281807120963576191077, 38788791467992256671671830281807322011998784751⟩
  | 0, 2 => ⟨112720137981748109245554104512808926795245102504, 112720137981748109245554104512809723729109453782⟩
  | 1, 1 => ⟨114200959744353718806795786309283395894487932557, 114200959744353718806795786309284847687112084888⟩
  | 0, 3 => ⟨226410946839146438146803887626206113648766593202, 226410946839146438146803887626208743634180142392⟩
  | 1, 2 => ⟨304599352713082082822202201554602296350835303102, 304599352713082082822202201554607043881536321199⟩
  | 2, 1 => ⟨308114504832295929630085692311822738164319208593, 308114504832295929630085692311831422704868375404⟩
  | 0, 4 => ⟨377817958997695384121059338207479086533670094403, 377817958997695384121059338207488175719734413463⟩
  | 1, 3 => ⟨561341747565359699162646381605141008388400961602, 561341747565359699162646381605157614788768893316⟩
  | 2, 2 => ⟨746550177922505729340963226354369416859103352322, 746550177922505729340963226354400139823377109369⟩
  | 3, 1 => ⟨754105972918137574071538341595471750915373396404, 754105972918137574071538341595529028626304850345⟩
  | 0, 5 => ⟨-1871587344434449556253624276987087081851896711984190, 1881644278905534377203026312334480706150105907164830⟩
  | 1, 4 => ⟨-3668958332236889686233496782621734088620207909863057, 3684144642202697532401073521612725010452512372573109⟩
  | 2, 3 => ⟨-7199331997409155539020800340824716237750326964605054, 7221262513496449376961204026436629376342978235339062⟩
  | 3, 2 => ⟨-14135942371798633532332401892231696146499285501630919, 14164807172144974225106326881908258430623479003064088⟩
  | 4, 1 => ⟨-27770296553119781296885221689764360412851477774492445, 27800000731944868701927659073833041234304093872658684⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0273Geometry.ds, E8TAxisProd0273Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 36482734242101874935149444740690964229583882186 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0273CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0274CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0274CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0274GraphCenterA.qJetBox,
   E8TAxisProd0274GraphCenterB.qJetBox,
   E8TAxisProd0274GraphCenterC.qJetBox,
   E8TAxisProd0274GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0274GraphWholeA.qJetBox,
   E8TAxisProd0274GraphWholeB.qJetBox,
   E8TAxisProd0274GraphWholeC.qJetBox,
   E8TAxisProd0274GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨42942796132633726734092608787407576856660385125, 42942796132633726734092608787407798376790035751⟩
  | 0, 2 => ⟨123852852796423680641763948018462805898538097047, 123852852796423680641763948018463691134531768591⟩
  | 1, 1 => ⟨125358768914019713838073043750085519021564361707, 125358768914019713838073043750087135683270110897⟩
  | 0, 3 => ⟨246904442531954246872916789157918911582317462102, 246904442531954246872916789157921845107956526277⟩
  | 1, 2 => ⟨331764215449381294506308161825940454787154408015, 331764215449381294506308161825945762280090471779⟩
  | 2, 1 => ⟨335311184342062805243616825882847600204578534197, 335311184342062805243616825882857326311947878460⟩
  | 0, 4 => ⟨409278404373480591015780659339827288031338193961, 409278404373480591015780659339837479595665699251⟩
  | 1, 3 => ⟨607081213522607263254881199410861539763507422217, 607081213522607263254881199410880195014966493327⟩
  | 2, 2 => ⟨806571338960757622362884956855981350225406571631, 806571338960757622362884956856015913758369507447⟩
  | 3, 1 => ⟨814155665504132037788780239873355882543078297145, 814155665504132037788780239873420405446682753965⟩
  | 0, 5 => ⟨-2091360944457839036314440865728989111106265395807868, 2102362319323718885531878303333156298088410211599622⟩
  | 1, 4 => ⟨-4101854713427476805076137281011506305642132042596578, 4118461677910112958390783010164603548471044509927282⟩
  | 2, 3 => ⟨-8052715183771622718118730768405155321122761313462907, 8076688179970900742384910795991437396787207914699936⟩
  | 3, 2 => ⟨-15819246637819528462245127595180298794473514319277503, 15850785663342467847828820557431880829757437856598219⟩
  | 4, 1 => ⟨-31092293328277009038084771937368408988249939492995953, 31124722304625505759241192300526411322909017497210976⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0274Geometry.ds, E8TAxisProd0274Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 40409037335435874354017384224103503564503704719 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0274CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0275CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0275CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0275GraphCenterA.qJetBox,
   E8TAxisProd0275GraphCenterB.qJetBox,
   E8TAxisProd0275GraphCenterC.qJetBox,
   E8TAxisProd0275GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0275GraphWholeA.qJetBox,
   E8TAxisProd0275GraphWholeB.qJetBox,
   E8TAxisProd0275GraphWholeC.qJetBox,
   E8TAxisProd0275GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨38648068056136345699294269389953512149428293701, 38648068056136345699294269389953712780817547516⟩
  | 0, 2 => ⟨112437419287141470313047473957736491038542780156, 112437419287141470313047473957737286216223857739⟩
  | 1, 1 => ⟨113820648820901371342662092498281522199457749062, 113820648820901371342662092498282970758204643621⟩
  | 0, 3 => ⟨225939109541050942766256383173710101167161594583, 225939109541050942766256383173712725231902683781⟩
  | 1, 2 => ⟨303898349354483269579718908205410858963152031671, 303898349354483269579718908205415595708170115801⟩
  | 2, 1 => ⟨307182298757734095744267831721774120061032585866, 307182298757734095744267831721782784709332606980⟩
  | 0, 4 => ⟨377121913006890316359053236035682951701096720195, 377121913006890316359053236035692019523556187922⟩
  | 1, 3 => ⟨560263937229659885426441567875822115063098908624, 560263937229659885426441567875838682263073420602⟩
  | 2, 2 => ⟨744980012598955412694948481637099799200367105333, 744980012598955412694948481637130449309626718286⟩
  | 3, 1 => ⟨752039517429798179405099018441242731615603750802, 752039517429798179405099018441299872824552090659⟩
  | 0, 5 => ⟨-1867249207317844038210457097992543583151406612067652, 1877284527186510321170310610124671409383405276501080⟩
  | 1, 4 => ⟨-3660425961168350435134549970565409364526399984055785, 3675578737294560669475458999179015941141488027191944⟩
  | 2, 3 => ⟨-7182532583271548564290973498423043908569000476923292, 7204412362237823847833466718784935873014463511069689⟩
  | 3, 2 => ⟨-14102841710906703440462947931367818524258693338247593, 14131632929472101170691008237645902994861322367518705⟩
  | 4, 1 => ⟨-27705039729065415365328578179756326509861439046241511, 27734645803667641294529927615495975903925979835821664⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0275Geometry.ds, E8TAxisProd0275Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 36349486328574936828650495701735393103420204041 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0275CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0276CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0276CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0276GraphCenterA.qJetBox,
   E8TAxisProd0276GraphCenterB.qJetBox,
   E8TAxisProd0276GraphCenterC.qJetBox,
   E8TAxisProd0276GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0276GraphWholeA.qJetBox,
   E8TAxisProd0276GraphWholeB.qJetBox,
   E8TAxisProd0276GraphWholeC.qJetBox,
   E8TAxisProd0276GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨34877940946673764124631501979358361541058297463, 34877940946673764124631501979358543721894239977⟩
  | 0, 2 => ⟨102243116592219580107650544344322815326426340349, 102243116592219580107650544344323531274671525310⟩
  | 1, 1 => ⟨103602377132652300215017518282556388354540355693, 103602377132652300215017518282557689209537588792⟩
  | 0, 3 => ⟨207029869337156883822995160992736723904693766732, 207029869337156883822995160992739076597170844418⟩
  | 1, 2 => ⟨278813019917486311776102395679519664065002493295, 278813019917486311776102395679523900997746452027⟩
  | 2, 1 => ⟨282066147188684708489617925287881477176625557554, 282066147188684708489617925287889213497480397641⟩
  | 0, 4 => ⟨347945741776072018929755026722515135175567315616, 347945741776072018929755026722523223340911593817⟩
  | 1, 3 => ⟨517796797956554526111861085566821183277270004112, 517796797956554526111861085566835932260735543494⟩
  | 2, 2 => ⟨689219560147723467395557386221462824417397976113, 689219560147723467395557386221490070489393260123⟩
  | 3, 1 => ⟨696252216620922638034801653214372152222432595711, 696252216620922638034801653214422879327671971723⟩
  | 0, 5 => ⟨-1665651699077231253352537442370852871989524869251383, 1674776324014554850675482918071365358792669987285862⟩
  | 1, 4 => ⟨-3263499241212769552524875677144648340627016628625813, 3277277311212525899048891390274364603737915060223265⟩
  | 2, 3 => ⟨-6400394037284369588510943615657553334922009128471272, 6420291071197984668406252844486389848330927756108637⟩
  | 3, 2 => ⟨-12560743875132133984471926009869401845830537846232795, 12586930772863851000937955173407004505642684239450466⟩
  | 4, 1 => ⟨-24663071597166239907199108603148524002350249708819635, 24690008976785058943291333222926702246603319833374168⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0276Geometry.ds, E8TAxisProd0276Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 32787923606828684497346779181829298102069319942 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0276CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0277CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0277CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0277GraphCenterA.qJetBox,
   E8TAxisProd0277GraphCenterB.qJetBox,
   E8TAxisProd0277GraphCenterC.qJetBox,
   E8TAxisProd0277GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0277GraphWholeA.qJetBox,
   E8TAxisProd0277GraphWholeB.qJetBox,
   E8TAxisProd0277GraphWholeC.qJetBox,
   E8TAxisProd0277GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨31331595614724525388148075782598463774882139654, 31331595614724525388148075782598628945023442801⟩
  | 0, 2 => ⟨92656663686609880863654665410350235504028151199, 92656663686609880863654665410350879180373920598⟩
  | 1, 1 => ⟨93903449568785368426239945047531065237640255481, 93903449568785368426239945047532231664379265880⟩
  | 0, 3 => ⟨189156898747843796126713592009653605511521854268, 189156898747843796126713592009655713727780513460⟩
  | 1, 2 => ⟨255012860085262563495555303314832753446010052941, 255012860085262563495555303314836541272575797176⟩
  | 2, 1 => ⟨258022110284201010948555212480989374185488452921, 258022110284201010948555212480996278213275271266⟩
  | 0, 4 => ⟨320249505948674905914407926758493379336723379232, 320249505948674905914407926758500599071161390177⟩
  | 1, 3 => ⟨477374745577854015732856335210341631259440194435, 477374745577854015732856335210354772497422255341⟩
  | 2, 2 => ⟨635966452663864404921910579589528376532002467596, 635966452663864404921910579589552618660278654464⟩
  | 3, 1 => ⟨642511849873195992576569162894644016836895404218, 642511849873195992576569162894689093540544144962⟩
  | 0, 5 => ⟨-1476759660475237184705592260150730482736262553444455, 1484991648729380618882342002124984182102872971583453⟩
  | 1, 4 => ⟨-2891742014557921170527402534333239309980289708709752, 2904168080544124761217188006825364028770841051799063⟩
  | 2, 3 => ⟨-5668156349727309356658441442326912905221285475016384, 5686096615708940284352021466831868704417662353124868⟩
  | 3, 2 => ⟨-11117641074116920676649785763035651065885310406373897, 11141246204019765894673789168390005885854168693194895⟩
  | 4, 1 => ⟨-21817602442940722968856649897324365495859156094562595, 21841865800256178618347078064674629797107356299504522⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0277Geometry.ds, E8TAxisProd0277Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 29439325893330163131505207891902025195457803809 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0277CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0278CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0278CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0278GraphCenterA.qJetBox,
   E8TAxisProd0278GraphCenterB.qJetBox,
   E8TAxisProd0278GraphCenterC.qJetBox,
   E8TAxisProd0278GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0278GraphWholeA.qJetBox,
   E8TAxisProd0278GraphWholeB.qJetBox,
   E8TAxisProd0278GraphWholeC.qJetBox,
   E8TAxisProd0278GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨34750298679807782355009258746321522743204827515, 34750298679807782355009258746321704546800574269⟩
  | 0, 2 => ⟨101984600920298260828884353639219566204726337760, 101984600920298260828884353639220280573369213331⟩
  | 1, 1 => ⟨103254265126128871550837301739170523937086674489, 103254265126128871550837301739171821888879066710⟩
  | 0, 3 => ⟨206595339968882672884527029632340409813448455169, 206595339968882672884527029632342757199914842634⟩
  | 1, 2 => ⟨278166398729644584297212301178475381020868958320, 278166398729644584297212301178479608304697270595⟩
  | 2, 1 => ⟨281205534058562479209657486800884458286726493538, 281205534058562479209657486800892176835897848814⟩
  | 0, 4 => ⟨347301428489983485901751440137221782988392026677, 347301428489983485901751440137229852091474408853⟩
  | 1, 3 => ⟨516797391613328398357841222296394780804786076477, 516797391613328398357841222296409494863268905171⟩
  | 2, 2 => ⟨687761886249415888469400591530159254948460476846, 687761886249415888469400591530186436183343987960⟩
  | 3, 1 => ⟨694332608676064364963483303725397882105606239116, 694332608676064364963483303725448487850248243911⟩
  | 0, 5 => ⟨-1661674772681422410022666892061018384329376362940046, 1670779193070935636039605257908744954276580567282939⟩
  | 1, 4 => ⟨-3255679707339731649700842014270794620726309535007649, 3269426503048722030858588824999190735308742480665204⟩
  | 2, 3 => ⟨-6385002887263243123025404608422270579733864354367496, 6404852850710558467363225575035663820651889215218778⟩
  | 3, 2 => ⟨-12530427455661677626875634363899950441931466393167537, 12556546820728939860317442904694482345083741095530608⟩
  | 4, 1 => ⟨-24603322715659848566665222944427450949930638999375433, 24630172126789409649350028504834276596566862953958118⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0278Geometry.ds, E8TAxisProd0278Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 32667125107416373339178340314133838394563359416 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0278CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0279CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0279CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0279GraphCenterA.qJetBox,
   E8TAxisProd0279GraphCenterB.qJetBox,
   E8TAxisProd0279GraphCenterC.qJetBox,
   E8TAxisProd0279GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0279GraphWholeA.qJetBox,
   E8TAxisProd0279GraphWholeB.qJetBox,
   E8TAxisProd0279GraphWholeC.qJetBox,
   E8TAxisProd0279GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨31215922459744070964240527997449800737905309751, 31215922459744070964240527997449965566679217413⟩
  | 0, 2 => ⟨92420467602763603800973810642805253710361206081, 92420467602763603800973810642805895973611193831⟩
  | 1, 1 => ⟨93585056201317914874860695522675780131507580479, 93585056201317914874860695522676943967506764506⟩
  | 0, 3 => ⟨188756959624096987950393785880682140145544116085, 188756959624096987950393785880684243677878747402⟩
  | 1, 2 => ⟨254416720883422146196286239690904767267213574109, 254416720883422146196286239690908546600084139635⟩
  | 2, 1 => ⟨257227998109111762549336633342998806523222639329, 257227998109111762549336633343005694941311460843⟩
  | 0, 4 => ⟨319653260014444218891955439835860215274936113895, 319653260014444218891955439835867418462219247157⟩
  | 1, 3 => ⟨476448245890707259520045054005745833104679135186, 476448245890707259520045054005758944113862818113⟩
  | 2, 2 => ⟨634613434939836696243462114071724960905432696679, 634613434939836696243462114071749147033334110520⟩
  | 3, 1 => ⟨640728897001141742852525544488518443325603687280, 640728897001141742852525544488563415389125082760⟩
  | 0, 5 => ⟨-1473128815875891508542441007629301588144845037522266, 1481342071830105253788336801166897270019436972591454⟩
  | 1, 4 => ⟨-2884605384511311474205831860219713527676882406722835, 2897002557505998392522096514699051224001309118491828⟩
  | 2, 3 => ⟨-5654114124373884667106109525175032354356337479188857, 5672011205337252025976795503920328733518977671252889⟩
  | 3, 2 => ⟨-11089991106033038089030008646981112093658343688102991, 11113535110768621177206514595766658554661150970288324⟩
  | 4, 1 => ⟨-21763127451825328983547404354911284462169160683387707, 21787313492313877576367702082860068741193801579339124⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0279Geometry.ds, E8TAxisProd0279Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 29329912483872627894250763189719422852091547718 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0279CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0280CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0280CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0280GraphCenterA.qJetBox,
   E8TAxisProd0280GraphCenterB.qJetBox,
   E8TAxisProd0280GraphCenterC.qJetBox,
   E8TAxisProd0280GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0280GraphWholeA.qJetBox,
   E8TAxisProd0280GraphWholeB.qJetBox,
   E8TAxisProd0280GraphWholeC.qJetBox,
   E8TAxisProd0280GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨42788172827566380817512793818885095722534038828, 42788172827566380817512793818885316782429891343⟩
  | 0, 2 => ⟨123544541796499421632513435829719014164199302583, 123544541796499421632513435829719897451711901411⟩
  | 1, 1 => ⟨124944537624663148845847840634872540237659106213, 124944537624663148845847840634874153304892067931⟩
  | 0, 3 => ⟨246393313691480190324766103099385231909616694571, 246393313691480190324766103099388158832998346611⟩
  | 1, 2 => ⟨331006089211014470851916889565012854120079660738, 331006089211014470851916889565018149563488282337⟩
  | 2, 1 => ⟨334304025507039094054496096113832840625362041337, 334304025507039094054496096113842544477336508437⟩
  | 0, 4 => ⟨408527950164797064499055858928612840934427253404, 408527950164797064499055858928623008489871129807⟩
  | 1, 3 => ⟨605921101987924174187895953179157796927071036425, 605921101987924174187895953179176408046185786856⟩
  | 2, 2 => ⟨804883302901437974644130701086027971863173525743, 804883302901437974644130701086062453264679164851⟩
  | 3, 1 => ⟨811935766944253954576575920735306316957740034327, 811935766944253954576575920735370685796833737427⟩
  | 0, 5 => ⟨-2086635692484749552970667261594887819249324254974900, 2097614224410247188649089432764895846372359060362744⟩
  | 1, 4 => ⟨-4092557814932873989498668524069823922408734436856951, 4109129332109128854612602978396586815214091823302352⟩
  | 2, 3 => ⟨-8034404282279056121154265944342365274896907270513198, 8058323518296740984914011913292334732574897979393055⟩
  | 3, 2 => ⟨-15783155497924131512052839967246320065664605886300340, 15814616062361941110693195361806853809263647826563676⟩
  | 4, 1 => ⟨-31021116346712963912916700519617739613835164885586270, 31053439161366774748026605669426027281965619085425918⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0280Geometry.ds, E8TAxisProd0280Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 40262555549379112450389217019998948856536502774 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0280CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0281CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0281CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0281GraphCenterA.qJetBox,
   E8TAxisProd0281GraphCenterB.qJetBox,
   E8TAxisProd0281GraphCenterC.qJetBox,
   E8TAxisProd0281GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0281GraphWholeA.qJetBox,
   E8TAxisProd0281GraphWholeB.qJetBox,
   E8TAxisProd0281GraphWholeC.qJetBox,
   E8TAxisProd0281GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨38507697674252286148964491026483437038098739672, 38507697674252286148964491026483637253315043128⟩
  | 0, 2 => ⟨112155289845676170238473634275891902082073189263, 112155289845676170238473634275892695507356981900⟩
  | 1, 1 => ⟨113441213310093745499334899033244567695463760675, 113441213310093745499334899033246013027335550730⟩
  | 0, 3 => ⟨225468141569379301024491365266286857693249210479, 225468141569379301024491365266289475850437855610⟩
  | 1, 2 => ⟨303198692093047014522556944314618902648404288824, 303198692093047014522556944314623628631705397620⟩
  | 2, 1 => ⟨306252053623733233493298765104224135448288742103, 306252053623733233493298765104232780248640348634⟩
  | 0, 4 => ⟨376427036415956579735714669270349226704704338842, 376427036415956579735714669270358273212686173255⟩
  | 1, 3 => ⟨559187991600315553853053447343499643324843378567, 559187991600315553853053447343516171414623322621⟩
  | 2, 2 => ⟨743412672232392193529615155858757348923232945407, 743412672232392193529615155858787926345169162568⟩
  | 3, 1 => ⟨749977114017829454693192890137592318013152244564, 749977114017829454693192890137649323034486819477⟩
  | 0, 5 => ⟨-1862918733037181249922156769837508892951500110488484, 1872932476498095333072701928537588088258174494348968⟩
  | 1, 4 => ⟨-3651908674398149110359662266482562505920654527773957, 3667027979785777346916464890458864098744944355896745⟩
  | 2, 3 => ⟨-7165762902488285924400302663972368410928762937109573, 7187592050323425581009376030542582577951488956205536⟩
  | 3, 2 => ⟨-14069799711884025470874147921414568964906462738219158, 14098517530798166485886717302834578198389162103827507⟩
  | 4, 1 => ⟨-27639898718222142579750560491414214271165926754483019, 27669407010064898038881527889977168229340271832395367⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0281Geometry.ds, E8TAxisProd0281Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 36216574469630016954669497113698145187209359168 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0281CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0282CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0282CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0282GraphCenterA.qJetBox,
   E8TAxisProd0282GraphCenterB.qJetBox,
   E8TAxisProd0282GraphCenterC.qJetBox,
   E8TAxisProd0282GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0282GraphWholeA.qJetBox,
   E8TAxisProd0282GraphWholeB.qJetBox,
   E8TAxisProd0282GraphWholeC.qJetBox,
   E8TAxisProd0282GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨42633934512173719683991865493166709788200535361, 42633934512173719683991865493166930388813211633⟩
  | 0, 2 => ⟨123236869121661058374171206956045391057777280886, 123236869121661058374171206956046272401006290874⟩
  | 1, 1 => ⟨124531253087289262619965898749336544836410650151, 124531253087289262619965898749338154316944212712⟩
  | 0, 3 => ⟨245883122132499817895744308537349891301418066698, 245883122132499817895744308537352811637178628493⟩
  | 1, 2 => ⟨330249411859779019132135283678602386415558822127, 330249411859779019132135283678607669836218526367⟩
  | 2, 1 => ⟨333298974821310368272190677181369376059684867715, 333298974821310368272190677181379057705825442881⟩
  | 0, 4 => ⟨407778753658050609389108440809843740151581462430, 407778753658050609389108440809853883753518529973⟩
  | 1, 3 => ⟨604762993571317791804595726881417476832688105646, 604762993571317791804595726881436043921319926766⟩
  | 2, 2 => ⟨803198299239604244922120413600514089173218679687, 803198299239604244922120413600548488632907948671⟩
  | 3, 1 => ⟨809720215860348744905436276525673541641321099093, 809720215860348744905436276525737756771852707676⟩
  | 0, 5 => ⟨-2081918503015079476855117141201144679660067029999247, 2092874226674996104347012133682701485991694273401968⟩
  | 1, 4 => ⟨-4083276788632077498397012026228582081044463793680663, 4099812914225820944771829582516733441158274672070291⟩
  | 2, 3 => ⟨-8016124670440252050439326056628890689828713810115857, 8039990237337860662634477207280173276948184822202387⟩
  | 3, 2 => ⟨-15747126097984964216564812402415613877767224800672477, 15778508354093855545042557918650044091855845071444182⟩
  | 4, 1 => ⟨-30950061271910635957360903303571834136390249687236853, 30982278189830610550789303711623733474335490955909585⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0282Geometry.ds, E8TAxisProd0282Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 40116440411703930824915576617947647996974815366 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0282CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0283CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0283CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0283GraphCenterA.qJetBox,
   E8TAxisProd0283GraphCenterB.qJetBox,
   E8TAxisProd0283GraphCenterC.qJetBox,
   E8TAxisProd0283GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0283GraphWholeA.qJetBox,
   E8TAxisProd0283GraphWholeB.qJetBox,
   E8TAxisProd0283GraphWholeC.qJetBox,
   E8TAxisProd0283GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨38367679586452432099913044525127064448901354565, 38367679586452432099913044525127264248803308562⟩
  | 0, 2 => ⟨111873748571607298685752003263795479220705147529, 111873748571607298685752003263796270897369530232⟩
  | 1, 1 => ⟨113062651530765401227865473933658236399371793483, 113062651530765401227865473933659678511355642268⟩
  | 0, 3 => ⟨224998041463519546781153426179234843205719417548, 224998041463519546781153426179237455468446703563⟩
  | 1, 2 => ⟨302500378599782997128119356623872521666145082805, 302500378599782997128119356623877236911642408522⟩
  | 2, 1 => ⟨305323765902067650313402005972356334625879570788, 305323765902067650313402005972364959622486139056⟩
  | 0, 4 => ⟨375733327404717764344779977880858199826425540924, 375733327404717764344779977880867225068945062240⟩
  | 1, 3 => ⟨558113907649882461596282977709287173470319102199, 558113907649882461596282977709303662539898275856⟩
  | 2, 2 => ⟨741848152071193350663758488880993620586454970469, 741848152071193350663758488881024125488378129433⟩
  | 3, 1 => ⟨747918755554328130086360353916574197822335080342, 747918755554328130086360353916631066969713605234⟩
  | 0, 5 => ⟨-1858595913515030318078557898374865788022272181552636, 1868588118783514979047962005123211666101564019501032⟩
  | 1, 4 => ⟨-3643406456129791201529183290622904105123805068187970, 3658492353938127051588733328641845196930936417389650⟩
  | 2, 3 => ⟨-7149022924069286081698327364412731611382152314045612, 7170801546890811827780485079428889190548625398942080⟩
  | 3, 2 => ⟨-14036816313827372376132524800559362682491125781799325, 14065460915486721394217230477809037987036339095479950⟩
  | 4, 1 => ⟨-27574873400769240017202038370235523819961287332399135, 27604284231841788662100322918447369516232397976566448⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0283Geometry.ds, E8TAxisProd0283Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 36083997961425725795375777455820233392085527183 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0283CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0284CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0284CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0284GraphCenterA.qJetBox,
   E8TAxisProd0284GraphCenterB.qJetBox,
   E8TAxisProd0284GraphCenterC.qJetBox,
   E8TAxisProd0284GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0284GraphWholeA.qJetBox,
   E8TAxisProd0284GraphWholeB.qJetBox,
   E8TAxisProd0284GraphWholeC.qJetBox,
   E8TAxisProd0284GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨34622979218265282303433242344546192302645924174, 34622979218265282303433242344546373729778812899⟩
  | 0, 2 => ⟨101726627907000274324442159376999989552668894178, 101726627907000274324442159377000702345117489164⟩
  | 1, 1 => ⟨102906960615755454246527364222715514653085139848, 102906960615755454246527364222716809707967253346⟩
  | 0, 3 => ⟨206161615313716948310836383283038887711922898536, 206161615313716948310836383283041229804151450137⟩
  | 1, 2 => ⟨277521025716483251735969080807592651179779758677, 277521025716483251735969080807596868836168616219⟩
  | 2, 1 => ⟨280346741378480292521474145017165578568075894418, 280346741378480292521474145017173279385223258648⟩
  | 0, 4 => ⟨346658200519917939243810390585252048309826339867, 346658200519917939243810390585260098394562073568⟩
  | 1, 3 => ⟨515799717997617342228088980014625294537887978471, 515799717997617342228088980014639973751918729417⟩
  | 2, 2 => ⟨686306839345444652422572158792249351139349985794, 686306839345444652422572158792276467686707543785⟩
  | 3, 1 => ⟨692416770625119238106357015286126000225560537406, 692416770625119238106357015286176484889828876457⟩
  | 0, 5 => ⟨-1657705160227899040488290696789799114324080500909396, 1666789415362455975875236532653547219929751742023861⟩
  | 1, 4 => ⟨-3247874571371985258097507547118299807839202178706439, 3261590158384070485054841547689244527012301510853797⟩
  | 2, 3 => ⟨-6369640117308626975907294155832548916056293942234444, 6389443121368095892136491393628815436807614912595871⟩
  | 3, 2 => ⟨-12500167026137925393757112125173733596288941290344608, 12526219050261386333055353191852322358652120195367197⟩
  | 4, 1 => ⟨-24543684366589428875615235683005657258404064527343421, 24570446147464382888311801050193519345956807130948799⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0284Geometry.ds, E8TAxisProd0284Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 32546633736037181162890158025724160004742593585 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0284CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0285CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0285CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0285GraphCenterA.qJetBox,
   E8TAxisProd0285GraphCenterB.qJetBox,
   E8TAxisProd0285GraphCenterC.qJetBox,
   E8TAxisProd0285GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0285GraphWholeA.qJetBox,
   E8TAxisProd0285GraphWholeB.qJetBox,
   E8TAxisProd0285GraphWholeC.qJetBox,
   E8TAxisProd0285GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨31100544237609992442797370237776907014948084729, 31100544237609992442797370237777071503057116698⟩
  | 0, 2 => ⟨92184770977267221754720037511701256954462318958, 92184770977267221754720037511701897807649116663⟩
  | 1, 1 => ⟨93267407284444278762793999514039496004880802588, 93267407284444278762793999514040657255727838716⟩
  | 0, 3 => ⟨188357765178215838776229809527360124509707115928, 188357765178215838776229809527362223368364134253⟩
  | 1, 2 => ⟨253821738799773498246642249909693849626312433429, 253821738799773498246642249909697620484113292424⟩
  | 2, 1 => ⟨256435575679058480345273200177614050965683449702, 256435575679058480345273200177620923808371826877⟩
  | 0, 4 => ⟨319058021100719448731993668125373288690547246371, 319058021100719448731993668125380475367869370595⟩
  | 1, 3 => ⟨475523356033206011782298060129678690938655222527, 475523356033206011782298060129691771786956655589⟩
  | 2, 2 => ⟨633262859919081069651831206996032832387220981568, 633262859919081069651831206996056962640495627344⟩
  | 3, 1 => ⟨638949451410376967355105643334988499078859471301, 638949451410376967355105643335033366737202610915⟩
  | 0, 5 => ⟨-1469504925075867271060453706604175217634066979448458, 1477699488440508155929646427960501136819881636914083⟩
  | 1, 4 => ⟨-2877482443151904694863815811840792846951186080140064, 2889850789880202324428271310351863855043280632175456⟩
  | 2, 3 => ⟨-5640098879699645158362165188578882164418676920460473, 5657952889120238531691329659887391087792892966666845⟩
  | 3, 2 => ⟨-11062394363121522617518902987296402575962785552584181, 11085877438728858166369246624891618632259456532841301⟩
  | 4, 1 => ⟨-21708757525677683109064389073538697744186673304520136, 21732866594088202423188439089872141119601113874784500⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0285Geometry.ds, E8TAxisProd0285Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 29220779537662755701998813475647581829956750184 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0285CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0286CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0286CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0286GraphCenterA.qJetBox,
   E8TAxisProd0286GraphCenterB.qJetBox,
   E8TAxisProd0286GraphCenterC.qJetBox,
   E8TAxisProd0286GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0286GraphWholeA.qJetBox,
   E8TAxisProd0286GraphWholeB.qJetBox,
   E8TAxisProd0286GraphWholeC.qJetBox,
   E8TAxisProd0286GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨34495981884351313764902396350762473001856516674, 34495981884351313764902396350762654053302271244⟩
  | 0, 2 => ⟨101469196547281696758097955904209943016005042982, 101469196547281696758097955904210654235660083244⟩
  | 1, 1 => ⟨102560462042666656603543683412440412080541100087, 102560462042666656603543683412441704244794019929⟩
  | 0, 3 => ⟨205728694016073849448130554457052086355925422053, 205728694016073849448130554457054423165663019844⟩
  | 1, 2 => ⟨276876898713855681995758986577047979729184446311, 276876898713855681995758986577052187779562723851⟩
  | 2, 1 => ⟨279489765867462060162794771155601115577318621465, 279489765867462060162794771155608798702014254552⟩
  | 0, 4 => ⟨346016056171599584966538005603267128386704480800, 346016056171599584966538005603275159496908692228⟩
  | 1, 3 => ⟨514803774289708938630926315486559710283939581868, 514803774289708938630926315486574354733865620338⟩
  | 2, 2 => ⟨684854415010044244942882200149845446817016592051, 684854415010044244942882200149872498826094281152⟩
  | 3, 1 => ⟨690504695830771698604737373314920096349918754751, 690504695830771698604737373314970460213401966828⟩
  | 0, 5 => ⟨-1653742853534878345615466320405092334259100983659614, 1662806982710586205024717195845755131261520888569470⟩
  | 1, 4 => ⟨-3240083817289582386864098270756785945045103697065602, 3253768261221228192482337566488378776779002874498939⟩
  | 2, 3 => ⟨-6354305695960392834796538881280456868054847925034598, 6374061851766363287198325423782589049329476140489211⟩
  | 3, 2 => ⟨-12469962524678550027845765400518252435471465802615184, 12495947399702181493999881592276184359652189019559794⟩
  | 4, 1 => ⟨-24484156428106998921575365055674167301455827993949754, 24510830917202794564271836658435890863775622488429655⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0286Geometry.ds, E8TAxisProd0286Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 32426448844762841584493546053955242254583372289 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0286CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0287CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0287CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0287GraphCenterA.qJetBox,
   E8TAxisProd0287GraphCenterB.qJetBox,
   E8TAxisProd0287GraphCenterC.qJetBox,
   E8TAxisProd0287GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0287GraphWholeA.qJetBox,
   E8TAxisProd0287GraphWholeB.qJetBox,
   E8TAxisProd0287GraphWholeC.qJetBox,
   E8TAxisProd0287GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨30985460324580804359773627623534251103284754762, 30985460324580804359773627623534415251429974238⟩
  | 0, 2 => ⟨91949572880059726782176153729081548909658945560, 91949572880059726782176153729082188355808675305⟩
  | 1, 1 => ⟨92950501373023715958412296341863317630595760583, 92950501373023715958412296341864476301866418426⟩
  | 0, 3 => ⟨187959314152410135387202391380177140536312901437, 187959314152410135387202391380179234731516340786⟩
  | 1, 2 => ⟨253227911823670549071761666636446497351638940484, 253227911823670549071761666636450259752954961894⟩
  | 2, 1 => ⟨255644839943237847558598975685453925818377623194, 255644839943237847558598975685460783119888508693⟩
  | 0, 4 => ⟨318463787631197642043095818288912359344218003446, 318463787631197642043095818288919529548689564029⟩
  | 1, 3 => ⟨474600073380434089828107472584633936132349455220, 474600073380434089828107472584646986887532879423⟩
  | 2, 2 => ⟨631914723481453515236350393479468545851501668180, 631914723481453515236350393479492620355617161649⟩
  | 3, 1 => ⟨637173506923670858932377157243897412477680052801, 637173506923670858932377157243942175965271622980⟩
  | 0, 5 => ⟨-1465887979792418396310609444611131787446746108722355, 1474063890265352771429944804295020998797249983643634⟩
  | 1, 4 => ⟨-2870373174244569456611621986354085713394699760975474, 2882712761422111703683703088944691571434264220650776⟩
  | 2, 3 => ⟨-5626110583793594756599028550315134179199833608401052, 5643921635138603313018052081825530451626039383485394⟩
  | 3, 2 => ⟨-11034850782564161153985021429734852843284952218241739, 11058273125077960007165378968312877578673169158228481⟩
  | 4, 1 => ⟨-21654492540718131929005841031986005141191583947119652, 21678524981788260988270797134718902849213515742498396⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0287Geometry.ds, E8TAxisProd0287Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 29111926458606157337985384437671443089443212378 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0287CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0288CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0288CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0288GraphCenterA.qJetBox,
   E8TAxisProd0288GraphCenterB.qJetBox,
   E8TAxisProd0288GraphCenterC.qJetBox,
   E8TAxisProd0288GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0288GraphWholeA.qJetBox,
   E8TAxisProd0288GraphWholeB.qJetBox,
   E8TAxisProd0288GraphWholeC.qJetBox,
   E8TAxisProd0288GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨28118687157616895229029464242937356701859905373, 28118687157616895229029464242937506531172172538⟩
  | 0, 2 => ⟨83891972220171438531493576864955366530233761023, 83891972220171438531493576864955945405121608253⟩
  | 1, 1 => ⟨85034740439049579554618997715339118531911429861, 85034740439049579554618997715340164632167810047⟩
  | 0, 3 => ⟨172683761694849583806320311278710108750711124659, 172683761694849583806320311278711998721236132211⟩
  | 1, 2 => ⟨233057483694307942344966592565186096435682599492, 233057483694307942344966592565189484049217130654⟩
  | 2, 1 => ⟨235839761049533259147795778088645979152434165133, 235839761049533259147795778088652142655313340039⟩
  | 0, 4 => ⟨294576611752331138937636040293199394919987590642, 294576611752331138937636040293205844146305675186⟩
  | 1, 3 => ⟨439858059588916782573636327608060090543199866277, 439858059588916782573636327608071807452129159959⟩
  | 2, 2 => ⟨586507878238567625263434909937004446221956428474, 586507878238567625263434909937026030497047590194⟩
  | 3, 1 => ⟨592599370356224821048828589338068855157072549686, 592599370356224821048828589338108938406596232360⟩
  | 0, 5 => ⟨-1304525620323683362994238204883283339669647017862158, 1311912998786139507947651901729695431396731523579792⟩
  | 1, 4 => ⟨-2552921263106112921064800728103044919776854887078200, 2564063557540368036678739916989829380352822817609142⟩
  | 2, 3 => ⟨-5001095218081740396623523239979430522266246507806969, 5017172740213751802732412124847822786340045590857370⟩
  | 3, 2 => ⟨-9803594119550912575034193002570984744502678017282225, 9824737644766290989013104197361603170781941367854106⟩
  | 4, 1 => ⟨-19227814440250889837792265079425250196685426169458923, 19249526006619579599719809738338610672009302539355299⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0288Geometry.ds, E8TAxisProd0288Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 26407216550612720092221893763952862522934024077 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0288CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0289CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0289CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0289GraphCenterA.qJetBox,
   E8TAxisProd0289GraphCenterB.qJetBox,
   E8TAxisProd0289GraphCenterC.qJetBox,
   E8TAxisProd0289GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0289GraphWholeA.qJetBox,
   E8TAxisProd0289GraphWholeB.qJetBox,
   E8TAxisProd0289GraphWholeC.qJetBox,
   E8TAxisProd0289GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨25210552702701439338755347287972541129838798808, 25210552702701439338755347287972677120320817838⟩
  | 0, 2 => ⟨75885137933872310421617692702820201982632820548, 75885137933872310421617692702820722662171004804⟩
  | 1, 1 => ⟨76931759009660449780864232825433642353046694363, 76931759009660449780864232825434580571936642206⟩
  | 0, 3 => ⟨157509726358171940160325421645081927029375985407, 157509726358171940160325421645083621362155254069⟩
  | 1, 2 => ⟨212815310949112363130333612215291435959858158327, 212815310949112363130333612215294465386796219165⟩
  | 2, 1 => ⟨215386363995110554337080107468945509238827142608, 215386363995110554337080107468951010909365197202⟩
  | 0, 4 => ⟨270785034852545991929670632262235805227780296054, 270785034852545991929670632262241565641144146506⟩
  | 1, 3 => ⟨405044402991027991688838077240803203681901283181, 405044402991027991688838077240813648859658367399⟩
  | 2, 2 => ⟨540580667628957013019154859061773541817672144239, 540580667628957013019154859061792755562531523579⟩
  | 3, 1 => ⟨546249243231289724620828328883834647439256879523, 546249243231289724620828328883870281732634091653⟩
  | 0, 5 => ⟨-1151174879232753572226846580884437284741256078571249, 1157767256205656206294101401362149939711917295641603⟩
  | 1, 4 => ⟨-2251405995341206050642002321499246214094597940601908, 2261336620176920303337743029985224282774226940598954⟩
  | 2, 3 => ⟨-4407784667379102414409566511686546391911123878122410, 4422100531601381470779451018517321435895900893082149⟩
  | 3, 2 => ⟨-8635422924315216787832167807935697069321570219254018, 8654236564760052153119724860600360966249962023769826⟩
  | 4, 1 => ⟨-16926691542673605537987923042740909663122957497312032, 16945993961690509508660006911449318969492539431985065⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0289Geometry.ds, E8TAxisProd0289Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 23664000867085183996455537448027205721244476343 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0289CertifiedArithmetic

end


