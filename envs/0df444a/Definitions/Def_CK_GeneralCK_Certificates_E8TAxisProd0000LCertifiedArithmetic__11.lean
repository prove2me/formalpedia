-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000LCertifiedArithmetic__11
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0000LCertifiedArithmetic__11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T14:31:13.661741+00:00
-- url     : https://prove2.me/theorems/e8716512-efe5-4bfc-b166-26a1f3537101
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0000LCertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0023LCertifiedArithmetic, GeneralCK.Certificates.E8…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0000LCertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0023LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0024LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0028LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0073LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0074LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0079LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0080LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0087LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0088LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0093LCertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0000LCertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0023LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0024LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0028LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0073LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0074LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0079LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0080LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0087LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0088LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0093LCertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0000LCertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0023LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0024LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0028LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0073LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0074LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0079LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0080LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0087LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0088LCertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0093LCertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0000LCertifiedArithmetic (+10 modules: GeneralCK/Certificates/E8TAxisProd0023LCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0024LCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0028LCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0073LCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0074LCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0079LCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0080LCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0087LCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0088LCertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0093LCertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000LGraphCenterA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000LGraphCenterB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000LGraphCenterC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000LGraphCenterD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000LGraphWholeA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000LGraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000LGraphWholeC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000LGraphWholeD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000LGeometry__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor

-- ===== source module GeneralCK.Certificates.E8TAxisProd0000LCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0000LCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0000LGraphCenterA.qJetBox,
   E8TAxisProd0000LGraphCenterB.qJetBox,
   E8TAxisProd0000LGraphCenterC.qJetBox,
   E8TAxisProd0000LGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0000LGraphWholeA.qJetBox,
   E8TAxisProd0000LGraphWholeB.qJetBox,
   E8TAxisProd0000LGraphWholeC.qJetBox,
   E8TAxisProd0000LGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨275331718934448214402794500687686224031, 275331718934448214402794501403135884752⟩
  | 0, 2 => ⟨10873266654444359131046207570314588551577, 10873266654444359131046207573170744542463⟩
  | 1, 1 => ⟨13413565232074918889264738948031710502137, 13413565232074918889264738951543630317718⟩
  | 0, 3 => ⟨235685706307918190492032721945762198172400, 235685706307918190492032721949597286667098⟩
  | 1, 2 => ⟨442171045998663595223777958172312598553387, 442171045998663595223777958176465789777432⟩
  | 2, 1 => ⟨520396432226655478638651193404100311702081, 520396432226655478638651193408960421414764⟩
  | 0, 4 => ⟨2273787429317947214593716303749083010508487, 2273787429317947214593716303761345396560252⟩
  | 1, 3 => ⟨7475153328419718139812189331168718282717197, 7475153328419718139812189331181870792540244⟩
  | 2, 2 => ⟨13475310736784859642670241060768414673932451, 13475310736784859642670241060784508515876842⟩
  | 3, 1 => ⟨15085942154814172896272321015135128935650969, 15085942154814172896272321015158777385119736⟩
  | 0, 5 => ⟨-69021324118304858566534866115594065200803268413, 69001594573605732903256917477581009724568884352⟩
  | 1, 4 => ⟨-86805804508726101258025947319688080823329834798, 86507434902702905912444000675077173729783894210⟩
  | 2, 3 => ⟨-126044910683775687281623421002106906034924492421, 125538018822674129161537456477780560959323654116⟩
  | 3, 2 => ⟨-196381502281368180149291672137128656435800978559, 195774267328197045258461422416891330375617205740⟩
  | 4, 1 => ⟨-303115467996708426985569024185075509129741113017, 302940918248078011268404464879053199811689573717⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0000LGeometry.ds, E8TAxisProd0000LGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 144566182072338023771287547957267403396 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0000LCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0023LCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0023LCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0023LGraphCenterA.qJetBox,
   E8TAxisProd0023LGraphCenterB.qJetBox,
   E8TAxisProd0023LGraphCenterC.qJetBox,
   E8TAxisProd0023LGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0023LGraphWholeA.qJetBox,
   E8TAxisProd0023LGraphWholeB.qJetBox,
   E8TAxisProd0023LGraphWholeC.qJetBox,
   E8TAxisProd0023LGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨499979534555005251750243366870881795396, 499979534555005251750243367617810922588⟩
  | 0, 2 => ⟨18111512399048914164999974272145483745563, 18111512399048914164999974275039231103122⟩
  | 1, 1 => ⟨21545749871040011705863125228670825635409, 21545749871040011705863125232223084194172⟩
  | 0, 3 => ⟨353518801327649872838218833336523025593250, 353518801327649872838218833340467281214370⟩
  | 1, 2 => ⟨647878052846089223928329449188913505550974, 647878052846089223928329449193189169478844⟩
  | 2, 1 => ⟨740855367905512942993332330417376400109778, 740855367905512942993332330422420726512156⟩
  | 0, 4 => ⟨3056172784875511168238229839188886209619576, 3056172784875511168238229839201380035813632⟩
  | 1, 3 => ⟨9810020286734584946926352423556606907272703, 9810020286734584946926352423570035062053083⟩
  | 2, 2 => ⟨17398372579581859589938803309635586835086590, 17398372579581859589938803309652104378319133⟩
  | 3, 1 => ⟨19085023704036717562788810129374492456966598, 19085023704036717562788810129398804941530618⟩
  | 0, 5 => ⟨-50017664184529970493660918521586196903353814624, 49920691259101743510736134137564530314192301457⟩
  | 1, 4 => ⟨-73031941704862950325394519205997501010170961550, 72578899754909652427123732452890743584912418173⟩
  | 2, 3 => ⟨-113551183536079137200185390150380137063573616182, 112749621173606615822658014616300744052336483571⟩
  | 3, 2 => ⟨-180233710033948800905673593051370747902538273705, 179135258049799452921492675097635085552769999916⟩
  | 4, 1 => ⟨-282668391028291514587810605992386461629101823449, 281718147736741604382954411950829396983855874107⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0023LGeometry.ds, E8TAxisProd0023LGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 352884490453987550888734079875887061363 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0023LCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0024LCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0024LCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0024LGraphCenterA.qJetBox,
   E8TAxisProd0024LGraphCenterB.qJetBox,
   E8TAxisProd0024LGraphCenterC.qJetBox,
   E8TAxisProd0024LGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0024LGraphWholeA.qJetBox,
   E8TAxisProd0024LGraphWholeB.qJetBox,
   E8TAxisProd0024LGraphWholeC.qJetBox,
   E8TAxisProd0024LGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨455797543967574571138315954864039145847, 455797543967574571138315955605996019232⟩
  | 0, 2 => ⟨17237261237826960624838430737052886199048, 17237261237826960624838430739939919236008⟩
  | 1, 1 => ⟨19956554357501557836688799431057605704140, 19956554357501557836688799434602593087280⟩
  | 0, 3 => ⟨345883996626843955515732058940274933375132, 345883996626843955515732058944199678081061⟩
  | 1, 2 => ⟨623541003359968102652678440482397125465378, 623541003359968102652678440486651882709130⟩
  | 2, 1 => ⟨697929972084295937371280120030773455799604, 697929972084295937371280120035790477742818⟩
  | 0, 4 => ⟨3051687238225136990260133188316037685428835, 3051687238225136990260133188328489911153497⟩
  | 1, 3 => ⟨9659671306262932960543935799379548844252484, 9659671306262932960543935799392932536311870⟩
  | 2, 2 => ⟨16942612440872618964833988003942456745145405, 16942612440872618964833988003958912254521656⟩
  | 3, 1 => ⟨18306495362438826047657536285591052332527636, 18306495362438826047657536285615266034203367⟩
  | 0, 5 => ⟨-49887017327920921190018344314973246669487018213, 49788982405146373220520054384131113937662854984⟩
  | 1, 4 => ⟨-72820687005942405677546527665778447167435432954, 72372713830142778973063226507809461094896714952⟩
  | 2, 3 => ⟨-113182150643111072088474591832475936569220155850, 112387805445546352742476148627789443263691681588⟩
  | 3, 2 => ⟨-179570926655561385435316627323501762080091466011, 178474881121951042796090319982016130891610868977⟩
  | 4, 1 => ⟨-281457648796463749511995362473102975098559572670, 280495897790181118307858493336398841292702728033⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0024LGeometry.ds, E8TAxisProd0024LGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 317927080994275696688931387079073249175 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0024LCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0028LCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0028LCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0028LGraphCenterA.qJetBox,
   E8TAxisProd0028LGraphCenterB.qJetBox,
   E8TAxisProd0028LGraphCenterC.qJetBox,
   E8TAxisProd0028LGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0028LGraphWholeA.qJetBox,
   E8TAxisProd0028LGraphWholeB.qJetBox,
   E8TAxisProd0028LGraphWholeC.qJetBox,
   E8TAxisProd0028LGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨413777334136110270513009955398558077723, 413777334136110270513009956135552454904⟩
  | 0, 2 => ⟨16382083172632771598609552249326358104491, 16382083172632771598609552252206703743291⟩
  | 1, 1 => ⟨18427731950894308034321041560917418660421, 18427731950894308034321041564455163486190⟩
  | 0, 3 => ⟨338260283874315864623289606379753502607974, 338260283874315864623289606383658789415939⟩
  | 1, 2 => ⟨599579438287361454754772345765746100337905, 599579438287361454754772345769980007479226⟩
  | 2, 1 => ⟨656138969948259627281418772350078174160002, 656138969948259627281418772355067973163402⟩
  | 0, 4 => ⟨3047299206312280851998885726406244639699984, 3047299206312280851998885726418655423069986⟩
  | 1, 3 => ⟨9509631958965231307363561772917070294507342, 9509631958965231307363561772930409691467978⟩
  | 2, 2 => ⟨16490855209826596468923380545526313220614897, 16490855209826596468923380545542706939223749⟩
  | 3, 1 => ⟨17539144454971369057524238421033559640193517, 17539144454971369057524238421057674956514360⟩
  | 0, 5 => ⟨-49758277200487805756061931329496498263120730552, 49660285637190602846143565521682874939589498428⟩
  | 1, 4 => ⟨-72612071016792174835870809868774584214591607349, 72170783721816309839697730266611313119060341813⟩
  | 2, 3 => ⟨-112817420495534330658518451723181365391379031726, 112032609540890044075771717266605458392355896207⟩
  | 3, 2 => ⟨-178915710182611954737574219584833573440686099298, 177825093338029148271630372670933409044212549802⟩
  | 4, 1 => ⟨-280260111260252543688991816622094863091378599432, 279289804952230530504691059260544649207088779797⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0028LGeometry.ds, E8TAxisProd0028LGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 284809223227936817414517858882976850634 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0028LCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0073LCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0073LCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0073LGraphCenterA.qJetBox,
   E8TAxisProd0073LGraphCenterB.qJetBox,
   E8TAxisProd0073LGraphCenterC.qJetBox,
   E8TAxisProd0073LGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0073LGraphWholeA.qJetBox,
   E8TAxisProd0073LGraphWholeB.qJetBox,
   E8TAxisProd0073LGraphWholeC.qJetBox,
   E8TAxisProd0073LGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1910639959873514546025162117714873380203386, 1910639959873514546025162117717040504928167⟩
  | 0, 2 => ⟨15990822593448435427375544413082128369410451, 15990822593448435427375544413087177990219791⟩
  | 1, 1 => ⟨16804406968804652008306147763512781411528856, 16804406968804652008306147763519001581768928⟩
  | 0, 3 => ⟨71805024257926842379004485420641179364804179, 71805024257926842379004485420650991379998731⟩
  | 1, 2 => ⟨117498438406844961861960077193692041311610797, 117498438406844961861960077193703650764257669⟩
  | 2, 1 => ⟨122139777275592597692667179766276883264580128, 122139777275592597692667179766293191988727771⟩
  | 0, 4 => ⟨186000193634249938695475445693882834915298571, 186000193634249938695475445693909261976481517⟩
  | 1, 3 => ⟨435612711599918984746154149508385491671985981, 435612711599918984746154149508417411237013480⟩
  | 2, 2 => ⟨693225659617460488816023526291743548165690277, 693225659617460488816023526291789240621536504⟩
  | 3, 1 => ⟨713436583730734058428844892093145259531365136, 713436583730734058428844892093216972033287362⟩
  | 0, 5 => ⟨-587537742212584777688394023144899879055807356814, 594184320539648286495206322548330862159162763408⟩
  | 1, 4 => ⟨-988902273535727347982911439615458041325594708644, 989774251484383484506142556633511672946534903919⟩
  | 2, 3 => ⟨-1702938617335778013291669366909534102670091223067, 1696738105502276138952984170941228317258676406968⟩
  | 3, 2 => ⟨-2949466415398136963230964083152196718526586193290, 2936533397239612941508205341741615335270967672606⟩
  | 4, 1 => ⟨-5093606325260418551576451935049738050951138919468, 5081804010753236458815294510918108908639355179276⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0073LGeometry.ds, E8TAxisProd0073LGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1595095563186928218655825977635781620766379 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0073LCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0074LCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0074LCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0074LGraphCenterA.qJetBox,
   E8TAxisProd0074LGraphCenterB.qJetBox,
   E8TAxisProd0074LGraphCenterC.qJetBox,
   E8TAxisProd0074LGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0074LGraphWholeA.qJetBox,
   E8TAxisProd0074LGraphWholeB.qJetBox,
   E8TAxisProd0074LGraphWholeC.qJetBox,
   E8TAxisProd0074LGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1870886810304408921765932991266767049698580, 1870886810304408921765932991268926156647649⟩
  | 0, 2 => ⟨15811890340955348378072172281459345556468249, 15811890340955348378072172281464380339149576⟩
  | 1, 1 => ⟨16512019523427130193017260136752164010054516, 16512019523427130193017260136758366267149162⟩
  | 0, 3 => ⟨71341154140977245962867381619610985527623504, 71341154140977245962867381619620759521432315⟩
  | 1, 2 => ⟨116412572112997381569608672660313468426418904, 116412572112997381569608672660325031483961094⟩
  | 2, 1 => ⟨120413278330381820076520494146067269636180870, 120413278330381820076520494146083509931181620⟩
  | 0, 4 => ⟨185096822593759501409124700195320400669454453, 185096822593759501409124700195346732861873965⟩
  | 1, 3 => ⟨433082587600200248613098839959895216027418947, 433082587600200248613098839959927017046613067⟩
  | 2, 2 => ⟨687978333748635228921397673906744603039921264, 687978333748635228921397673906790112405627159⟩
  | 3, 1 => ⟨705421175063378147711114541161089233513611352, 705421175063378147711114541161160641557134157⟩
  | 0, 5 => ⟨-585206583901168098231076504761515410694739778157, 591858873239879697079820752550848343900807803155⟩
  | 1, 4 => ⟨-984766238112987584210084684879708673248504885882, 985683310011466761040620412022125181887136872208⟩
  | 2, 3 => ⟨-1695413976032195826987291831979574200630446262343, 1689317524574005684410473962970759382204191409871⟩
  | 3, 2 => ⟨-2935599631648114419350868620304793155110624470475, 2922863701165836624262033560394140771143149837909⟩
  | 4, 1 => ⟨-5067858233907480136665263378314322722306002602539, 5056414699392420928791992891876300104163814793718⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0074LGeometry.ds, E8TAxisProd0074LGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1560448590731243229075199799046950292577871 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0074LCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0079LCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0079LCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0079LGraphCenterA.qJetBox,
   E8TAxisProd0079LGraphCenterB.qJetBox,
   E8TAxisProd0079LGraphCenterC.qJetBox,
   E8TAxisProd0079LGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0079LGraphWholeA.qJetBox,
   E8TAxisProd0079LGraphWholeB.qJetBox,
   E8TAxisProd0079LGraphWholeC.qJetBox,
   E8TAxisProd0079LGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1831579544121348229067909344548913955357010, 1831579544121348229067909344551065063822295⟩
  | 0, 2 => ⟨15634114946480604830200188748816098637189346, 15634114946480604830200188748821118632809959⟩
  | 1, 1 => ⟨16222338851278453390044205175177825837874718, 16222338851278453390044205175184010245018470⟩
  | 0, 3 => ⟨70879535541544080665888518275567943930718192, 70879535541544080665888518275577680025745202⟩
  | 1, 2 => ⟨115333014178689045678367435772075664278734830, 115333014178689045678367435772087181097203345⟩
  | 2, 1 => ⟨118699861488016499565456538922999353256175653, 118699861488016499565456538923015525365556566⟩
  | 0, 4 => ⟨184198975654722744406919458427026036058975815, 184198975654722744406919458427052273733114576⟩
  | 1, 3 => ⟨430566011798133975303333646722335301346708881, 430566011798133975303333646722366984269590701⟩
  | 2, 2 => ⟨682759950506057970894655980160283657766304459, 682759950506057970894655980160328984751870213⟩
  | 3, 1 => ⟨697457498020626376999136694872158909184440871, 697457498020626376999136694872230013971981698⟩
  | 0, 5 => ⟨-582884205661244596252665674787232047561596786643, 589614566511565169784092056665709559658544332227⟩
  | 1, 4 => ⟨-980645895387918524864401213170399070496343475870, 981694863219296388850426596078735000411579198002⟩
  | 2, 3 => ⟨-1687918213919980693658020879607153599712754129896, 1682012556055116595858065412024705687944530659760⟩
  | 3, 2 => ⟨-2921786806675174149074499015922516334806691549243, 2909305591868948121765243495492543962847500582001⟩
  | 4, 1 => ⟨-5042211812529845368537635700969608203313541219224, 5031126471166571621892704707834496159274990394583⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0079LGeometry.ds, E8TAxisProd0079LGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1526201704211893239960408333592376117633433 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0079LCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0080LCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0080LCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0080LGraphCenterA.qJetBox,
   E8TAxisProd0080LGraphCenterB.qJetBox,
   E8TAxisProd0080LGraphCenterC.qJetBox,
   E8TAxisProd0080LGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0080LGraphWholeA.qJetBox,
   E8TAxisProd0080LGraphWholeB.qJetBox,
   E8TAxisProd0080LGraphWholeC.qJetBox,
   E8TAxisProd0080LGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1792715276200908642508120755103427223676867, 1792715276200908642508120755105570352890023⟩
  | 0, 2 => ⟨15457490798468477514061097722152074117868766, 15457490798468477514061097722157079377332647⟩
  | 1, 1 => ⟨15935349223721917926218367426825086637136776, 15935349223721917926218367426831253257312942⟩
  | 0, 3 => ⟨70420154679062939518348049458567201467967733, 70420154679062939518348049458576899786351973⟩
  | 1, 2 => ⟨114259730824557035885325233445728319829000622, 114259730824557035885325233445739790563826003⟩
  | 2, 1 => ⟨116999454592860027890927431229873953335729278, 116999454592860027890927431229890057502076628⟩
  | 0, 4 => ⟨183306629089195800950010062552072326106645947, 183306629089195800950010062552098469611661593⟩
  | 1, 3 => ⟨428062911347373694916117191358492445828279421, 428062911347373694916117191358524011102625974⟩
  | 2, 2 => ⟨677570349279890390971640464071048023947203048, 677570349279890390971640464071093169259840739⟩
  | 3, 1 => ⟨689545261713132904640069893216654749679795430, 689545261713132904640069893216725552409014530⟩
  | 0, 5 => ⟨-580570509646708005150750611348609239307293018082, 587378666938866396891518800930734682389048603867⟩
  | 1, 4 => ⟨-976541135632677964750721241159114496827558042450, 977721601668316448052411658698211738447886003079⟩
  | 2, 3 => ⟨-1680451184687104943127761565665693802116451382104, 1674735834090824124845361396362404563534223518381⟩
  | 3, 2 => ⟨-2908027704583214188766607897189788354442469129500, 2895800683929969356248723852366838386829113127968⟩
  | 4, 1 => ⟨-5016666649424562069232992929690888658932113235528, 5005938910688160390622110398662495144612901276779⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0080LGeometry.ds, E8TAxisProd0080LGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1492352282644154202890095478235122053253905 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0080LCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0087LCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0087LCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0087LGraphCenterA.qJetBox,
   E8TAxisProd0087LGraphCenterB.qJetBox,
   E8TAxisProd0087LGraphCenterC.qJetBox,
   E8TAxisProd0087LGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0087LGraphWholeA.qJetBox,
   E8TAxisProd0087LGraphWholeB.qJetBox,
   E8TAxisProd0087LGraphWholeC.qJetBox,
   E8TAxisProd0087LGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1754291135405553091102738020017831380869379, 1754291135405553091102738020019966550001971⟩
  | 0, 2 => ⟨15282012319740646698684557640443500371038917, 15282012319740646698684557640448490945087373⟩
  | 1, 1 => ⟨15651034996341948525842221798830619479274558, 15651034996341948525842221798836768375256061⟩
  | 0, 3 => ⟨69962997832113716552695813195901832135647295, 69962997832113716552695813195911492799064678⟩
  | 1, 2 => ⟨113192688452915364399392035907917357847385021, 113192688452915364399392035907928782653399637⟩
  | 2, 1 => ⟨115311985889801791623818183048172638354955056, 115311985889801791623818183048188674819918009⟩
  | 0, 4 => ⟨182419759309591543629953028697970899374944725, 182419759309591543629953028697996949058675919⟩
  | 1, 3 => ⟨425573213752424544503233198733293239615807012, 425573213752424544503233198733324687687659199⟩
  | 2, 2 => ⟨672409370258502735095744921480673238898320467, 672409370258502735095744921480718203242466634⟩
  | 3, 1 => ⟨681684176786369664655330080086921157927011985, 681684176786369664655330080086991659790834098⟩
  | 0, 5 => ⟨-578266150273945385503722966540105948259021993937, 585152482942103563339072871531840929500595399246⟩
  | 1, 4 => ⟨-972452217942905185889651536189101794887654824415, 973764452544321592336659579402017308422527559269⟩
  | 2, 3 => ⟨-1673012852562689051338083351695347506025945935862, 1667487998913045029675569693924950109924876048939⟩
  | 3, 2 => ⟨-2894322150682125903540407495824594440185890350071, 2882349433080758198680907319895736571854665337829⟩
  | 4, 1 => ⟨-4991222349898387327205222944554139298525767583476, 4980852106410188064022341501239780629456306043005⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0087LGeometry.ds, E8TAxisProd0087LGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1458897717058918221285637427646114962438072 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0087LCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0088LCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0088LCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0088LGraphCenterA.qJetBox,
   E8TAxisProd0088LGraphCenterB.qJetBox,
   E8TAxisProd0088LGraphCenterC.qJetBox,
   E8TAxisProd0088LGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0088LGraphWholeA.qJetBox,
   E8TAxisProd0088LGraphWholeB.qJetBox,
   E8TAxisProd0088LGraphWholeC.qJetBox,
   E8TAxisProd0088LGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1716304264497872200240482350650296953184855, 1716304264497872200240482350652424181348569⟩
  | 0, 2 => ⟨15107673967348777491179363918047355404404720, 15107673967348777491179363918052331343617026⟩
  | 1, 1 => ⟨15369380608491000541874447891172425623203637, 15369380608491000541874447891178556857553840⟩
  | 0, 3 => ⟨69508051338070390200693174519958222966832725, 69508051338070390200693174519967846096497899⟩
  | 1, 2 => ⟨112131853646880068707164331140872674063422024, 112131853646880068707164331140884053094862535⟩
  | 2, 1 => ⟨113637384022266684792462595147694767090184282, 113637384022266684792462595147710736094478834⟩
  | 0, 4 => ⟨181538342868139866813108112068740578234504894, 181538342868139866813108112068766534443477280⟩
  | 1, 3 => ⟨423096846866865497313215534159442327366752506, 423096846866865497313215534159473658680423268⟩
  | 2, 2 => ⟨667276854424449584492420670341331762158323209, 667276854424449584492420670341376546235652311⟩
  | 3, 1 => ⟨673873955413025525646273085573931010946303646, 673873955413025525646273085574001213132941159⟩
  | 0, 5 => ⟨-575970715004290311574754765365966960798835411712, 582936608271190526433484796305862387099527778748⟩
  | 1, 4 => ⟨-968378902430589108170552996534746032736289028547, 969823993337767341823877285621832226926235370396⟩
  | 2, 3 => ⟨-1665603049704653014802716908279351962789125207020, 1660269573920201059716204720765513824994594154339⟩
  | 3, 2 => ⟨-2880669920253562004038248100450641273340664919945, 2868952336317641499580881753034594250053858308928⟩
  | 4, 1 => ⟨-4965878530099614042106678124284860941783711147605, 4955866482945690193484821463525728512876305143849⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0088LGeometry.ds, E8TAxisProd0088LGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1425835411009499351143020142197323526625096 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0088LCertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0093LCertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0093LCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0093LGraphCenterA.qJetBox,
   E8TAxisProd0093LGraphCenterB.qJetBox,
   E8TAxisProd0093LGraphCenterC.qJetBox,
   E8TAxisProd0093LGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0093LGraphWholeA.qJetBox,
   E8TAxisProd0093LGraphWholeB.qJetBox,
   E8TAxisProd0093LGraphWholeC.qJetBox,
   E8TAxisProd0093LGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1678751820055192697344418155077282889370391, 1678751820055192697344418155079402195617203⟩
  | 0, 2 => ⟨14934470232427970993965045677678642347862236, 14934470232427970993965045677683603702656259⟩
  | 1, 1 => ⟨15090370582838643902507690303814302771482295, 15090370582838643902507690303820416406555826⟩
  | 0, 3 => ⟨69055301592752152396162141266327374660446398, 69055301592752152396162141266336960377114444⟩
  | 1, 2 => ⟨111077193169498741359809013764638153319212029, 111077193169498741359809013764649486729721666⟩
  | 2, 1 => ⟨111975578030234659622518477295358800874115858, 111975578030234659622518477295374702657528432⟩
  | 0, 4 => ⟨180662356456350838567530999404465002179153083, 180662356456350838567530999404490865258584134⟩
  | 1, 3 => ⟨420633738891579111558044227375517255698798360, 420633738891579111558044227375548470696878714⟩
  | 2, 2 => ⟨662172643550463580088898262786832311784947478, 662172643550463580088898262786876916294381158⟩
  | 3, 1 => ⟨666114311285440922450916523038907356719148340, 666114311285440922450916523038977260412116610⟩
  | 0, 5 => ⟨-573683787502586066518468029109813303988810379899, 580728954975607445860047024276208395579667301873⟩
  | 1, 4 => ⟨-964320949152175423813930953632817539303729099733, 965898494429274272299040606062986189652507057189⟩
  | 2, 3 => ⟨-1658221617694576205257514608897234133534230799453, 1653079030971571566542612786154128321239170915747⟩
  | 3, 2 => ⟨-2867070757526831433452384233706668864080785081286, 2855607773536885390203511662540741478443244725037⟩
  | 4, 1 => ⟨-4940634747704512994390583003004152342260637641946, 4930980280753606308343195216706534810508860902231⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0093LGeometry.ds, E8TAxisProd0093LGeometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1393162780647458644281114116140737074923006 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0093LCertifiedArithmetic

end


