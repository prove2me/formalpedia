-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0047CertifiedArithmetic__15
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0047CertifiedArithmetic__15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T18:27:48.202982+00:00
-- url     : https://prove2.me/theorems/895285bd-f82c-4789-9a40-99ab64d4b70d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0047CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisZero0048CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0047CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisZero0048CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0049CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0050CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0051CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0052CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0053CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0054CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0055CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0056CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0057CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0058CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0059CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0060CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0061CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0047CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisZero0048CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0049CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0050CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0051CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0052CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0053CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0054CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0055CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0056CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0057CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0058CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0059CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0060CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0061CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0047CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisZero0048CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0049CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0050CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0051CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0052CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0053CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0054CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0055CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0056CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0057CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0058CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0059CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0060CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0061CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0047CertifiedArithmetic (+14 modules: GeneralCK/Certificates/E8TAxisZero0048CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0049CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0050CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0051CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0052CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0053CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0054CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0055CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0056CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0057CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0058CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0059CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0060CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0061CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0044GraphCenterA__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0046GraphCenterB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0036GraphCenterC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0031GraphCenterD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0043GraphWholeA__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0034GraphWholeB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0045GraphWholeC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0046GraphWholeD__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularInverseBoxes
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0043Geometry__25
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0048GraphCenterD__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0049GraphWholeB__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051GraphCenterC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0061GraphCenterD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0061GraphWholeD__12

-- ===== source module GeneralCK.Certificates.E8TAxisZero0047CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0047CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0047GraphCenterA.qJetBox,
   E8TAxisZero0047GraphCenterB.qJetBox,
   E8TAxisZero0047GraphCenterC.qJetBox,
   E8TAxisZero0047GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0047GraphWholeA.qJetBox,
   E8TAxisZero0047GraphWholeB.qJetBox,
   E8TAxisZero0047GraphWholeC.qJetBox,
   E8TAxisZero0047GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨99961800248602911649887904518374975349475694, 99961800248602911649887904518379344513367214⟩
  | 0, 2 => ⟨488974435841893748880796970295136889772951525, 488974435841893748880796970295147858799195687⟩
  | 1, 1 => ⟨489828077522665783739637242424077637488690237, 489828077522665783739637242424094870444497393⟩
  | 0, 3 => ⟨1435363769647042721220444142024686432340312253, 1435363769647042721220444142024714790997304577⟩
  | 1, 2 => ⟨2119824824589792562701580550983361136128586996, 2119824824589792562701580550983405668921071467⟩
  | 2, 1 => ⟨2122920535216347126155694989133921292233658089, 2122920535216347126155694989133993878928779730⟩
  | 0, 4 => ⟨3241133555805177600375278892455776500500210576, 3241133555805177600375278892457611513464497858⟩
  | 1, 3 => ⟨5719889578542638785134545001947542778508016930, 5719889578542638785134545001947670373268613530⟩
  | 2, 2 => ⟨8201529081516618699260365929705270261684388623, 8201529081516618699260365929705481918890324173⟩
  | 3, 1 => ⟨8211671115679387561603496370597448815860366596, 8211671115679387561603496370597806772194993877⟩
  | 0, 5 => ⟨-22638623352165191194317539268082751822807806450872, 22823662078441764127279780100089619896844285260162⟩
  | 1, 4 => ⟨-42354127667835250629848470355395659940684123461533, 42561458877662751504744133409278370612118454168629⟩
  | 2, 3 => ⟨-79614066039034198398257211638776780928794564845370, 79849891239849252981564780467861182066019067529847⟩
  | 3, 2 => ⟨-149927125520034012942604860322111725985447391242839, 150195995088148569640241891285117547742705047821917⟩
  | 4, 1 => ⟨-282438689750762516288819597713610689027496393332019, 282728106330131513938414298217792706522014725617622⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0047Geometry.ds, E8TAxisZero0047Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 70655610638481712050762368069560893937867605 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0047CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0048CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0048CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0048GraphCenterA.qJetBox,
   E8TAxisZero0048GraphCenterB.qJetBox,
   E8TAxisZero0048GraphCenterC.qJetBox,
   E8TAxisZero0048GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0048GraphWholeA.qJetBox,
   E8TAxisZero0048GraphWholeB.qJetBox,
   E8TAxisZero0048GraphWholeC.qJetBox,
   E8TAxisZero0048GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨73177395837207641701160361834167379168423507, 73177395837207641701160361834171278111929941⟩
  | 0, 2 => ⟨371386587268957318866682693080457383635673991, 371386587268957318866682693080467046439626871⟩
  | 1, 1 => ⟨372065344522311190707289597090400855350600915, 372065344522311190707289597090415915480355176⟩
  | 0, 3 => ⟨1115707747264086679638522381160858908222791024, 1115707747264086679638522381160883475062133949⟩
  | 1, 2 => ⟨1659972960800218547844540521299730090288575034, 1659972960800218547844540521299768346512993254⟩
  | 2, 1 => ⟨1662492068659587252492755606514703630507525472, 1662492068659587252492755606514765582327610139⟩
  | 0, 4 => ⟨2533236030410243676985124333406600155067948994, 2533236030410243676985124333408314261969124154⟩
  | 1, 3 => ⟨4550269769847069044900609012637958871639372376, 4550269769847069044900609012638067654473879209⟩
  | 2, 2 => ⟨6569737774052418731280188969089284386430795433, 6569737774052418731280188969089463593886094758⟩
  | 3, 1 => ⟨6578101296824637564386393206468096645922430102, 6578101296824637564386393206468397921301800902⟩
  | 0, 5 => ⟨-18040894178805174442749264444211702055439505207746, 18187540113298473982185123285999990860470600510917⟩
  | 1, 4 => ⟨-33588218653590863984783880862890960115262998859167, 33743361065745486627966067811584800129262748726037⟩
  | 2, 3 => ⟨-62860607721122696556009284548404754174556226383064, 63026268007854241531735060987904633527185844775758⟩
  | 3, 2 => ⟨-117874906799474953681536266672024057642723085517938, 118054920462090922024239840625002159650649387507460⟩
  | 4, 1 => ⟨-221098329254960216872100125025333428885584669536416, 221295659521907754128613497391507778923090113375423⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0048Geometry.ds, E8TAxisZero0048Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 50602602682858390035369215847939539566399496 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0048CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0049CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0049CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0049GraphCenterA.qJetBox,
   E8TAxisZero0049GraphCenterB.qJetBox,
   E8TAxisZero0049GraphCenterC.qJetBox,
   E8TAxisZero0049GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0049GraphWholeA.qJetBox,
   E8TAxisZero0049GraphWholeB.qJetBox,
   E8TAxisZero0049GraphWholeC.qJetBox,
   E8TAxisZero0049GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨52917062118410323828662604194329677904600152, 52917062118410323828662604194333161635676219⟩
  | 0, 2 => ⟨279561136213907822171574793399770976295762285, 279561136213907822171574793399779514225616159⟩
  | 1, 1 => ⟨280097776574483037484431682511107310226213451, 280097776574483037484431682511120511570458114⟩
  | 0, 3 => ⟨861910862567342797698799580088464898994911189, 861910862567342797698799580088486234323204983⟩
  | 1, 2 => ⟨1292245024698351856050482264238509768460484861, 1292245024698351856050482264238542713869086762⟩
  | 2, 1 => ⟨1294289051105050028113392616192641900515843952, 1294289051105050028113392616192694906070131561⟩
  | 0, 4 => ⟨1968423039693726140866739684240757429741655387, 1968423039693726140866739684242356044500335306⟩
  | 1, 3 => ⟨3605030454802916760429796860464995483010357865, 3605030454802916760429796860465088697811540281⟩
  | 2, 2 => ⟨5243693983747443697692350743180801526366623796, 5243693983747443697692350743180954054275625089⟩
  | 3, 1 => ⟨5250578926537885387565741292070971952447347266, 5250578926537885387565741292071226900325991800⟩
  | 0, 5 => ⟨-14450129181007619391469240801066292143840424435105, 14567254192268227984229351570000754385351927932588⟩
  | 1, 4 => ⟨-26764143377043971081044761836870051992307262387852, 26880208087850095446213822898496007251876423700469⟩
  | 2, 3 => ⟨-49856618905206430303832908015644416002605143171456, 49970784451798624028475051434111296013668984812960⟩
  | 3, 2 => ⟨-93066805076773803824982010404705480349728081776960, 93182301979677827157738672884574073047200501747070⟩
  | 4, 1 => ⟨-173757323703874560300501828001629757080202943756519, 173887407162353100267998804717510364593500428757249⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0049Geometry.ds, E8TAxisZero0049Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 35579992298416820244540757397338794694021042 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0049CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0050CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0050CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0050GraphCenterA.qJetBox,
   E8TAxisZero0050GraphCenterB.qJetBox,
   E8TAxisZero0050GraphCenterC.qJetBox,
   E8TAxisZero0050GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0050GraphWholeA.qJetBox,
   E8TAxisZero0050GraphWholeB.qJetBox,
   E8TAxisZero0050GraphWholeC.qJetBox,
   E8TAxisZero0050GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨37736858625071096020769742353259486104193481, 37736858625071096020769742353262601951140523⟩
  | 0, 2 => ⟨208300564944037983207385034698619442137971376, 208300564944037983207385034698627008988503551⟩
  | 1, 1 => ⟨208722064901990881802258553129431407883807942, 208722064901990881802258553129443015439931558⟩
  | 0, 3 => ⟨661252859569538487107933538300314619090296905, 661252859569538487107933538300333184878036660⟩
  | 1, 2 => ⟨999279305298630172612295050168454893521233168, 999279305298630172612295050168483318102978295⟩
  | 2, 1 => ⟨1000932533441932020859511742151443573169562787, 1000932533441932020859511742151489003426349746⟩
  | 0, 4 => ⟨1519993211824069894873437113504225079983290675, 1519993211824069894873437113505712829963565159⟩
  | 1, 3 => ⟨2843667134507797633402616818301704992142359180, 2843667134507797633402616818301785031404325395⟩
  | 2, 2 => ⟨4169079134776681811365830976038409810012799663, 4169079134776681811365830976038539861240835390⟩
  | 3, 1 => ⟨4174738277883008922308797170534350463759888389, 4174738277883008922308797170534566541197237524⟩
  | 0, 5 => ⟨-11942298015473634591242074948612122635593387038449, 12031614167140640004457992671706250636136776237187⟩
  | 1, 4 => ⟨-22014477638962343262360585480062403941915596521464, 22093395625189717785387377520677568341574071016273⟩
  | 2, 3 => ⟨-40828695000641284776258404496677243100146535319683, 40893552243068341267732834914606305932404746256583⟩
  | 3, 2 => ⟨-75879553899490193617460347898383735419464977094236, 75933136680577723287292567292901070822859024349729⟩
  | 4, 1 => ⟨-141017520775806015375103504047819630958155019916441, 141083672019251092734970188361163628230565750801757⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0050Geometry.ds, E8TAxisZero0050Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 24297025569897450206564693413502599108110279 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0050CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0051CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0051CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0051GraphCenterA.qJetBox,
   E8TAxisZero0051GraphCenterB.qJetBox,
   E8TAxisZero0051GraphCenterC.qJetBox,
   E8TAxisZero0051GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0051GraphWholeA.qJetBox,
   E8TAxisZero0051GraphWholeB.qJetBox,
   E8TAxisZero0051GraphWholeC.qJetBox,
   E8TAxisZero0051GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨92153181838299265258681437911206108138618913791, 92153181838299265258681437911206581655014714820⟩
  | 0, 2 => ⟨252316717256232169083237704912460611780306267467, 252316717256232169083237704912462630046098463987⟩
  | 1, 1 => ⟨252415073717484490091480989496766162449963695352, 252415073717484490091480989496769928141845212886⟩
  | 0, 3 => ⟨476740255408537495779946856768368445285184226070, 476740255408537495779946856768375349812569205035⟩
  | 1, 2 => ⟨634220487697918582198399488685407890029410992112, 634220487697918582198399488685420620773137866045⟩
  | 2, 1 => ⟨634440270513937925670994826743823850591749456231, 634440270513937925670994826743847497108622655187⟩
  | 0, 4 => ⟨755591531514329446134199565916932163548946993334, 755591531514329446134199565916957157989810180009⟩
  | 1, 3 => ⟨1107371748367464906498935542225959293337723343182, 1107371748367464906498935542226005740990070206956⟩
  | 2, 2 => ⟨1459252044553661925308099659287909577703045960104, 1459252044553661925308099659287996578691508723854⟩
  | 3, 1 => ⟨1459707612915690161947086127107363604338571620605, 1459707612915690161947086127107527610022512837230⟩
  | 0, 5 => ⟨-4634881637049370962133333415300666614456523000210662, 4655755414718063838870839558106402011017461682382387⟩
  | 1, 4 => ⟨-9120647010391954553294395055409327070136867326926033, 9151996861618798593424429012737839361023313918929730⟩
  | 2, 3 => ⟨-17963806765841712594916427187334709549207288673637928, 18008824645953432634051450614408081764242826151869249⟩
  | 3, 2 => ⟨-35403771429838196167194020904384612104733565649465694, 35462612906339123370808223273391778091011923654351594⟩
  | 4, 1 => ⟨-69812241234788734654834052354715744939040393906309742, 69871847194741064894601143165080360756568877489488375⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0051Geometry.ds, E8TAxisZero0051Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 87023190750141703398419292423161546741452733259 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0051CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0052CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0052CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0052GraphCenterA.qJetBox,
   E8TAxisZero0052GraphCenterB.qJetBox,
   E8TAxisZero0052GraphCenterC.qJetBox,
   E8TAxisZero0052GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0052GraphWholeA.qJetBox,
   E8TAxisZero0052GraphWholeB.qJetBox,
   E8TAxisZero0052GraphWholeC.qJetBox,
   E8TAxisZero0052GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨83480627164306403914688010389785599494032207753, 83480627164306403914688010389786026359087226291⟩
  | 0, 2 => ⟨230443154865805395194797271979637023280352572143, 230443154865805395194797271979638833733734429601⟩
  | 1, 1 => ⟨230533900187578659569186980444929296223035049484, 230533900187578659569186980444932669161214878150⟩
  | 0, 3 => ⟨438440609802051186285654845984693187979970415049, 438440609802051186285654845984699362202985620478⟩
  | 1, 2 => ⟨583735118146400847840359130455738069613076191676, 583735118146400847840359130455749436768435508415⟩
  | 2, 1 => ⟨583939099848396311364807639759256313692308515311, 583939099848396311364807639759277397605813008678⟩
  | 0, 4 => ⟨698599111477899910163588527424524395077551940332, 698599111477899910163588527424546642187767620200⟩
  | 1, 3 => ⟨1025088632037733090331188728418220801596790230947, 1025088632037733090331188728418262092135493197224⟩
  | 2, 2 => ⟨1351671445168459422162591787523298929650170523629, 1351671445168459422162591787523376181701616555857⟩
  | 3, 1 => ⟨1352095613127484802212724935971109703588834333291, 1352095613127484802212724935971255169493646884284⟩
  | 0, 5 => ⟨-4220214427630436670610402066242146872410407563872803, 4239551307962831452213960932927751148678668596757027⟩
  | 1, 4 => ⟨-8301807803040076341323594341481803652913059225275790, 8330871007852477402309210103307830584132575015576292⟩
  | 2, 3 => ⟨-16345419342057601906299336599937689640614919459315951, 16387178667558577285367086325455007741226269231098817⟩
  | 3, 2 => ⟨-32203004889203822525532342099964439559926655127179898, 32257610122809666198542714348432331971899668480429251⟩
  | 4, 1 => ⟨-63478350075292182648947748941143413777101708450269076, 63533685228860130460713381045291627797162666717884198⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0052Geometry.ds, E8TAxisZero0052Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 78795846602939970952707113885035631064841358373 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0052CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0053CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0053CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0053GraphCenterA.qJetBox,
   E8TAxisZero0053GraphCenterB.qJetBox,
   E8TAxisZero0053GraphCenterC.qJetBox,
   E8TAxisZero0053GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0053GraphWholeA.qJetBox,
   E8TAxisZero0053GraphWholeB.qJetBox,
   E8TAxisZero0053GraphWholeC.qJetBox,
   E8TAxisZero0053GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨75562633463017096700500518041289003986344898453, 75562633463017096700500518041289388907407923247⟩
  | 0, 2 => ⟨210316093482916309949048399780836598920015612513, 210316093482916309949048399780838223046691495422⟩
  | 1, 1 => ⟨210399775710604124347012897209640743910263990694, 210399775710604124347012897209643765083979457731⟩
  | 0, 3 => ⟨402992508063036476397411577591053097031924992667, 402992508063036476397411577591058617942710223261⟩
  | 1, 2 => ⟨536978709838151217564753086104876445739007242311, 536978709838151217564753086104886594499499979154⟩
  | 2, 1 => ⟨537167979889167678492974630752370531527763828319, 537167979889167678492974630752389328327273122181⟩
  | 0, 4 => ⟨645665788587011492032461485487984811391570318267, 645665788587011492032461485488004610362601110201⟩
  | 1, 3 => ⟨948608359647644990799706838163587216959314244724, 948608359647644990799706838163623916579626418903⟩
  | 2, 2 => ⟨1251637903182387159657046874102080403939037960156, 1251637903182387159657046874102148985568925059441⟩
  | 3, 1 => ⟨1252032815865493432434483727860832238850055154131, 1252032815865493432434483727860961231341379024261⟩
  | 0, 5 => ⟨-3831204452198004211962325909360609033809683711139732, 3849088870468220772876112373886620209016379070304029⟩
  | 1, 4 => ⟨-7533812553019646126777467744491677298195924229266199, 7560709335667201717968878783759761259964084038876259⟩
  | 2, 3 => ⟨-14827907260633139782095046019099438674024143478901078, 14866573558940298739967818014536663523612653018898923⟩
  | 3, 2 => ⟨-29202553576657512962524690530619007883884458938684439, 29253133330676116528418670391126608250928606786567614⟩
  | 4, 1 => ⟨-57542535844378603777661513345877240229271719039693604, 57593811789668835059240103290888596101266793958214782⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0053Geometry.ds, E8TAxisZero0053Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 71288072432177041695144736846576409813714112708 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0053CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0054CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0054CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0054GraphCenterA.qJetBox,
   E8TAxisZero0054GraphCenterB.qJetBox,
   E8TAxisZero0054GraphCenterC.qJetBox,
   E8TAxisZero0054GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0054GraphWholeA.qJetBox,
   E8TAxisZero0054GraphWholeB.qJetBox,
   E8TAxisZero0054GraphWholeC.qJetBox,
   E8TAxisZero0054GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨68338767472153433756443269714678012397945982985, 68338767472153433756443269714678359599658167768⟩
  | 0, 2 => ⟨191806283654251001506349806525171799741479633704, 191806283654251001506349806525173256794124588221⟩
  | 1, 1 => ⟨191883413034513163186160181390805598688804563931, 191883413034513163186160181390808304796047730671⟩
  | 0, 3 => ⟨370194658668843790402236315381523936498694607014, 370194658668843790402236315381528873004418045268⟩
  | 1, 2 => ⟨493689456032832120757908586880269132519552633987, 493689456032832120757908586880278192711874111432⟩
  | 2, 1 => ⟨493865029410413975509260617116206859882161725967, 493865029410413975509260617116223615676541142871⟩
  | 0, 4 => ⟨596511974235879197968736664016942080018061639613, 596511974235879197968736664016959697932080900493⟩
  | 1, 3 => ⟨877532125892542969073902582569981667065840144890, 877532125892542969073902582570014280802453487891⟩
  | 2, 2 => ⟨1158633364785251811237936118856408493998284101928, 1158633364785251811237936118856469366491551106893⟩
  | 3, 1 => ⟨1159001023912727462787389760832592099558896275652, 1159001023912727462787389760832706458998023647409⟩
  | 0, 5 => ⟨-3467924533385501413831667239917031888298811964512900, 3484427728664590633377551810819119754753500369995975⟩
  | 1, 4 => ⟨-6816803727609616668852300727837313608045452706496295, 6841635681513097375351462827895161416681906437098814⟩
  | 2, 3 => ⟨-13411538881329871522755095026159175296076910038233333, 13447251951552539632403270889674076379979192395277688⟩
  | 3, 2 => ⟨-26402907040256078815827385147137384524239355069955104, 26449638765554815832520657685649423118846055101862574⟩
  | 4, 1 => ⟨-52005661054863516901021928182736131652966686010559775, 52053053789909067007741074086868477771024797915602922⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0054Geometry.ds, E8TAxisZero0054Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 64441880823322261084780530717356528073029028545 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0054CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0055CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0055CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0055GraphCenterA.qJetBox,
   E8TAxisZero0055GraphCenterB.qJetBox,
   E8TAxisZero0055GraphCenterC.qJetBox,
   E8TAxisZero0055GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0055GraphWholeA.qJetBox,
   E8TAxisZero0055GraphWholeB.qJetBox,
   E8TAxisZero0055GraphWholeC.qJetBox,
   E8TAxisZero0055GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨61753077020167642274334991504473117803919244573, 61753077020167642274334991504473431078388383150⟩
  | 0, 2 => ⟨174793557628264876350497245356575910137452792085, 174793557628264876350497245356577217369711201796⟩
  | 1, 1 => ⟨174864609195234492330313866568805656370748827698, 174864609195234492330313866568808080270624271093⟩
  | 0, 3 => ⟨339859619860307553784413760973262603281797834118, 339859619860307553784413760973267017004748912023⟩
  | 1, 2 => ⟨453623540179298840684308300397138739782660987660, 453623540179298840684308300397146827392634008698⟩
  | 2, 1 => ⟨453786362364031035924090797338499822072880512582, 453786362364031035924090797338514756518350946721⟩
  | 0, 4 => ⟨550876646257127822495745384907821238515259221815, 550876646257127822495745384907836913283523257647⟩
  | 1, 3 => ⟨811487676072065634820143314755709652549807815818, 811487676072065634820143314755738629888385713375⟩
  | 2, 2 => ⟨1072174312979443684685733659278938228411852335537, 1072174312979443684685733659278992246617252672636⟩
  | 3, 1 => ⟨1072516585949891896688206366161180817901046875548, 1072516585949891896688206366161282179552705787202⟩
  | 0, 5 => ⟨-3130505165987365064688809377356624617008839816778846, 3145687836971694260440937411223642647199713093356042⟩
  | 1, 4 => ⟨-6151026934272061686217448080275719494953837023908847, 6173879595033742309469681761444200929714914840278993⟩
  | 2, 3 => ⟨-12096767141343389830616039350133231709443623456198441, 12129643337439623900645521564840926841687500883256318⟩
  | 3, 2 => ⟨-23804884375541926210116301507595110311277399127561447, 23847914148161313317707066770581207396509024764067302⟩
  | 4, 1 => ⟨-46869174338584956510366256180686096859080088585519578, 46912826243159379315971328575511310440475932122221179⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0055Geometry.ds, E8TAxisZero0055Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 58203590635544972915555873791556468981590664576 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0055CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0056CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0056CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0056GraphCenterA.qJetBox,
   E8TAxisZero0056GraphCenterB.qJetBox,
   E8TAxisZero0056GraphCenterC.qJetBox,
   E8TAxisZero0056GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0056GraphWholeA.qJetBox,
   E8TAxisZero0056GraphWholeB.qJetBox,
   E8TAxisZero0056GraphWholeC.qJetBox,
   E8TAxisZero0056GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨55753775917154727762522297773301751087340661164, 55753775917154727762522297773302033839042494203⟩
  | 0, 2 => ⟨159166204655631512674760297761453535169146756621, 159166204655631512674760297761454708044902718061⟩
  | 1, 1 => ⟨159231620643579506138041970834768071286241740442, 159231620643579506138041970834770242403280688574⟩
  | 0, 3 => ⟨311812876083434107205996841765844642150829425693, 311812876083434107205996841765848588218053891904⟩
  | 1, 2 => ⟨416553934531401369716510213545160325695700001082, 416553934531401369716510213545167544380228400064⟩
  | 2, 1 => ⟨416704886180044857731837542484061459205644023821, 416704886180044857731837542484074768417139241022⟩
  | 0, 4 => ⟨508516170349019946342640223529550644793377795585, 508516170349019946342640223529564588492637790216⟩
  | 1, 3 => ⟨750127622702225419019617311082990252716998710818, 750127622702225419019617311083015993989343057331⟩
  | 2, 2 => ⟨991809579238144510956739425031719938649082185763, 991809579238144510956739425031767863305687600776⟩
  | 3, 1 => ⟨992128207603707118328341750007500428371334117358, 992128207603707118328341750007590246287336817680⟩
  | 0, 5 => ⟨-2816726760048646268510671464212267481267599785747842, 2830661340088995407958001986967780590076034980588366⟩
  | 1, 4 => ⟨-5532075186878927236998878360620227146243487237772585, 5553054098124752792012737161990516259732840102262263⟩
  | 2, 3 => ⟨-10874834876228785204233039451140877992514203344092905, 10905022014916801754732687721624832862669141360969422⟩
  | 3, 2 => ⟨-21391073777971561077356892314378858724585729023872535, 21430591441657235945666564717415557100379265606943309⟩
  | 4, 1 => ⟨-42098438668376946940499723350930301929696278431178290, 42138539242065596331844103976331073003927362149864695⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0056Geometry.ds, E8TAxisZero0056Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 52523694141161441458133961593037863478522326089 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0056CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0057CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0057CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0057GraphCenterA.qJetBox,
   E8TAxisZero0057GraphCenterB.qJetBox,
   E8TAxisZero0057GraphCenterC.qJetBox,
   E8TAxisZero0057GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0057GraphWholeA.qJetBox,
   E8TAxisZero0057GraphWholeB.qJetBox,
   E8TAxisZero0057GraphWholeC.qJetBox,
   E8TAxisZero0057GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨50292950542781581822696111275589331931987285248, 50292950542781581822696111275589587217952363514⟩
  | 0, 2 => ⟨144820388083821800637559090791923593709938080761, 144820388083821800637559090791924646090487121088⟩
  | 1, 1 => ⟨144880580177229249158443149968387806350422890704, 144880580177229249158443149968389751035984677256⟩
  | 0, 3 => ⟨285891972846047921289304396683751073600521368052, 285891972846047921289304396683754601335518258498⟩
  | 1, 2 => ⟨382269274710023931344328353927515167333379116831, 382269274710023931344328353927521609742809240933⟩
  | 2, 1 => ⟨382409176034381270993937244845957312620997508290, 382409176034381270993937244845969171714728816160⟩
  | 0, 4 => ⟨469203202091130521826475411953711132772807558968, 469203202091130521826475411953723534488638058524⟩
  | 1, 3 => ⟨693127876544815303472092116602506405769297809853, 693127876544815303472092116602529267596091054592⟩
  | 2, 2 => ⟨917118303419674623533817575931826368135380091958, 917118303419674623533817575931868876352544590834⟩
  | 3, 1 => ⟨917414910794681029539402139423131907973793700702, 917414910794681029539402139423211475283855000568⟩
  | 0, 5 => ⟨-2526865153099749708611107556336553464170117393156767, 2539630679311372988673776363604503507972755020894912⟩
  | 1, 4 => ⟨-4960523317521657285085448618744905012718060645407483, 4979745179174078446875796556006176113957288622814205⟩
  | 2, 3 => ⟨-9746930357168370410619217506442807296800132770224306, 9774593512497607177486547089370782993629045537650692⟩
  | 3, 2 => ⟨-19163917872734623259284395356867458207721148985236711, 19200136360002726905103056778383686683441283272563790⟩
  | 4, 1 => ⟨-37698453177977133400001463411735783117410395665525994, 37735213921620468279411240486498052198057194105575977⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0057Geometry.ds, E8TAxisZero0057Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 47356222630761988036345865925256367159289364952 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0057CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0058CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0058CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0058GraphCenterA.qJetBox,
   E8TAxisZero0058GraphCenterB.qJetBox,
   E8TAxisZero0058GraphCenterC.qJetBox,
   E8TAxisZero0058GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0058GraphWholeA.qJetBox,
   E8TAxisZero0058GraphWholeB.qJetBox,
   E8TAxisZero0058GraphWholeC.qJetBox,
   E8TAxisZero0058GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨45326286676792731968752559095120986349582130042, 45326286676792731968752559095121216915367178320⟩
  | 0, 2 => ⟨131659601609858516211286426294811030894447088269, 131659601609858516211286426294811975205917469076⟩
  | 1, 1 => ⟨131714953041115410618617489840198833421979485297, 131714953041115410618617489840200575277320262589⟩
  | 0, 3 => ⟨261945706030751165428059335812423634508410260709, 261945706030751165428059335812426788043887890706⟩
  | 1, 2 => ⟨350572805080980355856909530782287525210867793641, 350572805080980355856909530782293274159162121856⟩
  | 2, 1 => ⟨350702419952091900963983708120123764251272724234, 350702419952091900963983708120134329592347260817⟩
  | 0, 4 => ⟨432725663529562040297730208136822977884003233890, 432725663529562040297730208136834006204163964078⟩
  | 1, 3 => ⟨640186183578417554635473363361249300200669465565, 640186183578417554635473363361269600260672061263⟩
  | 2, 2 => ⟨847708031005236784296330911183643238140526614385, 847708031005236784296330911183680932575294607027⟩
  | 3, 1 => ⟨847984130450452159630791923212320028400148095323, 847984130450452159630791923212390495071994486000⟩
  | 0, 5 => ⟨-2262762912741137706792647677712033681725153824729062, 2274464636244954084429661213257571727508687624647101⟩
  | 1, 4 => ⟨-4439957296957182862062921800181492039433027359663715, 4457581682218583459296045264313480629489879928063374⟩
  | 2, 3 => ⟨-8720023996791947345087103137284689826712798718341804, 8745394457385936728409906752083191570129604571453378⟩
  | 3, 2 => ⟨-17136952067480202718209285268158170600587863566466106, 17170177063029399916252683678677346328536980163183458⟩
  | 4, 1 => ⟨-33695476848870772751539059024937053441699947846644706, 33729214850061407680941627974531000239370273051543723⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0058Geometry.ds, E8TAxisZero0058Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 42658568261308555882244374549261180618479067991 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0058CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0059CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0059CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0059GraphCenterA.qJetBox,
   E8TAxisZero0059GraphCenterB.qJetBox,
   E8TAxisZero0059GraphCenterC.qJetBox,
   E8TAxisZero0059GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0059GraphWholeA.qJetBox,
   E8TAxisZero0059GraphWholeB.qJetBox,
   E8TAxisZero0059GraphWholeC.qJetBox,
   E8TAxisZero0059GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨40812815209178769767814010156994993772457886478, 40812815209178769767814010156995202084347440232⟩
  | 0, 2 => ⟨119594162232682154688838696788312808461478768677, 119594162232682154688838696788313655844599594185⟩
  | 1, 1 => ⟨119645029736953803245423901775431030943486679290, 119645029736953803245423901775432591108583922729⟩
  | 0, 3 => ⟨239833362004871322997141743309367422569098084005, 239833362004871322997141743309370241394680457014⟩
  | 1, 2 => ⟨321281390204908063372973805633342397447798689826, 321281390204908063372973805633347526957770241543⟩
  | 2, 1 => ⟨321401430000680590618315705417587865957464726876, 321401430000680590618315705417597277166182196404⟩
  | 0, 4 => ⟨398885788539860075410673702914906217256206590305, 398885788539860075410673702914916022506662193909⟩
  | 1, 3 => ⟨591020759721121337967344528927428458343898612263, 591020759721121337967344528927446479649453481831⟩
  | 2, 2 => ⟨783212937071959176180448455189709931114939012672, 783212937071959176180448455189743348196639892356⟩
  | 3, 1 => ⟨783469937995685078965529827041808074223080173208, 783469937995685078965529827041870462972939522715⟩
  | 0, 5 => ⟨-2025583247389283071271398228171439211058968386291969, 2036319607415345374605078968707161828478552914413882⟩
  | 1, 4 => ⟨-3972641450835035956505312756299614892392311469555321, 3988817834054549928274196499830205772610102153222400⟩
  | 2, 3 => ⟨-7798516234187920478103055648200834354134107932227274, 7821811286327507889002868527805409034904878456530772⟩
  | 3, 2 => ⟨-15318716190122962238190459120732397938498416203619795, 15349236647671849072145348102471392944166573621867759⟩
  | 4, 1 => ⟨-30106061088506129069711541632856285934654254406688294, 30137081417592413792091407629968054445333627533615801⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0059Geometry.ds, E8TAxisZero0059Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 38391384858587715907951667115318418829378414484 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0059CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0060CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0060CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0060GraphCenterA.qJetBox,
   E8TAxisZero0060GraphCenterB.qJetBox,
   E8TAxisZero0060GraphCenterC.qJetBox,
   E8TAxisZero0060GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0060GraphWholeA.qJetBox,
   E8TAxisZero0060GraphWholeB.qJetBox,
   E8TAxisZero0060GraphWholeC.qJetBox,
   E8TAxisZero0060GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨36714675452489479789274688732009167406519013365, 36714675452489479789274688732009355680355643610⟩
  | 0, 2 => ⟨108540737610274799584172208442047574823514297798, 108540737610274799584172208442048335267603681096⟩
  | 1, 1 => ⟨108587453246453028432214339460329279427451848584, 108587453246453028432214339460330676839234917168⟩
  | 0, 3 => ⟨219424005157859785369309735990683932088481311449, 219424005157859785369309735990686451929622155667⟩
  | 1, 2 => ⟨294224587990371715446797340190618640865276332149, 294224587990371715446797340190623217880914661730⟩
  | 2, 1 => ⟨294335715203273551887566526869851857051352356074, 294335715203273551887566526869860240351450528092⟩
  | 0, 4 => ⟨367499231374093134582773206532174882487922506933, 367499231374093134582773206532183603248442982229⟩
  | 1, 3 => ⟨545369015362674696994816187250424493936414203483, 545369015362674696994816187250440497460386902706⟩
  | 2, 2 => ⟨723292166710089742682550707706393456520973711284, 723292166710089742682550707706423090956575286772⟩
  | 3, 1 => ⟨723531381326557992649045047481450612992195899017, 723531381326557992649045047481505866900809841835⟩
  | 0, 5 => ⟨-1806986695079292406807006419239721188208038108298879, 1816774981980161254559363213200946389791224126871428⟩
  | 1, 4 => ⟨-3542091158057614633174295097662470994553214440201841, 3556842419701673459139069344264980927415044613036028⟩
  | 2, 3 => ⟨-6949818311135080644478896891001070350728910594000734, 6971067294297320126088113603342315746995284362932356⟩
  | 3, 2 => ⟨-13644779214423962707366839956774846101305191941435821, 13672628868402996427818138944711697136804766178450501⟩
  | 4, 1 => ⟨-26802807922526155755567151684782910856120656897322198, 26831131953317916688249969957055582881308968846164711⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0060Geometry.ds, E8TAxisZero0060Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 34518986217367246670851682825507631372627740557 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0060CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0061CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0061CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0061GraphCenterA.qJetBox,
   E8TAxisZero0061GraphCenterB.qJetBox,
   E8TAxisZero0061GraphCenterC.qJetBox,
   E8TAxisZero0061GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0061GraphWholeA.qJetBox,
   E8TAxisZero0061GraphWholeB.qJetBox,
   E8TAxisZero0061GraphWholeC.qJetBox,
   E8TAxisZero0061GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨32996894858524381416376347396726187357745522279, 32996894858524381416376347396726357584744604670⟩
  | 0, 2 => ⟨98421905677106400575738240546526432473786752799, 98421905677106400575738240546527114969188687353⟩
  | 1, 1 => ⟨98464778523190855341180008153931596862296940693, 98464778523190855341180008153932848550653511634⟩
  | 0, 3 => ⟨200595809777887946150902244260533113360306025065, 200595809777887946150902244260535366138443643669⟩
  | 1, 2 => ⟨269243780546250008248017553023896712924315940724, 269243780546250008248017553023900797170525977771⟩
  | 2, 1 => ⟨269346612166268032162294491290241833143170686433, 269346612166268032162294491290249300973330142068⟩
  | 0, 4 => ⟨338394232981279542370528629044664212932149089250, 338394232981279542370528629044671970585938768793⟩
  | 1, 3 => ⟨502986361993089910312821267297008026917258018751, 502986361993089910312821267297022240820234878886⟩
  | 2, 2 => ⟨667628281869047508505431340521700920642882473922, 667628281869047508505431340521727204187930413401⟩
  | 3, 1 => ⟨667850931253718069057509578216164899153800590430, 667850931253718069057509578216213839946517017783⟩
  | 0, 5 => ⟨-1606457244125431067917776890186167293636780081005098, 1615333779523060459982739364306050536536389490460685⟩
  | 1, 4 => ⟨-3147288456089782220961260505882026950635611763134877, 3160665402952886409298499760209891307752296870992475⟩
  | 2, 3 => ⟨-6171912593085597853822239708978579644228417527475386, 6191184248060067532566299470836152714118348580422997⟩
  | 3, 2 => ⟨-12111127317475279201705194924050458564327612704714701, 12136392451246193192182208527135793944718332853588153⟩
  | 4, 1 => ⟨-23777708171158887797188239591464361254120059756070023, 23803421144189063438170772888919636349019931259394779⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0061Geometry.ds, E8TAxisZero0061Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 31007904497442637104584750307496455695273289085 := by decide

theorem centerEnclosed_of_contains {s t : ℝ} (h : centerBoxes.ContainsRegularAt s t) :
    data.CenterEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← center_0_1_checked]
    exact InverseBoxes.coeff_regular_sound h 0 1
  · rw [← center_0_2_checked]
    exact InverseBoxes.coeff_regular_sound h 0 2
  · rw [← center_1_1_checked]
    exact InverseBoxes.coeff_regular_sound h 1 1
  · rw [← center_0_3_checked]
    exact InverseBoxes.coeff_regular_sound h 0 3
  · rw [← center_1_2_checked]
    exact InverseBoxes.coeff_regular_sound h 1 2
  · rw [← center_2_1_checked]
    exact InverseBoxes.coeff_regular_sound h 2 1
  · rw [← center_0_4_checked]
    exact InverseBoxes.coeff_regular_sound h 0 4
  · rw [← center_1_3_checked]
    exact InverseBoxes.coeff_regular_sound h 1 3
  · rw [← center_2_2_checked]
    exact InverseBoxes.coeff_regular_sound h 2 2
  · rw [← center_3_1_checked]
    exact InverseBoxes.coeff_regular_sound h 3 1

theorem wholeEnclosed_of_contains {s t : ℝ} (h : wholeBoxes.ContainsRegularAt s t) :
    data.RemainderEnclosed (mixed E8TAxisRegularGermJet.regularQJet s t) := by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · rw [← whole_0_5_checked]
    exact InverseBoxes.coeff_regular_sound h 0 5
  · rw [← whole_1_4_checked]
    exact InverseBoxes.coeff_regular_sound h 1 4
  · rw [← whole_2_3_checked]
    exact InverseBoxes.coeff_regular_sound h 2 3
  · rw [← whole_3_2_checked]
    exact InverseBoxes.coeff_regular_sound h 3 2
  · rw [← whole_4_1_checked]
    exact InverseBoxes.coeff_regular_sound h 4 1

#print axioms center_0_1_checked
#print axioms whole_4_1_checked
#print axioms replay_positive
#print axioms centerEnclosed_of_contains
end GeneralCK.Certificates.E8TAxisZero0061CertifiedArithmetic

end


