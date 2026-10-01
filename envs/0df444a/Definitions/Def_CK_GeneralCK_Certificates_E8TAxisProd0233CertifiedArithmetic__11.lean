-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0233CertifiedArithmetic__11
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0233CertifiedArithmetic__11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:43:41.08589+00:00
-- url     : https://prove2.me/theorems/7f6816c2-5370-4bc9-b643-6aa52f0da191
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0233CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0234CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0233CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0234CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0235CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0236CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0237CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0238CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0239CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0240CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0241CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0242CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0243CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0233CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0234CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0235CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0236CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0237CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0238CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0239CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0240CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0241CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0242CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0243CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0233CertifiedArithmetic (+10 modules: GeneralCK.Certificates.E8TAxisProd0234CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0235CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0236CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0237CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0238CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0239CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0240CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0241CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0242CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0243CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0233CertifiedArithmetic (+10 modules: GeneralCK/Certificates/E8TAxisProd0234CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0235CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0236CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0237CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0238CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0239CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0240CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0241CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0242CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0243CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0230GraphCenterA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0221GraphCenterB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0223GraphCenterC__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0231GraphCenterD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0231GraphWholeA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0230GraphWholeB__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0226GraphWholeC__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0231GraphWholeD__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0216Geometry__18
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0234Geometry__23
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0235GraphCenterB__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0236GraphWholeC__6
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0238GraphCenterC__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0238GraphWholeB__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0238GraphWholeD__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0241GraphCenterA__4
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0241GraphCenterD__6
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0242GraphCenterB__5
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0242GraphWholeA__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0242GraphWholeC__11

-- ===== source module GeneralCK.Certificates.E8TAxisProd0233CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0233CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0233GraphCenterA.qJetBox,
   E8TAxisProd0233GraphCenterB.qJetBox,
   E8TAxisProd0233GraphCenterC.qJetBox,
   E8TAxisProd0233GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0233GraphWholeA.qJetBox,
   E8TAxisProd0233GraphWholeB.qJetBox,
   E8TAxisProd0233GraphWholeC.qJetBox,
   E8TAxisProd0233GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨58381761615810422251633682463414156396441021233, 58381761615810422251633682463414454778967326673⟩
  | 0, 2 => ⟨164300834725488454378337837154870453769727166689, 164300834725488454378337837154871673264673898534⟩
  | 1, 1 => ⟨166100478861941499708538863939788608660516162123, 166100478861941499708538863939790851180149372357⟩
  | 0, 3 => ⟨320174436582893260983062152563797328107640392212, 320174436582893260983062152563801418154185508446⟩
  | 1, 2 => ⟨428894527463638492011175995101769305805009150730, 428894527463638492011175995101776753217066914350⟩
  | 2, 1 => ⟨433040718106508358115979357266552226796268619519, 433040718106508358115979357266565944290900284504⟩
  | 0, 4 => ⟨520642730584113882142891466514531443216297911328, 520642730584113882142891466514545881849646340765⟩
  | 1, 3 => ⟨768784048795429296036161482390617699379703784495, 768784048795429296036161482390644268324591275564⟩
  | 2, 2 => ⟨1018859290371688007637744302579727252318490716257, 1018859290371688007637744302579776684272013902466⟩
  | 3, 1 => ⟨1027602700352101961901016716131680658722328770013, 1027602700352101961901016716131773293341746377928⟩
  | 0, 5 => ⟨-2897705652303584132284849926583536477606115772720289, 2911967328820446102562404023735095806660243391126541⟩
  | 1, 4 => ⟨-5691305196600748430506637867745356088379739614104576, 5712815220134811246373469752258038350685531843013967⟩
  | 2, 3 => ⟨-11188376901359692030571935307294606634742726336721716, 11219401554183695911609751525638433839311441532456367⟩
  | 3, 2 => ⟨-22009018950633561112405591127257591784346623721039102, 22049801129165219540449524163168713019544759348694197⟩
  | 4, 1 => ⟨-43317128723685115377242158700492543253984235859475048, 43358998813002462073773781592295945235440474075477077⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0233Geometry.ds, E8TAxisProd0233Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 55016545795947776349589044283716854484918655599 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0233CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0234CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0234CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0234GraphCenterA.qJetBox,
   E8TAxisProd0234GraphCenterB.qJetBox,
   E8TAxisProd0234GraphCenterC.qJetBox,
   E8TAxisProd0234GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0234GraphWholeA.qJetBox,
   E8TAxisProd0234GraphWholeB.qJetBox,
   E8TAxisProd0234GraphWholeC.qJetBox,
   E8TAxisProd0234GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨64413526146596547876556526956356632039984251614, 64413526146596547876556526956356961398903469792⟩
  | 0, 2 => ⟨179953875773750331465934431087464055363122470814, 179953875773750331465934431087465410583667186046⟩
  | 1, 1 => ⟨181760946266325796199805400756450512320095096934, 181760946266325796199805400756453009683540340913⟩
  | 0, 3 => ⟨348212964594823477155086410967638240261441124530, 348212964594823477155086410967642802433892048462⟩
  | 1, 2 => ⟨465934414256958903840326047029533752067987834285, 465934414256958903840326047029542075576877714700⟩
  | 2, 1 => ⟨470069650678945850952303581295931077387282309285, 470069650678945850952303581295946433227007093693⟩
  | 0, 4 => ⟨562942742919766569170978553604161868518590133366, 562942742919766569170978553604178055252754746578⟩
  | 1, 3 => ⟨830025781349044540767186197596680282719676977271, 830025781349044540767186197596710116865172503058⟩
  | 2, 2 => ⟨1099026799953928762185142438451839919204524772396, 1099026799953928762185142438451895499034911313601⟩
  | 3, 1 => ⟨1107712423358382414251693324517955311060088757213, 1107712423358382414251693324518059593396223594358⟩
  | 0, 5 => ⟨-3211041413724729685341220921911890389313371865691695, 3226547281151593991456249624032365091428120252731876⟩
  | 1, 4 => ⟨-6309402899943687244693299007930461818358780791926793, 6332782278124924184809061463014682692655989749734008⟩
  | 2, 3 => ⟨-12408669558368262938918299379721562524661911641402776, 12442379715185736654933045013899070342735549325402962⟩
  | 3, 2 => ⟨-24419692452188181062678311118807275226656586874964291, 24463988080585214471114195524346510580607695018383450⟩
  | 4, 1 => ⟨-48081880296846292275937748654500327764420089963869987, 48127319046101154510665904069615211653149443029813866⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0234Geometry.ds, E8TAxisProd0234Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 60728432875462199864618140049316895969934888791 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0234CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0235CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0235CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0235GraphCenterA.qJetBox,
   E8TAxisProd0235GraphCenterB.qJetBox,
   E8TAxisProd0235GraphCenterC.qJetBox,
   E8TAxisProd0235GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0235GraphWholeA.qJetBox,
   E8TAxisProd0235GraphWholeB.qJetBox,
   E8TAxisProd0235GraphWholeC.qJetBox,
   E8TAxisProd0235GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨58176635539278798075205328724652459591693101392, 58176635539278798075205328724652757351814968560⟩
  | 0, 2 => ⟨163901023186436618230098633927813188671903182529, 163901023186436618230098633927814405492546113397⟩
  | 1, 1 => ⟨165564960937396662769099846344440709208818033368, 165564960937396662769099846344442946770221897770⟩
  | 0, 3 => ⟨319524222183551022212223362186865718438633881522, 319524222183551022212223362186869799327300625458⟩
  | 1, 2 => ⟨427934453881116974804215489345320003970703650834, 427934453881116974804215489345327434589002915975⟩
  | 2, 1 => ⟨431768458866565075043138720916634362541436660271, 431768458866565075043138720916648048901650031528⟩
  | 0, 4 => ⟨519700569712976357602122382780001832821245143526, 519700569712976357602122382780016237695425123395⟩
  | 1, 3 => ⟨767334098250206446674736752529402096033024279073, 767334098250206446674736752529428602664184647518⟩
  | 2, 2 => ⟨1016756120726232571966712527427388090911458116191, 1016756120726232571966712527427437406530916216834⟩
  | 3, 1 => ⟨1024841789776329227240092707252530617503264236265, 1024841789776329227240092707252623033284742863338⟩
  | 0, 5 => ⟨-2891450779130402211106028506448880291552479137429853, 2905682648602854551149569854705444956789462695013135⟩
  | 1, 4 => ⟨-5678986910521155764787114261577953379253498035497349, 5700450582557287350204322661563562057998495408569014⟩
  | 2, 3 => ⟨-11164092258159748905063933389496456476529205329175465, 11195046330569085780780110709427211738140387379761778⟩
  | 3, 2 => ⟨-21961108756291041203451832473450537126676835809573366, 22001787160546809865271172380012072221750501883667174⟩
  | 4, 1 => ⟨-43222555111785886243792037982993847365547827489752846, 43264282703684420834149686965163314926541092546538005⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0235Geometry.ds, E8TAxisProd0235Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 54821952588960358816497615363556829503518236917 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0235CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0236CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0236CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0236GraphCenterA.qJetBox,
   E8TAxisProd0236GraphCenterB.qJetBox,
   E8TAxisProd0236GraphCenterC.qJetBox,
   E8TAxisProd0236GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0236GraphWholeA.qJetBox,
   E8TAxisProd0236GraphWholeB.qJetBox,
   E8TAxisProd0236GraphWholeC.qJetBox,
   E8TAxisProd0236GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨52684366079497059032146505407092259426429204204, 52684366079497059032146505407092529297286628965⟩
  | 0, 2 => ⟨149528574010988109759348705068579419427171386633, 149528574010988109759348705068580514495988613639⟩
  | 1, 1 => ⟨151184728119229980185712808247469943462912991450, 151184728119229980185712808247471952725792411488⟩
  | 0, 3 => ⟨293607498926505541707967529692347658079267269441, 293607498926505541707967529692351316565291125854⟩
  | 1, 2 => ⟨393672745452378618277901029539334832323753923342, 393672745452378618277901029539341480206397195175⟩
  | 2, 1 => ⟨397515705496303515895485617887567753124071563912, 397515705496303515895485617887579977597519816947⟩
  | 0, 4 => ⟨480440668175657871887025676239090857743151779197, 480440668175657871887025676239103705245918177872⟩
  | 1, 3 => ⟨710440814170635325837799975113502591306074048866, 710440814170635325837799975113526192368296252516⟩
  | 2, 2 => ⟨942244500983306225652668394018380245894661154514, 942244500983306225652668394018424096479204717026⟩
  | 3, 1 => ⟨950383697946750307181837103545467238327846100366, 950383697946750307181837103545549310584214546411⟩
  | 0, 5 => ⟨-2601394445949302013420720907074089652323780199844314, 2614460647068532039232021922234384200693419649154948⟩
  | 1, 4 => ⟨-5107020592884154738598965165914241843322521438659200, 5126731195048974214580059123618392149687359956402904⟩
  | 2, 3 => ⟨-10035303088331566650278283277177188258100529842183625, 10063736738254602453336244874304908010049995413405408⟩
  | 3, 2 => ⟨-19732066793571558257948239815424464066629676808774079, 19769445930749675089767177707003104759126604261720761⟩
  | 4, 1 => ⟨-38818557513957835007665195367663735565498767036805689, 38856932431843212835654746668736983277082679814612248⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0236Geometry.ds, E8TAxisProd0236Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 49623589381060045529350562912565304223455011966 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0236CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0237CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0237CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0237GraphCenterA.qJetBox,
   E8TAxisProd0237GraphCenterB.qJetBox,
   E8TAxisProd0237GraphCenterC.qJetBox,
   E8TAxisProd0237GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0237GraphWholeA.qJetBox,
   E8TAxisProd0237GraphWholeB.qJetBox,
   E8TAxisProd0237GraphWholeC.qJetBox,
   E8TAxisProd0237GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨47500651543268090028469420758662872289115382895, 47500651543268090028469420758663116481602449785⟩
  | 0, 2 => ⟨135973808332344127388143269856194290500292371636, 135973808332344127388143269856195273940772195506⟩
  | 1, 1 => ⟨137496988683656624811302658614868385043928221864, 137496988683656624811302658614870185332999604747⟩
  | 0, 3 => ⟨269061778423976834626858449518364071045326454188, 269061778423976834626858449518367343416154262636⟩
  | 1, 2 => ⟨361105854590403031255509046738149722550687262812, 361105854590403031255509046738155656124682420408⟩
  | 2, 1 => ⟨364666543260694955726834973725584821195846707341, 364666543260694955726834973725595713528857325907⟩
  | 0, 4 => ⟨443136398110318292484129287527925743402822574106, 443136398110318292484129287527937173475146641663⟩
  | 1, 3 => ⟨656249202059210257305431154097885815789735638057, 656249202059210257305431154097906776127345717075⟩
  | 2, 2 => ⟨871044131084608200625262831146730568304026147747, 871044131084608200625262831146769458070879753538⟩
  | 3, 1 => ⟨878620625958685502497005971297386820698590565090, 878620625958685502497005971297459514637976236938⟩
  | 0, 5 => ⟨-2328920348614749744655939546343522363896324976266941, 2340879819164021142883779229803939276898395104199558⟩
  | 1, 4 => ⟨-4569937302800103914977058526394220739688916736458071, 4587981607839787966791457107384326033889427819175224⟩
  | 2, 3 => ⟨-8975778350450481309846414583074797867182973341646389, 9001812600227474838394488090394559215432045211306552⟩
  | 3, 2 => ⟨-17640645038832625881821605043469282160616888380153642, 17674874026404160904993417523988785291180131858480679⟩
  | 4, 1 => ⟨-34688148497819218982769547317617062010732620608363682, 34723293197269593644845343543085810436737008870366963⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0237Geometry.ds, E8TAxisProd0237Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 44719303567254000237578761706033573697720626233 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0237CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0238CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0238CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0238GraphCenterA.qJetBox,
   E8TAxisProd0238GraphCenterB.qJetBox,
   E8TAxisProd0238GraphCenterC.qJetBox,
   E8TAxisProd0238GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0238GraphWholeA.qJetBox,
   E8TAxisProd0238GraphWholeB.qJetBox,
   E8TAxisProd0238GraphWholeC.qJetBox,
   E8TAxisProd0238GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨52497684586519502710985861178653663620552288785, 52497684586519502710985861178653932929156590038⟩
  | 0, 2 => ⟨149161939754135668979451582050164262390974817115, 149161939754135668979451582050165355055341006123⟩
  | 1, 1 => ⟨150693191868741995621737296103208645982968902106, 150693191868741995621737296103210650795083679701⟩
  | 0, 3 => ⟨293007493934560272784133560877344266624136266370, 293007493934560272784133560877347916904664102452⟩
  | 1, 2 => ⟨392785535654631589044762934580785653018240410183, 392785535654631589044762934580792285876717723006⟩
  | 2, 1 => ⟨396339121264410678310083428996642755400086498378, 396339121264410678310083428996654952053608774549⟩
  | 0, 4 => ⟨479567561767467528156282517475464210587671662632, 479567561767467528156282517475477027977128993324⟩
  | 1, 3 => ⟨709095248180893220027418357876572929929087714823, 709095248180893220027418357876596475481504262494⟩
  | 2, 2 => ⟨940290853618026395239757562452233295360657879921, 940290853618026395239757562452277042419317134087⟩
  | 3, 1 => ⟨947817758487457554658402949204296922684031895078, 947817758487457554658402949204378800374179615740⟩
  | 0, 5 => ⟨-2595636162819774876362999127697285797497990531404594, 2608674779032076129191577740241385940291097627842753⟩
  | 1, 4 => ⟨-5095683905173083040814848373997738215315745858867145, 5115351637728791523023936270162154567450729757106305⟩
  | 2, 3 => ⟨-10012960832572609524477491692072876922395394672511731, 10041329314331883617977291783840866064842120763265885⟩
  | 3, 2 => ⟨-19688003111918595260784357318553836709323371771982327, 19725286776325740504902170633481921837283832359354981⟩
  | 4, 1 => ⟨-38731605696286580593013968051087498826471581497210546, 38769850505539074164758556370154419943516779588680078⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0238Geometry.ds, E8TAxisProd0238Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 49446577696060953865783204704683357449362112022 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0238CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0239CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0239CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0239GraphCenterA.qJetBox,
   E8TAxisProd0239GraphCenterB.qJetBox,
   E8TAxisProd0239GraphCenterC.qJetBox,
   E8TAxisProd0239GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0239GraphWholeA.qJetBox,
   E8TAxisProd0239GraphWholeB.qJetBox,
   E8TAxisProd0239GraphWholeC.qJetBox,
   E8TAxisProd0239GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨47330894343182784988223287043558138659304039454, 47330894343182784988223287043558382343709622186⟩
  | 0, 2 => ⟨135637827098887669402808151466885132974991886384, 135637827098887669402808151466886114253420253647⟩
  | 1, 1 => ⟨137046118734850630902369415531486119222341082513, 137046118734850630902369415531487915516028797994⟩
  | 0, 3 => ⟨268508363625866526534004366389453107130188721742, 268508363625866526534004366389456372148825276531⟩
  | 1, 2 => ⟨360286323592706309886822599248459288087288196304, 360286323592706309886822599248465208220946065472⟩
  | 2, 1 => ⟨363578872494282477581291699186385317144931133596, 363578872494282477581291699186396184621851726814⟩
  | 0, 4 => ⟨442327504424592755551995227147168478583767798986, 442327504424592755551995227147179881797104773782⟩
  | 1, 3 => ⟨655000753109591266280960961760769330611853204293, 655000753109591266280960961760790241507111263394⟩
  | 2, 2 => ⟨869229638071379450361649718315364301285906665365, 869229638071379450361649718315403098939552284598⟩
  | 3, 1 => ⟨876236167590560056842434799055689505296524549683, 876236167590560056842434799055762026280906295454⟩
  | 0, 5 => ⟨-2323810582971808576049277310302342298936212507297357, 2335745988363322149961879245570091683214274179607975⟩
  | 1, 4 => ⟨-4559881300459538427381971195629344658725314639120363, 4577888301920879637207672693481047187545586079020394⟩
  | 2, 3 => ⟨-8955967143033171149807977039201088202067140937988612, 8981944769529669401960326868822536899025467407627688⟩
  | 3, 2 => ⟨-17601586312922540882801772386494527038561200794137152, 17635732300555961252257399824520724334625493023820113⟩
  | 4, 1 => ⟨-34611098002509289168441584551075268008907228263472714, 34646129098113499871279609903159751742647938193110639⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0239Geometry.ds, E8TAxisProd0239Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 44558404787991840171909366856177063321011310709 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0239CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0240CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0240CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0240GraphCenterA.qJetBox,
   E8TAxisProd0240GraphCenterB.qJetBox,
   E8TAxisProd0240GraphCenterC.qJetBox,
   E8TAxisProd0240GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0240GraphWholeA.qJetBox,
   E8TAxisProd0240GraphWholeB.qJetBox,
   E8TAxisProd0240GraphWholeC.qJetBox,
   E8TAxisProd0240GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨95667932535219227574104022334634518190859798104, 95667932535219227574104022334635012166174959230⟩
  | 0, 2 => ⟨258943791152683753430563527558872207759147260036, 258943791152683753430563527558874290387208607942⟩
  | 1, 1 => ⟨261241002764799577039636263795696082201870942924, 261241002764799577039636263795699949702243952163⟩
  | 0, 3 => ⟨487231983767136077790435320851872446395150330873, 487231983767136077790435320851879554968429318090⟩
  | 1, 2 => ⟨649603334647916714240592085540951703190279301730, 649603334647916714240592085540964767630567575503⟩
  | 2, 1 => ⟨654730894802668857593545993639964139021142594935, 654730894802668857593545993639988388064658353053⟩
  | 0, 4 => ⟨770523042382174871059834362298697416739054626777, 770523042382174871059834362298723133423970731830⟩
  | 1, 3 => ⟨1130204405246938610888041091181649305499187193847, 1130204405246938610888041091181696989285366731802⟩
  | 2, 2 => ⟨1492218753263622867298598281623925089436304708254, 1492218753263622867298598281624014362163782851345⟩
  | 3, 1 => ⟨1502840944451732975254869894585130736592602347418, 1502840944451732975254869894585299010631135085049⟩
  | 0, 5 => ⟨-4732757993397444248377062337514441546653027974546331, 4754013124815766454544826818340713416734371203579928⟩
  | 1, 4 => ⟨-9313235247020638030077454908132623533670738664925671, 9345202854588001024571415062160178371164981277398767⟩
  | 2, 3 => ⟨-18343326422157853632030351367401487957514013543406714, 18389320550182265956218536042434974963576029443917476⟩
  | 3, 2 => ⟨-36152368248064867960894943109115092311534591663373640, 36212697996833564454302775706594129967398530489452261⟩
  | 4, 1 => ⟨-71289890146959634530824315761583015236752725560535405, 71351630080500980578191797707018028701113889091015310⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0240Geometry.ds, E8TAxisProd0240Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 90364819829741768178851682389338534738751588253 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0240CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0241CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0241CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0241GraphCenterA.qJetBox,
   E8TAxisProd0241GraphCenterB.qJetBox,
   E8TAxisProd0241GraphCenterC.qJetBox,
   E8TAxisProd0241GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0241GraphWholeA.qJetBox,
   E8TAxisProd0241GraphWholeB.qJetBox,
   E8TAxisProd0241GraphWholeC.qJetBox,
   E8TAxisProd0241GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨86690971055959857572295340111681940113676971290, 86690971055959857572295340111682385996853687749⟩
  | 0, 2 => ⟨236538187289808995328724516701929683322999265386, 236538187289808995328724516701931552550582744635⟩
  | 1, 1 => ⟨238657826146098994896140973363436925450574388905, 238657826146098994896140973363440390343633355303⟩
  | 0, 3 => ⟨448141311312829428987353869378179388104720957707, 448141311312829428987353869378185747243657057958⟩
  | 1, 2 => ⟨597975443055459160104701705298052504941124972126, 597975443055459160104701705298064171716355873259⟩
  | 2, 1 => ⟨602734577077050934714951207146797136639964116063, 602734577077050934714951207146818759794567968783⟩
  | 0, 4 => ⟨712453880028931220598853307162136829410405912793, 712453880028931220598853307162159726162858472091⟩
  | 1, 3 => ⟨1046297590952849455442299366680615907011469555772, 1046297590952849455442299366680658301668478214587⟩
  | 2, 2 => ⟨1382316050099007699248780918034536476263128706089, 1382316050099007699248780918034615752543748764900⟩
  | 3, 1 => ⟨1392206196573367884732647664015596161419223429234, 1392206196573367884732647664015745425999754163722⟩
  | 0, 5 => ⟨-4311927801191143083380511114239069166751259261742501, 4331620803341858747721054402161043562676773724430249⟩
  | 1, 4 => ⟨-8482244662176804704238464525513997786464212884433926, 8511887122995300192259595073411347168507603926826177⟩
  | 2, 3 => ⟨-16700940695220805515940379321915780256745515549477842, 16743618305770152623312487991597459122225519451659011⟩
  | 3, 2 => ⟨-32904154399571388620052738257751466323277183355916790, 32960162435752225947879439580009210538437893132199746⟩
  | 4, 1 => ⟨-64862111916190144270493079147589340891600003026655679, 64919459810445942900778901375165824732304350906945791⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0241Geometry.ds, E8TAxisProd0241Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 81846710880900379220561778833592353853875849526 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0241CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0242CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0242CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0242GraphCenterA.qJetBox,
   E8TAxisProd0242GraphCenterB.qJetBox,
   E8TAxisProd0242GraphCenterC.qJetBox,
   E8TAxisProd0242GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0242GraphWholeA.qJetBox,
   E8TAxisProd0242GraphWholeB.qJetBox,
   E8TAxisProd0242GraphWholeC.qJetBox,
   E8TAxisProd0242GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨95344633195555819221553079468066122073837198395, 95344633195555819221553079468066615014031026715⟩
  | 0, 2 => ⟨258335352787551380520830177767668418552798559176, 258335352787551380520830177767670496641049556159⟩
  | 1, 1 => ⟨260429881023299582074293732188048077796823313203, 260429881023299582074293732188051936819883865769⟩
  | 0, 3 => ⟨486269685567805217898848225431495333649748726787, 486269685567805217898848225431502426430255860809⟩
  | 1, 2 => ⟨648191887872208617089604668901580543375147658029, 648191887872208617089604668901593578652974199920⟩
  | 2, 1 => ⟨652867511690883451246540550904120853344463323761, 652867511690883451246540550904145048020059901266⟩
  | 0, 4 => ⟨769154451231082141599930976755374326857652603202, 769154451231082141599930976755399984089253864516⟩
  | 1, 3 => ⟨1128111028512845251482278597120348401317041116401, 1128111028512845251482278597120395974695568600849⟩
  | 2, 2 => ⟨1489195119396898687295879473092408289479239007578, 1489195119396898687295879473092497355108841426215⟩
  | 3, 1 => ⟨1498881602574874177494185977612041548669612478530, 1498881602574874177494185977612209431469280948729⟩
  | 0, 5 => ⟨-4723855992303601989514631631990370117178963220793882, 4745070283368830558533525520892801468174340199783875⟩
  | 1, 4 => ⟨-9295688344825973823679577932805268657610695652065978, 9327592784142515438674113625754993742279207368929970⟩
  | 2, 3 => ⟨-18308701252517448206924453785349394386591060162404905, 18354599260234302214550275740110870289724915333656376⟩
  | 3, 2 => ⟨-36083989904650411739104536437770827331613756696765172, 36144177266573672637458929530985685704518266193167618⟩
  | 4, 1 => ⟨-71154774089555213115546160473016872954825520151247833, 71216313915143187250849013524679403423723816213662036⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0242Geometry.ds, E8TAxisProd0242Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 90057426899792615904573317026689136370216350186 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0242CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0243CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0243CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0243GraphCenterA.qJetBox,
   E8TAxisProd0243GraphCenterB.qJetBox,
   E8TAxisProd0243GraphCenterC.qJetBox,
   E8TAxisProd0243GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0243GraphWholeA.qJetBox,
   E8TAxisProd0243GraphWholeB.qJetBox,
   E8TAxisProd0243GraphWholeC.qJetBox,
   E8TAxisProd0243GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨86395648200431876756006468950899598565119536457, 86395648200431876756006468950900043514640065027⟩
  | 0, 2 => ⟨235978566924415314195654376833090855249718159358, 235978566924415314195654376833092720397877826081⟩
  | 1, 1 => ⟨237911173755664203385750484904754382742812837085, 237911173755664203385750484904757840028346557619⟩
  | 0, 3 => ⟨447251537885236431023368172907225703925031122689, 447251537885236431023368172907232048914956942052⟩
  | 1, 2 => ⟨596668786754472139702089667322318823675128473601, 596668786754472139702089667322330464357050007979⟩
  | 2, 1 => ⟨601008439223929343425257213500320086358742566770, 601008439223929343425257213500341660918626274549⟩
  | 0, 4 => ⟨711183952730906570079871780715953883431483458730, 711183952730906570079871780715976727133610300017⟩
  | 1, 3 => ⟨1044353042393800527289403693591732281972687200183, 1044353042393800527289403693591774578224148529094⟩
  | 2, 2 => ⟨1379505347335346441009419740879083701621659206318, 1379505347335346441009419740879162793482512148629⟩
  | 3, 1 => ⟨1388524263329002106054512331202655786749786983112, 1388524263329002106054512331202804703216015159265⟩
  | 0, 5 => ⟨-4303584543708751540710835271135303893744111469500493, 4323239054836259656972973644176074234135244992096474⟩
  | 1, 4 => ⟨-8465801186648422208180370214028475208594747278929786, 8495383974256199415862608633156311029552670564983357⟩
  | 2, 3 => ⟨-16668497616003083035583762405798804017180418773129216, 16711084254109888055221509400135742219492583945619102⟩
  | 3, 2 => ⟨-32840095396697140318329671033859774589331580592234000, 32895968523130819147606844602026200598850533521348035⟩
  | 4, 1 => ⟨-64735552101204521810617737856167908433231827781571061, 64792710436262220360896350897318012711462556730140685⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0243Geometry.ds, E8TAxisProd0243Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 81566041956066486217244630235186499187933072316 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0243CertifiedArithmetic

end


