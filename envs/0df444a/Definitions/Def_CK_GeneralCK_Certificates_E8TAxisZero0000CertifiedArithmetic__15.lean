-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000CertifiedArithmetic__15
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0000CertifiedArithmetic__15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:16:06.970044+00:00
-- url     : https://prove2.me/theorems/63a291b2-d68a-4a72-91e1-15c9c8bd7559
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0000CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisZero0001CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0000CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisZero0001CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0002CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0003CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0004CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0005CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0006CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0007CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0008CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0009CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0010CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0011CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0012CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0013CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0015CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0000CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisZero0001CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0002CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0003CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0004CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0005CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0006CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0007CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0008CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0009CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0010CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0011CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0012CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0013CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0015CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0000CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisZero0001CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0002CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0003CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0004CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0005CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0006CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0007CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0008CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0009CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0010CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0011CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0012CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0013CertifiedArithmetic, GeneralCK.Certificates.E8TAxisZero0015CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0000CertifiedArithmetic (+14 modules: GeneralCK/Certificates/E8TAxisZero0001CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0002CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0003CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0004CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0005CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0006CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0007CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0008CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0009CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0010CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0011CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0012CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0013CertifiedArithmetic, GeneralCK/Certificates/E8TAxisZero0015CertifiedArithmetic).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphCenterA__21
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphCenterB__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphCenterC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphCenterD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphWholeA__20
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphWholeB__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphWholeC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000GraphWholeD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularInverseBoxes
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000Geometry__22
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0012GraphCenterC__12

-- ===== source module GeneralCK.Certificates.E8TAxisZero0000CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0000CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0000GraphCenterA.qJetBox,
   E8TAxisZero0000GraphCenterB.qJetBox,
   E8TAxisZero0000GraphCenterC.qJetBox,
   E8TAxisZero0000GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0000GraphWholeA.qJetBox,
   E8TAxisZero0000GraphWholeB.qJetBox,
   E8TAxisZero0000GraphWholeC.qJetBox,
   E8TAxisZero0000GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨64399390603600916413000350137813004866, 64399390603600916413000350818301947562⟩
  | 0, 2 => ⟨3761164507792138552219590870674733221189, 3761164507792138552219591653686983712477⟩
  | 1, 1 => ⟨4149858255084090886776366273972412567721, 4149858255084090886776366279646331507816⟩
  | 0, 3 => ⟨113010593596158381072818364669360938828527, 113010593596158381072820714245604524821604⟩
  | 1, 2 => ⟨198310090410761165665084229630380095367446, 198310090410761165665084239929992686315860⟩
  | 2, 1 => ⟨213770778242381412841020666442934457582448, 213770778242381412841020666447462443617464⟩
  | 0, 4 => ⟨1461616696233255830613993320988695890158651, 1461616696233255830620590661991415563900196⟩
  | 1, 3 => ⟨4552509841137313497137393555368691928632790, 4552509841137313497137424445083989745670299⟩
  | 2, 2 => ⟨7847917893741900428558524298264775060869391, 7847917893741900428558524298607769922222142⟩
  | 3, 1 => ⟨8258944038844606575980320361472388011354993, 8258944038844606575980320361495755447451069⟩
  | 0, 5 => ⟨-39286295112894725494008829681489098342094482155, 39614310514604385912565400355147637524176993400⟩
  | 1, 4 => ⟨-57881715810781169108175600796031002087980263893, 58060609049722929892750128328893681676708567828⟩
  | 2, 3 => ⟨-88719403237418690976669576456314827430750387720, 88777717600055108987345157009508220250623520483⟩
  | 3, 2 => ⟨-137788800549551791254394348927278790196023555931, 137793599474526149056926096561654765499195597721⟩
  | 4, 1 => ⟨-211480422820691121065799394914660488246167693661, 211784669728974618949216981327632207474778335605⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0000Geometry.ds, E8TAxisZero0000Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 27833540112767765544808014968570831055 := by decide

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
end GeneralCK.Certificates.E8TAxisZero0000CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0001CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0001CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0001GraphCenterA.qJetBox,
   E8TAxisZero0001GraphCenterB.qJetBox,
   E8TAxisZero0001GraphCenterC.qJetBox,
   E8TAxisZero0001GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0001GraphWholeA.qJetBox,
   E8TAxisZero0001GraphWholeB.qJetBox,
   E8TAxisZero0001GraphWholeC.qJetBox,
   E8TAxisZero0001GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨50269649890351596400221790617257923073, 50269649890351596400221791280495105591⟩
  | 0, 2 => ⟨3070879275392722330846032424368144425896, 3070879275392722330846033168763495402713⟩
  | 1, 1 => ⟨3404436804618069264665170622802539679035, 3404436804618069264665170628465597910521⟩
  | 0, 3 => ⟨96787245581888303982092901478785125032286, 96787245581888303982095135225437264528139⟩
  | 1, 2 => ⟨170316696433401071480431053502481461722498, 170316696433401071480431063800862165823498⟩
  | 2, 1 => ⟨184274960157054865528412514182306522748894, 184274960157054865528412514186781189641611⟩
  | 0, 4 => ⟨1313639633482609684599544835277683974132502, 1313639633482609684605817851311938449405081⟩
  | 1, 3 => ⟨4103906350925573826707445310273054606963088, 4103906350925573826707476196379296956335790⟩
  | 2, 2 => ⟨7088454684862325720744881269119694614749331, 7088454684862325720744881269446325965232970⟩
  | 3, 1 => ⟨7478731041743546632286676316642373613650730, 7478731041743546632286676316665566098309416⟩
  | 0, 5 => ⟨-39126407287684411200087151399295024185414392913, 39440738480934554683270216173094425919991987293⟩
  | 1, 4 => ⟨-57623027116581049589819431368690249264343559599, 57794456780050257467663212004095301063982630666⟩
  | 2, 3 => ⟨-88285600399354452075066884882541354305099833563, 88340775785558116317212501818748492655173390829⟩
  | 3, 2 => ⟨-137044793855232733081584087313418021280125895974, 137045565249505136982950171502010573566206759196⟩
  | 4, 1 => ⟨-210194135905507054626086309172892040753299436426, 210469712048221541485307173312575791546856260833⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0001Geometry.ds, E8TAxisZero0001Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 19120401661997526456965346681842217844 := by decide

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
end GeneralCK.Certificates.E8TAxisZero0001CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0002CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0002CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0002GraphCenterA.qJetBox,
   E8TAxisZero0002GraphCenterB.qJetBox,
   E8TAxisZero0002GraphCenterC.qJetBox,
   E8TAxisZero0002GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0002GraphWholeA.qJetBox,
   E8TAxisZero0002GraphWholeB.qJetBox,
   E8TAxisZero0002GraphWholeC.qJetBox,
   E8TAxisZero0002GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨38734617910587850146697730583502543988, 38734617910587850146697731229508645027⟩
  | 0, 2 => ⟨2480321490075864472922765984483583851410, 2480321490075864472922766690266478319353⟩
  | 1, 1 => ⟨2764231128560586297786933189386688231622, 2764231128560586297786933195038995103959⟩
  | 0, 3 => ⟨82201633925204741367949863841318323406951, 82201633925204741367951981771570037540214⟩
  | 1, 2 => ⟨145097556828113099890226249405264424224920, 145097556828113099890226259702474368175013⟩
  | 2, 1 => ⟨157631101521793223246870117396387717585760, 157631101521793223246870117400809378322527⟩
  | 0, 4 => ⟨1173837275461748213481968899179203485184899, 1173837275461748213487917627289194536317310⟩
  | 1, 3 => ⟨3679032679979802392693776811915494838541544, 3679032679979802392693807694595490180962778⟩
  | 2, 2 => ⟨6368290495946299200549478094863029356716646, 6368290495946299200549478095173305761730433⟩
  | 3, 1 => ⟨6737873433943293303516918067827553277691980, 6737873433943293303516918067850572475179040⟩
  | 0, 5 => ⟨-38967557973993031565361469276568990400172168032, 39268045363127120549665677405478130853138877005⟩
  | 1, 4 => ⟨-57365927627896961215923516941439740010758286424, 57529660990859102949201626558730672137715552999⟩
  | 2, 3 => ⟨-87854423653786437667008016841402449689005940993, 87906140572811594031485937903867649457426858431⟩
  | 3, 2 => ⟨-136305367220025188343312819353205632012189461926, 136301742413745894135107520014104485415471296404⟩
  | 4, 1 => ⟨-208916112028004037299829466460275260426697535187, 209162822758712626961190111582347370075121573303⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0002Geometry.ds, E8TAxisZero0002Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 12253272711731688455481214217342289310 := by decide

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
end GeneralCK.Certificates.E8TAxisZero0002CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0003CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0003CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0003GraphCenterA.qJetBox,
   E8TAxisZero0003GraphCenterB.qJetBox,
   E8TAxisZero0003GraphCenterC.qJetBox,
   E8TAxisZero0003GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0003GraphWholeA.qJetBox,
   E8TAxisZero0003GraphWholeB.qJetBox,
   E8TAxisZero0003GraphWholeC.qJetBox,
   E8TAxisZero0003GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨29419442786753054421363029145457279562, 29419442786753054421363029774252758132⟩
  | 0, 2 => ⟨1979363671309043907346197020905428321902, 1979363671309043907346197688080080491912⟩
  | 1, 1 => ⟨2218822741673294457455685554156576122184, 2218822741673294457455685559798240415727⟩
  | 0, 3 => ⟨69164968198674257492161566182118139229363, 69164968198674257492163568308475076220512⟩
  | 1, 2 => ⟨122505577335737683427981555115012692806510, 122505577335737683427981565411112973721245⟩
  | 2, 1 => ⟨133691902299376893581535120056192315868356, 133691902299376893581535120060561280229996⟩
  | 0, 4 => ⟨1042147720897950185126078780934993855439945, 1042147720897950185131703256245832230677134⟩
  | 1, 3 => ⟨3277785023190609560340543977585597758734365, 3277785023190609560340574857022071171697077⟩
  | 2, 2 => ⟨5687278871703728552593498053075841343479395, 5687278871703728552593498053369770964133715⟩
  | 3, 1 => ⟨6036221771104251854276829621813841042058290, 6036221771104251854276829621836688602553941⟩
  | 0, 5 => ⟨-38809436459493379924316955539841867902614087775, 39096085042240071210785001994795786741301827983⟩
  | 1, 4 => ⟨-57110098986515216613487633680783671897964295919, 57266064871069122785308135612586807457769191487⟩
  | 2, 3 => ⟨-87425539577831212183211870553141900229633246295, 87473633581990648152495539028726176733129166171⟩
  | 3, 2 => ⟨-135570161324578393422122180702351619127579104699, 135561916810446354255916504428819231085208320098⟩
  | 4, 1 => ⟨-207645949658657860935499649232628490007723559555, 207863733244498783602267523705400391450578123069⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0003Geometry.ds, E8TAxisZero0003Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6930256047020201802448297334152665880 := by decide

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
end GeneralCK.Certificates.E8TAxisZero0003CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0004CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0004CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0004GraphCenterA.qJetBox,
   E8TAxisZero0004GraphCenterB.qJetBox,
   E8TAxisZero0004GraphCenterC.qJetBox,
   E8TAxisZero0004GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0004GraphWholeA.qJetBox,
   E8TAxisZero0004GraphWholeB.qJetBox,
   E8TAxisZero0004GraphWholeC.qJetBox,
   E8TAxisZero0004GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨244694370569809773441465755867064453050, 244694370569809773441465756657309072133⟩
  | 0, 2 => ⟨11185692373092027581673260146833010851379, 11185692373092027581673261174536910910435⟩
  | 1, 1 => ⟨12069931019397739295740212593755078530679, 12069931019397739295740212599500359019234⟩
  | 0, 3 => ⟨259581465442625893825726322382022361270586, 259581465442625893825729405896265055804013⟩
  | 1, 2 => ⟨449604083895760254356525878322255996043939, 449604083895760254356525888631092169161091⟩
  | 2, 1 => ⟨476399577589553089594771398612897706831625, 476399577589553089594771398617770860030964⟩
  | 0, 4 => ⟨2593145608015242562297347270950059750326414, 2593145608015242562305999654271511798829890⟩
  | 1, 3 => ⟨7952272777873031385675238712185143324060645, 7952272777873031385675269629009061298765340⟩
  | 2, 2 => ⟨13581101264401515234197397246856092813520442, 13581101264401515234197397247302948291850424⟩
  | 3, 1 => ⟨14125045868554952502518930024812474253470000, 14125045868554952502518930024836989297361754⟩
  | 0, 5 => ⟨-53251745514337146828115559283380550105851076444, 53669059412766668832573000807632020892238626963⟩
  | 1, 4 => ⟨-79683672608485398513101756518955162966834881817, 79793804876853746842193298536374047213894318089⟩
  | 2, 3 => ⟨-123610675825525142594383731146702460451836006815, 123415708301165923419229512949531466827632262650⟩
  | 3, 2 => ⟨-193809130244418764526151512841184646146014673268, 193400361292816044620775968068163928337930921227⟩
  | 4, 1 => ⟨-300275839937785206863219410646213704690336458196, 300279094848198452191168944456701184952601374766⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0004Geometry.ds, E8TAxisZero0004Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 117424138431108789249593457232224503468 := by decide

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
end GeneralCK.Certificates.E8TAxisZero0004CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0005CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0005CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0005GraphCenterA.qJetBox,
   E8TAxisZero0005GraphCenterB.qJetBox,
   E8TAxisZero0005GraphCenterC.qJetBox,
   E8TAxisZero0005GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0005GraphWholeA.qJetBox,
   E8TAxisZero0005GraphWholeB.qJetBox,
   E8TAxisZero0005GraphWholeC.qJetBox,
   E8TAxisZero0005GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨178004867346974201781480835549334383351, 178004867346974201781480836310611470298⟩
  | 0, 2 => ⟨8629902245556681597514087307143422442488, 8629902245556681597514088270433346130733⟩
  | 1, 1 => ⟨9357063121535250722412271711581896043889, 9357063121535250722412271717307961233353⟩
  | 0, 3 => ⟨213006363347916847503220301950515022122659, 213006363347916847503223192259423526028619⟩
  | 1, 2 => ⟨369982753838740474700911544275343455134303, 369982753838740474700911554581514035932845⟩
  | 2, 1 => ⟨393488867738847542041124036589915780291176, 393488867738847542041124036594696823136021⟩
  | 0, 4 => ⟨2262274619536403715388397892488583385530818, 2262274619536403715396509296258288282554736⟩
  | 1, 3 => ⟨6963122335341290997273869919764216339907364, 6963122335341290997273900828741608278962539⟩
  | 2, 2 => ⟨11916448611416860054293370864392122537895370, 11916448611416860054293370864811605605362274⟩
  | 3, 1 => ⟨12425140734168721853630831355109779323040171, 12425140734168721853630831355133985627848422⟩
  | 0, 5 => ⟨-52870470217346747561749953551561180624578684015, 53265447005172077968600879666947840503326722006⟩
  | 1, 4 => ⟨-79058297586732293277132376273424855114664438256, 79164082715745019297216093212056288975184455998⟩
  | 2, 3 => ⟨-122551943922069988968808580936271217930839984972, 122369449248176067782934863374089956696230791311⟩
  | 3, 2 => ⟨-191983928618185468799154493484342568638794981291, 191593760317889923947421452396451258367307472110⟩
  | 4, 1 => ⟨-297111613859018970875117933789651105702236187913, 297083365831416525063210753520371900572677623990⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0005Geometry.ds, E8TAxisZero0005Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 74492358328591439696785501392176219342 := by decide

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
end GeneralCK.Certificates.E8TAxisZero0005CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0006CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0006CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0006GraphCenterA.qJetBox,
   E8TAxisZero0006GraphCenterB.qJetBox,
   E8TAxisZero0006GraphCenterC.qJetBox,
   E8TAxisZero0006GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0006GraphWholeA.qJetBox,
   E8TAxisZero0006GraphWholeB.qJetBox,
   E8TAxisZero0006GraphWholeC.qJetBox,
   E8TAxisZero0006GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨126719464917199383618846037391128255469, 126719464917199383618846038123498762838⟩
  | 0, 2 => ⟨6539962602979716834506562945677220960640, 6539962602979716834506563844569117664623⟩
  | 1, 1 => ⟨7129917159051307417838733330002529314023, 7129917159051307417838733335709692268131⟩
  | 0, 3 => ⟨172401084908207169444048206055485770525186, 172401084908207169444050903206508467806976⟩
  | 1, 2 => ⟨300415379008162143509363196230658663819826, 300415379008162143509363206534333993833074⟩
  | 2, 1 => ⟨320851795964594848412032915527062412582158, 320851795964594848412032915531752266437687⟩
  | 0, 4 => ⟨1955266122694313287975311864819147265150218, 1955266122694313287982882422197187541252780⟩
  | 1, 3 => ⟨6041822018935582248886139986285797178466985, 6041822018935582248886170887926012872502719⟩
  | 2, 2 => ⟨10363684706656337838934875321857368425978599, 10363684706656337838934875322249509261182742⟩
  | 3, 1 => ⟨10837328448167603889527158034146987131986529, 10837328448167603889527158034170889551372441⟩
  | 0, 5 => ⟨-52492305755454117449137990135879697037925881273, 52864935478366685293501621376132434209879034708⟩
  | 1, 4 => ⟨-78438395137683259696176029990047834706412945953, 78539535324591358059816278896555169141398590706⟩
  | 2, 3 => ⟨-121503108599970247251375287570874732559815514517, 121332434806666973464839003184840272365190658739⟩
  | 3, 2 => ⟨-190176923141617749356586002948815730169859729691, 189804473058206693993765053707139054014792087544⟩
  | 4, 1 => ⟨-293981159129422095332302633486096932742073005755, 293921107498605285650996745229102005104383068295⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0006Geometry.ds, E8TAxisZero0006Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 42827584556636751602157627153201087364 := by decide

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
end GeneralCK.Certificates.E8TAxisZero0006CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0007CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0007CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0007GraphCenterA.qJetBox,
   E8TAxisZero0007GraphCenterB.qJetBox,
   E8TAxisZero0007GraphCenterC.qJetBox,
   E8TAxisZero0007GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0007GraphWholeA.qJetBox,
   E8TAxisZero0007GraphWholeB.qJetBox,
   E8TAxisZero0007GraphWholeC.qJetBox,
   E8TAxisZero0007GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨87998506334808492595001587623273014190, 87998506334808492595001588326796852242⟩
  | 0, 2 => ⟨4855215759285447758555219424921847581284, 4855215759285447758555220259430604422153⟩
  | 1, 1 => ⟨5326466322698402817389434967588075224019, 5326466322698402817389434973276646204225⟩
  | 0, 3 => ⟨137343530427132501466752067934887127601459, 137343530427132501466754571972290540160819⟩
  | 1, 2 => ⟨240205419243849515053097794540954741382722, 240205419243849515053097804842304988039672⟩
  | 2, 1 => ⟨257790590471250691958507453784909222745284, 257790590471250691958507453789508793430381⟩
  | 0, 4 => ⟨1671749001894009296394243174411435590509566, 1671749001894009296401273009648397437857964⟩
  | 1, 3 => ⟨5187750862722119585521488517811868021395924, 5187750862722119585521519412623760977189559⟩
  | 2, 2 => ⟨8921935224959648078768543077443873088428352, 8921935224959648078768543077808699987732950⟩
  | 3, 1 => ⟨9360720621612458491254177894873757174562110, 9360720621612458491254177894897360492760033⟩
  | 0, 5 => ⟨-52117734427865132849543787625168282303459717545, 52467701850955868364240465987393847381652497574⟩
  | 1, 4 => ⟨-77824412645570371428795185738156455165179001205, 77920301442955968803285684079491390183834090170⟩
  | 2, 3 => ⟨-120464556783870895433813801151989158204887025307, 120304743026261033045886860947069490157523516992⟩
  | 3, 2 => ⟨-188388392049018970500819627586966749388921600715, 188032473136759925438060876019090510954532388089⟩
  | 4, 1 => ⟨-290884558908678108748933225736091846202559416001, 290792112526664189695657716648697109877582364903⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0007Geometry.ds, E8TAxisZero0007Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 20106875275514589028802266822251466078 := by decide

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
end GeneralCK.Certificates.E8TAxisZero0007CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0008CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0008CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0008GraphCenterA.qJetBox,
   E8TAxisZero0008GraphCenterB.qJetBox,
   E8TAxisZero0008GraphCenterC.qJetBox,
   E8TAxisZero0008GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0008GraphWholeA.qJetBox,
   E8TAxisZero0008GraphWholeB.qJetBox,
   E8TAxisZero0008GraphWholeC.qJetBox,
   E8TAxisZero0008GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨19431090048745930510547269711732715581311, 19431090048745930510547269712419915791197⟩
  | 0, 2 => ⟨396368471579896021804499810680724252001753, 396368471579896021804499810682935980879406⟩
  | 1, 1 => ⟨402908502520920845604352232108435149049957, 402908502520920845604352232111454175959167⟩
  | 0, 3 => ⟨3983215653294609423307402166307272408524363, 3983215653294609423307402166768519278203315⟩
  | 1, 2 => ⟨6640462716431746227033448680724349685068300, 6640462716431746227033448680729407015235221⟩
  | 2, 1 => ⟨6723203261933309033260218250376178274510827, 6723203261933309033260218250383096770850241⟩
  | 0, 4 => ⟨18009115243274431408967554012993898118067380, 18009115243274431408967556577915952391455097⟩
  | 1, 3 => ⟨51121591963379429601447804222108198483687043, 51121591963379429601447804224028845154091636⟩
  | 2, 2 => ⟨84576294226701869383839928601263415758297717, 84576294226701869383839928601284328778786989⟩
  | 3, 1 => ⟨85294382786579050333122936110403494433334185, 85294382786579050333122936110435080954651949⟩
  | 0, 5 => ⟨-142508855782133529361279102454342790292022542901, 142787769572997843488265517757042467196956483319⟩
  | 1, 4 => ⟨-226076615832849588480250496284407403820012713706, 224225929059019158281858161113220917410785180068⟩
  | 2, 3 => ⟨-367340476405053067044062736635404585944663879978, 362899596645863564053622911405640580763562849490⟩
  | 3, 2 => ⟨-599361337916150055132760881142187213535328109766, 592497329219562719509139248550356681473654531094⟩
  | 4, 1 => ⟨-968034019535211587631247300209368824409461283242, 961945156471239475947418402944793955375647794740⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0008Geometry.ds, E8TAxisZero0008Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 13603266042521282968973978555347291026325 := by decide

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
end GeneralCK.Certificates.E8TAxisZero0008CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0009CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0009CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0009GraphCenterA.qJetBox,
   E8TAxisZero0009GraphCenterB.qJetBox,
   E8TAxisZero0009GraphCenterC.qJetBox,
   E8TAxisZero0009GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0009GraphWholeA.qJetBox,
   E8TAxisZero0009GraphWholeB.qJetBox,
   E8TAxisZero0009GraphWholeC.qJetBox,
   E8TAxisZero0009GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨12968450047450380153392805037759467129790, 12968450047450380153392805038415921072592⟩
  | 0, 2 => ⟨285926302235320174648146765664334346057306, 285926302235320174648146765666489841827559⟩
  | 1, 1 => ⟨291037321463977642812290085737784276850378, 291037321463977642812290085740728824547353⟩
  | 0, 3 => ⟨3102447907105917486952170264111499651918477, 3102447907105917486952170264536892481173666⟩
  | 1, 2 => ⟨5181675973477813176978778011116461660900044, 5181675973477813176978778011121308462724413⟩
  | 2, 1 => ⟨5251566884854437814700767699626371848042207, 5251566884854437814700767699632967458817634⟩
  | 0, 4 => ⟨14998970852260768081701336321319457069454190, 14998970852260768081701338686251735438163394⟩
  | 1, 3 => ⟨42967915857642788423949150165918243108814417, 42967915857642788423949150167834879261706991⟩
  | 2, 2 => ⟨71250195848075955284690813872999165147894756, 71250195848075955284690813873019272584350936⟩
  | 3, 1 => ⟨71903147402033361103839710455778645094534906, 71903147402033361103839710455808939375913044⟩
  | 0, 5 => ⟨-138633023299266975486109894148968860317075042042, 138797151987654420871788434797604724968007912255⟩
  | 1, 4 => ⟨-219407179268142837917454294174796367060123449260, 217572231466369533832266844917861891271721026949⟩
  | 2, 3 => ⟨-355659465073786040662618050333707132354620940850, 351380972251053974906851559072664207016982620849⟩
  | 3, 2 => ⟨-578750314206957878196432306587230448501789045065, 572141753087495777868411769825173276371625459965⟩
  | 4, 1 => ⟨-931661179636675586711704290068947042766184876738, 925584164345048671254539339152567614155621718892⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0009Geometry.ds, E8TAxisZero0009Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 8591244638821431899709578161277340981014 := by decide

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
end GeneralCK.Certificates.E8TAxisZero0009CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0010CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0010CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0010GraphCenterA.qJetBox,
   E8TAxisZero0010GraphCenterB.qJetBox,
   E8TAxisZero0010GraphCenterC.qJetBox,
   E8TAxisZero0010GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0010GraphWholeA.qJetBox,
   E8TAxisZero0010GraphWholeB.qJetBox,
   E8TAxisZero0010GraphWholeC.qJetBox,
   E8TAxisZero0010GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨8359056739186759341909218724713699507479, 8359056739186759341909218725340061847833⟩
  | 0, 2 => ⟨200571213328270649951911717154848773701160, 200571213328270649951911717156949912236564⟩
  | 1, 1 => ⟨204482843218887935427483547866859528687363, 204482843218887935427483547869732562853711⟩
  | 0, 3 => ⟨2366776474705460388321554609932890531420921, 2366776474705460388321554610322496693075794⟩
  | 1, 2 => ⟨3960433918087019566775329347342580043584497, 3960433918087019566775329347347223431255065⟩
  | 2, 1 => ⟨4018674039453760803266489756376279983754528, 4018674039453760803266489756382564246121574⟩
  | 0, 4 => ⟨12331620050408060756574718791122911105329724, 12331620050408060756574720956418001468812217⟩
  | 1, 3 => ⟨35637163103349562022965138016884302065013204, 35637163103349562022965138018797238600170365⟩
  | 2, 2 => ⟨59227737904662129958222723328315030324078683, 59227737904662129958222723328334367135556561⟩
  | 3, 1 => ⟨59817911273767723598818785373272531648348206, 59817911273767723598818785373301592558277872⟩
  | 0, 5 => ⟨-134880588586388471575773168604503528136451863133, 134934325035086965440821038627081271114150881886⟩
  | 1, 4 => ⟨-212959899840991723200562328603768778387162397130, 211140626621448367517054538864051273488936023954⟩
  | 2, 3 => ⟨-344384008179533036564140978778943241793114326574, 340270186747802151506017966857009651444900052226⟩
  | 3, 2 => ⟨-558884062595496912781864090864946186666072163624, 552571609978982582312556853013921544349089059003⟩
  | 4, 1 => ⟨-896661465447461765750184189852112867458863271713, 890797131295313100775979715912796298625834451737⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0010Geometry.ds, E8TAxisZero0010Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5114789039198139899548659255383759650263 := by decide

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
end GeneralCK.Certificates.E8TAxisZero0010CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0011CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0011CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0011GraphCenterA.qJetBox,
   E8TAxisZero0011GraphCenterB.qJetBox,
   E8TAxisZero0011GraphCenterC.qJetBox,
   E8TAxisZero0011GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0011GraphWholeA.qJetBox,
   E8TAxisZero0011GraphWholeB.qJetBox,
   E8TAxisZero0011GraphWholeC.qJetBox,
   E8TAxisZero0011GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5168770724437534840927205936555715731881, 5168770724437534840927205937152617015436⟩
  | 0, 2 => ⟨136074811813374623004329270640713506415657, 136074811813374623004329270642762099451437⟩
  | 1, 1 => ⟨138994597640987203304664486625215758432088, 138994597640987203304664486628020139692820⟩
  | 0, 3 => ⟨1761178900825989678610181758633447192105760, 1761178900825989678610181758987328444807870⟩
  | 1, 2 => ⟨2952862210360933262944352633822683668526394, 2952862210360933262944352633827130427855326⟩
  | 2, 1 => ⟨3000608296937170547016665371753833638852410, 3000608296937170547016665371759817539893122⟩
  | 0, 4 => ⟨9981238625830849249848074928268072163475648, 9981238625830849249848076894248234981294911⟩
  | 1, 3 => ⟨29086616662944968178019773349491607345194435, 29086616662944968178019773351401152271278275⟩
  | 2, 2 => ⟨48449254390403491789432079046662501602518002, 48449254390403491789432079046681101169689615⟩
  | 3, 1 => ⟨48978781584398054663675705223534665644596231, 48978781584398054663675705223562549332824715⟩
  | 0, 5 => ⟨-131243630455765912643531807795480883759578241120, 131190312165565091564356424679019662047049212039⟩
  | 1, 4 => ⟨-206721384484314383465946402867504357932311823411, 204917906545613618162853568255388768544405189300⟩
  | 2, 3 => ⟨-333491010704403854120169744233510077352454252282, 329539230703842706378066743734159887107701838250⟩
  | 3, 2 => ⟨-539722938719974393557763017649184115432949069075, 533707980141077658917109070769061063684860167653⟩
  | 4, 1 => ⟨-862967226496733944855871778013888749800768845489, 857347200126343890889880046386354097048818737203⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0011Geometry.ds, E8TAxisZero0011Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2791891409723352529384775542120380942663 := by decide

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
end GeneralCK.Certificates.E8TAxisZero0011CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0012CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0012CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0012GraphCenterA.qJetBox,
   E8TAxisZero0012GraphCenterB.qJetBox,
   E8TAxisZero0012GraphCenterC.qJetBox,
   E8TAxisZero0012GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0012GraphWholeA.qJetBox,
   E8TAxisZero0012GraphWholeB.qJetBox,
   E8TAxisZero0012GraphWholeC.qJetBox,
   E8TAxisZero0012GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨3039008991473600532526256503868304291088, 3039008991473600532526256504436351800885⟩
  | 0, 2 => ⟨88646215022493558093307885853962029369970, 88646215022493558093307885855959827579449⟩
  | 1, 1 => ⟨90760374722844658082455779514180421335091, 90760374722844658082455779516918910542171⟩
  | 0, 3 => ⟨1271392907714142248240935556152636663487481, 1271392907714142248240935556470849195587901⟩
  | 1, 2 => ⟨2136148681673121601309434226417957208216345, 2136148681673121601309434226422213811498580⟩
  | 2, 1 => ⟨2174519579136712007670720878608420574315689, 2174519579136712007670720878614114576760542⟩
  | 0, 4 => ⟨7924648596659381063847634132011193122582255, 7924648596659381063847635898968558766529259⟩
  | 1, 3 => ⟨23277879491613959005517431777798394439081300, 23277879491613959005517431779704853099974604⟩
  | 2, 2 => ⟨38861074880278654297499706952461239035876571, 38861074880278654297499706952479133244613917⟩
  | 3, 1 => ⟨39331868789913417628251902343708815250157606, 39331868789913417628251902343735575295695095⟩
  | 0, 5 => ⟨-127850017593107419679147508085432217191810597090, 127817106590086935967554948076961464136975874161⟩
  | 1, 4 => ⟨-200921753801177512008923102082120403608619292125, 199332751354224665868216632724671980498721023982⟩
  | 2, 3 => ⟨-323389124165672738846361722723642442111270729971, 319892828916221408109954373570595783239109658684⟩
  | 3, 2 => ⟨-521980828229698625281468711891767180233158987921, 516651444940677303815606327216445992282156104064⟩
  | 4, 1 => ⟨-831799534836375860353356835044979759424039398625, 826811874456097752627875327655670835935495201945⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0012Geometry.ds, E8TAxisZero0012Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 1310083225152767416630283261270996118406 := by decide

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
end GeneralCK.Certificates.E8TAxisZero0012CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0013CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0013CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0013GraphCenterA.qJetBox,
   E8TAxisZero0013GraphCenterB.qJetBox,
   E8TAxisZero0013GraphCenterC.qJetBox,
   E8TAxisZero0013GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0013GraphWholeA.qJetBox,
   E8TAxisZero0013GraphWholeB.qJetBox,
   E8TAxisZero0013GraphWholeC.qJetBox,
   E8TAxisZero0013GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨1678708449645612634778728219196422324962, 1678708449645612634778728219736200896544⟩
  | 0, 2 => ⟨54913175792811804855141912311296411910388, 54913175792811804855141912313245107845718⟩
  | 1, 1 => ⟨56387272665389641097878997566053281418478, 56387272665389641097878997568728544697159⟩
  | 0, 3 => ⟨883836942286060404799181153029709020200513, 883836942286060404799181153312303489845793⟩
  | 1, 2 => ⟨1488432990605552251095733789183200495826964, 1488432990605552251095733789187273115909804⟩
  | 2, 1 => ⟨1518513677595420723654282145119174800091772, 1518513677595420723654282145124588866654247⟩
  | 0, 4 => ⟨6141211058443789061997682377908200599608024, 6141211058443789061997683946104948032057698⟩
  | 1, 3 => ⟨18176712437966474345741633259932348049372933, 18176712437966474345741633261836023346404777⟩
  | 2, 2 => ⟨30415307298732941568986830257110985017616398, 30415307298732941568986830257128204338356740⟩
  | 3, 1 => ⟨30829068604885932648529341707038770092557425, 30829068604885932648529341707064457644142652⟩
  | 0, 5 => ⟨-124556052642107797550056625193657285096349772799, 124541296712319446436313418700820964430674798606⟩
  | 1, 4 => ⟨-195302276621954673765201593792529618287078965719, 193919002619618052390849959817982355235235952079⟩
  | 2, 3 => ⟨-313617938543407310069907999761470959148525772905, 310559800846021734916903346390584200242304234976⟩
  | 3, 2 => ⟨-504850844243454579848330672774695016025545738262, 500181553501931761932067968418980767156998403351⟩
  | 4, 1 => ⟨-801769588986342768137304689723388930462477627003, 797390875808378200546251901224072480063220711672⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0013Geometry.ds, E8TAxisZero0013Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 420864228639999314359925658018736731713 := by decide

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
end GeneralCK.Certificates.E8TAxisZero0013CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0015CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisZero0015CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisRegularCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0015GraphCenterA.qJetBox,
   E8TAxisZero0015GraphCenterB.qJetBox,
   E8TAxisZero0015GraphCenterC.qJetBox,
   E8TAxisZero0015GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisZero0015GraphWholeA.qJetBox,
   E8TAxisZero0015GraphWholeB.qJetBox,
   E8TAxisZero0015GraphWholeC.qJetBox,
   E8TAxisZero0015GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨459098335131547889343952092544085217398, 459098335131547889343952093034158143260⟩
  | 0, 2 => ⟨19606045383325129751794066873227436850490, 19606045383325129751794066875055675037796⟩
  | 1, 1 => ⟨19946624413487417965305986054658556642409, 19946624413487417965305986057226243992121⟩
  | 0, 3 => ⟨408343978938418780487531936372483053690976, 408343978938418780487531936375042902026735⟩
  | 1, 2 => ⟨685265708387758056782877699811658041918565, 685265708387758056782877699815099079519311⟩
  | 2, 1 => ⟨694214868395897772610898029364956638794609, 694214868395897772610898029369890063191522⟩
  | 0, 4 => ⟨3621438129918392751970925387362877084556372, 3621438129918392751970925387518893220037935⟩
  | 1, 3 => ⟨10781500766430302612945803948851110091540641, 10781500766430302612945803948862380875029840⟩
  | 2, 2 => ⟨18019596695961278437156310402293972574539092, 18019596695961278437156310402310034336195339⟩
  | 3, 1 => ⟨18177412854930728234346190753411291513479961, 18177412854930728234346190753435169149415228⟩
  | 0, 5 => ⟨-46350432458695799354122563551621611740811340080, 46384050095090242800197025232513361314568796047⟩
  | 1, 4 => ⟨-71312315812006654001002781901588562172973907491, 70990642064049721970582159076375161323671678142⟩
  | 2, 3 => ⟨-112803145797969414367506148423226396868202291793, 112106777040793909844604659017546804479732008588⟩
  | 3, 2 => ⟨-179235323558388835482652689070809353927382110275, 178191838512977745633848590703950085159152248704⟩
  | 4, 1 => ⟨-281095511794182877683391465721244136212165353761, 280177678621060837175674870521822196254796387482⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisZero0015Geometry.ds, E8TAxisZero0015Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 317947318045926859561741100982214928735 := by decide

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
end GeneralCK.Certificates.E8TAxisZero0015CertifiedArithmetic

end


