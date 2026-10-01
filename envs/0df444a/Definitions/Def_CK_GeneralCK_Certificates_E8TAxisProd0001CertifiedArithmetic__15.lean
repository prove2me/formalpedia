-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0001CertifiedArithmetic__15
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0001CertifiedArithmetic__15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:05:51.770645+00:00
-- url     : https://prove2.me/theorems/edf5d566-1650-4548-a9b7-8a304bbbe845
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0001CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0002CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0001CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0002CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0003CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0004CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0005CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0006CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0007CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0008CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0009CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0010CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0011CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0012CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0013CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0014CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0015CertifiedArithmetic)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0001CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0002CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0003CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0004CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0005CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0006CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0007CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0008CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0009CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0010CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0011CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0012CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0013CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0014CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0015CertifiedArithmetic)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0001CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0002CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0003CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0004CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0005CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0006CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0007CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0008CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0009CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0010CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0011CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0012CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0013CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0014CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0015CertifiedArithmetic) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0001CertifiedArithmetic (+14 modules: GeneralCK/Certificates/E8TAxisProd0002CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0003CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0004CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0005CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0006CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0007CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0008CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0009CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0010CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0011CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0012CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0013CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0014CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0015CertifiedArithmetic).lean)

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
import Definitions.Def_GeneralCK_E8_Prod0001_graph_mixed_data

-- ===== source module GeneralCK.Certificates.E8TAxisProd0001CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0001CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000




































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

theorem replay_lo : data.replay.lo = 94623890401408949361200427687881554461 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0001CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0002CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0002CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0002GraphCenterA.qJetBox,
   E8TAxisProd0002GraphCenterB.qJetBox,
   E8TAxisProd0002GraphCenterC.qJetBox,
   E8TAxisProd0002GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0002GraphWholeA.qJetBox,
   E8TAxisProd0002GraphWholeB.qJetBox,
   E8TAxisProd0002GraphWholeC.qJetBox,
   E8TAxisProd0002GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨143696766180399838364770309250263902699, 143696766180399838364770309935777566979⟩
  | 0, 2 => ⟨6312359587404424877637431072488039837297, 6312359587404424877637431075308573657559⟩
  | 1, 1 => ⟨7995169696504034800698208600202550538816, 7995169696504034800698208603676562117355⟩
  | 0, 3 => ⟨154097699991109952677535811562867971622453, 154097699991109952677535811566598993270179⟩
  | 1, 2 => ⟨294262565793532776496670607790446021973402, 294262565793532776496670607794483553246631⟩
  | 2, 1 => ⟨353674196518017041731346923921830364776883, 353674196518017041731346923926518547416295⟩
  | 0, 4 => ⟨1679227932357367935012643230140899953229702, 1679227932357367935012643230152943124621057⟩
  | 1, 3 => ⟨5624140745656828343941072144016060575777828, 5624140745656828343941072144028955972424154⟩
  | 2, 2 => ⟨10264717920236836385825100984129630577100660, 10264717920236836385825100984145332567725042⟩
  | 3, 1 => ⟨11664689949216069631194522499721485312011155, 11664689949216069631194522499744520174334744⟩
  | 0, 5 => ⟨-68025677112932845992291637691948463472979572039, 68012104394342104269306906421143043663871656165⟩
  | 1, 4 => ⟨-85514028991089525289574983590990883528205791381, 85256112460284532748816832816851947958288376301⟩
  | 2, 3 => ⟨-123894638984538607181001879693685613975705699599, 123451313198792700294229325087339139542296701960⟩
  | 3, 2 => ⟨-192707748502684657005626596030987319100129586041, 192163617543244342152684108281887842125626900048⟩
  | 4, 1 => ⟨-296768936977836071957123322590028739297696304661, 296558887676837225089906603125390119491116397743⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0002Geometry.ds, E8TAxisProd0002Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 57353638721917874838097731785710175014 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0002CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0003CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0003CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0003GraphCenterA.qJetBox,
   E8TAxisProd0003GraphCenterB.qJetBox,
   E8TAxisProd0003GraphCenterC.qJetBox,
   E8TAxisProd0003GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0003GraphWholeA.qJetBox,
   E8TAxisProd0003GraphWholeB.qJetBox,
   E8TAxisProd0003GraphWholeC.qJetBox,
   E8TAxisProd0003GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨25834902616030904397372105162402726815549, 25834902616030904397372105163504051299702⟩
  | 0, 2 => ⟨458154398456472818191986622421818185330486, 458154398456472818191986622425172586442275⟩
  | 1, 1 => ⟨508362904071100492262878895280893723902289, 508362904071100492262878895284964606632121⟩
  | 0, 3 => ⟨4255698564175906650399826890030377517674314, 4255698564175906650399826890035621291253424⟩
  | 1, 2 => ⟨7426580409492534635623481650973588490702752, 7426580409492534635623481650979363300944482⟩
  | 2, 1 => ⟨8043929403225795678858735566327507271866388, 8043929403225795678858735566334796392679680⟩
  | 0, 4 => ⟨18325373919416125883628135059519004087207155, 18325373919416125883628135059534359440385684⟩
  | 1, 3 => ⟨53704141142293972582858637480926458841523724, 53704141142293972582858637480943385347318412⟩
  | 2, 2 => ⟨91560774976973137440179073699191524120710492, 91560774976973137440179073699213423408653060⟩
  | 3, 1 => ⟨96774771964962388640141749430187463935288020, 96774771964962388640141749430220313823655693⟩
  | 0, 5 => ⟨-154774356505230558957435078982623611333230762009, 154395844634807772709357921293661885483590923028⟩
  | 1, 4 => ⟨-235119917082425710130377008902745022828269705190, 232500735488650965061045704901924887477072749123⟩
  | 2, 3 => ⟨-377695502615612204318602647619077534552901455592, 372442147031165567915178422234526016071422780739⟩
  | 3, 2 => ⟨-616306386454146919000866065796274255962824117143, 608619773240999150637924322105948896008059010502⟩
  | 4, 1 => ⟨-997051848162573303109572204004250407341829915127, 990102428275689790724144080999505289979689027737⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0003Geometry.ds, E8TAxisProd0003Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 18767422712732489976679464520928697825605 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0003CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0004CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0004CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0004GraphCenterA.qJetBox,
   E8TAxisProd0004GraphCenterB.qJetBox,
   E8TAxisProd0004GraphCenterC.qJetBox,
   E8TAxisProd0004GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0004GraphWholeA.qJetBox,
   E8TAxisProd0004GraphWholeB.qJetBox,
   E8TAxisProd0004GraphWholeC.qJetBox,
   E8TAxisProd0004GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨17614840900292201592292125225106715812074, 17614840900292201592292125226158068822852⟩
  | 0, 2 => ⟨334159506202064425873792497121253688168872, 334159506202064425873792497124539793748548⟩
  | 1, 1 => ⟨373681846580733589954730555701722510022006, 373681846580733589954730555705713985209227⟩
  | 0, 3 => ⟨3329263428919588688518204561017116292443885, 3329263428919588688518204561022170838193034⟩
  | 1, 2 => ⟨5843325259063158665420912583141040028970503, 5843325259063158665420912583146590930501635⟩
  | 2, 1 => ⟨6367280747589439432544975532747590095439713, 6367280747589439432544975532754540919372242⟩
  | 0, 4 => ⟨15245964358379118247312261825428105532988654, 15245964358379118247312261825443033290369430⟩
  | 1, 3 => ⟨45260445558249268388569247372400700254739693, 45260445558249268388569247372417089208251130⟩
  | 2, 2 => ⟨77548790124860692340903577421905251568715460, 77548790124860692340903577421926317001917886⟩
  | 3, 1 => ⟨82299764977404368571778890829999412094617588, 82299764977404368571778890830030929931212066⟩
  | 0, 5 => ⟨-150587482200650928714338288416673343905129311630, 150176013148966630013444984884668958304584617303⟩
  | 1, 4 => ⟨-228210304670348222906841023854684731795311115671, 225694971337014979628278760131119713402965983000⟩
  | 2, 3 => ⟨-365657162710294700388442695381662670716429243672, 360656093224477672973980647423870033949431876791⟩
  | 3, 2 => ⟨-595112549207133845309411695876188144679799230145, 587772726194149650136127833165958554836841233398⟩
  | 4, 1 => ⟨-959669150143420667632074095700172869847945250928, 952831137146486837020470419301217213042135374518⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0004Geometry.ds, E8TAxisProd0004Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 12258586511051379896899319370402071369443 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0004CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0005CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0005CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0005GraphCenterA.qJetBox,
   E8TAxisProd0005GraphCenterB.qJetBox,
   E8TAxisProd0005GraphCenterC.qJetBox,
   E8TAxisProd0005GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0005GraphWholeA.qJetBox,
   E8TAxisProd0005GraphWholeB.qJetBox,
   E8TAxisProd0005GraphWholeC.qJetBox,
   E8TAxisProd0005GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨23596945641768697844558783239571077655733, 23596945641768697844558783240661128434552⟩
  | 0, 2 => ⟨437104521616340695088988741990800161872981, 437104521616340695088988741994137565893946⟩
  | 1, 1 => ⟨471897681860836216841287587392307926637643, 471897681860836216841287587396359909295518⟩
  | 0, 3 => ⟨4164341930908615300373891762259834453364195, 4164341930908615300373891762265031841409494⟩
  | 1, 2 => ⟨7160231440905914390454101188870539112325184, 7160231440905914390454101188876262652874209⟩
  | 2, 1 => ⟨7592024440590049870967302686834065395473276, 7592024440590049870967302686841284919827687⟩
  | 0, 4 => ⟨18217662888234705581365119491640571098043604, 18217662888234705581365119491655821781708823⟩
  | 1, 3 => ⟨52836579795544269142759609034060083095032492, 52836579795544269142759609034076892835399457⟩
  | 2, 2 => ⟨89205731852866460594823309285779218798956338, 89205731852866460594823309285800949455840148⟩
  | 3, 1 => ⟨92885166115739504815215677464598108727806517, 92885166115739504815215677464630686355323656⟩
  | 0, 5 => ⟨-153838244863886820843231637496826905506403424760, 153481891955002978143202000572374070652563891988⟩
  | 1, 4 => ⟨-233555059039401771220335788528158046636432371528, 231000769647098778983889427372079682076702324566⟩
  | 2, 3 => ⟨-374917649833846854307613675190651557940794979962, 369769672544307289679360609585559603865280837870⟩
  | 3, 2 => ⟨-611265999522232022479661392065800217342124461002, 603714876500134420753504984140368453635957343985⟩
  | 4, 1 => ⟨-987788584972578502061632829930611398081424346592, 980988092881589584767910402166647154439685356063⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0005Geometry.ds, E8TAxisProd0005Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 16956290831875540361093728090089778171454 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0005CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0006CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0006CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0006GraphCenterA.qJetBox,
   E8TAxisProd0006GraphCenterB.qJetBox,
   E8TAxisProd0006GraphCenterC.qJetBox,
   E8TAxisProd0006GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0006GraphWholeA.qJetBox,
   E8TAxisProd0006GraphWholeB.qJetBox,
   E8TAxisProd0006GraphWholeC.qJetBox,
   E8TAxisProd0006GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨15985341979651649463419536697807163305538, 15985341979651649463419536698847439259057⟩
  | 0, 2 => ⟨317703410599532678030766856982748646410119, 317703410599532678030766856986018278169837⟩
  | 1, 1 => ⟨345027762253393628887134331763068298529461, 345027762253393628887134331767041526941223⟩
  | 0, 3 => ⟨3253245014522428109884019936306371082157884, 3253245014522428109884019936311380359764208⟩
  | 1, 2 => ⟨5618949995732048282199360265987422605606981, 5618949995732048282199360265992923706580665⟩
  | 2, 1 => ⟨5984858060590449632267109006856503172232918, 5984858060590449632267109006863386740333864⟩
  | 0, 4 => ⟨15161721292045162648462145817495515471932874, 15161721292045162648462145817510341789216112⟩
  | 1, 3 => ⟨44490615327717516353312632382559126984633497, 44490615327717516353312632382575403458174697⟩
  | 2, 2 => ⟨75424455784593054731664878239133142013206055, 75424455784593054731664878239154045718459329⟩
  | 3, 1 => ⟨78774862818428870503394167191880555430438284, 78774862818428870503394167191911812618007374⟩
  | 0, 5 => ⟨-149694204777115390765535512015496765375077602147, 149289518845193205917409897585599134886926118630⟩
  | 1, 4 => ⟨-226709617098246783684115807285249025681999785682, 224242016342836269501651811582447414337151574058⟩
  | 2, 3 => ⟨-362984536139863841006166407569145351291773153861, 358069196463731177434469397314190149699694948547⟩
  | 3, 2 => ⟨-590254861012273090397799985205081355269904102435, 583027887518121377249736029037158134711630045602⟩
  | 4, 1 => ⟨-950735138937550589378909419082272143897615287318, 944020434574643684104563903122431681645177516777⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0006Geometry.ds, E8TAxisProd0006Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 10966850560567351554171330776284147645840 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0006CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0007CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0007CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0007GraphCenterA.qJetBox,
   E8TAxisProd0007GraphCenterB.qJetBox,
   E8TAxisProd0007GraphCenterC.qJetBox,
   E8TAxisProd0007GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0007GraphWholeA.qJetBox,
   E8TAxisProd0007GraphWholeB.qJetBox,
   E8TAxisProd0007GraphWholeC.qJetBox,
   E8TAxisProd0007GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨11640849811767190614623024742298371404712, 11640849811767190614623024743300478158773⟩
  | 0, 2 => ⟨237467122990838564582302512435697393851516, 237467122990838564582302512438917286995016⟩
  | 1, 1 => ⟨267974065469778673505496155381256720248057, 267974065469778673505496155385171973201519⟩
  | 0, 3 => ⟨2553150671432010390744993469326014628290938, 2553150671432010390744993469330884795572607⟩
  | 1, 2 => ⟨4510124111168282903897000331235344716329301, 4510124111168282903897000331240679150410276⟩
  | 2, 1 => ⟨4949204290372838840616982390883286330607587, 4949204290372838840616982390889910795087118⟩
  | 0, 4 => ⟨12520632888861374435915152592766447171247758, 12520632888861374435915152592780961602908472⟩
  | 1, 3 => ⟨37661892800000773736800800316250673372333938, 37661892800000773736800800316266546927501361⟩
  | 2, 2 => ⟨64877285212922641907627490291390467905624005, 64877285212922641907627490291410735600923421⟩
  | 3, 1 => ⟨69182401199209112826121705690920457036407107, 69182401199209112826121705690950703457007738⟩
  | 0, 5 => ⟨-146567388598593371279528297796272044947569603794, 146091276450768477923820875659460095554307463633⟩
  | 1, 4 => ⟨-221569580443972749704398500633065101110024907226, 219119971264533708000230444595119497950194285743⟩
  | 2, 3 => ⟨-354078396324670914893408587451624069324362584407, 349290040240715681213829076090104965947856778538⟩
  | 3, 2 => ⟨-574728464660108457070610754210542736390265285741, 567731445614841358357210017434866111740049436325⟩
  | 4, 1 => ⟨-923744362170141146272867556699056281036508948701, 917172319575166319853916438053874040527346635213⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0007Geometry.ds, E8TAxisProd0007Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 7637070162384175679863047556201524482050 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0007CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0008CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0008CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0008GraphCenterA.qJetBox,
   E8TAxisProd0008GraphCenterB.qJetBox,
   E8TAxisProd0008GraphCenterC.qJetBox,
   E8TAxisProd0008GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0008GraphWholeA.qJetBox,
   E8TAxisProd0008GraphWholeB.qJetBox,
   E8TAxisProd0008GraphWholeC.qJetBox,
   E8TAxisProd0008GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨7413659342150715995070822319012605441918, 7413659342150715995070822319966163580382⟩
  | 0, 2 => ⟨163620570803128708148393502270112812769244, 163620570803128708148393502273268508034609⟩
  | 1, 1 => ⟨186626088277819726061597806752429887950434, 186626088277819726061597806756271994224771⟩
  | 0, 3 => ⟨1911941872474618223903394275219552010816936, 1911941872474618223903394275224242434899971⟩
  | 1, 2 => ⟨3402445530684603500336320121990711997643849, 3402445530684603500336320121995837063567352⟩
  | 2, 1 => ⟨3764861978487566298325343102109845461811711, 3764861978487566298325343102116154935061163⟩
  | 0, 4 => ⟨10122404107379580586883377229838090958559036, 10122404107379580586883377229852205748341190⟩
  | 1, 3 => ⟨30863579291862008962656010579202883604777622, 30863579291862008962656010579218262956548621⟩
  | 2, 2 => ⟨53483030004486955588913220120332528095724339, 53483030004486955588913220120352032541435415⟩
  | 3, 1 => ⟨57357839591400680839315499837342128989756893, 57357839591400680839315499837371161828394374⟩
  | 0, 5 => ⟨-142667742387469144606601281218002475894091729652, 142129748311699889024378352004636911452732119999⟩
  | 1, 4 => ⟨-215144348073514268060194297575376480815169185494, 212759919915978423963875807145135802912596944943⟩
  | 2, 3 => ⟨-342893067595083183518625597726239501360224170150, 338313907004119900189105506853697789021265857635⟩
  | 3, 2 => ⟨-555068471631712809295639474174451641385655379359, 548414705376820887028756335968682522305322830452⟩
  | 4, 1 => ⟨-889158846684937652349344001313564324549640907847, 882883145800463195945781139540835286659073704455⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0008Geometry.ds, E8TAxisProd0008Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 4459806605025057105106510707354881612546 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0008CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0009CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0009CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0009GraphCenterA.qJetBox,
   E8TAxisProd0009GraphCenterB.qJetBox,
   E8TAxisProd0009GraphCenterC.qJetBox,
   E8TAxisProd0009GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0009GraphWholeA.qJetBox,
   E8TAxisProd0009GraphWholeB.qJetBox,
   E8TAxisProd0009GraphWholeC.qJetBox,
   E8TAxisProd0009GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨10485168072504800521908023151691587290411, 10485168072504800521908023152682808219220⟩
  | 0, 2 => ⟨224857606820302491642233081141621790277852, 224857606820302491642233081144825719536524⟩
  | 1, 1 => ⟨245891381889240974616336796267760727782007, 245891381889240974616336796271658366347700⟩
  | 0, 3 => ⟨2490709612326893588456807067992694401146686, 2490709612326893588456807067997520377726544⟩
  | 1, 2 => ⟨4323515662159662068436625152937420165240379, 4323515662159662068436625152942706205674697⟩
  | 2, 1 => ⟨4629592759854019180209740409652712619944989, 4629592759854019180209740409659272066828408⟩
  | 0, 4 => ⟨12456054119574610878402371205618798980019708, 12456054119574610878402371205633215092585069⟩
  | 1, 3 => ⟨36982282047141990359732666739551575728917863, 36982282047141990359732666739567340917933078⟩
  | 2, 2 => ⟨62971180813324116459514281232981936295348580, 62971180813324116459514281233002048877514049⟩
  | 3, 1 => ⟨66004664186340511194952149434942089005905676, 66004664186340511194952149434972085891490013⟩
  | 0, 5 => ⟨-145699837893868478588221671054964275759242524630, 145230325267643923360061724794996409848322757341⟩
  | 1, 4 => ⟨-220114528935451526532846020358183849301859713722, 217711370605642528381129313930879036646071620982⟩
  | 2, 3 => ⟨-351489987872602050132406713722435975249935172642, 346784685133043923244748976760830547800117336757⟩
  | 3, 2 => ⟨-570028264613257922227436071595403294035921072161, 563139698321135372632354183377488770914422057953⟩
  | 4, 1 => ⟨-915107220861090527458706064414150571890388833580, 908651866168243095112585789120573126487500186424⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0009Geometry.ds, E8TAxisProd0009Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 6744003529206790536952434138033781762866 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0009CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0010CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0010CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0010GraphCenterA.qJetBox,
   E8TAxisProd0010GraphCenterB.qJetBox,
   E8TAxisProd0010GraphCenterC.qJetBox,
   E8TAxisProd0010GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0010GraphWholeA.qJetBox,
   E8TAxisProd0010GraphWholeB.qJetBox,
   E8TAxisProd0010GraphWholeC.qJetBox,
   E8TAxisProd0010GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨6619245131849772188053735655597092839350, 6619245131849772188053735656539951143597⟩
  | 0, 2 => ⟨154187188776926474877547058258276251115855, 154187188776926474877547058261416479698123⟩
  | 1, 1 => ⟨169997167253371892620257760701423984674934, 169997167253371892620257760705249089033465⟩
  | 0, 3 => ⟨1861451214147798952158233497194462326150721, 1861451214147798952158233497199109598650415⟩
  | 1, 2 => ⟨3249619685368351215982128515075299258339625, 3249619685368351215982128515080377277996752⟩
  | 2, 1 => ⟨3501703640880974417432503654942277182429144, 3501703640880974417432503654948523778563001⟩
  | 0, 4 => ⟨10074072650765704595111289619785863697074591, 10074072650765704595111289619799883185490987⟩
  | 1, 3 => ⟨30267410515295557530773690444940707072931593, 30267410515295557530773690444955982009285550⟩
  | 2, 2 => ⟨51783873471816726409659472577245704138248577, 51783873471816726409659472577265059812196731⟩
  | 3, 1 => ⟨54511391758289073509952705028916461818508684, 54511391758289073509952705028945255764612592⟩
  | 0, 5 => ⟨-141824937105572072303407585157945869026737499205, 141293310976610481886567204099193719353025462257⟩
  | 1, 4 => ⟨-213733166005880179437069159328736521571837551377, 211393854040758588824426617940337560569375481368⟩
  | 2, 3 => ⟨-340385638257681080525016331076791758250144424817, 335886804453586242976822179984472666897808267494⟩
  | 3, 2 => ⟨-550519777058270166988337454404861043103058882662, 543970044642182449495944828147218304760350155141⟩
  | 4, 1 => ⟨-880807488521123398957039199866526385398048976351, 874641936615049976702140692124764753837539626343⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0010Geometry.ds, E8TAxisProd0010Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3865401213999472725959313086341652390465 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0010CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0011CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0011CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0011GraphCenterA.qJetBox,
   E8TAxisProd0011GraphCenterB.qJetBox,
   E8TAxisProd0011GraphCenterC.qJetBox,
   E8TAxisProd0011GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0011GraphWholeA.qJetBox,
   E8TAxisProd0011GraphWholeB.qJetBox,
   E8TAxisProd0011GraphWholeC.qJetBox,
   E8TAxisProd0011GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨21463098325798738498031210710303336046258, 21463098325798738498031210711382160339893⟩
  | 0, 2 => ⟨416510091130168476829879204573997808673872, 416510091130168476829879204577318341758276⟩
  | 1, 1 => ⟨436753388202236192532647385665214006745128, 436753388202236192532647385669247228629704⟩
  | 0, 3 => ⟨4073518109883514412278140297085701456931867, 4073518109883514412278140297090852725926510⟩
  | 1, 2 => ⟨6898203366096445875876493746654090778740858, 6898203366096445875876493746659763349116787⟩
  | 2, 1 => ⟨7151827115582767205821958713314232851489107, 7151827115582767205821958713321383221725355⟩
  | 0, 4 => ⟨18112247111258906659678928755739535868675142, 18112247111258906659678928755754682656679366⟩
  | 1, 3 => ⟨51975765737338907756871039799196055500673248, 51975765737338907756871039799212749341546733⟩
  | 2, 2 => ⟨86877670305347582025835825425366284350666118, 86877670305347582025835825425387847665387003⟩
  | 3, 1 => ⟨89058563290541161661754196146349022583549489, 89058563290541161661754196146381330077583649⟩
  | 0, 5 => ⟨-152907648302788261896745495158027735042865405666, 152573386154411156690572595401450831550988233902⟩
  | 1, 4 => ⟨-231999728367444660514179483238622857212930263601, 229509962982542186056163290938518791783472198318⟩
  | 2, 3 => ⟨-372157104311357750051327892977546877527002161344, 367113763894054837212344085906710113452999006492⟩
  | 3, 2 => ⟨-606257650331850097072541330165836380929072972685, 598840780713915683009175359648415368557523633846⟩
  | 4, 1 => ⟨-978585308327055970312647223449946786886174142011, 971931777213711724492936590692821926790567430897⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0011Geometry.ds, E8TAxisProd0011Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 15235084111160529695938917651144653419025 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0011CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0012CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0012CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0012GraphCenterA.qJetBox,
   E8TAxisProd0012GraphCenterB.qJetBox,
   E8TAxisProd0012GraphCenterC.qJetBox,
   E8TAxisProd0012GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0012GraphWholeA.qJetBox,
   E8TAxisProd0012GraphWholeB.qJetBox,
   E8TAxisProd0012GraphWholeC.qJetBox,
   E8TAxisProd0012GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨14437175051920455869962789433053995442782, 14437175051920455869962789434083240342328⟩
  | 0, 2 => ⟨301626362018556519761480478277974781549455, 301626362018556519761480478281228062789039⟩
  | 1, 1 => ⟨317485955153869652035075373831334416429300, 317485955153869652035075373835289533444430⟩
  | 0, 3 => ⟨3177643024589874950259721460720830561537955, 3177643024589874950259721460725794829181840⟩
  | 1, 2 => ⟨5398409630070571325017393788722451669252698, 5398409630070571325017393788727903257798947⟩
  | 2, 1 => ⟨5612994703189318325486884108127711248735906, 5612994703189318325486884108134527985108094⟩
  | 0, 4 => ⟨15079393078100928912069535120798186734383632, 15079393078100928912069535120812912363352064⟩
  | 1, 3 => ⟨43726470546803252012501885165395972356051731, 43726470546803252012501885165412137184445548⟩
  | 2, 2 => ⟨73325013477048032345630182773904677151166156, 73325013477048032345630182773925420366614438⟩
  | 3, 1 => ⟨75309499115605201366159995554810588726572237, 75309499115605201366159995554841587305918414⟩
  | 0, 5 => ⟨-148806115050039486149294733413490711834238537305, 148408243550329373397698195753164666220956288161⟩
  | 1, 4 => ⟨-225217929637481490247605394205435305795314456649, 222797820470014388233839663669797512608430862386⟩
  | 2, 3 => ⟨-360328325790593186462478095937747902545174415489, 355498143104405842729171184485565871813242481039⟩
  | 3, 2 => ⟨-585427659955855585163536474592236657625883095341, 578312525888081900119931317643119100071088257780⟩
  | 4, 1 => ⟨-941858373924746162689039818331631543053508807522, 935265310519564201084018062189189599004973597514⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0012Geometry.ds, E8TAxisProd0012Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 9744473713936238276254828210720165747595 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0012CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0013CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0013CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0013GraphCenterA.qJetBox,
   E8TAxisProd0013GraphCenterB.qJetBox,
   E8TAxisProd0013GraphCenterC.qJetBox,
   E8TAxisProd0013GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0013GraphWholeA.qJetBox,
   E8TAxisProd0013GraphWholeB.qJetBox,
   E8TAxisProd0013GraphWholeC.qJetBox,
   E8TAxisProd0013GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨9391754738024304725080448001408118349623, 9391754738024304725080448002388498272634⟩
  | 0, 2 => ⟨212559495287637834733693134010391873046349, 212559495287637834733693134013579958977130⟩
  | 1, 1 => ⟨224733265211981245656450038504566671625080, 224733265211981245656450038508446827439075⟩
  | 0, 3 => ⟨2428587502325929341046193680789281900967884, 2428587502325929341046193680794063937019899⟩
  | 1, 2 => ⟨4140293409003197854137636533178240859490668, 4140293409003197854137636533183478783490496⟩
  | 2, 1 => ⟨4319454145745068227111227644088892191818039, 4319454145745068227111227644095387027768112⟩
  | 0, 4 => ⟨12393052102122018320009054802344787112413984, 12393052102122018320009054802359105636531333⟩
  | 1, 3 => ⟨36307400327437126447049532209592819827296149, 36307400327437126447049532209608477455361445⟩
  | 2, 2 => ⟨61088078403622504033907517613690456430563612, 61088078403622504033907517613710415089524371⟩
  | 3, 1 => ⟨62883325764009081120169357745276875344364071, 62883325764009081120169357745306624653623211⟩
  | 0, 5 => ⟨-144837300300024764712534428223791525139506794957, 144374416948856470110854099010697477415977887238⟩
  | 1, 4 => ⟨-218668165623191395883949452038822932880718837830, 216311220953592272535022392531934265476294963576⟩
  | 2, 3 => ⟨-348917426687356568995510432976916057382913311957, 344294618137876722106861598139123581905707541831⟩
  | 3, 2 => ⟨-565357501743653735093798109238871125842449108333, 558576413292229353912851106428257623069280188480⟩
  | 4, 1 => ⟨-906525376755574397094060014688077149002822937062, 900185127243941593022443777583174431867611862119⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0013Geometry.ds, E8TAxisProd0013Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 5903221607395226326819029288370187760178 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0013CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0014CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0014CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0014GraphCenterA.qJetBox,
   E8TAxisProd0014GraphCenterB.qJetBox,
   E8TAxisProd0014GraphCenterC.qJetBox,
   E8TAxisProd0014GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0014GraphWholeA.qJetBox,
   E8TAxisProd0014GraphWholeB.qJetBox,
   E8TAxisProd0014GraphWholeC.qJetBox,
   E8TAxisProd0014GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨5871367698691881953797553163182949973856, 5871367698691881953797553164115152111150⟩
  | 0, 2 => ⟨145005661229450159927557137857853057202657, 145005661229450159927557137860977937023087⟩
  | 1, 1 => ⟨154124939559932262339161977743549687323145, 154124939559932262339161977747357917828918⟩
  | 0, 3 => ⟨1811199015997731350708960257546196123733346, 1811199015997731350708960257550800487099622⟩
  | 1, 2 => ⟨3099764971019418978047797478718568024528619, 3099764971019418978047797478723599264662284⟩
  | 2, 1 => ⟨3246987739400169039549543127008136128551464, 3246987739400169039549543127014320237550370⟩
  | 0, 4 => ⟨10027019180260845229609116350216883539103719, 10027019180260845229609116350230808436559805⟩
  | 1, 3 => ⟨29675114459959573871908035029739979804532024, 29675114459959573871908035029755151102473443⟩
  | 2, 2 => ⟨50106019647537132667644710401868884466525346, 50106019647537132667644710401888092512843171⟩
  | 3, 1 => ⟨51718514105073507337072705130399646717461632, 51718514105073507337072705130428203651854452⟩
  | 0, 5 => ⟨-140986977739596390403276587211618721190149971627, 140461747952885386573703976442430889854893448494⟩
  | 1, 4 => ⟨-212330374214015168970118592737143184034082990484, 210035945010138915642793138227682723177902404437⟩
  | 2, 3 => ⟨-337893514098045100997549081434032775448732948087, 333474461135676358301319027076603192086381272978⟩
  | 3, 2 => ⟨-545999521638969830034765724653130455473844746918, 539552882127712436449879996652706692440858851283⟩
  | 4, 1 => ⟨-872509579473108928140851989399333407311446835405, 866452676110909990495919117924235528560689794745⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0014Geometry.ds, E8TAxisProd0014Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 3309328481674170647153238645871690568791 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0014CertifiedArithmetic

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0015CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0015CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0015GraphCenterA.qJetBox,
   E8TAxisProd0015GraphCenterB.qJetBox,
   E8TAxisProd0015GraphCenterC.qJetBox,
   E8TAxisProd0015GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0015GraphWholeA.qJetBox,
   E8TAxisProd0015GraphWholeB.qJetBox,
   E8TAxisProd0015GraphWholeC.qJetBox,
   E8TAxisProd0015GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨4516205542882306955981860961526529061531, 4516205542882306955981860962432209561405⟩
  | 0, 2 => ⟨108612384451204457598319106951891430108810, 108612384451204457598319106954984876768537⟩
  | 1, 1 => ⟨125479124683446078976224858242869189051065, 125479124683446078976224858246641119956556⟩
  | 0, 3 => ⟨1391018903655380954360308700203684158545255, 1391018903655380954360308700208199269693053⟩
  | 1, 2 => ⟨2496885743277973807975672205580599995127427, 2496885743277973807975672205585522465595119⟩
  | 2, 1 => ⟨2790573087545791513162997127084147929733283, 2790573087545791513162997127090153237292983⟩
  | 0, 4 => ⟨8027005268038590917457247516725933231495767, 8027005268038590917457247516739661505854349⟩
  | 1, 3 => ⟨24825014182287255503087040739178979820824816, 24825014182287255503087040739193885254425675⟩
  | 2, 2 => ⟨43308930363329426270728864672832448282132546, 43308930363329426270728864672851222424054339⟩
  | 3, 1 => ⟨46767431303193189769994550501280753339654144, 46767431303193189769994550501308627780717257⟩
  | 0, 5 => ⟨-138963622831732596709037831411570783758435753617, 138442280704680469287165383987849293043994542699⟩
  | 1, 4 => ⟨-209069771255588106842925978035917108251393027158, 206871219976137300292370464988972540936685139734⟩
  | 2, 3 => ⟨-332340901630058487117566716114257935382899646827, 328147753476125204188092018724051212941490768160⟩
  | 3, 2 => ⟨-536551006779875759793064317137585907998410873596, 530473489727214233226642398227069377984609893149⟩
  | 4, 1 => ⟨-856627043647120435539787639091714929476616778580, 850881323225774106181963125587789311414474095589⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0015Geometry.ds, E8TAxisProd0015Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 2359979697870852242888146492012816709570 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0015CertifiedArithmetic

end


