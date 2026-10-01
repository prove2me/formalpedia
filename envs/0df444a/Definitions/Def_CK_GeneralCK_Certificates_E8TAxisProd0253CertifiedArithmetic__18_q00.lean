-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0253CertifiedArithmetic__18_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0253CertifiedArithmetic__18_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:51:18.760974+00:00
-- url     : https://prove2.me/theorems/89e8af96-3c66-49bc-aa88-f5d8fee9935c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0255CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0256CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0258CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0259CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0260CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0261CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0263CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0264CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0265CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0267CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0268CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0270CertifiedArithmetic) (piece 1 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0255CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0256CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0258CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0259CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0260CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0261CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0263CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0264CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0265CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0267CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0268CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0270CertifiedArithmetic) (piece 1 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0255CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0256CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0258CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0259CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0260CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0261CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0263CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0264CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0265CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0267CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0268CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0270CertifiedArithmetic) (piece 1 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK/Certificates/E8TAxisProd0254CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0255CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0256CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0257CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0258CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0259CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0260CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0261CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0262CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0263CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0264CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0265CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0266CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0267CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0268CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0269CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0270CertifiedArithmetic) (piece 1 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0245GraphCenterA__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0252GraphCenterB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0252GraphCenterC__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0247GraphCenterD__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0249GraphWholeA__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0245GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0253GraphWholeC__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0246GraphWholeD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0234Geometry__23
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0256GraphCenterA__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0256GraphCenterD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0256GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0257GraphWholeD__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0257Geometry__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0261GraphCenterC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0261GraphWholeA__7
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0264GraphCenterB__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0264GraphWholeC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0265GraphCenterA__8
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0267GraphCenterD__10
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0267GraphWholeB__11
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0268GraphWholeA__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0268GraphWholeD__17

-- ===== source module GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0253GraphCenterA.qJetBox,
   E8TAxisProd0253GraphCenterB.qJetBox,
   E8TAxisProd0253GraphCenterC.qJetBox,
   E8TAxisProd0253GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0253GraphWholeA.qJetBox,
   E8TAxisProd0253GraphWholeB.qJetBox,
   E8TAxisProd0253GraphWholeC.qJetBox,
   E8TAxisProd0253GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨70520156674118571371693808741730430168990481389, 70520156674118571371693808741730792350075335103⟩
  | 0, 2 => ⟨196008926193173791833079863187096945706258362739, 196008926193173791833079863187098445330005180951⟩
  | 1, 1 => ⟨197493264634099452413452971601296030302074322786, 197493264634099452413452971601298799290428984766⟩
  | 0, 3 => ⟨376960047828353221971536886658256138663242968121, 376960047828353221971536886658261204681754668698⟩
  | 1, 2 => ⟨503645503979372562573120186400822061663320030605, 503645503979372562573120186400831321827072595122⟩
  | 2, 1 => ⟨507020923732084583088644541532251002160895408694, 507020923732084583088644541532268112358659997986⟩
  | 0, 4 => ⟨606248078579690934329153878514577320494508667400, 606248078579690934329153878514595380406008615799⟩
  | 1, 3 => ⟨892470300869367613089967158939084442473724927898, 892470300869367613089967158939117781044032091713⟩
  | 2, 2 => ⟨1180250166328742807840316940175096492568479492475, 1180250166328742807840316940175158679641793473785⟩
  | 3, 1 => ⟨1187314355822505831713202317668170912949205454797, 1187314355822505831713202317668287729215659241154⟩
  | 0, 5 => ⟨-3532987692723384369849527745770285910405114799157972, 3549734545778211027203361221871088949334137570905519⟩
  | 1, 4 => ⟨-6944707493488118631943318212950516882651065978640693, 6969943360228676059559024185837218537884928244985572⟩
  | 2, 3 => ⟨-13663375825621938662914316599564167981277031647931182, 13699737714192491490671904877409826970488409981446530⟩
  | 3, 2 => ⟨-26899239110912533611029501698481084658179400101493335, 26946968741672047151794927191870499492086252244912370⟩
  | 4, 1 => ⟨-52984558849142928604544669192845939401440597614628401, 53033381255896739687398253729805088420428849055260810⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0253Geometry.ds, E8TAxisProd0253Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 66513007883032807791947103964098163068692426481 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic

end


