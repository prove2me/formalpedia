-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0031CertifiedArithmetic__15_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0031CertifiedArithmetic__15_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T14:45:40.935627+00:00
-- url     : https://prove2.me/theorems/80bef6f0-8f90-4868-9272-1768b7c76e7b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic) (piece 1 of 15)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic) (piece 1 of 15)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic) (piece 1 of 15) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK/Certificates/E8TAxisProd0032CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0033CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0034CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0035CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0036CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0037CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0038CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0039CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0040CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0041CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0042CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0043CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0044CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0045CertifiedArithmetic) (piece 1 of 15).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0029GraphCenterA__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0031GraphCenterB__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0018GraphCenterC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0030GraphCenterD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0022GraphWholeA__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0017GraphWholeB__14
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0018GraphWholeC__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0030GraphWholeD__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellBridge
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0025Geometry__23
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0034GraphWholeB__13
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0034GraphWholeC__12
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0038GraphCenterC__17
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0042GraphCenterA__16
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0042GraphWholeA__15
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0043GraphCenterB__14

-- ===== source module GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0031GraphCenterA.qJetBox,
   E8TAxisProd0031GraphCenterB.qJetBox,
   E8TAxisProd0031GraphCenterC.qJetBox,
   E8TAxisProd0031GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0031GraphWholeA.qJetBox,
   E8TAxisProd0031GraphWholeB.qJetBox,
   E8TAxisProd0031GraphWholeC.qJetBox,
   E8TAxisProd0031GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨509398957778416260821067151090914770726, 509398957778416260821067151840651697395⟩
  | 0, 2 => ⟨20638227812313642719665393941349874240156, 20638227812313642719665393944244261448555⟩
  | 1, 1 => ⟨21693651790136428894806688373845370955286, 21693651790136428894806688377398245516116⟩
  | 0, 3 => ⟨417404171310002876836484350605311854106287, 417404171310002876836484350609257822701118⟩
  | 1, 2 => ⟨712424595471062424087825608057237166700683, 712424595471062424087825608061518653367023⟩
  | 2, 1 => ⟨739865154400801105852003610098906876248386, 739865154400801105852003610103975173534915⟩
  | 0, 4 => ⟨3626735070566200821970472053117000042579800, 3626735070566200821970472053129497126162019⟩
  | 1, 3 => ⟨10945666948597006692613434437873911764856185, 10945666948597006692613434437887363248253855⟩
  | 2, 2 => ⟨18501309321241489280076235060537647996371004, 18501309321241489280076235060554224628893207⟩
  | 3, 1 => ⟨18980152124237608816463654511528991541824026, 18980152124237608816463654511553391248513652⟩
  | 0, 5 => ⟨-50074660173568702048719774662541072075168721979, 49988405368074854988445994605543955115976711188⟩
  | 1, 4 => ⟨-73098370740911356208424156354638231787794665081, 72662748338234270155915182521676402034252630482⟩
  | 2, 3 => ⟨-113632898511367537127743275842738671992823063361, 112845381322414944605827609791459480520770051732⟩
  | 3, 2 => ⟨-180287406876443520321402926146786049793184682161, 179182971648116233965033331867255656909109981590⟩
  | 4, 1 => ⟨-282542081427914345155579396795924534674965214747, 281577329253670040676108469647084490697719169467⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0031Geometry.ds, E8TAxisProd0031Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 358017884429158393023955765086308281759 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic

end


