-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0103CertifiedArithmetic__19_q13
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0103CertifiedArithmetic__19_q13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T17:28:44.112992+00:00
-- url     : https://prove2.me/theorems/85f0d7e6-29f9-41ca-b57c-75a91d9f00c3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0105CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0106CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0107CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0108CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0109CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0111CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0112CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0113CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0114CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0117CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0118CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0120CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0121CertifiedArithmetic) (piece 14 of 19)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0105CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0106CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0107CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0108CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0109CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0111CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0112CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0113CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0114CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0117CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0118CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0120CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0121CertifiedArithmetic) (piece 14 of 19)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0105CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0106CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0107CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0108CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0109CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0111CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0112CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0113CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0114CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0117CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0118CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0120CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0121CertifiedArithmetic) (piece 14 of 19) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK/Certificates/E8TAxisProd0104CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0105CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0106CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0107CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0108CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0109CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0110CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0111CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0112CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0113CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0114CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0115CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0116CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0117CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0118CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0119CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0120CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0121CertifiedArithmetic) (piece 14 of 19).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0103CertifiedArithmetic__19_q12

-- ===== source module GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0116GraphCenterA.qJetBox,
   E8TAxisProd0116GraphCenterB.qJetBox,
   E8TAxisProd0116GraphCenterC.qJetBox,
   E8TAxisProd0116GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0116GraphWholeA.qJetBox,
   E8TAxisProd0116GraphWholeB.qJetBox,
   E8TAxisProd0116GraphWholeC.qJetBox,
   E8TAxisProd0116GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨575696061388500887398469918759441713525441727, 575696061388500887398469918759453143943508713⟩
  | 0, 2 => ⟨2318147539473734152978114131320062090945143454, 2318147539473734152978114131320091259582352644⟩
  | 1, 1 => ⟨2365873076748181187322082461134024081205531889, 2365873076748181187322082461134068602781729904⟩
  | 0, 3 => ⟨6096809060584605318663237598521226138831099959, 6096809060584605318663237598521305821291798088⟩
  | 1, 2 => ⟨8719974880712651636079615491433660076286649585, 8719974880712651636079615491433783305589794955⟩
  | 2, 1 => ⟨8875621656554880183397949727871260741938975973, 8875621656554880183397949727871466168340722722⟩
  | 0, 4 => ⟨13207455340220714560636475987447614783568781547, 13207455340220714560636475987447849396253972047⟩
  | 1, 3 => ⟨21623247216598459288648815980451863997416840029, 21623247216598459288648815980452239720910052192⟩
  | 2, 2 => ⟨30159837221151745908372807764572257217285665059, 30159837221151745908372807764572898268521470687⟩
  | 3, 1 => ⟨30630511733194150628338746110884310848673865744, 30630511733194150628338746110885430583250497249⟩
  | 0, 5 => ⟨-104728206002951135872450136167546226226868562399406, 105530875408206214010676508264997724153408851232102⟩
  | 1, 4 => ⟨-200610021297718493688166622052564924712028474901621, 201725534203569322507704637627873247568851618522949⟩
  | 2, 3 => ⟨-385259031737360745302092591761089669955942251239186, 386793177313575149886736052956884458243077768503472⟩
  | 3, 2 => ⟨-740733474437992202692542336683622792133419173434480, 742722586788411133718031050354241545551280218269399⟩
  | 4, 1 => ⟨-1424928335465439760256631536327083431544712395423596, 1427066966733412686849545029977272636390745834625758⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0116Geometry.ds, E8TAxisProd0116Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 432432659243293238895209174899694482821117147 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic

end


