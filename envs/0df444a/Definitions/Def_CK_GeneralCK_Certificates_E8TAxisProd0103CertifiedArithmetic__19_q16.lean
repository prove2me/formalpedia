-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0103CertifiedArithmetic__19_q16
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0103CertifiedArithmetic__19_q16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T18:17:53.597175+00:00
-- url     : https://prove2.me/theorems/b865c231-e691-43bf-a202-6a17cbedaf26
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0105CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0106CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0107CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0108CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0109CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0111CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0112CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0113CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0114CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0117CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0118CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0120CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0121CertifiedArithmetic) (piece 17 of 19)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0105CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0106CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0107CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0108CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0109CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0111CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0112CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0113CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0114CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0117CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0118CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0120CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0121CertifiedArithmetic) (piece 17 of 19)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK.Certificates.E8TAxisProd0104CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0105CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0106CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0107CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0108CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0109CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0110CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0111CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0112CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0113CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0114CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0115CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0116CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0117CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0118CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0120CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0121CertifiedArithmetic) (piece 17 of 19) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0103CertifiedArithmetic (+18 modules: GeneralCK/Certificates/E8TAxisProd0104CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0105CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0106CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0107CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0108CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0109CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0110CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0111CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0112CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0113CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0114CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0115CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0116CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0117CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0118CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0119CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0120CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0121CertifiedArithmetic) (piece 17 of 19).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0103CertifiedArithmetic__19_q15

-- ===== source module GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0119GraphCenterA.qJetBox,
   E8TAxisProd0119GraphCenterB.qJetBox,
   E8TAxisProd0119GraphCenterC.qJetBox,
   E8TAxisProd0119GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0119GraphWholeA.qJetBox,
   E8TAxisProd0119GraphWholeB.qJetBox,
   E8TAxisProd0119GraphWholeC.qJetBox,
   E8TAxisProd0119GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨439422125938202358272776060994894229256730254, 439422125938202358272776060994904406229020824⟩
  | 0, 2 => ⟨1816155428198127626683435887553049139693000364, 1816155428198127626683435887553074531977291106⟩
  | 1, 1 => ⟨1849699812095689967162979214751368368445128301, 1849699812095689967162979214751406584720235499⟩
  | 0, 3 => ⟨4848409900989725391770180939613378946227563192, 4848409900989725391770180939613447278512172438⟩
  | 1, 2 => ⟨6968202407539748090231294600276626621379163046, 6968202407539748090231294600276730866376191734⟩
  | 2, 1 => ⟨7079284751392523836322174839157920336476240959, 7079284751392523836322174839158092840158339426⟩
  | 0, 4 => ⟨10591122392398823952497605690997853383165556823, 10591122392398823952497605690998052342543691366⟩
  | 1, 3 => ⟨17508822109369963439993320252077761307139977292, 17508822109369963439993320252078075874990295157⟩
  | 2, 2 => ⟨24515145858830044958179526162219624100469452466, 24515145858830044958179526162220156969960106322⟩
  | 3, 1 => ⟨24856020601124151062100748242979580776606538360, 24856020601124151062100748242980506607915886409⟩
  | 0, 5 => ⟨-80484588053215513420572112003521954417883128306217, 81103196849430258972275072293263919634581397315959⟩
  | 1, 4 => ⟨-153669131025515194910256937135238991364205452568514, 154508729301639307257740949829142287666659885001019⟩
  | 2, 3 => ⟨-294243537299103712155872564657725633746756611803057, 295377906832182859965274329428732630980941308492160⟩
  | 3, 2 => ⟨-564131592218764724315568454756004147403585921350211, 565586051145531011905496508096346944892167084869531⟩
  | 4, 1 => ⟨-1082121805063169160108475128176991540467806950276734, 1083680496745661455278062004813644889570213592159923⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0119Geometry.ds, E8TAxisProd0119Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 328702578231553797222420560226659838556176479 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0119CertifiedArithmetic

end


