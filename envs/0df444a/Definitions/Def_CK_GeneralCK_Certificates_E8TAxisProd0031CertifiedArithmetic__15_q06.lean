-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0031CertifiedArithmetic__15_q06
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0031CertifiedArithmetic__15_q06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T15:20:03.110369+00:00
-- url     : https://prove2.me/theorems/4e0c21d2-5825-4bbd-80b8-2753f68c8474
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic) (piece 7 of 15)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic) (piece 7 of 15)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK.Certificates.E8TAxisProd0032CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0033CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0034CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0035CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0036CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0038CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0039CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0040CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0041CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0042CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0043CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0044CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0045CertifiedArithmetic) (piece 7 of 15) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0031CertifiedArithmetic (+14 modules: GeneralCK/Certificates/E8TAxisProd0032CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0033CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0034CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0035CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0036CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0037CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0038CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0039CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0040CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0041CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0042CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0043CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0044CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0045CertifiedArithmetic) (piece 7 of 15).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0031CertifiedArithmetic__15_q05

-- ===== source module GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0037GraphCenterA.qJetBox,
   E8TAxisProd0037GraphCenterB.qJetBox,
   E8TAxisProd0037GraphCenterC.qJetBox,
   E8TAxisProd0037GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0037GraphWholeA.qJetBox,
   E8TAxisProd0037GraphWholeB.qJetBox,
   E8TAxisProd0037GraphWholeC.qJetBox,
   E8TAxisProd0037GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨389794375585041179707763795854775539398015, 389794375585041179707763795856403503636786⟩
  | 0, 2 => ⟨4287624708678437647346302205890334424128302, 4287624708678437647346302205894472498731727⟩
  | 1, 1 => ⟨4563222350443326717295821984963767404698387, 4563222350443326717295821984968796111625097⟩
  | 0, 3 => ⟨24717578337002011704986015645576067393635012, 24717578337002011704986015645583440011899799⟩
  | 1, 2 => ⟨41475116605918143571537242141738809324137593, 41475116605918143571537242141747212169243542⟩
  | 2, 1 => ⟨43516943998045068064553336248336023235509642, 43516943998045068064553336248347331809644134⟩
  | 0, 4 => ⟨73721548051670033887381974215070457595162307, 73721548051670033887381974215090820732897240⟩
  | 1, 3 => ⟨191081058644936991178576615539796130217663701, 191081058644936991178576615539819623685275198⟩
  | 2, 2 => ⟨313201557671246562853229854783071470893105594, 313201557671246562853229854783103682650744624⟩
  | 3, 1 => ⟨324145354094624871044593688995939157540210534, 324145354094624871044593688995988684009629944⟩
  | 0, 5 => ⟨-468878873772741373592628065259884728704455865231, 473789259113936526168062896648992820586632606506⟩
  | 1, 4 => ⟨-766352698316203500836008031801366843811969936889, 766270705743828643486709035828662878290466282404⟩
  | 2, 3 => ⟨-1292925905489056644848480848238709838928041774615, 1286851435490958516298897757717234994333987055843⟩
  | 3, 2 => ⟨-2197045249878732132322188207140875874803488443714, 2185502025540229663718391809573343930283952154682⟩
  | 4, 1 => ⟨-3713193803500496518565776225568429822265050152637, 3703698992400455616053696851250774000939991660417⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0037Geometry.ds, E8TAxisProd0037Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 287215191600565903747139564294767505988009 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0037CertifiedArithmetic

end


