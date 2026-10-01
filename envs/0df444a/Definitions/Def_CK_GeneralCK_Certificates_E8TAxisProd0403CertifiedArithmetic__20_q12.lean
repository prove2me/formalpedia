-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0403CertifiedArithmetic__20_q12
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0403CertifiedArithmetic__20_q12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:34:33.036311+00:00
-- url     : https://prove2.me/theorems/4583e38e-3ca3-4ffd-ae3f-e2e66a47bd7a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0405CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0406CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0407CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0408CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0409CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0410CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0412CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0414CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0417CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0418CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0420CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0421CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0422CertifiedArithmetic) (piece 13 of 20)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0405CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0406CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0407CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0408CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0409CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0410CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0412CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0414CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0417CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0418CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0420CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0421CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0422CertifiedArithmetic) (piece 13 of 20)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK.Certificates.E8TAxisProd0404CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0405CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0406CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0407CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0408CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0409CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0410CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0411CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0412CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0413CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0414CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0416CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0417CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0418CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0419CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0420CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0421CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0422CertifiedArithmetic) (piece 13 of 20) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0403CertifiedArithmetic (+19 modules: GeneralCK/Certificates/E8TAxisProd0404CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0405CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0406CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0407CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0408CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0409CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0410CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0411CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0412CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0413CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0414CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0415CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0416CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0417CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0418CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0419CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0420CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0421CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0422CertifiedArithmetic) (piece 13 of 20).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0403CertifiedArithmetic__20_q11

-- ===== source module GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0415GraphCenterA.qJetBox,
   E8TAxisProd0415GraphCenterB.qJetBox,
   E8TAxisProd0415GraphCenterC.qJetBox,
   E8TAxisProd0415GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0415GraphWholeA.qJetBox,
   E8TAxisProd0415GraphWholeB.qJetBox,
   E8TAxisProd0415GraphWholeC.qJetBox,
   E8TAxisProd0415GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨19516671584549801905513634858147391055927738689, 19516671584549801905513634858147501242983036029⟩
  | 0, 2 => ⟨60456018703035732634270244840459557619907594002, 60456018703035732634270244840459970834450186908⟩
  | 1, 1 => ⟨60818145593576632204283359262312427304046416760, 60818145593576632204283359262313167058164082180⟩
  | 0, 3 => ⟨128143893886732883028748564505680566901179012573, 128143893886732883028748564505681901585908387941⟩
  | 1, 2 => ⟨173167263377171928215806589774066227805226042559, 173167263377171928215806589774068601015398516767⟩
  | 2, 1 => ⟨174074818727150107040118976377966281690137926329, 174074818727150107040118976377970574152150877603⟩
  | 0, 4 => ⟨224431366230594117523676224628904183660235821567, 224431366230594117523676224628908683295724135936⟩
  | 1, 3 => ⟨336686897967260275540065528841735378683101589230, 336686897967260275540065528841743502855736432903⟩
  | 2, 2 => ⟨449403683377341106880167797920961211091258477306, 449403683377341106880167797920976108050096786680⟩
  | 3, 1 => ⟨451438281981059031871285235172550144011280650947, 451438281981059031871285235172577693126821175569⟩
  | 0, 5 => ⟨-879440595952955767074691381081869701298867785474993, 884547559437228163788487985615358009904918408753249⟩
  | 1, 4 => ⟨-1717618472097572965115773934607827049232564141830753, 1725285901988519960160907546631552604586223186071915⟩
  | 2, 3 => ⟨-3358316449800849586359926384593228435585977959341611, 3369341974698296962284131122965406432777690570785406⟩
  | 3, 2 => ⟨-6570813431108428068549505321395428174687010883669820, 6585271817740744925749012523314751474277877661733175⟩
  | 4, 1 => ⟨-12862955627066675805675889413738199106262193431502881, 12877735623597379328511759328184803136828146583473761⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0415Geometry.ds, E8TAxisProd0415Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 18295481071711394743952384705021635559394042151 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0415CertifiedArithmetic

end


