-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0253CertifiedArithmetic__18_q04
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0253CertifiedArithmetic__18_q04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T22:23:46.448276+00:00
-- url     : https://prove2.me/theorems/e3e95919-8cb7-4321-90b5-dcdf27025bf6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0255CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0256CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0258CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0259CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0260CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0261CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0263CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0264CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0265CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0267CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0268CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0270CertifiedArithmetic) (piece 5 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0255CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0256CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0258CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0259CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0260CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0261CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0263CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0264CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0265CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0267CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0268CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0270CertifiedArithmetic) (piece 5 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0255CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0256CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0258CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0259CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0260CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0261CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0263CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0264CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0265CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0267CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0268CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0270CertifiedArithmetic) (piece 5 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK/Certificates/E8TAxisProd0254CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0255CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0256CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0257CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0258CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0259CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0260CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0261CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0262CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0263CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0264CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0265CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0266CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0267CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0268CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0269CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0270CertifiedArithmetic) (piece 5 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0253CertifiedArithmetic__18_q03

-- ===== source module GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0257GraphCenterA.qJetBox,
   E8TAxisProd0257GraphCenterB.qJetBox,
   E8TAxisProd0257GraphCenterC.qJetBox,
   E8TAxisProd0257GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0257GraphWholeA.qJetBox,
   E8TAxisProd0257GraphWholeB.qJetBox,
   E8TAxisProd0257GraphWholeC.qJetBox,
   E8TAxisProd0257GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨57972008719497554626921496004291885451528943073, 57972008719497554626921496004292182590536170902⟩
  | 0, 2 => ⟨163502023679728980950021315851741535520695428760, 163502023679728980950021315851742749672784805342⟩
  | 1, 1 => ⟨165030641972704308928594838698143735954695332424, 165030641972704308928594838698145968568557764297⟩
  | 0, 3 => ⟨318875184505739300752982993715013971749533581297, 318875184505739300752982993715018043500556259895⟩
  | 1, 2 => ⟨426976191181318050721833243300485692417236645807, 426976191181318050721833243300493106278934064665⟩
  | 2, 1 => ⟨430498826238028073647790546503938904011996574046, 430498826238028073647790546503952559306748294334⟩
  | 0, 4 => ⟨518759975733595668691497679527742392928019507330, 518759975733595668691497679527756764120490519413⟩
  | 1, 3 => ⟨765886635772999934242373493779124323835574952743, 765886635772999934242373493779150768295976717348⟩
  | 2, 2 => ⟨1014656711076386069994017638351897144538619578862, 1014656711076386069994017638351946344090848783626⟩
  | 3, 1 => ⟨1022086264130158062822582844991700610950922851190, 1022086264130158062822582844991792808396357944130⟩
  | 0, 5 => ⟨-2885205917828310949718619737841790360423963500216462, 2899408039513711087702582893086638255915842084280929⟩
  | 1, 4 => ⟨-5666688344165968965523417883438500453054413596522657, 5688105759570755759449823698002696574009311489951964⟩
  | 2, 3 => ⟨-11139846509555293411396672783474998510795292651089220, 11170730154238501858235945552679014862138511771400514⟩
  | 3, 2 => ⟨-21913275347831568598982639028907487297595201181391728, 21953850224894352974574611611210742710227833140547955⟩
  | 4, 1 => ⟨-43128133194309065808495144541189270539457354423628388, 43169718690448675132118726270556297604268628516680983⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0257Geometry.ds, E8TAxisProd0257Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 54627835428736072728340299309946857416693662966 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic

end


