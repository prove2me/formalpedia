-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0253CertifiedArithmetic__18_q09
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0253CertifiedArithmetic__18_q09
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T22:56:16.49191+00:00
-- url     : https://prove2.me/theorems/c6015368-2e04-408c-93d3-928134471c6c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TA…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0255CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0256CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0258CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0259CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0260CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0261CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0263CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0264CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0265CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0267CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0268CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0270CertifiedArithmetic) (piece 10 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0255CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0256CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0258CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0259CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0260CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0261CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0263CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0264CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0265CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0267CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0268CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0270CertifiedArithmetic) (piece 10 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK.Certificates.E8TAxisProd0254CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0255CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0256CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0257CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0258CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0259CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0260CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0261CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0263CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0264CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0265CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0266CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0267CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0268CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0269CertifiedArithmetic, GeneralCK.Certificates.E8TAxisProd0270CertifiedArithmetic) (piece 10 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0253CertifiedArithmetic (+17 modules: GeneralCK/Certificates/E8TAxisProd0254CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0255CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0256CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0257CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0258CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0259CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0260CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0261CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0262CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0263CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0264CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0265CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0266CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0267CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0268CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0269CertifiedArithmetic, GeneralCK/Certificates/E8TAxisProd0270CertifiedArithmetic) (piece 10 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0253CertifiedArithmetic__18_q08

-- ===== source module GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic =====
section

/-! Exact checked mixed outputs from the eight padded stable graphs.
Generated by scripts/e8_taxis_emit_certified_arithmetic.py. -/

namespace GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := 160

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0262GraphCenterA.qJetBox,
   E8TAxisProd0262GraphCenterB.qJetBox,
   E8TAxisProd0262GraphCenterC.qJetBox,
   E8TAxisProd0262GraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisProd0262GraphWholeA.qJetBox,
   E8TAxisProd0262GraphWholeB.qJetBox,
   E8TAxisProd0262GraphWholeC.qJetBox,
   E8TAxisProd0262GraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨52125694137814001388072297785042005871653065731, 52125694137814001388072297785042274059240444331⟩
  | 0, 2 => ⟨148430917851990995015235950937312640567126687892, 148430917851990995015235950937313728438098673158⟩
  | 1, 1 => ⟨149713441153813812858545678177847880283628947983, 149713441153813812858545678177849876223005005977⟩
  | 0, 3 => ⟨291810753550837437087195870128859140411118146183, 291810753550837437087195870128862774335061216157⟩
  | 1, 2 => ⟨391016154701910932278081695283366689888595692690, 391016154701910932278081695283373292798532577853⟩
  | 2, 1 => ⟨393993268047225506278927658439037428966823096584, 393993268047225506278927658439049570165526942567⟩
  | 0, 4 => ⟨477825714287829765024411065843752756446604939707, 477825714287829765024411065843765513816921063798⟩
  | 1, 3 => ⟨706411054093260340983695776226726458817154590172, 706411054093260340983695776226749893732483914205⟩
  | 2, 2 => ⟨936394048573024658320610436272668077173442362524, 936394048573024658320610436272711617893701918346⟩
  | 3, 1 => ⟨942700906385669487625391339960442624447276199825, 942700906385669487625391339960524114345856232721⟩
  | 0, 5 => ⟨-2584148167899821870925141007120900615060541356098901, 2597131780280173992398057954815348801541428757423316⟩
  | 1, 4 => ⟨-5073066800999610989580672151123179425223828765442669, 5092649049869908080533492545733337612239523691211806⟩
  | 2, 3 => ⟨-9968387299423769529496306167272243698684108399367153, 9996625847614356826530189930065002231307841696134250⟩
  | 3, 2 => ⟨-19600094820452854839378995500025593881659452993287545, 19637188181180283485922846002001416587592505649549681⟩
  | 4, 1 => ⟨-38558134799105082960446290567256594612118364349123605, 38596120414188977304113353418489032036072195047211836⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisProd0262Geometry.ds, E8TAxisProd0262Geometry.dt, coeff⟩

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

theorem replay_lo : data.replay.lo = 49093862496574390732620681732434409444351177134 := by decide

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
end GeneralCK.Certificates.E8TAxisProd0262CertifiedArithmetic

end


