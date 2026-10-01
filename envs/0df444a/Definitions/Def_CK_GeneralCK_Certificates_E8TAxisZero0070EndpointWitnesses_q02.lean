-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0070EndpointWitnesses_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0070EndpointWitnesses_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:49:27.95883+00:00
-- url     : https://prove2.me/theorems/bb4725ea-4e62-414d-b6c2-c4a189a91b03
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0070EndpointWitnesses (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0070EndpointWitnesses (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0070EndpointWitnesses (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0070EndpointWitnesses (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0070EndpointWitnesses (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0070EndpointWitnesses_q01

namespace GeneralCK.Certificates.E8TAxisZero0070EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0070Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem wholeCLower_yBox_eq : (yBox wholeCLowerInput).d0 = wholeCLowerYBox := by decide +kernel

theorem wholeCLower_contains :
    wholeCLowerYBox.Contains (Y (lower E8TAxisZero0070PaddedInputs.wholeCInput.alpha)) := by
  have e : lower E8TAxisZero0070PaddedInputs.wholeCInput.alpha = ((659917674403335303398947154306570012946005250351 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCLowerInput.alpha.Contains (lower E8TAxisZero0070PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 659917674403335303398947154306570012946005250351
  have h := checked_yBox_d0_contains (i := wholeCLowerInput) (we := wholeCLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCLower_primitive_checks.1 wholeCLower_primitive_checks.2 endpointLogTwo_checked
    wholeCLower_denominators ha
  rw [wholeCLower_yBox_eq] at h
  exact h

def wholeCUpperAlpha : DyadicInterval precision := ⟨671440902009004248126867720023776049226276500860, 671440902009004248126867720023776049226276500860⟩
def wholeCUpperExp : DyadicInterval precision := ⟨583113988827986525171167068164318274803275323865, 583113988827986525171167068164318274803275454938⟩
def wholeCUpperLog : DyadicInterval precision := ⟨490692434409458928876431019351388740990779004184, 490692434409458928876431019351388740990779098907⟩
def wholeCUpperYBox : DyadicInterval precision := ⟨3607625447899000672153408279258099866332019147318, 3607625447899000672153408279258099866332020625699⟩
def wholeCUpperInput : Inputs precision :=
  ⟨wholeCUpperAlpha, wholeCUpperExp, wholeCUpperLog, endpointLogTwo⟩
def wholeCUpperExpWitness : ExpWitness precision :=
  ⟨583113988827986525171167068164318274803275323865, scale precision, 583113988827986525171167068164318274803275454938, scale precision,
    0, 512, 0, 512, ⟨-1342881804018008496253735440047552098452553166947, -1342881804018008496253735440047552098452553165914⟩, ⟨-1342881804018008496253735440047552098452552838435, -1342881804018008496253735440047552098452552837396⟩⟩

theorem wholeCUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCUpperAlpha) wholeCUpperExp wholeCUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCUpperExp) wholeCUpperLog fastLogWitness = true := by decide +kernel

theorem wholeCUpper_denominators : DenominatorsPositive wholeCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeCUpper_yBox_eq : (yBox wholeCUpperInput).d0 = wholeCUpperYBox := by decide +kernel

theorem wholeCUpper_contains :
    wholeCUpperYBox.Contains (Y (upper E8TAxisZero0070PaddedInputs.wholeCInput.alpha)) := by
  have e : upper E8TAxisZero0070PaddedInputs.wholeCInput.alpha = ((671440902009004248126867720023776049226276500860 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCUpperInput.alpha.Contains (upper E8TAxisZero0070PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 671440902009004248126867720023776049226276500860
  have h := checked_yBox_d0_contains (i := wholeCUpperInput) (we := wholeCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCUpper_primitive_checks.1 wholeCUpper_primitive_checks.2 endpointLogTwo_checked
    wholeCUpper_denominators ha
  rw [wholeCUpper_yBox_eq] at h
  exact h

def wholeDLowerAlpha : DyadicInterval precision := ⟨659917674403335303398947154306570012946005250351, 659917674403335303398947154306570012946005250351⟩
def wholeDLowerExp : DyadicInterval precision := ⟨592382009410612930615839145836493982194259987576, 592382009410612930615839145836493982194260118649⟩
def wholeDLowerLog : DyadicInterval precision := ⟨497302293015079090720897450218278678648275488568, 497302293015079090720897450218278678648275582873⟩
def wholeDLowerYBox : DyadicInterval precision := ⟨3553275855760757719882708749541463091538405910475, 3553275855760757719882708749541463091538407358875⟩
def wholeDLowerInput : Inputs precision :=
  ⟨wholeDLowerAlpha, wholeDLowerExp, wholeDLowerLog, endpointLogTwo⟩
def wholeDLowerExpWitness : ExpWitness precision :=
  ⟨592382009410612930615839145836493982194259987576, scale precision, 592382009410612930615839145836493982194260118649, scale precision,
    0, 512, 0, 512, ⟨-1319835348806670606797894308613140025892010663359, -1319835348806670606797894308613140025892010662324⟩, ⟨-1319835348806670606797894308613140025892010339983, -1319835348806670606797894308613140025892010338948⟩⟩

theorem wholeDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDLowerAlpha) wholeDLowerExp wholeDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDLowerExp) wholeDLowerLog fastLogWitness = true := by decide +kernel

theorem wholeDLower_denominators : DenominatorsPositive wholeDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDLower_yBox_eq : (yBox wholeDLowerInput).d0 = wholeDLowerYBox := by decide +kernel

theorem wholeDLower_contains :
    wholeDLowerYBox.Contains (Y (lower E8TAxisZero0070PaddedInputs.wholeDInput.alpha)) := by
  have e : lower E8TAxisZero0070PaddedInputs.wholeDInput.alpha = ((659917674403335303398947154306570012946005250351 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDLowerInput.alpha.Contains (lower E8TAxisZero0070PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 659917674403335303398947154306570012946005250351
  have h := checked_yBox_d0_contains (i := wholeDLowerInput) (we := wholeDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDLower_primitive_checks.1 wholeDLower_primitive_checks.2 endpointLogTwo_checked
    wholeDLower_denominators ha
  rw [wholeDLower_yBox_eq] at h
  exact h

def wholeDUpperAlpha : DyadicInterval precision := ⟨671052481512572809340093335645151882932890891754, 671052481512572809340093335645151882932890891754⟩
def wholeDUpperExp : DyadicInterval precision := ⟨583424017396714902499808941799093864691228603789, 583424017396714902499808941799093864691228734862⟩
def wholeDUpperLog : DyadicInterval precision := ⟨490914027605645316992013980560028281716307636320, 490914027605645316992013980560028281716307731025⟩
def wholeDUpperYBox : DyadicInterval precision := ⟨3605798570852337043505653673217204512557449247560, 3605798570852337043505653673217204512557450724912⟩
def wholeDUpperInput : Inputs precision :=
  ⟨wholeDUpperAlpha, wholeDUpperExp, wholeDUpperLog, endpointLogTwo⟩
def wholeDUpperExpWitness : ExpWitness precision :=
  ⟨583424017396714902499808941799093864691228603789, scale precision, 583424017396714902499808941799093864691228734862, scale precision,
    0, 512, 0, 512, ⟨-1342104963025145618680186671290303765865781948647, -1342104963025145618680186671290303765865781947612⟩, ⟨-1342104963025145618680186671290303765865781620305, -1342104963025145618680186671290303765865781619268⟩⟩

theorem wholeDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDUpperAlpha) wholeDUpperExp wholeDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDUpperExp) wholeDUpperLog fastLogWitness = true := by decide +kernel

theorem wholeDUpper_denominators : DenominatorsPositive wholeDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDUpper_yBox_eq : (yBox wholeDUpperInput).d0 = wholeDUpperYBox := by decide +kernel

theorem wholeDUpper_contains :
    wholeDUpperYBox.Contains (Y (upper E8TAxisZero0070PaddedInputs.wholeDInput.alpha)) := by
  have e : upper E8TAxisZero0070PaddedInputs.wholeDInput.alpha = ((671052481512572809340093335645151882932890891754 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDUpperInput.alpha.Contains (upper E8TAxisZero0070PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 671052481512572809340093335645151882932890891754
  have h := checked_yBox_d0_contains (i := wholeDUpperInput) (we := wholeDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDUpper_primitive_checks.1 wholeDUpper_primitive_checks.2 endpointLogTwo_checked
    wholeDUpper_denominators ha
  rw [wholeDUpper_yBox_eq] at h
  exact h

theorem centerB_covers_slope {s : ℝ} (hs : s ∈ Icc (2 * centerS + centerT) (2 * centerS + centerT)) :
    ∃ a : ℝ, E8TAxisZero0070PaddedInputs.centerBInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerBLower_contains centerBUpper_contains _ _ hs
  · norm_num [centerBLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerBUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerB_covers :
    ∃ a : ℝ, E8TAxisZero0070PaddedInputs.centerBInput.alpha.Contains a ∧
      0 < a ∧ Y a = (2 * centerS + centerT) :=
  centerB_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerC_covers_slope {s : ℝ} (hs : s ∈ Icc (centerS + centerT) (centerS + centerT)) :
    ∃ a : ℝ, E8TAxisZero0070PaddedInputs.centerCInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerCLower_contains centerCUpper_contains _ _ hs
  · norm_num [centerCLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerCUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerC_covers :
    ∃ a : ℝ, E8TAxisZero0070PaddedInputs.centerCInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerS + centerT) :=
  centerC_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerD_covers_slope {s : ℝ} (hs : s ∈ Icc (centerS) (centerS)) :
    ∃ a : ℝ, E8TAxisZero0070PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerDLower_contains centerDUpper_contains _ _ hs
  · norm_num [centerDLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerDUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerD_covers :
    ∃ a : ℝ, E8TAxisZero0070PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerS) :=
  centerD_covers_slope ⟨le_rfl, le_rfl⟩

theorem wholeB_covers_slope {s : ℝ} (hs : s ∈ Icc (2 * sLower + tLower) (2 * sUpper + tUpper)) :
    ∃ a : ℝ, E8TAxisZero0070PaddedInputs.wholeBInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeBLower_contains wholeBUpper_contains _ _ hs
  · norm_num [wholeBLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeBUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem wholeC_covers_slope {s : ℝ} (hs : s ∈ Icc (sLower + tLower) (sUpper + tUpper)) :
    ∃ a : ℝ, E8TAxisZero0070PaddedInputs.wholeCInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeCLower_contains wholeCUpper_contains _ _ hs
  · norm_num [wholeCLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeCUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

end GeneralCK.Certificates.E8TAxisZero0070EndpointWitnesses


