-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0070EndpointWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0070EndpointWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:35:13.413759+00:00
-- url     : https://prove2.me/theorems/e8d26b02-8601-4397-a3c4-fbe0a834664e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0070EndpointWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0070EndpointWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0070EndpointWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0070EndpointWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0070EndpointWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0070EndpointWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0070EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0070Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerDLowerLog : DyadicInterval precision := ⟨494103945124224218680176638976803112022085061666, 494103945124224218680176638976803112022085156177⟩
def centerDLowerYBox : DyadicInterval precision := ⟨3579537213306547381694181211379333802047848661967, 3579537213306547381694181211379333802047850124813⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨587892208188294475401269251844616963792057408160, scale precision, 587892208188294475401269251844616963792057539233, scale precision,
    0, 512, 0, 512, ⟨-1330954601250866954722464005004005250691809543697, -1330954601250866954722464005004005250691809542662⟩, ⟨-1330954601250866954722464005004005250691809217849, -1330954601250866954722464005004005250691809216816⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

theorem centerDLower_denominators : DenominatorsPositive centerDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDLower_yBox_eq : (yBox centerDLowerInput).d0 = centerDLowerYBox := by decide +kernel

theorem centerDLower_contains :
    centerDLowerYBox.Contains (Y (lower E8TAxisZero0070PaddedInputs.centerDInput.alpha)) := by
  have e : lower E8TAxisZero0070PaddedInputs.centerDInput.alpha = ((665477300625433477361232002502002625345904689903 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDLowerInput.alpha.Contains (lower E8TAxisZero0070PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 665477300625433477361232002502002625345904689903
  have h := checked_yBox_d0_contains (i := centerDLowerInput) (we := centerDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDLower_primitive_checks.1 centerDLower_primitive_checks.2 endpointLogTwo_checked
    centerDLower_denominators ha
  rw [centerDLower_yBox_eq] at h
  exact h

def centerDUpperAlpha : DyadicInterval precision := ⟨665477300625433477361232002502002625345938244336, 665477300625433477361232002502002625345938244336⟩
def centerDUpperExp : DyadicInterval precision := ⟨587892208188294475401269251844616963792030413473, 587892208188294475401269251844616963792030544546⟩
def centerDUpperLog : DyadicInterval precision := ⟨494103945124224218680176638976803112022065810718, 494103945124224218680176638976803112022065905227⟩
def centerDUpperYBox : DyadicInterval precision := ⟨3579537213306547381694181211379333802048006938303, 3579537213306547381694181211379333802048008401140⟩
def centerDUpperInput : Inputs precision :=
  ⟨centerDUpperAlpha, centerDUpperExp, centerDUpperLog, endpointLogTwo⟩
def centerDUpperExpWitness : ExpWitness precision :=
  ⟨587892208188294475401269251844616963792030413473, scale precision, 587892208188294475401269251844616963792030544546, scale precision,
    0, 512, 0, 512, ⟨-1330954601250866954722464005004005250691876652563, -1330954601250866954722464005004005250691876651530⟩, ⟨-1330954601250866954722464005004005250691876326715, -1330954601250866954722464005004005250691876325682⟩⟩

theorem centerDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDUpperAlpha) centerDUpperExp centerDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDUpperExp) centerDUpperLog fastLogWitness = true := by decide +kernel

theorem centerDUpper_denominators : DenominatorsPositive centerDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDUpper_yBox_eq : (yBox centerDUpperInput).d0 = centerDUpperYBox := by decide +kernel

theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisZero0070PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisZero0070PaddedInputs.centerDInput.alpha = ((665477300625433477361232002502002625345938244336 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisZero0070PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 665477300625433477361232002502002625345938244336
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

def wholeBLowerAlpha : DyadicInterval precision := ⟨1587858894860446235976143311582642247749970131357, 1587858894860446235976143311582642247749970131357⟩
def wholeBLowerExp : DyadicInterval precision := ⟨166385172499093390938202185071882482935184920357, 166385172499093390938202185071882482935185051430⟩
def wholeBLowerLog : DyadicInterval precision := ⟨157576639748373200749695980667750103083395497440, 157576639748373200749695980667750103083395616147⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨7106551711521515439765417499082926183076915866786, 7106551711521515439765417499082926183076920997928⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨166385172499093390938202185071882482935184920357, scale precision, 166385172499093390938202185071882482935185051430, scale precision,
    0, 512, 0, 512, ⟨-3175717789720892471952286623165284495499940839185, -3175717789720892471952286623165284495499940838132⟩, ⟨-3175717789720892471952286623165284495499939687865, -3175717789720892471952286623165284495499939686814⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

theorem wholeBLower_denominators : DenominatorsPositive wholeBLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBLower_yBox_eq : (yBox wholeBLowerInput).d0 = wholeBLowerYBox := by decide +kernel

theorem wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisZero0070PaddedInputs.wholeBInput.alpha)) := by
  have e : lower E8TAxisZero0070PaddedInputs.wholeBInput.alpha = ((1587858894860446235976143311582642247749970131357 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBLowerInput.alpha.Contains (lower E8TAxisZero0070PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1587858894860446235976143311582642247749970131357
  have h := checked_yBox_d0_contains (i := wholeBLowerInput) (we := wholeBLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBLower_primitive_checks.1 wholeBLower_primitive_checks.2 endpointLogTwo_checked
    wholeBLower_denominators ha
  rw [wholeBLower_yBox_eq] at h
  exact h

def wholeBUpperAlpha : DyadicInterval precision := ⟨1621480652225727667592799454759990618247413284248, 1621480652225727667592799454759990618247413284248⟩
def wholeBUpperExp : DyadicInterval precision := ⟨158903251675320738035825572853393162264604670994, 158903251675320738035825572853393162264604802067⟩
def wholeBUpperLog : DyadicInterval precision := ⟨150843956919355702479650421140762544522464504588, 150843956919355702479650421140762544522464623841⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨7213424018751337715659061952475304378889362491833, 7213424018751337715659061952475304378889367832896⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨158903251675320738035825572853393162264604670994, scale precision, 158903251675320738035825572853393162264604802067, scale precision,
    0, 512, 0, 512, ⟨-3242961304451455335185598909519981236494827172058, -3242961304451455335185598909519981236494827170996⟩, ⟨-3242961304451455335185598909519981236494825966524, -3242961304451455335185598909519981236494825965460⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisZero0070PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisZero0070PaddedInputs.wholeBInput.alpha = ((1621480652225727667592799454759990618247413284248 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisZero0070PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1621480652225727667592799454759990618247413284248
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨659917674403335303398947154306570012946005250351, 659917674403335303398947154306570012946005250351⟩
def wholeCLowerExp : DyadicInterval precision := ⟨592382009410612930615839145836493982194259987576, 592382009410612930615839145836493982194260118649⟩
def wholeCLowerLog : DyadicInterval precision := ⟨497302293015079090720897450218278678648275488568, 497302293015079090720897450218278678648275582873⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨3553275855760757719882708749541463091538405910475, 3553275855760757719882708749541463091538407358875⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨592382009410612930615839145836493982194259987576, scale precision, 592382009410612930615839145836493982194260118649, scale precision,
    0, 512, 0, 512, ⟨-1319835348806670606797894308613140025892010663359, -1319835348806670606797894308613140025892010662324⟩, ⟨-1319835348806670606797894308613140025892010339983, -1319835348806670606797894308613140025892010338948⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

theorem wholeCLower_denominators : DenominatorsPositive wholeCLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0070EndpointWitnesses


