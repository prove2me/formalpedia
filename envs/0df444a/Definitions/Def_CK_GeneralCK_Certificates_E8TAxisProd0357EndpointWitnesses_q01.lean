-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0357EndpointWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0357EndpointWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T20:56:49.35124+00:00
-- url     : https://prove2.me/theorems/5391f9a0-a38d-4710-aee5-f3f4159ab6fa
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0357EndpointWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0357EndpointWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0357EndpointWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0357EndpointWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0357EndpointWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0357EndpointWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisProd0357EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisProd0357Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem centerCUpper_denominators : DenominatorsPositive centerCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerCUpper_yBox_eq : (yBox centerCUpperInput).d0 = centerCUpperYBox := by decide +kernel

theorem centerCUpper_contains :
    centerCUpperYBox.Contains (Y (upper E8TAxisProd0357PaddedInputs.centerCInput.alpha)) := by
  have e : upper E8TAxisProd0357PaddedInputs.centerCInput.alpha = ((806972136043735805908404043955502647134998140010 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerCUpperInput.alpha.Contains (upper E8TAxisProd0357PaddedInputs.centerCInput.alpha) := by
    rw [e]; exact point_contains precision 806972136043735805908404043955502647134998140010
  have h := checked_yBox_d0_contains (i := centerCUpperInput) (we := centerCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerCUpper_primitive_checks.1 centerCUpper_primitive_checks.2 endpointLogTwo_checked
    centerCUpper_denominators ha
  rw [centerCUpper_yBox_eq] at h
  exact h

def centerDLowerAlpha : DyadicInterval precision := ⟨803852177515934255585547919467375235228063908755, 803852177515934255585547919467375235228063908755⟩
def centerDLowerExp : DyadicInterval precision := ⟨486474140463139135434442039725801312843825596802, 486474140463139135434442039725801312843825598851⟩
def centerDLowerLog : DyadicInterval precision := ⟨419927923473864759956554512738531499109040501592, 419927923473864759956554512738531499109040503397⟩
def centerDLowerYBox : DyadicInterval precision := ⟨4209809794405499265169520295488230854274549138395, 4209809794405499265169520295488230854274549169271⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨486474140463139135434442039725801312843825596802, scale precision, 486474140463139135434442039725801312843825598851, scale precision,
    1, 128, 1, 128,
    ⟨-1607704355031868511171095838934750470456127821038, -1607704355031868511171095838934750470456127820498⟩, ⟨-1607704355031868511171095838934750470456127814880, -1607704355031868511171095838934750470456127814342⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

theorem centerDLower_denominators : DenominatorsPositive centerDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDLower_yBox_eq : (yBox centerDLowerInput).d0 = centerDLowerYBox := by decide +kernel

theorem centerDLower_contains :
    centerDLowerYBox.Contains (Y (lower E8TAxisProd0357PaddedInputs.centerDInput.alpha)) := by
  have e : lower E8TAxisProd0357PaddedInputs.centerDInput.alpha = ((803852177515934255585547919467375235228063908755 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDLowerInput.alpha.Contains (lower E8TAxisProd0357PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 803852177515934255585547919467375235228063908755
  have h := checked_yBox_d0_contains (i := centerDLowerInput) (we := centerDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDLower_primitive_checks.1 centerDLower_primitive_checks.2 endpointLogTwo_checked
    centerDLower_denominators ha
  rw [centerDLower_yBox_eq] at h
  exact h

def centerDUpperAlpha : DyadicInterval precision := ⟨803852177515934255585547919467375235228064039828, 803852177515934255585547919467375235228064039828⟩
def centerDUpperExp : DyadicInterval precision := ⟨486474140463139135434442039725801312843825509545, 486474140463139135434442039725801312843825511594⟩
def centerDUpperLog : DyadicInterval precision := ⟨419927923473864759956554512738531499109040436122, 419927923473864759956554512738531499109040437931⟩
def centerDUpperYBox : DyadicInterval precision := ⟨4209809794405499265169520295488230854274549714466, 4209809794405499265169520295488230854274549745357⟩
def centerDUpperInput : Inputs precision :=
  ⟨centerDUpperAlpha, centerDUpperExp, centerDUpperLog, endpointLogTwo⟩
def centerDUpperExpWitness : ExpWitness precision :=
  ⟨486474140463139135434442039725801312843825509545, scale precision, 486474140463139135434442039725801312843825511594, scale precision,
    1, 128, 1, 128,
    ⟨-1607704355031868511171095838934750470456128083186, -1607704355031868511171095838934750470456128082644⟩, ⟨-1607704355031868511171095838934750470456128077030, -1607704355031868511171095838934750470456128076486⟩⟩

theorem centerDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDUpperAlpha) centerDUpperExp centerDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDUpperExp) centerDUpperLog fastLogWitness = true := by decide +kernel

theorem centerDUpper_denominators : DenominatorsPositive centerDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDUpper_yBox_eq : (yBox centerDUpperInput).d0 = centerDUpperYBox := by decide +kernel

theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisProd0357PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisProd0357PaddedInputs.centerDInput.alpha = ((803852177515934255585547919467375235228064039828 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisProd0357PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 803852177515934255585547919467375235228064039828
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

def wholeALowerAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012888708, 2216017656540843594568486214625237657012888708⟩
def wholeALowerExp : DyadicInterval precision := ⟨1457076315351450948047082186788007226070285570916, 1457076315351450948047082186788007226070285572965⟩
def wholeALowerLog : DyadicInterval precision := ⟨1010821401672838003372446069258059722889029660898, 1010821401672838003372446069258059722889029662201⟩
def wholeALowerYBox : DyadicInterval precision := ⟨12788139326645400534282242286267476421989030048, 12788139326645400534282242286267476421989033065⟩
def wholeALowerInput : Inputs precision :=
  ⟨wholeALowerAlpha, wholeALowerExp, wholeALowerLog, endpointLogTwo⟩
def wholeALowerExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007226070285570916, scale precision, 1457076315351450948047082186788007226070285572965, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475314025778693, -4432035313081687189136972429250475314025778432⟩, ⟨-4432035313081687189136972429250475314025776639, -4432035313081687189136972429250475314025776378⟩⟩

theorem wholeALower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeALowerAlpha) wholeALowerExp wholeALowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeALowerExp) wholeALowerLog fastLogWitness = true := by decide +kernel

theorem wholeALower_denominators : DenominatorsPositive wholeALowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeALower_yBox_eq : (yBox wholeALowerInput).d0 = wholeALowerYBox := by decide +kernel

theorem wholeALower_contains :
    wholeALowerYBox.Contains (Y (lower E8TAxisProd0357PaddedInputs.wholeAInput.alpha)) := by
  have e : lower E8TAxisProd0357PaddedInputs.wholeAInput.alpha = ((2216017656540843594568486214625237657012888708 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeALowerInput.alpha.Contains (lower E8TAxisProd0357PaddedInputs.wholeAInput.alpha) := by
    rw [e]; exact point_contains precision 2216017656540843594568486214625237657012888708
  have h := checked_yBox_d0_contains (i := wholeALowerInput) (we := wholeALowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeALower_primitive_checks.1 wholeALower_primitive_checks.2 endpointLogTwo_checked
    wholeALower_denominators ha
  rw [wholeALower_yBox_eq] at h
  exact h

def wholeAUpperAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858937318, 2532592299075639559542598685704412299858937318⟩
def wholeAUpperExp : DyadicInterval precision := ⟨1456445219907862366338488118605723267323903211441, 1456445219907862366338488118605723267323903213490⟩
def wholeAUpperLog : DyadicInterval precision := ⟨1010505341326056445575717809135292021852864117646, 1010505341326056445575717809135292021852864118943⟩
def wholeAUpperYBox : DyadicInterval precision := ⟨14615016373309029182036848327162830196559702114, 14615016373309029182036848327162830196559705134⟩
def wholeAUpperInput : Inputs precision :=
  ⟨wholeAUpperAlpha, wholeAUpperExp, wholeAUpperLog, endpointLogTwo⟩
def wholeAUpperExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723267323903211441, scale precision, 1456445219907862366338488118605723267323903213490, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408824599717875913, -5065184598151279119085197371408824599717875652⟩, ⟨-5065184598151279119085197371408824599717873857, -5065184598151279119085197371408824599717873596⟩⟩

theorem wholeAUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAUpperAlpha) wholeAUpperExp wholeAUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAUpperExp) wholeAUpperLog fastLogWitness = true := by decide +kernel

theorem wholeAUpper_denominators : DenominatorsPositive wholeAUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeAUpper_yBox_eq : (yBox wholeAUpperInput).d0 = wholeAUpperYBox := by decide +kernel

theorem wholeAUpper_contains :
    wholeAUpperYBox.Contains (Y (upper E8TAxisProd0357PaddedInputs.wholeAInput.alpha)) := by
  have e : upper E8TAxisProd0357PaddedInputs.wholeAInput.alpha = ((2532592299075639559542598685704412299858937318 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeAUpperInput.alpha.Contains (upper E8TAxisProd0357PaddedInputs.wholeAInput.alpha) := by
    rw [e]; exact point_contains precision 2532592299075639559542598685704412299858937318
  have h := checked_yBox_d0_contains (i := wholeAUpperInput) (we := wholeAUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeAUpper_primitive_checks.1 wholeAUpper_primitive_checks.2 endpointLogTwo_checked
    wholeAUpper_denominators ha
  rw [wholeAUpper_yBox_eq] at h
  exact h

def wholeBLowerAlpha : DyadicInterval precision := ⟨2004365567763319348475137471186043242245625098768, 2004365567763319348475137471186043242245625098768⟩
def wholeBLowerExp : DyadicInterval precision := ⟨94097789596194195580133878013038690976589307284, 94097789596194195580133878013038690976589309333⟩
def wholeBLowerLog : DyadicInterval precision := ⟨91192629339425350376404722326798073551262738832, 91192629339425350376404722326798073551262741033⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨8379885013046064607250377909586987763952202956572, 8379885013046064607250377909586987763952203093006⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨94097789596194195580133878013038690976589307284, scale precision, 94097789596194195580133878013038690976589309333, scale precision,
    3, 128, 3, 128,
    ⟨-4008731135526638696950274942372086484491250214330, -4008731135526638696950274942372086484491250213242⟩, ⟨-4008731135526638696950274942372086484491250182508, -4008731135526638696950274942372086484491250181418⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

theorem wholeBLower_denominators : DenominatorsPositive wholeBLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBLower_yBox_eq : (yBox wholeBLowerInput).d0 = wholeBLowerYBox := by decide +kernel

theorem wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisProd0357PaddedInputs.wholeBInput.alpha)) := by
  have e : lower E8TAxisProd0357PaddedInputs.wholeBInput.alpha = ((2004365567763319348475137471186043242245625098768 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBLowerInput.alpha.Contains (lower E8TAxisProd0357PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 2004365567763319348475137471186043242245625098768
  have h := checked_yBox_d0_contains (i := wholeBLowerInput) (we := wholeBLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBLower_primitive_checks.1 wholeBLower_primitive_checks.2 endpointLogTwo_checked
    wholeBLower_denominators ha
  rw [wholeBLower_yBox_eq] at h
  exact h

def wholeBUpperAlpha : DyadicInterval precision := ⟨2040637016713598987314498814201704474493346497704, 2040637016713598987314498814201704474493346497704⟩
def wholeBUpperExp : DyadicInterval precision := ⟨89541185392435401307712788335794416042866022009, 89541185392435401307712788335794416042866024058⟩
def wholeBUpperLog : DyadicInterval precision := ⟨86905370785129428414758254738294238927684217008, 86905370785129428414758254738294238927684219201⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨8486757320275886883144022362979365959764543407098, 8486757320275886883144022362979365959764543549407⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨89541185392435401307712788335794416042866022009, scale precision, 89541185392435401307712788335794416042866024058, scale precision,
    4, 128, 4, 128,
    ⟨-4081274033427197974628997628403408948986693013267, -4081274033427197974628997628403408948986693011902⟩, ⟨-4081274033427197974628997628403408948986692979825, -4081274033427197974628997628403408948986692978458⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisProd0357EndpointWitnesses


