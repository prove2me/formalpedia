-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0065EndpointWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0065EndpointWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:35:12.412918+00:00
-- url     : https://prove2.me/theorems/78086ee7-491f-4285-80e8-2fb1eb38705d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0065EndpointWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0065EndpointWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0065EndpointWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0065EndpointWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0065EndpointWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0065EndpointWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0065EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0065Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerDLowerLog : DyadicInterval precision := ⟨462587568506596564045749998967475931231937007202, 462587568506596564045749998967475931231937103745⟩
def centerDLowerYBox : DyadicInterval precision := ⟨3842150788764443999808905829758040907142276198500, 3842150788764443999808905829758040907142277811523⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨544171400918647169539408046331758483299751165025, scale precision, 544171400918647169539408046331758483299751296098, scale precision,
    0, 512, 0, 512, ⟨-1443898482078523554210200459372528620770678945441, -1443898482078523554210200459372528620770678944400⟩, ⟨-1443898482078523554210200459372528620770678593413, -1443898482078523554210200459372528620770678592372⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

theorem centerDLower_denominators : DenominatorsPositive centerDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDLower_yBox_eq : (yBox centerDLowerInput).d0 = centerDLowerYBox := by decide +kernel

theorem centerDLower_contains :
    centerDLowerYBox.Contains (Y (lower E8TAxisZero0065PaddedInputs.centerDInput.alpha)) := by
  have e : lower E8TAxisZero0065PaddedInputs.centerDInput.alpha = ((721949241039261777105100229686264310385339384231 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDLowerInput.alpha.Contains (lower E8TAxisZero0065PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 721949241039261777105100229686264310385339384231
  have h := checked_yBox_d0_contains (i := centerDLowerInput) (we := centerDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDLower_primitive_checks.1 centerDLower_primitive_checks.2 endpointLogTwo_checked
    centerDLower_denominators ha
  rw [centerDLower_yBox_eq] at h
  exact h

def centerDUpperAlpha : DyadicInterval precision := ⟨721949241039261777105100229686264310385372938664, 721949241039261777105100229686264310385372938664⟩
def centerDUpperExp : DyadicInterval precision := ⟨544171400918647169539408046331758483299726177899, 544171400918647169539408046331758483299726308972⟩
def centerDUpperLog : DyadicInterval precision := ⟨462587568506596564045749998967475931231918799484, 462587568506596564045749998967475931231918896029⟩
def centerDUpperYBox : DyadicInterval precision := ⟨3842150788764443999808905829758040907142430009097, 3842150788764443999808905829758040907142431622130⟩
def centerDUpperInput : Inputs precision :=
  ⟨centerDUpperAlpha, centerDUpperExp, centerDUpperLog, endpointLogTwo⟩
def centerDUpperExpWitness : ExpWitness precision :=
  ⟨544171400918647169539408046331758483299726177899, scale precision, 544171400918647169539408046331758483299726308972, scale precision,
    0, 512, 0, 512, ⟨-1443898482078523554210200459372528620770746054307, -1443898482078523554210200459372528620770746053266⟩, ⟨-1443898482078523554210200459372528620770745702279, -1443898482078523554210200459372528620770745701238⟩⟩

theorem centerDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDUpperAlpha) centerDUpperExp centerDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDUpperExp) centerDUpperLog fastLogWitness = true := by decide +kernel

theorem centerDUpper_denominators : DenominatorsPositive centerDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDUpper_yBox_eq : (yBox centerDUpperInput).d0 = centerDUpperYBox := by decide +kernel

theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisZero0065PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisZero0065PaddedInputs.centerDInput.alpha = ((721949241039261777105100229686264310385372938664 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisZero0065PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 721949241039261777105100229686264310385372938664
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

def wholeBLowerAlpha : DyadicInterval precision := ⟨1755682615968192604006724080732632442415708551686, 1755682615968192604006724080732632442415708551686⟩
def wholeBLowerExp : DyadicInterval precision := ⟨132243658317910108282970638394685411985064961413, 132243658317910108282970638394685411985065092486⟩
def wholeBLowerLog : DyadicInterval precision := ⟨126598709706290185816284609458792174615147629396, 126598709706290185816284609458792174615147750627⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨7631778862437308675994866735840340393265768055604, 7631778862437308675994866735840340393265774322376⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨132243658317910108282970638394685411985064961413, scale precision, 132243658317910108282970638394685411985065092486, scale precision,
    0, 512, 0, 512, ⟨-3511365231936385208013448161465264884831417828430, -3511365231936385208013448161465264884831417827356⟩, ⟨-3511365231936385208013448161465264884831416379868, -3511365231936385208013448161465264884831416378794⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

theorem wholeBLower_denominators : DenominatorsPositive wholeBLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBLower_yBox_eq : (yBox wholeBLowerInput).d0 = wholeBLowerYBox := by decide +kernel

theorem wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisZero0065PaddedInputs.wholeBInput.alpha)) := by
  have e : lower E8TAxisZero0065PaddedInputs.wholeBInput.alpha = ((1755682615968192604006724080732632442415708551686 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBLowerInput.alpha.Contains (lower E8TAxisZero0065PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1755682615968192604006724080732632442415708551686
  have h := checked_yBox_d0_contains (i := wholeBLowerInput) (we := wholeBLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBLower_primitive_checks.1 wholeBLower_primitive_checks.2 endpointLogTwo_checked
    wholeBLower_denominators ha
  rw [wholeBLower_yBox_eq] at h
  exact h

def wholeBUpperAlpha : DyadicInterval precision := ⟨1790577155268251264318358183860781884376008230639, 1790577155268251264318358183860781884376008230639⟩
def wholeBUpperExp : DyadicInterval precision := ⟨126077209366697777120126321300719762095524636745, 126077209366697777120126321300719762095524767818⟩
def wholeBUpperLog : DyadicInterval precision := ⟨120932964172539280471025078043449529688782216920, 120932964172539280471025078043449529688782338621⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨7738651169667130951888511189232718589078210761494, 7738651169667130951888511189232718589078217294381⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨126077209366697777120126321300719762095524636745, scale precision, 126077209366697777120126321300719762095524767818, scale precision,
    0, 512, 0, 512, ⟨-3581154310536502528636716367721563768752017221731, -3581154310536502528636716367721563768752017220660⟩, ⟨-3581154310536502528636716367721563768752015702319, -3581154310536502528636716367721563768752015701246⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisZero0065PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisZero0065PaddedInputs.wholeBInput.alpha = ((1790577155268251264318358183860781884376008230639 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisZero0065PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 1790577155268251264318358183860781884376008230639
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨716228578308099727358082939138935890959882435278, 716228578308099727358082939138935890959882435278⟩
def wholeCLowerExp : DyadicInterval precision := ⟨548448150163327086956497611001597702787292282569, 548448150163327086956497611001597702787292413642⟩
def wholeCLowerLog : DyadicInterval precision := ⟨465700648921796470149242465934935276152324964134, 465700648921796470149242465934935276152325060473⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨3815889431218654337997433367920170196632833443444, 3815889431218654337997433367920170196632835040958⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨548448150163327086956497611001597702787292282569, scale precision, 548448150163327086956497611001597702787292413642, scale precision,
    0, 512, 0, 512, ⟨-1432457156616199454716165878277871781919765046163, -1432457156616199454716165878277871781919765045124⟩, ⟨-1432457156616199454716165878277871781919764696881, -1432457156616199454716165878277871781919764695840⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

theorem wholeCLower_denominators : DenominatorsPositive wholeCLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0065EndpointWitnesses


