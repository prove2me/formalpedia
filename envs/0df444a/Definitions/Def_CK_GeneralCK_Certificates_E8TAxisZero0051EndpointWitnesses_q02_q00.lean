-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses_q02_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses_q02_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T22:34:31.094984+00:00
-- url     : https://prove2.me/theorems/661b934c-be01-4bd4-a257-bc47f87c9a25
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 3 of 4) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 3 of 4) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 3 of 4) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 3 of 4) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0051EndpointWitnesses (piece 3 of 4) (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses_q01


namespace GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0051Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem wholeCLower_yBox_eq : (yBox wholeCLowerInput).d0 = wholeCLowerYBox := by decide +kernel

theorem wholeCLower_contains :
    wholeCLowerYBox.Contains (Y (lower E8TAxisZero0051PaddedInputs.wholeCInput.alpha)) := by
  have e : lower E8TAxisZero0051PaddedInputs.wholeCInput.alpha = ((883118980747789020882084464779538700246857628050 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCLowerInput.alpha.Contains (lower E8TAxisZero0051PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 883118980747789020882084464779538700246857628050
  have h := checked_yBox_d0_contains (i := wholeCLowerInput) (we := wholeCLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCLower_primitive_checks.1 wholeCLower_primitive_checks.2 endpointLogTwo_checked
    wholeCLower_denominators ha
  rw [wholeCLower_yBox_eq] at h
  exact h

def wholeCUpperAlpha : DyadicInterval precision := ⟨896039345883247891012692341783045457574250700463, 896039345883247891012692341783045457574250700463⟩
def wholeCUpperExp : DyadicInterval precision := ⟨428816764575366300703274760689464915912969264339, 428816764575366300703274760689464915912969395412⟩
def wholeCUpperLog : DyadicInterval precision := ⟨376016391746414710875486605814044609218111737988, 376016391746414710875486605814044609218111841387⟩
def wholeCUpperYBox : DyadicInterval precision := ⟨4605557034639007820989361829097186865690826701083, 4605557034639007820989361829097186865690828829288⟩
def wholeCUpperInput : Inputs precision :=
  ⟨wholeCUpperAlpha, wholeCUpperExp, wholeCUpperLog, endpointLogTwo⟩
def wholeCUpperExpWitness : ExpWitness precision :=
  ⟨428816764575366300703274760689464915912969264339, scale precision, 428816764575366300703274760689464915912969395412, scale precision,
    0, 1024, 0, 1024, ⟨-1792078691766495782025384683566090915148501626259, -1792078691766495782025384683566090915148501624198⟩, ⟨-1792078691766495782025384683566090915148501179535, -1792078691766495782025384683566090915148501177472⟩⟩

theorem wholeCUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCUpperAlpha) wholeCUpperExp wholeCUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCUpperExp) wholeCUpperLog fastLogWitness = true := by decide +kernel

theorem wholeCUpper_denominators : DenominatorsPositive wholeCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeCUpper_yBox_eq : (yBox wholeCUpperInput).d0 = wholeCUpperYBox := by decide +kernel

theorem wholeCUpper_contains :
    wholeCUpperYBox.Contains (Y (upper E8TAxisZero0051PaddedInputs.wholeCInput.alpha)) := by
  have e : upper E8TAxisZero0051PaddedInputs.wholeCInput.alpha = ((896039345883247891012692341783045457574250700463 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCUpperInput.alpha.Contains (upper E8TAxisZero0051PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 896039345883247891012692341783045457574250700463
  have h := checked_yBox_d0_contains (i := wholeCUpperInput) (we := wholeCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCUpper_primitive_checks.1 wholeCUpper_primitive_checks.2 endpointLogTwo_checked
    wholeCUpper_denominators ha
  rw [wholeCUpper_yBox_eq] at h
  exact h

def wholeDLowerAlpha : DyadicInterval precision := ⟨883118980747789020882084464779538700246857628050, 883118980747789020882084464779538700246857628050⟩
def wholeDLowerExp : DyadicInterval precision := ⟨436466074505762269046786189274013977157045631255, 436466074505762269046786189274013977157045762328⟩
def wholeDLowerLog : DyadicInterval precision := ⟨381918529993447746751868483809797875569916533574, 381918529993447746751868483809797875569916636563⟩
end GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses


