-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0053EndpointWitnesses_q02_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0053EndpointWitnesses_q02_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T23:19:29.340551+00:00
-- url     : https://prove2.me/theorems/2415ffb0-4193-4086-9139-eff9a3bb7dbf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 3 of 4) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 3 of 4) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 3 of 4) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 3 of 4) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0053EndpointWitnesses (piece 3 of 4) (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0053EndpointWitnesses_q01


namespace GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0053Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem wholeCLower_yBox_eq : (yBox wholeCLowerInput).d0 = wholeCLowerYBox := by decide +kernel

theorem wholeCLower_contains :
    wholeCLowerYBox.Contains (Y (lower E8TAxisZero0053PaddedInputs.wholeCInput.alpha)) := by
  have e : lower E8TAxisZero0053PaddedInputs.wholeCInput.alpha = ((858384943750592238779991986336301839154799216100 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCLowerInput.alpha.Contains (lower E8TAxisZero0053PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 858384943750592238779991986336301839154799216100
  have h := checked_yBox_d0_contains (i := wholeCLowerInput) (we := wholeCLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCLower_primitive_checks.1 wholeCLower_primitive_checks.2 endpointLogTwo_checked
    wholeCLower_denominators ha
  rw [wholeCLower_yBox_eq] at h
  exact h

def wholeCUpperAlpha : DyadicInterval precision := ⟨871143188090492117311131821217990885949995114836, 871143188090492117311131821217990885949995114836⟩
def wholeCUpperExp : DyadicInterval precision := ⟨443677962831186878806869585703732165299628948033, 443677962831186878806869585703732165299629079106⟩
def wholeCUpperLog : DyadicInterval precision := ⟨387461412435348922626507055203030608747829082328, 387461412435348922626507055203030608747829184929⟩
def wholeCUpperYBox : DyadicInterval precision := ⟨4500511604455849173743471981745704023653057483362, 4500511604455849173743471981745704023653059534680⟩
def wholeCUpperInput : Inputs precision :=
  ⟨wholeCUpperAlpha, wholeCUpperExp, wholeCUpperLog, endpointLogTwo⟩
def wholeCUpperExpWitness : ExpWitness precision :=
  ⟨443677962831186878806869585703732165299628948033, scale precision, 443677962831186878806869585703732165299629079106, scale precision,
    0, 1024, 0, 1024, ⟨-1742286376180984234622263642435981771899990447523, -1742286376180984234622263642435981771899990445462⟩, ⟨-1742286376180984234622263642435981771899990015765, -1742286376180984234622263642435981771899990013696⟩⟩

theorem wholeCUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCUpperAlpha) wholeCUpperExp wholeCUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCUpperExp) wholeCUpperLog fastLogWitness = true := by decide +kernel

theorem wholeCUpper_denominators : DenominatorsPositive wholeCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeCUpper_yBox_eq : (yBox wholeCUpperInput).d0 = wholeCUpperYBox := by decide +kernel

theorem wholeCUpper_contains :
    wholeCUpperYBox.Contains (Y (upper E8TAxisZero0053PaddedInputs.wholeCInput.alpha)) := by
  have e : upper E8TAxisZero0053PaddedInputs.wholeCInput.alpha = ((871143188090492117311131821217990885949995114836 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCUpperInput.alpha.Contains (upper E8TAxisZero0053PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 871143188090492117311131821217990885949995114836
  have h := checked_yBox_d0_contains (i := wholeCUpperInput) (we := wholeCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCUpper_primitive_checks.1 wholeCUpper_primitive_checks.2 endpointLogTwo_checked
    wholeCUpper_denominators ha
  rw [wholeCUpper_yBox_eq] at h
  exact h

def wholeDLowerAlpha : DyadicInterval precision := ⟨858384943750592238779991986336301839154799216100, 858384943750592238779991986336301839154799216100⟩
def wholeDLowerExp : DyadicInterval precision := ⟨451492192509468156215846209344698068505582009143, 451492192509468156215846209344698068505582140216⟩
def wholeDLowerLog : DyadicInterval precision := ⟨393443605556601543377574216062392476541342522528, 393443605556601543377574216062392476541342624723⟩
end GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses


