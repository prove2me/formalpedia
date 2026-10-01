-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0053EndpointWitnesses_q01_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0053EndpointWitnesses_q01_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T22:45:15.148432+00:00
-- url     : https://prove2.me/theorems/3125eb79-0304-4908-8cea-400c69170561
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 2 of 4) (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 2 of 4) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 2 of 4) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 2 of 4) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0053EndpointWitnesses (piece 2 of 4) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0053EndpointWitnesses_q01_q01

namespace GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0053Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def wholeBUpperLog : DyadicInterval precision := ⟨68740830243977076441342451274240015711211325768, 68740830243977076441342451274240015711211452875⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨8999196331865034718839189357450512693531447633140, 8999196331865034718839189357450512693531458564943⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨70383067545802394134786824794382051444050749480, scale precision, 70383067545802394134786824794382051444050880553, scale precision,
    0, 1024, 0, 1024, ⟨-4433124670066182774509629469550224159223254095280, -4433124670066182774509629469550224159223254093112⟩, ⟨-4433124670066182774509629469550224159223251373554, -4433124670066182774509629469550224159223251371394⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisZero0053PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisZero0053PaddedInputs.wholeBInput.alpha = ((2216562335033091387254814734775112079611626366410 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisZero0053PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 2216562335033091387254814734775112079611626366410
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨858384943750592238779991986336301839154799216100, 858384943750592238779991986336301839154799216100⟩
def wholeCLowerExp : DyadicInterval precision := ⟨451492192509468156215846209344698068505582009143, 451492192509468156215846209344698068505582140216⟩
def wholeCLowerLog : DyadicInterval precision := ⟨393443605556601543377574216062392476541342522528, 393443605556601543377574216062392476541342624723⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨4446162012317606221472772452029067248859459570119, 4446162012317606221472772452029067248859461582653⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨451492192509468156215846209344698068505582009143, scale precision, 451492192509468156215846209344698068505582140216, scale precision,
    0, 1024, 0, 1024, ⟨-1716769887501184477559983972672603678309598646323, -1716769887501184477559983972672603678309598644252⟩, ⟨-1716769887501184477559983972672603678309598222033, -1716769887501184477559983972672603678309598219970⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

end GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses


