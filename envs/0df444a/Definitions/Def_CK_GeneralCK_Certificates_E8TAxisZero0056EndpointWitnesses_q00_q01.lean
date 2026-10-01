-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0056EndpointWitnesses_q00_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0056EndpointWitnesses_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T18:53:22.365223+00:00
-- url     : https://prove2.me/theorems/ed59435e-33f3-47c4-8ead-6031dd21df8b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 1 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0056EndpointWitnesses (piece 1 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0056EndpointWitnesses_q00_q00

namespace GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0056Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerBUpperExp : DyadicInterval precision := ⟨83725694751933551945584007868802200292176214862, 83725694751933551945584007868802200292176345935⟩
def centerBUpperLog : DyadicInterval precision := ⟨81415307798043808102508102272081987634920066774, 81415307798043808102508102272081987634920192801⟩
def centerBUpperYBox : DyadicInterval precision := ⟨8630623887700647639154697588699875069511968510935, 8630623887700647639154697588699875069511977882874⟩
def centerBUpperInput : Inputs precision :=
  ⟨centerBUpperAlpha, centerBUpperExp, centerBUpperLog, endpointLogTwo⟩
def centerBUpperExpWitness : ExpWitness precision :=
  ⟨83725694751933551945584007868802200292176214862, scale precision, 83725694751933551945584007868802200292176345935, scale precision,
    0, 1024, 0, 1024, ⟨-4179417923673203105430459703727753728630655706604, -4179417923673203105430459703727753728630655704476⟩, ⟨-4179417923673203105430459703727753728630653418620, -4179417923673203105430459703727753728630653416488⟩⟩

theorem centerBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBUpperAlpha) centerBUpperExp centerBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBUpperExp) centerBUpperLog fastLogWitness = true := by decide +kernel

theorem centerBUpper_denominators : DenominatorsPositive centerBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerBUpper_yBox_eq : (yBox centerBUpperInput).d0 = centerBUpperYBox := by decide +kernel

theorem centerBUpper_contains :
    centerBUpperYBox.Contains (Y (upper E8TAxisZero0056PaddedInputs.centerBInput.alpha)) := by
  have e : upper E8TAxisZero0056PaddedInputs.centerBInput.alpha = ((2089708961836601552715229851863876864315327280483 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerBUpperInput.alpha.Contains (upper E8TAxisZero0056PaddedInputs.centerBInput.alpha) := by
    rw [e]; exact point_contains precision 2089708961836601552715229851863876864315327280483
  have h := checked_yBox_d0_contains (i := centerBUpperInput) (we := centerBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerBUpper_primitive_checks.1 centerBUpper_primitive_checks.2 endpointLogTwo_checked
    centerBUpper_denominators ha
  rw [centerBUpper_yBox_eq] at h
  exact h

def centerCLowerAlpha : DyadicInterval precision := ⟨828111166455057851428312994106305707957899050577, 828111166455057851428312994106305707957899050577⟩
def centerCLowerExp : DyadicInterval precision := ⟨470589610244570117397433420085616218374140579325, 470589610244570117397433420085616218374140710398⟩
def centerCLowerLog : DyadicInterval precision := ⟨407961430901942629435402392650758735923023545958, 407961430901942629435402392650758735923023647161⟩
def centerCLowerYBox : DyadicInterval precision := ⟨4315768663111989726739287445860161373199530763085, 4315768663111989726739287445860161373199532685051⟩
def centerCLowerInput : Inputs precision :=
  ⟨centerCLowerAlpha, centerCLowerExp, centerCLowerLog, endpointLogTwo⟩
def centerCLowerExpWitness : ExpWitness precision :=
  ⟨470589610244570117397433420085616218374140579325, scale precision, 470589610244570117397433420085616218374140710398, scale precision,
    0, 1024, 0, 1024, ⟨-1656222332910115702856625988212611415915798306667, -1656222332910115702856625988212611415915798304606⟩, ⟨-1656222332910115702856625988212611415915797899597, -1656222332910115702856625988212611415915797897540⟩⟩

end GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses


