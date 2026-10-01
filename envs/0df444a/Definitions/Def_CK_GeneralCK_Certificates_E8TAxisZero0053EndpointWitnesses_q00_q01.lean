-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0053EndpointWitnesses_q00_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0053EndpointWitnesses_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T18:58:23.745811+00:00
-- url     : https://prove2.me/theorems/3ddd32a3-d770-43f9-9e5c-ad9dd1f014df
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses (piece 1 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0053EndpointWitnesses (piece 1 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0053EndpointWitnesses_q00_q00

namespace GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0053Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerBUpperExp : DyadicInterval precision := ⟨72186018221563420262904968289895657326342884523, 72186018221563420262904968289895657326343015596⟩
def centerBUpperLog : DyadicInterval precision := ⟨70459932166004994217086871073398753830528622856, 70459932166004994217086871073398753830528749815⟩
def centerBUpperYBox : DyadicInterval precision := ⟨8945760178250123580892367130754323595625277797067, 8945760178250123580892367130754323595625288485453⟩
def centerBUpperInput : Inputs precision :=
  ⟨centerBUpperAlpha, centerBUpperExp, centerBUpperLog, endpointLogTwo⟩
def centerBUpperExpWitness : ExpWitness precision :=
  ⟨72186018221563420262904968289895657326342884523, scale precision, 72186018221563420262904968289895657326343015596, scale precision,
    0, 1024, 0, 1024, ⟨-4396157948530155341592303397102824438160660524490, -4396157948530155341592303397102824438160660522342⟩, ⟨-4396157948530155341592303397102824438160657870748, -4396157948530155341592303397102824438160657868604⟩⟩

theorem centerBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBUpperAlpha) centerBUpperExp centerBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBUpperExp) centerBUpperLog fastLogWitness = true := by decide +kernel

theorem centerBUpper_denominators : DenominatorsPositive centerBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerBUpper_yBox_eq : (yBox centerBUpperInput).d0 = centerBUpperYBox := by decide +kernel

theorem centerBUpper_contains :
    centerBUpperYBox.Contains (Y (upper E8TAxisZero0053PaddedInputs.centerBInput.alpha)) := by
  have e : upper E8TAxisZero0053PaddedInputs.centerBInput.alpha = ((2198078974265077670796151698551412219080329598017 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerBUpperInput.alpha.Contains (upper E8TAxisZero0053PaddedInputs.centerBInput.alpha) := by
    rw [e]; exact point_contains precision 2198078974265077670796151698551412219080329598017
  have h := checked_yBox_d0_contains (i := centerBUpperInput) (we := centerBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerBUpper_primitive_checks.1 centerBUpper_primitive_checks.2 endpointLogTwo_checked
    centerBUpper_denominators ha
  rw [centerBUpper_yBox_eq] at h
  exact h

def centerCLowerAlpha : DyadicInterval precision := ⟨864753682105473134926531948268092697857242845477, 864753682105473134926531948268092697857242845477⟩
def centerCLowerExp : DyadicInterval precision := ⟨447574384003629321525936368629525801900574164011, 447574384003629321525936368629525801900574295084⟩
def centerCLowerLog : DyadicInterval precision := ⟨390447383208798558243275011766813449127230504586, 390447383208798558243275011766813449127230606989⟩
def centerCLowerYBox : DyadicInterval precision := ⟨4473336808386727697608122216887385636256187289001, 4473336808386727697608122216887385636256189320868⟩
def centerCLowerInput : Inputs precision :=
  ⟨centerCLowerAlpha, centerCLowerExp, centerCLowerLog, endpointLogTwo⟩
def centerCLowerExpWitness : ExpWitness precision :=
  ⟨447574384003629321525936368629525801900574164011, scale precision, 447574384003629321525936368629525801900574295084, scale precision,
    0, 1024, 0, 1024, ⟨-1729507364210946269853063896536185395714485906931, -1729507364210946269853063896536185395714485904870⟩, ⟨-1729507364210946269853063896536185395714485478933, -1729507364210946269853063896536185395714485476870⟩⟩

end GeneralCK.Certificates.E8TAxisZero0053EndpointWitnesses


