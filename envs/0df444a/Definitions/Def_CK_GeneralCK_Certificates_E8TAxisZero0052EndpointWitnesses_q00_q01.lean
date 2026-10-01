-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0052EndpointWitnesses_q00_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0052EndpointWitnesses_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:41:10.513199+00:00
-- url     : https://prove2.me/theorems/4d70c22b-7563-4246-a1b0-fc05162ca34d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 1 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0052EndpointWitnesses (piece 1 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0052EndpointWitnesses_q00_q00

namespace GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0052Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerBUpperExp : DyadicInterval precision := ⟨68681977988023915269716644193796991563750064984, 68681977988023915269716644193796991563750196057⟩
def centerBUpperLog : DyadicInterval precision := ⟨67116996175154394811740681640706696029158199234, 67116996175154394811740681640706696029158326481⟩
def centerBUpperYBox : DyadicInterval precision := ⟨9050805608433282228138256978105806437663047560042, 9050805608433282228138256978105806437663058732867⟩
def centerBUpperInput : Inputs precision :=
  ⟨centerBUpperAlpha, centerBUpperExp, centerBUpperLog, endpointLogTwo⟩
def centerBUpperExpWitness : ExpWitness precision :=
  ⟨68681977988023915269716644193796991563750064984, scale precision, 68681977988023915269716644193796991563750196057, scale precision,
    0, 1024, 0, 1024, ⟨-4468881594835921925024912999151670970544822982711, -4468881594835921925024912999151670970544822980534⟩, ⟨-4468881594835921925024912999151670970544820193573, -4468881594835921925024912999151670970544820191402⟩⟩

theorem centerBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBUpperAlpha) centerBUpperExp centerBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBUpperExp) centerBUpperLog fastLogWitness = true := by decide +kernel

theorem centerBUpper_denominators : DenominatorsPositive centerBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerBUpper_yBox_eq : (yBox centerBUpperInput).d0 = centerBUpperYBox := by decide +kernel

theorem centerBUpper_contains :
    centerBUpperYBox.Contains (Y (upper E8TAxisZero0052PaddedInputs.centerBInput.alpha)) := by
  have e : upper E8TAxisZero0052PaddedInputs.centerBInput.alpha = ((2234440797417960962512456499575835485272410793283 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerBUpperInput.alpha.Contains (upper E8TAxisZero0052PaddedInputs.centerBInput.alpha) := by
    rw [e]; exact point_contains precision 2234440797417960962512456499575835485272410793283
  have h := checked_yBox_d0_contains (i := centerBUpperInput) (we := centerBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerBUpper_primitive_checks.1 centerBUpper_primitive_checks.2 endpointLogTwo_checked
    centerBUpper_denominators ha
  rw [centerBUpper_yBox_eq] at h
  exact h

def centerCLowerAlpha : DyadicInterval precision := ⟨877121961275332815348515408942289040848478547603, 877121961275332815348515408942289040848478547603⟩
def centerCLowerExp : DyadicInterval precision := ⟨440062738871947185827516025087252186574905978508, 440062738871947185827516025087252186574906109581⟩
def centerCLowerLog : DyadicInterval precision := ⟨384685466715325414884351721285691056669617992338, 384685466715325414884351721285691056669618095133⟩
def centerCLowerYBox : DyadicInterval precision := ⟨4525859523478307021231067140563127057275072794943, 4525859523478307021231067140563127057275074864591⟩
def centerCLowerInput : Inputs precision :=
  ⟨centerCLowerAlpha, centerCLowerExp, centerCLowerLog, endpointLogTwo⟩
def centerCLowerExpWitness : ExpWitness precision :=
  ⟨440062738871947185827516025087252186574905978508, scale precision, 440062738871947185827516025087252186574906109581, scale precision,
    0, 1024, 0, 1024, ⟨-1754243922550665630697030817884578081696957314833, -1754243922550665630697030817884578081696957312772⟩, ⟨-1754243922550665630697030817884578081696956879519, -1754243922550665630697030817884578081696956877458⟩⟩

end GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses


