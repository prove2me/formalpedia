-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0056EndpointWitnesses_q02_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0056EndpointWitnesses_q02_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T22:44:02.303995+00:00
-- url     : https://prove2.me/theorems/72a7b56b-3a65-45ca-9de7-58d16d94293e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 3 of 4) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 3 of 4) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 3 of 4) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 3 of 4) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0056EndpointWitnesses (piece 3 of 4) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0056EndpointWitnesses_q02_q00

namespace GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0056Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def wholeDLowerYBox : DyadicInterval precision := ⟨4288593867042868250603937681001842985802803042436, 4288593867042868250603937681001842985802804945970⟩
def wholeDLowerInput : Inputs precision :=
  ⟨wholeDLowerAlpha, wholeDLowerExp, wholeDLowerLog, endpointLogTwo⟩
def wholeDLowerExpWitness : ExpWitness precision :=
  ⟨474632069948069015840646238761706423500890798498, scale precision, 474632069948069015840646238761706423500890929571, scale precision,
    0, 1024, 0, 1024, ⟨-1643721355372151294587899937080600702344413607497, -1643721355372151294587899937080600702344413605436⟩, ⟨-1643721355372151294587899937080600702344413203889, -1643721355372151294587899937080600702344413201830⟩⟩

theorem wholeDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDLowerAlpha) wholeDLowerExp wholeDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDLowerExp) wholeDLowerLog fastLogWitness = true := by decide +kernel

theorem wholeDLower_denominators : DenominatorsPositive wholeDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDLower_yBox_eq : (yBox wholeDLowerInput).d0 = wholeDLowerYBox := by decide +kernel

theorem wholeDLower_contains :
    wholeDLowerYBox.Contains (Y (lower E8TAxisZero0056PaddedInputs.wholeDInput.alpha)) := by
  have e : lower E8TAxisZero0056PaddedInputs.wholeDInput.alpha = ((821860677686075647293949968540300351172206701855 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDLowerInput.alpha.Contains (lower E8TAxisZero0056PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 821860677686075647293949968540300351172206701855
  have h := checked_yBox_d0_contains (i := wholeDLowerInput) (we := wholeDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDLower_primitive_checks.1 wholeDLower_primitive_checks.2 endpointLogTwo_checked
    wholeDLower_denominators ha
  rw [wholeDLower_yBox_eq] at h
  exact h

def wholeDUpperAlpha : DyadicInterval precision := ⟨833959591445470778384083818034390997094888112115, 833959591445470778384083818034390997094888112115⟩
def wholeDUpperExp : DyadicInterval precision := ⟨466838367135635595432846250236128803062980569749, 466838367135635595432846250236128803062980700822⟩
def wholeDUpperLog : DyadicInterval precision := ⟨405121100734994108525530084726425876454672039312, 405121100734994108525530084726425876454672140711⟩
def wholeDUpperYBox : DyadicInterval precision := ⟨4341116582134447574226882604677584406821833764353, 4341116582134447574226882604677584406821835703657⟩
def wholeDUpperInput : Inputs precision :=
  ⟨wholeDUpperAlpha, wholeDUpperExp, wholeDUpperLog, endpointLogTwo⟩
def wholeDUpperExpWitness : ExpWitness precision :=
  ⟨466838367135635595432846250236128803062980569749, scale precision, 466838367135635595432846250236128803062980700822, scale precision,
    0, 1024, 0, 1024, ⟨-1667919182890941556768167636068781994189776431375, -1667919182890941556768167636068781994189776429318⟩, ⟨-1667919182890941556768167636068781994189776021035, -1667919182890941556768167636068781994189776018980⟩⟩

theorem wholeDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDUpperAlpha) wholeDUpperExp wholeDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDUpperExp) wholeDUpperLog fastLogWitness = true := by decide +kernel

theorem wholeDUpper_denominators : DenominatorsPositive wholeDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses


