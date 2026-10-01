-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057EndpointWitnesses_q00_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0057EndpointWitnesses_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:11:00.757972+00:00
-- url     : https://prove2.me/theorems/25e1bfce-a67a-4318-9f1b-b469047d910f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 1 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 1 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0057EndpointWitnesses (piece 1 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057EndpointWitnesses_q00_q00

namespace GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0057Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerBUpperExp : DyadicInterval precision := ⟨87936498323453739023942818534544665008264136228, 87936498323453739023942818534544665008264267301⟩
def centerBUpperLog : DyadicInterval precision := ⟨85392539053787661974621155986781909224922034808, 85392539053787661974621155986781909224922160493⟩
def centerBUpperYBox : DyadicInterval precision := ⟨8525578457517488991908807741348392227474198753918, 8525578457517488991908807741348392227474207728809⟩
def centerBUpperInput : Inputs precision :=
  ⟨centerBUpperAlpha, centerBUpperExp, centerBUpperLog, endpointLogTwo⟩
def centerBUpperExpWitness : ExpWitness precision :=
  ⟨87936498323453739023942818534544665008264136228, scale precision, 87936498323453739023942818534544665008264267301, scale precision,
    0, 1024, 0, 1024, ⟨-4107703459839463323782244320940382247708347206378, -4107703459839463323782244320940382247708347204244⟩, ⟨-4107703459839463323782244320940382247708345027936, -4107703459839463323782244320940382247708345025808⟩⟩

theorem centerBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBUpperAlpha) centerBUpperExp centerBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBUpperExp) centerBUpperLog fastLogWitness = true := by decide +kernel

theorem centerBUpper_denominators : DenominatorsPositive centerBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerBUpper_yBox_eq : (yBox centerBUpperInput).d0 = centerBUpperYBox := by decide +kernel

theorem centerBUpper_contains :
    centerBUpperYBox.Contains (Y (upper E8TAxisZero0057PaddedInputs.centerBInput.alpha)) := by
  have e : upper E8TAxisZero0057PaddedInputs.centerBInput.alpha = ((2053851729919731661891122160470191123854173057742 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerBUpperInput.alpha.Contains (upper E8TAxisZero0057PaddedInputs.centerBInput.alpha) := by
    rw [e]; exact point_contains precision 2053851729919731661891122160470191123854173057742
  have h := checked_yBox_d0_contains (i := centerBUpperInput) (we := centerBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerBUpper_primitive_checks.1 centerBUpper_primitive_checks.2 endpointLogTwo_checked
    centerBUpper_denominators ha
  rw [centerBUpper_yBox_eq] at h
  exact h

def centerCLowerAlpha : DyadicInterval precision := ⟨816048427260826356741020123173861709342026968130, 816048427260826356741020123173861709342026968130⟩
def centerCLowerExp : DyadicInterval precision := ⟨478422254686227980476844283326297540128456747943, 478422254686227980476844283326297540128456879016⟩
def centerCLowerLog : DyadicInterval precision := ⟨413874340783744681547561195285871418044911119940, 413874340783744681547561195285871418044911220741⟩
def centerCLowerYBox : DyadicInterval precision := ⟨4263245948020410403116342522184419952180645252397, 4263245948020410403116342522184419952180647138858⟩
def centerCLowerInput : Inputs precision :=
  ⟨centerCLowerAlpha, centerCLowerExp, centerCLowerLog, endpointLogTwo⟩
def centerCLowerExpWitness : ExpWitness precision :=
  ⟨478422254686227980476844283326297540128456747943, scale precision, 478422254686227980476844283326297540128456879016, scale precision,
    0, 1024, 0, 1024, ⟨-1632096854521652713482040246347723418684054138439, -1632096854521652713482040246347723418684054136382⟩, ⟨-1632096854521652713482040246347723418684053738037, -1632096854521652713482040246347723418684053735978⟩⟩

end GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses


