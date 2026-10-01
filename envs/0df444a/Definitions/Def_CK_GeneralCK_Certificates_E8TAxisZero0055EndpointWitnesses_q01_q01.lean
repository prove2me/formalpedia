-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses_q01_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses_q01_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T22:27:52.174295+00:00
-- url     : https://prove2.me/theorems/a12e5e81-5ae3-4f03-b4a3-690802945092
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 2 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 2 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 2 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 2 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0055EndpointWitnesses (piece 2 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses_q01_q00

namespace GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0055Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem centerDUpper_denominators : DenominatorsPositive centerDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDUpper_yBox_eq : (yBox centerDUpperInput).d0 = centerDUpperYBox := by decide +kernel

theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisZero0055PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisZero0055PaddedInputs.centerDInput.alpha = ((840037336037815392922282998599371946229825496054 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisZero0055PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 840037336037815392922282998599371946229825496054
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

def wholeBLowerAlpha : DyadicInterval precision := ⟨2107377137908424767296032998711315641015528444964, 2107377137908424767296032998711315641015528444964⟩
def wholeBLowerExp : DyadicInterval precision := ⟨81725641607503649950122630243962610652025302541, 81725641607503649950122630243962610652025433614⟩
def wholeBLowerLog : DyadicInterval precision := ⟨79522399063997544627745901596049331201387834022, 79522399063997544627745901596049331201387960209⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨8682233164268895148453765209355168813643470513732, 8682233164268895148453765209355168813643480088036⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨81725641607503649950122630243962610652025302541, scale precision, 81725641607503649950122630243962610652025433614, scale precision,
    0, 1024, 0, 1024, ⟨-4214754275816849534592065997422631282031058063552, -4214754275816849534592065997422631282031058061414⟩, ⟨-4214754275816849534592065997422631282031055719578, -4214754275816849534592065997422631282031055717440⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

theorem wholeBLower_denominators : DenominatorsPositive wholeBLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBLower_yBox_eq : (yBox wholeBLowerInput).d0 = wholeBLowerYBox := by decide +kernel

theorem wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisZero0055PaddedInputs.wholeBInput.alpha)) := by
  have e : lower E8TAxisZero0055PaddedInputs.wholeBInput.alpha = ((2107377137908424767296032998711315641015528444964 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBLowerInput.alpha.Contains (lower E8TAxisZero0055PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 2107377137908424767296032998711315641015528444964
  have h := checked_yBox_d0_contains (i := wholeBLowerInput) (we := wholeBLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBLower_primitive_checks.1 wholeBLower_primitive_checks.2 endpointLogTwo_checked
    wholeBLower_denominators ha
  rw [wholeBLower_yBox_eq] at h
  exact h

def wholeBUpperAlpha : DyadicInterval precision := ⟨2144066377438228262201980441661415519049659637203, 2144066377438228262201980441661415519049659637203⟩
def wholeBUpperExp : DyadicInterval precision := ⟨77723698479483751154188684458002790201149885358, 77723698479483751154188684458002790201150016431⟩
end GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses


