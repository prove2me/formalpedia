-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0052EndpointWitnesses_q01_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0052EndpointWitnesses_q01_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T23:06:18.299321+00:00
-- url     : https://prove2.me/theorems/c88c502e-d5e0-4b4e-a1a0-08a64eb21fba
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 2 of 4) (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 2 of 4) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 2 of 4) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses (piece 2 of 4) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0052EndpointWitnesses (piece 2 of 4) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0052EndpointWitnesses_q01_q01

namespace GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0052Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def wholeBUpperLog : DyadicInterval precision := ⟨65472825520062582058540430242163462136640517296, 65472825520062582058540430242163462136640644683⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨9104241762048193366085079204801995535569217395490, 9104241762048193366085079204801995535569228824129⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨66961508920173399729056217016390023978043092440, scale precision, 66961508920173399729056217016390023978043223513, scale precision,
    0, 1024, 0, 1024, ⟨-4505958247325518282727561336802110734842001642338, -4505958247325518282727561336802110734842001640180⟩, ⟨-4505958247325518282727561336802110734841998781548, -4505958247325518282727561336802110734841998779390⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisZero0052PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisZero0052PaddedInputs.wholeBInput.alpha = ((2252979123662759141363780668401055367421000105189 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisZero0052PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 2252979123662759141363780668401055367421000105189
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨870712988176454679833831807012927217752906166802, 870712988176454679833831807012927217752906166802⟩
def wholeCLowerExp : DyadicInterval precision := ⟨443939237141351316813290285207320725578082410616, 443939237141351316813290285207320725578082541689⟩
def wholeCLowerLog : DyadicInterval precision := ⟨387661827478115861734404726101104696717286354130, 387661827478115861734404726101104696717286456721⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨4498684727409185545095717375704808669878345076856, 4498684727409185545095717375704808669878347126880⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨443939237141351316813290285207320725578082410616, scale precision, 443939237141351316813290285207320725578082541689, scale precision,
    0, 1024, 0, 1024, ⟨-1741425976352909359667663614025854435505812551319, -1741425976352909359667663614025854435505812549256⟩, ⟨-1741425976352909359667663614025854435505812119805, -1741425976352909359667663614025854435505812117746⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

end GeneralCK.Certificates.E8TAxisZero0052EndpointWitnesses


