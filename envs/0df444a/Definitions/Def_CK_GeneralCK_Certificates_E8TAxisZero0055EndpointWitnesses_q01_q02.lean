-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses_q01_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses_q01_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T22:39:16.541709+00:00
-- url     : https://prove2.me/theorems/1f506c56-7873-4038-9a82-8fd23e7b41f8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 2 of 4) (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 2 of 4) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 2 of 4) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 2 of 4) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0055EndpointWitnesses (piece 2 of 4) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses_q01_q01

namespace GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0055Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def wholeBUpperLog : DyadicInterval precision := ⟨75727466618091101770600248616159124051305004320, 75727466618091101770600248616159124051305130835⟩
def wholeBUpperYBox : DyadicInterval precision := ⟨8789105471498717424347409662747547009455908106767, 8789105471498717424347409662747547009455918116248⟩
def wholeBUpperInput : Inputs precision :=
  ⟨wholeBUpperAlpha, wholeBUpperExp, wholeBUpperLog, endpointLogTwo⟩
def wholeBUpperExpWitness : ExpWitness precision :=
  ⟨77723698479483751154188684458002790201149885358, scale precision, 77723698479483751154188684458002790201150016431, scale precision,
    0, 1024, 0, 1024, ⟨-4288132754876456524403960883322831038099320508373, -4288132754876456524403960883322831038099320506236⟩, ⟨-4288132754876456524403960883322831038099318043695, -4288132754876456524403960883322831038099318041560⟩⟩

theorem wholeBUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBUpperAlpha) wholeBUpperExp wholeBUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBUpperExp) wholeBUpperLog fastLogWitness = true := by decide +kernel

theorem wholeBUpper_denominators : DenominatorsPositive wholeBUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisZero0055PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisZero0055PaddedInputs.wholeBInput.alpha = ((2144066377438228262201980441661415519049659637203 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisZero0055PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 2144066377438228262201980441661415519049659637203
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨833959591445470778384083818034390997094854557682, 833959591445470778384083818034390997094854557682⟩
def wholeCLowerExp : DyadicInterval precision := ⟨466838367135635595432846250236128803063002005916, 466838367135635595432846250236128803063002136989⟩
def wholeCLowerLog : DyadicInterval precision := ⟨405121100734994108525530084726425876454688285922, 405121100734994108525530084726425876454688387321⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨4341116582134447574226882604677584406821688552717, 4341116582134447574226882604677584406821690492027⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨466838367135635595432846250236128803063002005916, scale precision, 466838367135635595432846250236128803063002136989, scale precision,
    0, 1024, 0, 1024, ⟨-1667919182890941556768167636068781994189709322513, -1667919182890941556768167636068781994189709320452⟩, ⟨-1667919182890941556768167636068781994189708912167, -1667919182890941556768167636068781994189708910112⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

end GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses


