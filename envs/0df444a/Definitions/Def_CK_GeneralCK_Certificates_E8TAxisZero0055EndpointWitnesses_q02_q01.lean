-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses_q02_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses_q02_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:03:15.73842+00:00
-- url     : https://prove2.me/theorems/d7bf9c12-9bb9-44ef-8709-732815c94b45
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 3 of 4) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 3 of 4) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 3 of 4) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses (piece 3 of 4) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0055EndpointWitnesses (piece 3 of 4) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0055EndpointWitnesses_q02_q00

namespace GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0055Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def wholeDLowerYBox : DyadicInterval precision := ⟨4341116582134447574226882604677584406821688552717, 4341116582134447574226882604677584406821690492027⟩
def wholeDLowerInput : Inputs precision :=
  ⟨wholeDLowerAlpha, wholeDLowerExp, wholeDLowerLog, endpointLogTwo⟩
def wholeDLowerExpWitness : ExpWitness precision :=
  ⟨466838367135635595432846250236128803063002005916, scale precision, 466838367135635595432846250236128803063002136989, scale precision,
    0, 1024, 0, 1024, ⟨-1667919182890941556768167636068781994189709322513, -1667919182890941556768167636068781994189709320452⟩, ⟨-1667919182890941556768167636068781994189708912167, -1667919182890941556768167636068781994189708910112⟩⟩

theorem wholeDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDLowerAlpha) wholeDLowerExp wholeDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDLowerExp) wholeDLowerLog fastLogWitness = true := by decide +kernel

theorem wholeDLower_denominators : DenominatorsPositive wholeDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDLower_yBox_eq : (yBox wholeDLowerInput).d0 = wholeDLowerYBox := by decide +kernel

theorem wholeDLower_contains :
    wholeDLowerYBox.Contains (Y (lower E8TAxisZero0055PaddedInputs.wholeDInput.alpha)) := by
  have e : lower E8TAxisZero0055PaddedInputs.wholeDInput.alpha = ((833959591445470778384083818034390997094854557682 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDLowerInput.alpha.Contains (lower E8TAxisZero0055PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 833959591445470778384083818034390997094854557682
  have h := checked_yBox_d0_contains (i := wholeDLowerInput) (we := wholeDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDLower_primitive_checks.1 wholeDLower_primitive_checks.2 endpointLogTwo_checked
    wholeDLower_denominators ha
  rw [wholeDLower_yBox_eq] at h
  exact h

def wholeDUpperAlpha : DyadicInterval precision := ⟨846134075813431409586727826645377644661788746987, 846134075813431409586727826645377644661788746987⟩
def wholeDUpperExp : DyadicInterval precision := ⟨459125158042315647897421247370792078562228213631, 459125158042315647897421247370792078562228344704⟩
def wholeDUpperLog : DyadicInterval precision := ⟨399263485746125009998379766489542016005492211434, 399263485746125009998379766489542016005492313239⟩
def wholeDUpperYBox : DyadicInterval precision := ⟨4393639297226026897849827528353325827840718370191, 4393639297226026897849827528353325827840720345854⟩
def wholeDUpperInput : Inputs precision :=
  ⟨wholeDUpperAlpha, wholeDUpperExp, wholeDUpperLog, endpointLogTwo⟩
def wholeDUpperExpWitness : ExpWitness precision :=
  ⟨459125158042315647897421247370792078562228213631, scale precision, 459125158042315647897421247370792078562228344704, scale precision,
    0, 1024, 0, 1024, ⟨-1692268151626862819173455653290755289323577704559, -1692268151626862819173455653290755289323577702496⟩, ⟨-1692268151626862819173455653290755289323577287321, -1692268151626862819173455653290755289323577285262⟩⟩

theorem wholeDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDUpperAlpha) wholeDUpperExp wholeDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDUpperExp) wholeDUpperLog fastLogWitness = true := by decide +kernel

theorem wholeDUpper_denominators : DenominatorsPositive wholeDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0055EndpointWitnesses


