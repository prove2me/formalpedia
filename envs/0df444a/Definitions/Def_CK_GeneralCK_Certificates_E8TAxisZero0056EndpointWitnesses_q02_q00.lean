-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0056EndpointWitnesses_q02_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0056EndpointWitnesses_q02_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T22:34:28.253111+00:00
-- url     : https://prove2.me/theorems/bc779ede-cec3-49a1-b384-c6a8d730e05e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 3 of 4) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 3 of 4) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 3 of 4) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses (piece 3 of 4) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0056EndpointWitnesses (piece 3 of 4) (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0056EndpointWitnesses_q01


namespace GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0056Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem wholeCLower_yBox_eq : (yBox wholeCLowerInput).d0 = wholeCLowerYBox := by decide +kernel

theorem wholeCLower_contains :
    wholeCLowerYBox.Contains (Y (lower E8TAxisZero0056PaddedInputs.wholeCInput.alpha)) := by
  have e : lower E8TAxisZero0056PaddedInputs.wholeCInput.alpha = ((821860677686075647293949968540300351172206701855 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCLowerInput.alpha.Contains (lower E8TAxisZero0056PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 821860677686075647293949968540300351172206701855
  have h := checked_yBox_d0_contains (i := wholeCLowerInput) (we := wholeCLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCLower_primitive_checks.1 wholeCLower_primitive_checks.2 endpointLogTwo_checked
    wholeCLower_denominators ha
  rw [wholeCLower_yBox_eq] at h
  exact h

def wholeCUpperAlpha : DyadicInterval precision := ⟨834381778451564747097746049111687847015442018921, 834381778451564747097746049111687847015442018921⟩
def wholeCUpperExp : DyadicInterval precision := ⟨466568731900489908864567195721057952756844178271, 466568731900489908864567195721057952756844309344⟩
def wholeCUpperLog : DyadicInterval precision := ⟨404916728118958536875464286448801446776663424312, 404916728118958536875464286448801446776663525727⟩
def wholeCUpperYBox : DyadicInterval precision := ⟨4342943459181111202874637210718479760596403663662, 4342943459181111202874637210718479760596405604231⟩
def wholeCUpperInput : Inputs precision :=
  ⟨wholeCUpperAlpha, wholeCUpperExp, wholeCUpperLog, endpointLogTwo⟩
def wholeCUpperExpWitness : ExpWitness precision :=
  ⟨466568731900489908864567195721057952756844178271, scale precision, 466568731900489908864567195721057952756844309344, scale precision,
    0, 1024, 0, 1024, ⟨-1668763556903129494195492098223375694030884245111, -1668763556903129494195492098223375694030884243050⟩, ⟨-1668763556903129494195492098223375694030883834533, -1668763556903129494195492098223375694030883832470⟩⟩

theorem wholeCUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCUpperAlpha) wholeCUpperExp wholeCUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCUpperExp) wholeCUpperLog fastLogWitness = true := by decide +kernel

theorem wholeCUpper_denominators : DenominatorsPositive wholeCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeCUpper_yBox_eq : (yBox wholeCUpperInput).d0 = wholeCUpperYBox := by decide +kernel

theorem wholeCUpper_contains :
    wholeCUpperYBox.Contains (Y (upper E8TAxisZero0056PaddedInputs.wholeCInput.alpha)) := by
  have e : upper E8TAxisZero0056PaddedInputs.wholeCInput.alpha = ((834381778451564747097746049111687847015442018921 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCUpperInput.alpha.Contains (upper E8TAxisZero0056PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 834381778451564747097746049111687847015442018921
  have h := checked_yBox_d0_contains (i := wholeCUpperInput) (we := wholeCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCUpper_primitive_checks.1 wholeCUpper_primitive_checks.2 endpointLogTwo_checked
    wholeCUpper_denominators ha
  rw [wholeCUpper_yBox_eq] at h
  exact h

def wholeDLowerAlpha : DyadicInterval precision := ⟨821860677686075647293949968540300351172206701855, 821860677686075647293949968540300351172206701855⟩
def wholeDLowerExp : DyadicInterval precision := ⟨474632069948069015840646238761706423500890798498, 474632069948069015840646238761706423500890929571⟩
def wholeDLowerLog : DyadicInterval precision := ⟨411016094834480306545789264008568524744922692560, 411016094834480306545789264008568524744922793557⟩
end GeneralCK.Certificates.E8TAxisZero0056EndpointWitnesses


