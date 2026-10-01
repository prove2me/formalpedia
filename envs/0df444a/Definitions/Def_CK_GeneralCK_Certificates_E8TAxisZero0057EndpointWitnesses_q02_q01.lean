-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057EndpointWitnesses_q02_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0057EndpointWitnesses_q02_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:48:01.602855+00:00
-- url     : https://prove2.me/theorems/e2892864-0f34-4e29-a775-e0a716ed877b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 3 of 4) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 3 of 4) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 3 of 4) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 3 of 4) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0057EndpointWitnesses (piece 3 of 4) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057EndpointWitnesses_q02_q00

namespace GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0057Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def wholeDLowerYBox : DyadicInterval precision := ⟨4236071151951288926980992757326101564783917531353, 4236071151951288926980992757326101564783919399676⟩
def wholeDLowerInput : Inputs precision :=
  ⟨wholeDLowerAlpha, wholeDLowerExp, wholeDLowerLog, endpointLogTwo⟩
def wholeDLowerExpWitness : ExpWitness precision :=
  ⟨482506534178222248007502303634473307517604214653, scale precision, 482506534178222248007502303634473307517604345726, scale precision,
    0, 1024, 0, 1024, ⟨-1619673005471191522833966148615398345155008410163, -1619673005471191522833966148615398345155008408104⟩, ⟨-1619673005471191522833966148615398345155008013149, -1619673005471191522833966148615398345155008011088⟩⟩

theorem wholeDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDLowerAlpha) wholeDLowerExp wholeDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDLowerExp) wholeDLowerLog fastLogWitness = true := by decide +kernel

theorem wholeDLower_denominators : DenominatorsPositive wholeDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDLower_yBox_eq : (yBox wholeDLowerInput).d0 = wholeDLowerYBox := by decide +kernel

theorem wholeDLower_contains :
    wholeDLowerYBox.Contains (Y (lower E8TAxisZero0057PaddedInputs.wholeDInput.alpha)) := by
  have e : lower E8TAxisZero0057PaddedInputs.wholeDInput.alpha = ((809836502735595761416983074307699172577504104839 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDLowerInput.alpha.Contains (lower E8TAxisZero0057PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 809836502735595761416983074307699172577504104839
  have h := checked_yBox_d0_contains (i := wholeDLowerInput) (we := wholeDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDLower_primitive_checks.1 wholeDLower_primitive_checks.2 endpointLogTwo_checked
    wholeDLower_denominators ha
  rw [wholeDLower_yBox_eq] at h
  exact h

def wholeDUpperAlpha : DyadicInterval precision := ⟨821860677686075647293949968540300351172240256288, 821860677686075647293949968540300351172240256288⟩
def wholeDUpperExp : DyadicInterval precision := ⟨474632069948069015840646238761706423500869004461, 474632069948069015840646238761706423500869135534⟩
def wholeDUpperLog : DyadicInterval precision := ⟨411016094834480306545789264008568524744906241204, 411016094834480306545789264008568524744906342201⟩
def wholeDUpperYBox : DyadicInterval precision := ⟨4288593867042868250603937681001842985802949158919, 4288593867042868250603937681001842985802951062450⟩
def wholeDUpperInput : Inputs precision :=
  ⟨wholeDUpperAlpha, wholeDUpperExp, wholeDUpperLog, endpointLogTwo⟩
def wholeDUpperExpWitness : ExpWitness precision :=
  ⟨474632069948069015840646238761706423500869004461, scale precision, 474632069948069015840646238761706423500869135534, scale precision,
    0, 1024, 0, 1024, ⟨-1643721355372151294587899937080600702344480716361, -1643721355372151294587899937080600702344480714302⟩, ⟨-1643721355372151294587899937080600702344480312757, -1643721355372151294587899937080600702344480310698⟩⟩

theorem wholeDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDUpperAlpha) wholeDUpperExp wholeDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDUpperExp) wholeDUpperLog fastLogWitness = true := by decide +kernel

theorem wholeDUpper_denominators : DenominatorsPositive wholeDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses


