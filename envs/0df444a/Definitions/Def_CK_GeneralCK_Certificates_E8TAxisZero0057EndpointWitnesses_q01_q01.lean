-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057EndpointWitnesses_q01_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0057EndpointWitnesses_q01_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:05:22.978494+00:00
-- url     : https://prove2.me/theorems/21c974d2-f216-485d-94c0-d852d183b82f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 2 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 2 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 2 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 2 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0057EndpointWitnesses (piece 2 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057EndpointWitnesses_q01_q00

namespace GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0057Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem centerDUpper_denominators : DenominatorsPositive centerDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDUpper_yBox_eq : (yBox centerDUpperInput).d0 = centerDUpperYBox := by decide +kernel

theorem centerDUpper_contains :
    centerDUpperYBox.Contains (Y (upper E8TAxisZero0057PaddedInputs.centerDInput.alpha)) := by
  have e : upper E8TAxisZero0057PaddedInputs.centerDInput.alpha = ((815839300550668055994007428828159575323530087505 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDUpperInput.alpha.Contains (upper E8TAxisZero0057PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 815839300550668055994007428828159575323530087505
  have h := checked_yBox_d0_contains (i := centerDUpperInput) (we := centerDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDUpper_primitive_checks.1 centerDUpper_primitive_checks.2 endpointLogTwo_checked
    centerDUpper_denominators ha
  rw [centerDUpper_yBox_eq] at h
  exact h

def wholeBLowerAlpha : DyadicInterval precision := ⟨2035667381927356861675842006603351527460063291297, 2035667381927356861675842006603351527460063291297⟩
def wholeBLowerExp : DyadicInterval precision := ⟨90152205635118743298799537426527509541792669497, 90152205635118743298799537426527509541792800570⟩
def wholeBLowerLog : DyadicInterval precision := ⟨87481003657361805674317820684111609601462755348, 87481003657361805674317820684111609601462880865⟩
def wholeBLowerYBox : DyadicInterval precision := ⟨8472142303902577853961985514652203129567930214400, 8472142303902577853961985514652203129567938994860⟩
def wholeBLowerInput : Inputs precision :=
  ⟨wholeBLowerAlpha, wholeBLowerExp, wholeBLowerLog, endpointLogTwo⟩
def wholeBLowerExpWitness : ExpWitness precision :=
  ⟨90152205635118743298799537426527509541792669497, scale precision, 90152205635118743298799537426527509541792800570, scale precision,
    0, 1024, 0, 1024, ⟨-4071334763854713723351684013206703054920127646693, -4071334763854713723351684013206703054920127644578⟩, ⟨-4071334763854713723351684013206703054920125521815, -4071334763854713723351684013206703054920125519686⟩⟩

theorem wholeBLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBLowerAlpha) wholeBLowerExp wholeBLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBLowerExp) wholeBLowerLog fastLogWitness = true := by decide +kernel

theorem wholeBLower_denominators : DenominatorsPositive wholeBLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeBLower_yBox_eq : (yBox wholeBLowerInput).d0 = wholeBLowerYBox := by decide +kernel

theorem wholeBLower_contains :
    wholeBLowerYBox.Contains (Y (lower E8TAxisZero0057PaddedInputs.wholeBInput.alpha)) := by
  have e : lower E8TAxisZero0057PaddedInputs.wholeBInput.alpha = ((2035667381927356861675842006603351527460063291297 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBLowerInput.alpha.Contains (lower E8TAxisZero0057PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 2035667381927356861675842006603351527460063291297
  have h := checked_yBox_d0_contains (i := wholeBLowerInput) (we := wholeBLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBLower_primitive_checks.1 wholeBLower_primitive_checks.2 endpointLogTwo_checked
    wholeBLower_denominators ha
  rw [wholeBLower_yBox_eq] at h
  exact h

def wholeBUpperAlpha : DyadicInterval precision := ⟨2072074267602144435651804304621012994419402138738, 2072074267602144435651804304621012994419402138738⟩
def wholeBUpperExp : DyadicInterval precision := ⟨85770764774929215372249378512379604908281856761, 85770764774929215372249378512379604908281987834⟩
end GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses


