-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses_q02_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses_q02_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T22:44:37.189423+00:00
-- url     : https://prove2.me/theorems/b38a7c94-0813-4eab-8515-e392335d6173
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 3 of 4) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 3 of 4) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 3 of 4) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 3 of 4) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0051EndpointWitnesses (piece 3 of 4) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses_q02_q00

namespace GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0051Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def wholeDLowerYBox : DyadicInterval precision := ⟨4551207442500764868718662299380550090897230581998, 4551207442500764868718662299380550090897232670121⟩
def wholeDLowerInput : Inputs precision :=
  ⟨wholeDLowerAlpha, wholeDLowerExp, wholeDLowerLog, endpointLogTwo⟩
def wholeDLowerExpWitness : ExpWitness precision :=
  ⟨436466074505762269046786189274013977157045631255, scale precision, 436466074505762269046786189274013977157045762328, scale precision,
    0, 1024, 0, 1024, ⟨-1766237961495578041764168929559077400493715477523, -1766237961495578041764168929559077400493715475458⟩, ⟨-1766237961495578041764168929559077400493715038631, -1766237961495578041764168929559077400493715036564⟩⟩

theorem wholeDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDLowerAlpha) wholeDLowerExp wholeDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDLowerExp) wholeDLowerLog fastLogWitness = true := by decide +kernel

theorem wholeDLower_denominators : DenominatorsPositive wholeDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDLower_yBox_eq : (yBox wholeDLowerInput).d0 = wholeDLowerYBox := by decide +kernel

theorem wholeDLower_contains :
    wholeDLowerYBox.Contains (Y (lower E8TAxisZero0051PaddedInputs.wholeDInput.alpha)) := by
  have e : lower E8TAxisZero0051PaddedInputs.wholeDInput.alpha = ((883118980747789020882084464779538700246857628050 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDLowerInput.alpha.Contains (lower E8TAxisZero0051PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 883118980747789020882084464779538700246857628050
  have h := checked_yBox_d0_contains (i := wholeDLowerInput) (we := wholeDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDLower_primitive_checks.1 wholeDLower_primitive_checks.2 endpointLogTwo_checked
    wholeDLower_denominators ha
  rw [wholeDLower_yBox_eq] at h
  exact h

def wholeDUpperAlpha : DyadicInterval precision := ⟨895603670620266646532188138393358736598424840854, 895603670620266646532188138393358736598424840854⟩
def wholeDUpperExp : DyadicInterval precision := ⟨429072502312048699316189665111836194345767278055, 429072502312048699316189665111836194345767409128⟩
def wholeDUpperLog : DyadicInterval precision := ⟨376214102269711135965559641860188011090940455718, 376214102269711135965559641860188011090940559103⟩
def wholeDUpperYBox : DyadicInterval precision := ⟨4603730157592344192341607223056291511916256801601, 4603730157592344192341607223056291511916258928450⟩
def wholeDUpperInput : Inputs precision :=
  ⟨wholeDUpperAlpha, wholeDUpperExp, wholeDUpperLog, endpointLogTwo⟩
def wholeDUpperExpWitness : ExpWitness precision :=
  ⟨429072502312048699316189665111836194345767278055, scale precision, 429072502312048699316189665111836194345767409128, scale precision,
    0, 1024, 0, 1024, ⟨-1791207341240533293064376276786717473196849906917, -1791207341240533293064376276786717473196849904850⟩, ⟨-1791207341240533293064376276786717473196849460457, -1791207341240533293064376276786717473196849458388⟩⟩

theorem wholeDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDUpperAlpha) wholeDUpperExp wholeDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDUpperExp) wholeDUpperLog fastLogWitness = true := by decide +kernel

theorem wholeDUpper_denominators : DenominatorsPositive wholeDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

end GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses


