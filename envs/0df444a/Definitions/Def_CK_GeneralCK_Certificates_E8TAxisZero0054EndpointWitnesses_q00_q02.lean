-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses_q00_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses_q00_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:05:09.610307+00:00
-- url     : https://prove2.me/theorems/87cc605e-fc26-42c4-a15e-aa7f09e25aaa
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 1 of 4) (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 1 of 4) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 1 of 4) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 1 of 4) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0054EndpointWitnesses (piece 1 of 4) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses_q00_q01

namespace GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0054Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem centerCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCLowerAlpha) centerCLowerExp centerCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCLowerExp) centerCLowerLog fastLogWitness = true := by decide +kernel

theorem centerCLower_denominators : DenominatorsPositive centerCLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerCLower_yBox_eq : (yBox centerCLowerInput).d0 = centerCLowerYBox := by decide +kernel

theorem centerCLower_contains :
    centerCLowerYBox.Contains (Y (lower E8TAxisZero0054PaddedInputs.centerCInput.alpha)) := by
  have e : lower E8TAxisZero0054PaddedInputs.centerCInput.alpha = ((852462981405285549387058583896780795777561794292 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerCLowerInput.alpha.Contains (lower E8TAxisZero0054PaddedInputs.centerCInput.alpha) := by
    rw [e]; exact point_contains precision 852462981405285549387058583896780795777561794292
  have h := checked_yBox_d0_contains (i := centerCLowerInput) (we := centerCLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerCLower_primitive_checks.1 centerCLower_primitive_checks.2 endpointLogTwo_checked
    centerCLower_denominators ha
  rw [centerCLower_yBox_eq] at h
  exact h

def centerCUpperAlpha : DyadicInterval precision := ⟨852462981405285549387058583896780795777595348725, 852462981405285549387058583896780795777595348725⟩
def centerCUpperExp : DyadicInterval precision := ⟨455165924860857228347636676448316249980398912290, 455165924860857228347636676448316249980399043363⟩
def centerCUpperLog : DyadicInterval precision := ⟨396247596272224741565612833007079880265584861008, 396247596272224741565612833007079880265584963015⟩
def centerCUpperYBox : DyadicInterval precision := ⟨4420814093295148373985177293211644215237445623031, 4420814093295148373985177293211644215237447617696⟩
def centerCUpperInput : Inputs precision :=
  ⟨centerCUpperAlpha, centerCUpperExp, centerCUpperLog, endpointLogTwo⟩
def centerCUpperExpWitness : ExpWitness precision :=
  ⟨455165924860857228347636676448316249980398912290, scale precision, 455165924860857228347636676448316249980399043363, scale precision,
    0, 1024, 0, 1024, ⟨-1704925962810571098774117167793561591555190909861, -1704925962810571098774117167793561591555190907802⟩, ⟨-1704925962810571098774117167793561591555190488995, -1704925962810571098774117167793561591555190486934⟩⟩

theorem centerCUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCUpperAlpha) centerCUpperExp centerCUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCUpperExp) centerCUpperLog fastLogWitness = true := by decide +kernel

theorem centerCUpper_denominators : DenominatorsPositive centerCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerCUpper_yBox_eq : (yBox centerCUpperInput).d0 = centerCUpperYBox := by decide +kernel

theorem centerCUpper_contains :
    centerCUpperYBox.Contains (Y (upper E8TAxisZero0054PaddedInputs.centerCInput.alpha)) := by
  have e : upper E8TAxisZero0054PaddedInputs.centerCInput.alpha = ((852462981405285549387058583896780795777595348725 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerCUpperInput.alpha.Contains (upper E8TAxisZero0054PaddedInputs.centerCInput.alpha) := by
    rw [e]; exact point_contains precision 852462981405285549387058583896780795777595348725
  have h := checked_yBox_d0_contains (i := centerCUpperInput) (we := centerCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerCUpper_primitive_checks.1 centerCUpper_primitive_checks.2 endpointLogTwo_checked
    centerCUpper_denominators ha
  rw [centerCUpper_yBox_eq] at h
  exact h

def centerDLowerAlpha : DyadicInterval precision := ⟨852249911794452062012049136358764955095117012268, 852249911794452062012049136358764955095117012268⟩
end GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses


