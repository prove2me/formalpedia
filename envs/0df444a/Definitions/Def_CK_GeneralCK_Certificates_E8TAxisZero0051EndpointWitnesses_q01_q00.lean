-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses_q01_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses_q01_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T20:09:28.120203+00:00
-- url     : https://prove2.me/theorems/311e1890-9082-43d6-a6fb-082f80e7ba19
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 2 of 4) (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 2 of 4) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 2 of 4) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses (piece 2 of 4) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0051EndpointWitnesses (piece 2 of 4) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051EndpointWitnesses_q00


namespace GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0051Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerDLowerLog : DyadicInterval precision := ⟨379061432685197727184727484874290047264760982946, 379061432685197727184727484874290047264761086131⟩
def centerDLowerYBox : DyadicInterval precision := ⟨4577468800046554530530134761218420801406673333917, 4577468800046554530530134761218420801406675441313⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨432759351678313928226043309926168446810743084062, scale precision, 432759351678313928226043309926168446810743215135, scale precision,
    0, 1024, 0, 1024, ⟨-1778702885224526593375881959248831911046573382575, -1778702885224526593375881959248831911046573380506⟩, ⟨-1778702885224526593375881959248831911046572939919, -1778702885224526593375881959248831911046572937854⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

theorem centerDLower_denominators : DenominatorsPositive centerDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDLower_yBox_eq : (yBox centerDLowerInput).d0 = centerDLowerYBox := by decide +kernel

theorem centerDLower_contains :
    centerDLowerYBox.Contains (Y (lower E8TAxisZero0051PaddedInputs.centerDInput.alpha)) := by
  have e : lower E8TAxisZero0051PaddedInputs.centerDInput.alpha = ((889351442612263296687940979624415955523286579636 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDLowerInput.alpha.Contains (lower E8TAxisZero0051PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 889351442612263296687940979624415955523286579636
  have h := checked_yBox_d0_contains (i := centerDLowerInput) (we := centerDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDLower_primitive_checks.1 centerDLower_primitive_checks.2 endpointLogTwo_checked
    centerDLower_denominators ha
  rw [centerDLower_yBox_eq] at h
  exact h

def centerDUpperAlpha : DyadicInterval precision := ⟨889351442612263296687940979624415955523320134069, 889351442612263296687940979624415955523320134069⟩
def centerDUpperExp : DyadicInterval precision := ⟨432759351678313928226043309926168446810723212727, 432759351678313928226043309926168446810723343800⟩
def centerDUpperLog : DyadicInterval precision := ⟨379061432685197727184727484874290047264745651380, 379061432685197727184727484874290047264745754565⟩
def centerDUpperYBox : DyadicInterval precision := ⟨4577468800046554530530134761218420801406814496750, 4577468800046554530530134761218420801406816604147⟩
def centerDUpperInput : Inputs precision :=
  ⟨centerDUpperAlpha, centerDUpperExp, centerDUpperLog, endpointLogTwo⟩
def centerDUpperExpWitness : ExpWitness precision :=
  ⟨432759351678313928226043309926168446810723212727, scale precision, 432759351678313928226043309926168446810723343800, scale precision,
    0, 1024, 0, 1024, ⟨-1778702885224526593375881959248831911046640491437, -1778702885224526593375881959248831911046640489378⟩, ⟨-1778702885224526593375881959248831911046640048781, -1778702885224526593375881959248831911046640046720⟩⟩

theorem centerDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDUpperAlpha) centerDUpperExp centerDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDUpperExp) centerDUpperLog fastLogWitness = true := by decide +kernel

end GeneralCK.Certificates.E8TAxisZero0051EndpointWitnesses


