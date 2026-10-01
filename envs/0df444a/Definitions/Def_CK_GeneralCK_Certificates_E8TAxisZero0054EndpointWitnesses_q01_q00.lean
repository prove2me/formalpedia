-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses_q01_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses_q01_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T20:10:13.428426+00:00
-- url     : https://prove2.me/theorems/2842df7f-e22c-4703-a013-de4b6d173c11
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 2 of 4) (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 2 of 4) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 2 of 4) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses (piece 2 of 4) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0054EndpointWitnesses (piece 2 of 4) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0054EndpointWitnesses_q00


namespace GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0054Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerDLowerLog : DyadicInterval precision := ⟨396348806111750593903736846609666707737506687776, 396348806111750593903736846609666707737506789771⟩
def centerDLowerYBox : DyadicInterval precision := ⟨4419900654771816559661299990191196538350016816229, 4419900654771816559661299990191196538350018810234⟩
def centerDLowerInput : Inputs precision :=
  ⟨centerDLowerAlpha, centerDLowerExp, centerDLowerLog, endpointLogTwo⟩
def centerDLowerExpWitness : ExpWitness precision :=
  ⟨455298659801689467951201474539649437154591597997, scale precision, 455298659801689467951201474539649437154591729070, scale precision,
    0, 1024, 0, 1024, ⟨-1704499823588904124024098272717529910190234236881, -1704499823588904124024098272717529910190234234818⟩, ⟨-1704499823588904124024098272717529910190233816139, -1704499823588904124024098272717529910190233814076⟩⟩

theorem centerDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDLowerAlpha) centerDLowerExp centerDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDLowerExp) centerDLowerLog fastLogWitness = true := by decide +kernel

theorem centerDLower_denominators : DenominatorsPositive centerDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem centerDLower_yBox_eq : (yBox centerDLowerInput).d0 = centerDLowerYBox := by decide +kernel

theorem centerDLower_contains :
    centerDLowerYBox.Contains (Y (lower E8TAxisZero0054PaddedInputs.centerDInput.alpha)) := by
  have e : lower E8TAxisZero0054PaddedInputs.centerDInput.alpha = ((852249911794452062012049136358764955095117012268 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : centerDLowerInput.alpha.Contains (lower E8TAxisZero0054PaddedInputs.centerDInput.alpha) := by
    rw [e]; exact point_contains precision 852249911794452062012049136358764955095117012268
  have h := checked_yBox_d0_contains (i := centerDLowerInput) (we := centerDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    centerDLower_primitive_checks.1 centerDLower_primitive_checks.2 endpointLogTwo_checked
    centerDLower_denominators ha
  rw [centerDLower_yBox_eq] at h
  exact h

def centerDUpperAlpha : DyadicInterval precision := ⟨852249911794452062012049136358764955095150566701, 852249911794452062012049136358764955095150566701⟩
def centerDUpperExp : DyadicInterval precision := ⟨455298659801689467951201474539649437154570691707, 455298659801689467951201474539649437154570822780⟩
def centerDUpperLog : DyadicInterval precision := ⟨396348806111750593903736846609666707737490747368, 396348806111750593903736846609666707737490849365⟩
def centerDUpperYBox : DyadicInterval precision := ⟨4419900654771816559661299990191196538350160673356, 4419900654771816559661299990191196538350162667367⟩
def centerDUpperInput : Inputs precision :=
  ⟨centerDUpperAlpha, centerDUpperExp, centerDUpperLog, endpointLogTwo⟩
def centerDUpperExpWitness : ExpWitness precision :=
  ⟨455298659801689467951201474539649437154570691707, scale precision, 455298659801689467951201474539649437154570822780, scale precision,
    0, 1024, 0, 1024, ⟨-1704499823588904124024098272717529910190301345747, -1704499823588904124024098272717529910190301343688⟩, ⟨-1704499823588904124024098272717529910190300925005, -1704499823588904124024098272717529910190300922946⟩⟩

theorem centerDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDUpperAlpha) centerDUpperExp centerDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDUpperExp) centerDUpperLog fastLogWitness = true := by decide +kernel

end GeneralCK.Certificates.E8TAxisZero0054EndpointWitnesses


