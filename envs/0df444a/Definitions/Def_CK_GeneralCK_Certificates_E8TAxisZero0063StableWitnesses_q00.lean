-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0063StableWitnesses_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0063StableWitnesses_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:58:51.810084+00:00
-- url     : https://prove2.me/theorems/7a91a5a3-9b17-4d43-9e7d-3e7a63d547b1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0063StableWitnesses (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0063StableWitnesses (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0063StableWitnesses (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0063StableWitnesses (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0063StableWitnesses (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval



/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0063StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨745000746231477256788872225997272556554271720183, 745000746231477256788872225997272556554271720184⟩
def centerDExp : DyadicInterval precision := ⟨527273459613343376350322664808293438125402667750, 527273459613343376350322664808293440324425923303⟩
def centerDLog : DyadicInterval precision := ⟨450222147616224759094825146719602335307459476714, 450222147616224759094825146719602337506482732267⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨527273459613343376350322664808293438675158481638, scale precision, 527273459613343376350322664808293439774670109415, scale precision,
    0, 512, 0, 512, ⟨-1490001492462954513577744451994545114632362931693, -1490001492462954513577744451994545114632360834540⟩, ⟨-1490001492462954513577744451994545111584726046197, -1490001492462954513577744451994545111584723949044⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨745202392843182672568481927353952567927248719088, 745202392843182672568481927353952567927248719089⟩
def centerCExp : DyadicInterval precision := ⟨527127981516568675852540508495744758686425760804, 527127981516568675852540508495744760885449016357⟩
def centerCLog : DyadicInterval precision := ⟨450115235450166998520446421794529680328829223678, 450115235450166998520446421794529682527852479231⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
end GeneralCK.Certificates.E8TAxisZero0063StableWitnesses


