-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0070StableWitnesses_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0070StableWitnesses_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:47:32.268207+00:00
-- url     : https://prove2.me/theorems/f03014d6-4414-4a42-9e0d-99b2ac1cf9ae
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0070StableWitnesses (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0070StableWitnesses (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0070StableWitnesses (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0070StableWitnesses (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0070StableWitnesses (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval



/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0070StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨665477300625433477361232002502002625345921467119, 665477300625433477361232002502002625345921467120⟩
def centerDExp : DyadicInterval precision := ⟨587892208188294475401269251844616962692532348577, 587892208188294475401269251844616964891555604130⟩
def centerDLog : DyadicInterval precision := ⟨494103945124224218680176638976803110922563855190, 494103945124224218680176638976803113121587110743⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨587892208188294475401269251844616963242288162465, scale precision, 587892208188294475401269251844616964341799790242, scale precision,
    0, 512, 0, 512, ⟨-1330954601250866954722464005004005252058538439621, -1330954601250866954722464005004005252058536342468⟩, ⟨-1330954601250866954722464005004005249325149526009, -1330954601250866954722464005004005249325147428856⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨665670958141235826866978701625655109648398553268, 665670958141235826866978701625655109648398553269⟩
def centerCExp : DyadicInterval precision := ⟨587736430517897015450132223503546875616424374830, 587736430517897015450132223503546877815447630383⟩
def centerCLog : DyadicInterval precision := ⟨493992849848889760201719841657314452209825957866, 493992849848889760201719841657314454408849213419⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
end GeneralCK.Certificates.E8TAxisZero0070StableWitnesses


