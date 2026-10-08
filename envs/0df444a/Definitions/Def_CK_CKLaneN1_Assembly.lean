-- Prove2me | Definitions.Def_CK_CKLaneN1_Assembly
-- name    : CK_CKLaneN1_Assembly
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T23:58:10.716262+00:00
-- url     : https://prove2.me/theorems/815c78ff-0e41-42c6-9f2b-52e78e061c11
-- title:
--   Courtade–Kumar proof module `CKLaneN1.Assembly` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.Assembly` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.Assembly` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.Assembly (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/Assembly.lean)

import Definitions.Def_CK_CKLaneN23_SameSideRows56
import Definitions.Def_CK_CKLaneN4_CentralSubrows
import Definitions.Def_CK_CKLaneN4_EightCentral
import Definitions.Def_CK_CKLaneN1_Central
import Definitions.Def_CK_CKLaneN1_SmallRatio
import Definitions.Def_CK_CKLaneN1_DiagBand

-- ===== source module CKLaneN1.Assembly =====
section

/-!
# Lane N1: central-square assembly from the rows that are still open (CONDITIONAL)

`CentralSquareRow` (verbatim `CKRoute.CentralSquare`) follows from the `CK_OPPOSITE_EXTENSION.zip`
`PROOF.md` §4 assembly (`centralSquare_of_subrows`). Closed inputs used here:

* N1 rows 1, 2, 4: `row_smallRatioT1Cover`, `row_smallRatioT4Rest`, `row_noSepA_moderateRest`
  (gates `N1/audit/gate_smallratio.json`, `N1/audit/gate_diagband.json`);
* N23 rows 5, 6 (inside `CKLaneN23.sameSideHalf_of_remaining_six_rows` /
  `CKLaneN23.diagonalBand_of_remaining_four_rows`, N23 gates);
* `SR_SmallRatio`: `row_SR_SmallRatio` (N1);
* `SR_LargeRatio` along the archive-literal route (canonical): parent dominance (2)
  `CKLaneN4.sr_parent8` and the central EIGHT_RATIO theorem (3) `CKLaneN4.sr_eightRatio_central`
  (module `CKLaneN4.EightCentral`), bound by definitional equality (verbatim row texts).
  The older global-eight route `CKLaneN4.sr_largeRatio` is kept only as `largeRatio_of_N4`.

The five inputs that remain open (other lanes):
`CentralCap` (M06), `SmallRatioT3NearRest` (N6), `FullEntropySSCoverRest` (M05), `SR_Moderate` (N1b),
`SR_Transition` (N1c-b).

Every theorem here is CONDITIONAL on those inputs. None of them closes `CentralSquareRow` by itself.
-/

namespace CKLaneN1

/-- `SR_LargeRatio` from lane N4 (`CKLaneN4.SR_LargeRatio` is the verbatim text of `SR_LargeRatio`). -/
theorem largeRatio_of_N4 : SR_LargeRatio := CKLaneN4.sr_largeRatio

/-- `SR_Parent8` from lane N4 (verbatim row text). -/
theorem parent8_of_N4 : SR_Parent8 := CKLaneN4.sr_parent8

/-- CONDITIONAL (not a closure): the central square from six inputs (the five open rows and
`SR_LargeRatio`). -/
theorem centralSquare_of_open_rows
    (hcap : CKLaneN23.CentralCap) (hNear : CKLaneN23.SmallRatioT3NearRest)
    (hFE : CKLaneN23.FullEntropySSCoverRest)
    (hmod : SR_Moderate) (htr : SR_Transition) (hlr : SR_LargeRatio) :
    CentralSquareRow :=
  centralSquare_of_subrows
    { sameSideHalf := CKLaneN23.sameSideHalf_of_remaining_six_rows
        row_smallRatioT1Cover row_smallRatioT4Rest hcap row_noSepA_moderateRest hNear hFE
      diagonalBand := CKLaneN23.diagonalBand_of_remaining_four_rows
        row_smallRatioT1Cover row_smallRatioT4Rest hcap row_noSepA_moderateRest
      moderate := hmod
      smallRatio := row_SR_SmallRatio
      transition := htr
      largeRatio := hlr }

/-- CONDITIONAL (not a closure): the central square from exactly the five genuinely open inputs;
`SR_LargeRatio` is lane N4's closed `CKLaneN4.sr_largeRatio`. -/
theorem centralSquare_of_five_open_rows
    (hcap : CKLaneN23.CentralCap) (hNear : CKLaneN23.SmallRatioT3NearRest)
    (hFE : CKLaneN23.FullEntropySSCoverRest)
    (hmod : SR_Moderate) (htr : SR_Transition) :
    CentralSquareRow :=
  centralSquare_of_open_rows hcap hNear hFE hmod htr largeRatio_of_N4

/-- CONDITIONAL (not a closure): archive-literal large-ratio routing, parent dominance (2) from lane N4
and a central eight-ratio theorem (3) supplied as `SR_EightRatio`. -/
theorem centralSquare_of_five_open_rows_eight
    (hcap : CKLaneN23.CentralCap) (hNear : CKLaneN23.SmallRatioT3NearRest)
    (hFE : CKLaneN23.FullEntropySSCoverRest)
    (hmod : SR_Moderate) (htr : SR_Transition) (he : SR_EightRatio) :
    CentralSquareRow :=
  centralSquare_of_open_rows hcap hNear hFE hmod htr
    (largeRatio_of_parent8_eightRatio parent8_of_N4 he)

/-- `SR_EightRatio` from lane N4's literal central EIGHT_RATIO proof (verbatim row text). -/
theorem eightRatio_of_N4_central : SR_EightRatio := CKLaneN4.sr_eightRatio_central

/-- `SR_LargeRatio` along the archive-literal route: parent8 ∪ central eight-ratio (both lane N4). -/
theorem largeRatio_of_N4_central : SR_LargeRatio :=
  largeRatio_of_parent8_eightRatio parent8_of_N4 eightRatio_of_N4_central

/-- CONDITIONAL (not a closure), CANONICAL: the central square from exactly the five genuinely open
inputs, with `SR_LargeRatio` along the archive-literal route (`CKLaneN4.sr_parent8` ∪
`CKLaneN4.sr_eightRatio_central`). -/
theorem centralSquare_of_five_open_rows_central
    (hcap : CKLaneN23.CentralCap) (hNear : CKLaneN23.SmallRatioT3NearRest)
    (hFE : CKLaneN23.FullEntropySSCoverRest)
    (hmod : SR_Moderate) (htr : SR_Transition) :
    CentralSquareRow :=
  centralSquare_of_five_open_rows_eight hcap hNear hFE hmod htr eightRatio_of_N4_central

end CKLaneN1

end


