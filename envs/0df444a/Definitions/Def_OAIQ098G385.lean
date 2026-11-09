-- Prove2me | Definitions.Def_OAIQ098G385
-- name    : OAIQ098G385
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T05:25:36.854212+00:00
-- url     : https://prove2.me/theorems/7498b253-6094-481b-a0d7-56d852db3746
-- title:
--   Definitions bundle OAIQ098G385 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.allColumns`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TableDensityExpr`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableDensityExpr.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G024`, `OAIQ098G028`, `OAIQ098G038`, `OAIQ098G047`, `OAIQ098G107`, `OAIQ098G109`, `OAIQ098G111`, `OAIQ098G113`, `OAIQ098G115`, `OAIQ098G117`, `OAIQ098G125`, `OAIQ098G129`, `OAIQ098G132`, `OAIQ098G133`, `OAIQ098G136`, `OAIQ098G139`, `OAIQ098G142`, `OAIQ098G145`, `OAIQ098G148`, `OAIQ098G151`, `OAIQ098G161`, `OAIQ098G164`, `OAIQ098G167`, `OAIQ098G170`, `OAIQ098G173`, `OAIQ098G176`, `OAIQ098G180`, `OAIQ098G186`, `OAIQ098G189`, `OAIQ098G191`, `OAIQ098G193`, `OAIQ098G195`, `OAIQ098G197`, `OAIQ098G199`, `OAIQ098G201`, `OAIQ098G203`, `OAIQ098G205`, `OAIQ098G207`, `OAIQ098G209`, `OAIQ098G211`, `OAIQ098G213`, `OAIQ098G215`, `OAIQ098G217`, `OAIQ098G220`, `OAIQ098G222`, `OAIQ098G224`, `OAIQ098G226`, `OAIQ098G228`, `OAIQ098G230`, `OAIQ098G232`, `OAIQ098G234`, `OAIQ098G236` and `OAIQ098G384` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G397`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G024
import Definitions.Def_OAIQ098G028
import Definitions.Def_OAIQ098G038
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G107
import Definitions.Def_OAIQ098G109
import Definitions.Def_OAIQ098G111
import Definitions.Def_OAIQ098G113
import Definitions.Def_OAIQ098G115
import Definitions.Def_OAIQ098G117
import Definitions.Def_OAIQ098G125
import Definitions.Def_OAIQ098G129
import Definitions.Def_OAIQ098G132
import Definitions.Def_OAIQ098G133
import Definitions.Def_OAIQ098G136
import Definitions.Def_OAIQ098G139
import Definitions.Def_OAIQ098G142
import Definitions.Def_OAIQ098G145
import Definitions.Def_OAIQ098G148
import Definitions.Def_OAIQ098G151
import Definitions.Def_OAIQ098G161
import Definitions.Def_OAIQ098G164
import Definitions.Def_OAIQ098G167
import Definitions.Def_OAIQ098G170
import Definitions.Def_OAIQ098G173
import Definitions.Def_OAIQ098G176
import Definitions.Def_OAIQ098G180
import Definitions.Def_OAIQ098G186
import Definitions.Def_OAIQ098G189
import Definitions.Def_OAIQ098G191
import Definitions.Def_OAIQ098G193
import Definitions.Def_OAIQ098G195
import Definitions.Def_OAIQ098G197
import Definitions.Def_OAIQ098G199
import Definitions.Def_OAIQ098G201
import Definitions.Def_OAIQ098G203
import Definitions.Def_OAIQ098G205
import Definitions.Def_OAIQ098G207
import Definitions.Def_OAIQ098G209
import Definitions.Def_OAIQ098G211
import Definitions.Def_OAIQ098G213
import Definitions.Def_OAIQ098G215
import Definitions.Def_OAIQ098G217
import Definitions.Def_OAIQ098G220
import Definitions.Def_OAIQ098G222
import Definitions.Def_OAIQ098G224
import Definitions.Def_OAIQ098G226
import Definitions.Def_OAIQ098G228
import Definitions.Def_OAIQ098G230
import Definitions.Def_OAIQ098G232
import Definitions.Def_OAIQ098G234
import Definitions.Def_OAIQ098G236
import Definitions.Def_OAIQ098G384

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensityExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
noncomputable def allColumns (n : Fin 101) (d : Bool) (j : Fin 6) (i k : Fin 16) : CBox := match n.val with
  | 0 => if d then column0_1 j i k else column0_0 j i k
  | 1 => if d then column1_1 j i k else column1_0 j i k
  | 3 => if d then column3_1 j i k else column3_0 j i k
  | 4 => if d then column4_1 j i k else column4_0 j i k
  | 7 => if d then column7_1 j i k else column7_0 j i k
  | 9 => if d then column9_1 j i k else column9_0 j i k
  | 12 => if d then column12_1 j i k else column12_0 j i k
  | 13 => if d then column13_1 j i k else column13_0 j i k
  | 15 => if d then column15_1 j i k else column15_0 j i k
  | 16 => if d then column16_1 j i k else column16_0 j i k
  | 19 => if d then column19_1 j i k else column19_0 j i k
  | 21 => if d then column21_1 j i k else column21_0 j i k
  | 24 => if d then column24_1 j i k else column24_0 j i k
  | 25 => if d then column25_1 j i k else column25_0 j i k
  | 27 => if d then column27_1 j i k else column27_0 j i k
  | 28 => if d then column28_1 j i k else column28_0 j i k
  | 31 => if d then column31_1 j i k else column31_0 j i k
  | 33 => if d then column33_1 j i k else column33_0 j i k
  | 36 => if d then column36_1 j i k else column36_0 j i k
  | 37 => if d then column37_1 j i k else column37_0 j i k
  | 39 => if d then column39_1 j i k else column39_0 j i k
  | 40 => if d then column40_1 j i k else column40_0 j i k
  | 43 => if d then column43_1 j i k else column43_0 j i k
  | 45 => if d then column45_1 j i k else column45_0 j i k
  | 48 => if d then column48_1 j i k else column48_0 j i k
  | 49 => if d then column49_1 j i k else column49_0 j i k
  | 51 => if d then column51_1 j i k else column51_0 j i k
  | 52 => if d then column52_1 j i k else column52_0 j i k
  | 55 => if d then column55_1 j i k else column55_0 j i k
  | 57 => if d then column57_1 j i k else column57_0 j i k
  | 60 => if d then column60_1 j i k else column60_0 j i k
  | 61 => if d then column61_1 j i k else column61_0 j i k
  | 63 => if d then column63_1 j i k else column63_0 j i k
  | 64 => if d then column64_1 j i k else column64_0 j i k
  | 67 => if d then column67_1 j i k else column67_0 j i k
  | 69 => if d then column69_1 j i k else column69_0 j i k
  | 72 => if d then column72_1 j i k else column72_0 j i k
  | 73 => if d then column73_1 j i k else column73_0 j i k
  | 75 => if d then column75_1 j i k else column75_0 j i k
  | 76 => if d then column76_1 j i k else column76_0 j i k
  | 79 => if d then column79_1 j i k else column79_0 j i k
  | 81 => if d then column81_1 j i k else column81_0 j i k
  | 84 => if d then column84_1 j i k else column84_0 j i k
  | 85 => if d then column85_1 j i k else column85_0 j i k
  | 87 => if d then column87_1 j i k else column87_0 j i k
  | 88 => if d then column88_1 j i k else column88_0 j i k
  | 91 => if d then column91_1 j i k else column91_0 j i k
  | 93 => if d then column93_1 j i k else column93_0 j i k
  | 96 => if d then column96_1 j i k else column96_0 j i k
  | 97 => if d then column97_1 j i k else column97_0 j i k
  | 99 => if d then column99_1 j i k else column99_0 j i k
  | 100 => if d then column100_1 j i k else column100_0 j i k
  | _ => CBox.rat 0 1 0 1
end SharpPlanar.CachedData

end OAI
end


