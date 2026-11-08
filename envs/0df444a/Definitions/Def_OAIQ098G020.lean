-- Prove2me | Definitions.Def_OAIQ098G020
-- name    : OAIQ098G020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T17:29:32.668616+00:00
-- url     : https://prove2.me/theorems/4efe1c8c-5fb9-4cd7-af9f-6aa4331ddf0e
-- title:
--   Definitions bundle OAIQ098G020 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 9 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.amp1_0Expr`, `OAI.SharpPlanar.CachedData.amp1_1Expr`, `OAI.SharpPlanar.CachedData.amp3_0Expr`, `OAI.SharpPlanar.CachedData.amp3_1Expr`, `OAI.SharpPlanar.CachedData.amp4_0Expr`, `OAI.SharpPlanar.CachedData.amp4_1Expr`, `OAI.SharpPlanar.IntegerGrid.gridRows`, `OAI.SharpPlanar.IntegerGrid.row5`, `OAI.SharpPlanar.IntegerGrid.row5_7`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Amplitudes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Amplitudes.lean), [`PlanarPacking_Grid`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Grid.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G018` and `OAIQ098G019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G061`, `OAIQ098G062`, `OAIQ098G063`, `OAIQ098G066`, `OAIQ098G067`, `OAIQ098G068`, `OAIQ098G103`, `OAIQ098G104`, `OAIQ098G1405`, `OAIQ098G1406`, `OAIQ098G1410`, `OAIQ098G1413`, `OAIQ098G1414`, `OAIQ098G1417`, `OAIQ098G1420`, `OAIQ098G1421`, `OAIQ098G1424`, `OAIQ098G1427`, `OAIQ098G1430`, `OAIQ098G1431`, `OAIQ098G1434`, `OAIQ098G1437`, `OAIQ098G1438`, `OAIQ098G1441`, `OAIQ098G1442`, `OAIQ098G1445`, `OAIQ098G1448`, `OAIQ098G1451`, `OAIQ098G1454`, `OAIQ098G1455`, `OAIQ098G1458`, `OAIQ098G1459`, `OAIQ098G1460`, `OAIQ098G1461`, `OAIQ098G1462`, `OAIQ098G1463`, `OAIQ098G1464`, `OAIQ098G1465`, `OAIQ098G1466`, `OAIQ098G1467`, `OAIQ098G1468`, `OAIQ098G1469`, `OAIQ098G1470`, `OAIQ098G1471`, `OAIQ098G1472`, `OAIQ098G1473`, `OAIQ098G1474`, `OAIQ098G1475`, `OAIQ098G1476`, `OAIQ098G1477`, `OAIQ098G1478`, `OAIQ098G1479`, `OAIQ098G1480`, `OAIQ098G1481`, `OAIQ098G1482`, `OAIQ098G1483`, `OAIQ098G1484`, `OAIQ098G1485`, `OAIQ098G1486`, `OAIQ098G1487`, `OAIQ098G1488`, `OAIQ098G1489`, `OAIQ098G1490`, `OAIQ098G1491`, `OAIQ098G1492`, `OAIQ098G235`, `OAIQ098G237`, `OAIQ098G243`, `OAIQ098G248`, `OAIQ098G250`, `OAIQ098G256`, `OAIQ098G258`, `OAIQ098G263`, `OAIQ098G272`, `OAIQ098G274`, `OAIQ098G283`, `OAIQ098G286`, `OAIQ098G292`, `OAIQ098G299`, `OAIQ098G302`, `OAIQ098G308`, `OAIQ098G311`, `OAIQ098G313`, `OAIQ098G314`, `OAIQ098G316`, `OAIQ098G317`, `OAIQ098G319`, `OAIQ098G322`, `OAIQ098G324`, `OAIQ098G326`, `OAIQ098G328`, `OAIQ098G330`, `OAIQ098G332`, `OAIQ098G333`, `OAIQ098G335`, `OAIQ098G336`, `OAIQ098G338`, `OAIQ098G340`, `OAIQ098G341`, `OAIQ098G343`, `OAIQ098G345`, `OAIQ098G347`, `OAIQ098G349`, `OAIQ098G351` and `OAIQ098G352`; the statements `OAI.SharpPlanar.IntegerGrid.gridRows_contains_g` and `OAI.SharpPlanar.IntegerGrid.row5_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.amp1_0_contains_g`, `OAI.SharpPlanar.CachedData.amp4_0_contains_g`, `OAI.SharpPlanar.CachedData.cm3_3_0_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_4_0_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_4_1_1.contains_g`, `OAI.SharpPlanar.CachedData.cm4_4_1_1.contains_g`, `OAI.SharpPlanar.IntegerGrid.gridRows_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_contains_g`, `OAI.SharpPlanar.Numerical.U61.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U61.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U61.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U61.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U61.wuplus_column_g`, `OAI.SharpPlanar.Numerical.dentry1_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry1_3_contains_g`, `OAI.SharpPlanar.Numerical.dentry1_4_contains_g`, `OAI.SharpPlanar.Numerical.dentry1_5_contains_g`, `OAI.SharpPlanar.Numerical.dentry2_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry2_3_contains_g`, `OAI.SharpPlanar.Numerical.dentry2_4_contains_g`, `OAI.SharpPlanar.Numerical.dentry2_5_contains_g`, `OAI.SharpPlanar.Numerical.dentry4_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry4_3_contains_g`, `OAI.SharpPlanar.Numerical.dentry4_4_contains_g`, `OAI.SharpPlanar.Numerical.dentry4_5_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_3_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_4_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry3_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry3_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry3_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry3_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry8_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry8_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry8_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry8_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry9_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry9_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry9_4_contains_g` and `OAI.SharpPlanar.Numerical.lentry9_5_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G018
import Definitions.Def_OAIQ098G019

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourier quadrature grid

Certified rational enclosures for the quadrature points and their Fourier
kernels on each of the six subintervals.
-/

namespace SharpPlanar.IntegerGrid
open IntegerIntervals IntegerCompact
def row5_7 : Fin 16 → PointBox := ![p5_112,p5_113,p5_114,p5_115,p5_116,p5_117,p5_118,p5_119,p5_120,p5_121,p5_122,p5_123,p5_124,p5_125,p5_126,p5_127]
def row5 : Fin 16 → Fin 16 → PointBox := ![row5_0,row5_1,row5_2,row5_3,row5_4,row5_5,row5_6,row5_7,row5_8,row5_9,row5_10,row5_11,row5_12,row5_13,row5_14,row5_15]
def gridRows : Fin 6 → Fin 16 → Fin 16 → PointBox := ![row0,row1,row2,row3,row4,row5]
end SharpPlanar.IntegerGrid

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Amplitudes
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
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
noncomputable def amp1_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (rcast (weightRows i k)).mul (waveAmplitudeBox (gridRows j i k) (aLookup 1 j) (bLookup 1 j) false)
noncomputable def amp1_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (rcast (weightRows i k)).mul (waveAmplitudeBox (gridRows j i k) (aLookup 1 j) (bLookup 1 j) true)
noncomputable def amp3_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (rcast (weightRows i k)).mul (waveAmplitudeBox (gridRows j i k) (aLookup 3 j) (bLookup 3 j) false)
noncomputable def amp3_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (rcast (weightRows i k)).mul (waveAmplitudeBox (gridRows j i k) (aLookup 3 j) (bLookup 3 j) true)
noncomputable def amp4_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (rcast (weightRows i k)).mul (waveAmplitudeBox (gridRows j i k) (aLookup 4 j) (bLookup 4 j) false)
noncomputable def amp4_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (rcast (weightRows i k)).mul (waveAmplitudeBox (gridRows j i k) (aLookup 4 j) (bLookup 4 j) true)
end SharpPlanar.CachedData

end OAI
end


