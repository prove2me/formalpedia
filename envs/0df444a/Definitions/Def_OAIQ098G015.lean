-- Prove2me | Definitions.Def_OAIQ098G015
-- name    : OAIQ098G015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T16:18:02.324481+00:00
-- url     : https://prove2.me/theorems/6bea5d65-865b-4638-928f-338659a3a557
-- title:
--   Definitions bundle OAIQ098G015 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.tableC`, `OAI.SharpPlanar.tableCoords`, `OAI.SharpPlanar.tableD`, `OAI.SharpPlanar.tableRaw`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TableData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableData.lean), [`PlanarPacking_Certificate_TableList`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableList.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1673`, `OAIQ098G1681`, `OAIQ098G1686` and `OAIQ098G396`; the statements `OAI.SharpPlanar.tableC_offnode_g`, `OAI.SharpPlanar.tableCoords_mem_g`, `OAI.SharpPlanar.tableD_offnode_g`, `OAI.SharpPlanar.tableRaw_offnode_g` and `OAI.SharpPlanar.table_range_mass_g`; the proofs of `OAI.SharpPlanar.tableC_offnode_g`, `OAI.SharpPlanar.tableCoords_mem_g`, `OAI.SharpPlanar.tableD_offnode_g`, `OAI.SharpPlanar.tableRaw_offnode_g` and `OAI.SharpPlanar.table_range_mass_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G000

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableData
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

open scoped BigOperators
namespace SharpPlanar


noncomputable def tableRaw : ℕ → ℤ × ℤ × ℤ × ℤ
  | 1 => (-670689128, -6398628799, -250018302, 4107732082)
  | 3 => (93524468, 564897270, -186215974, -65204793)
  | 4 => (-64146977, 121133118, 82882809, -327822296)
  | 7 => (-1358193, -16329465, 1979670, 21637038)
  | 9 => (-2932910, -940875, 3636920, 2145806)
  | 12 => (3646952, -34846939, -6005382, 34369042)
  | 13 => (3183411, 63030995, -574123, -75237042)
  | 15 => (11390977, 27049982, -11312377, -34985096)
  | 16 => (-5593246, 13405071, 5915710, -10980954)
  | 19 => (54905, -1515007, -120136, 1498351)
  | 21 => (-210208, -634307, 177992, 747946)
  | 24 => (976077, -804949, -1037705, 105643)
  | 25 => (-824472, 7003719, 1011732, -6510015)
  | 27 => (611891, 4536095, -428528, -4440927)
  | 28 => (-472882, -107613, 399655, 403751)
  | 31 => (30744, -112653, -31773, 90515)
  | 33 => (-4974, -105568, 1240, 99081)
  | 36 => (128313, 246018, -114876, -267388)
  | 37 => (-176685, 505187, 166591, -396209)
  | 39 => (-21638, 472037, 32128, -402283)
  | 40 => (-18461, -165597, 10836, 164974)
  | 43 => (4565, -2296, -4050, 547)
  | 45 => (1477, -10734, -1524, 8978)
  | 48 => (10748, 50050, -8611, -45048)
  | 49 => (-20506, 7495, 17354, -266)
  | 51 => (-10361, 29035, 9641, -21534)
  | 52 => (2121, -26523, -2269, 23159)
  | 55 => (425, 858, -344, -839)
  | 57 => (302, -632, -266, 463)
  | 60 => (382, 5658, -231, -4688)
  | 61 => (-1481, -4320, 1140, 4098)
  | 63 => (-1494, -352, 1265, 647)
  | 64 => (558, -2609, -491, 2114)
  | 67 => (21, 169, -14, -145)
  | 69 => (34, 13, -28, -18)
  | 72 => (-55, 394, 53, -301)
  | 73 => (-21, -805, 5, 685)
  | 75 => (-136, -379, 108, 338)
  | 76 => (70, -144, -58, 104)
  | 79 => (-1, 19, 1, -15)
  | 81 => (2, 9, -2, -8)
  | 84 => (-13, 3, 11, 0)
  | 85 => (13, -87, -11, 70)
  | 87 => (-6, -60, 4, 49)
  | 88 => (6, 5, -4, -5)
  | 91 => (0, 1, 0, -1)
  | 93 => (0, 1, 0, -1)
  | 96 => (-2, -4, 1, 3)
  | 97 => (2, -6, -2, 4)
  | 99 => (0, -6, 0, 5)
  | 100 => (0, 2, 0, -2)
  | _ => (0,0,0,0)

noncomputable def tableC (i : Bool) (n : ℕ) : ℚ :=
  if n = 0 then (if i then 0 else 1)
  else (if i then (tableRaw n).2.2.1 else (tableRaw n).1)/10000000000

noncomputable def tableD (i : Bool) (n : ℕ) : ℚ :=
  if n = 0 then (if i then -46/125 else 11/25)
  else (if i then (tableRaw n).2.2.2 else (tableRaw n).2.1)/10000000000

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableList
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

namespace SharpPlanar
open Numerical
noncomputable def tableCoords (a : Bool) (ni : Node×Bool) : ℝ :=
  if ni.2 then (tableD a ni.1.val:ℝ) else (tableC a ni.1.val:ℝ)
end SharpPlanar

end OAI
end


