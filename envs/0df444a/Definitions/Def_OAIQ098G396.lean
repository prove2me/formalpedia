-- Prove2me | Definitions.Def_OAIQ098G396
-- name    : OAIQ098G396
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:38:13.161796+00:00
-- url     : https://prove2.me/theorems/95c0cb13-d66d-4ef3-8d34-1b2453531944
-- title:
--   Definitions bundle OAIQ098G396 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.tableCoordRat`, `OAI.SharpPlanar.tableNum`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_TableDensityBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TableDensityBase.lean), [`PlanarPacking_TableNorms`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TableNorms.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1694` and `OAIQ098G397`; the proof of `OAI.SharpPlanar.tail_second_bound_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G015

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableDensityBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite cardinal densities

Finite rational coefficient families determine the densities used in the quadrature estimates.
-/

namespace SharpPlanar
open scoped BigOperators

noncomputable def tableNum (i d : Bool) (n : ℕ) : ℤ :=
  if n=0 then (if d then (if i then -3680000000 else 4400000000) else (if i then 0 else 10000000000))
  else if d then (if i then (tableRaw n).2.2.2 else (tableRaw n).2.1)
    else (if i then (tableRaw n).2.2.1 else (tableRaw n).1)

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Norm bounds for the rational coefficient family

Finite rational sums give bounds for the mass of the cardinal coefficients.
-/

namespace SharpPlanar
open Numerical
open scoped BigOperators
noncomputable def tableCoordRat (a : Bool) (ni : Node×Bool) : ℚ :=
  if ni.2 then tableD a ni.1.val else tableC a ni.1.val
end SharpPlanar

end OAI
end


