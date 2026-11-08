-- Prove2me | Definitions.Def_OAIQ098G1681
-- name    : OAIQ098G1681
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:31:00.291355+00:00
-- url     : https://prove2.me/theorems/b417316d-6f49-442d-be6b-fc3f93abfbf0
-- title:
--   Definitions bundle OAIQ098G1681 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.tableDensity`, `OAI.SharpPlanar.tableMomentIntegral`, `OAI.SharpPlanar.tableMomentRule`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_TableDensityBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TableDensityBase.lean), [`PlanarPacking_TableMomentsBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TableMomentsBase.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G015` and `OAIQ098G072` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1682`; the statements `OAI.SharpPlanar.CachedData.density0_contains_g`, `OAI.SharpPlanar.CachedData.density1_contains_g` and `OAI.SharpPlanar.tableData_density_g`; the proofs of `OAI.SharpPlanar.CachedData.density0_contains_g`, `OAI.SharpPlanar.CachedData.density1_contains_g` and `OAI.SharpPlanar.tableData_density_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G015
import Definitions.Def_OAIQ098G072

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
open IntegerIntervals IntegerBasis IntegerGrid
open scoped BigOperators

noncomputable def tableDensity (i : Bool) (j : ℕ) (t : ℂ) : ℂ :=
  finiteDensity (fun n => (tableC i n:ℝ)) (fun n => (tableD i n:ℝ)) j t

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableMomentsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Certified quadrature and atomic bounds for the Gaussian moments -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid Numerical
open scoped BigOperators

noncomputable def tableMomentRule (a : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ∑ j : Fin 6, pieceRule (fun t => tableDensity a j.val t * complexTransformedFactor m 1 ell t) j.val
noncomputable def tableMomentIntegral (a : Bool) (m : ℝ) (ell : ℕ) : ℂ :=
  ∑ j : Fin 6, pieceIntegral (fun t => tableDensity a j.val t * complexTransformedFactor m 1 ell t) j.val
end SharpPlanar

end OAI
end


