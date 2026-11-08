-- Prove2me | Definitions.Def_OAIQ098G007
-- name    : OAIQ098G007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T17:28:42.118201+00:00
-- url     : https://prove2.me/theorems/c4f4a492-e926-4264-972c-6ade1cd74c00
-- title:
--   Definitions bundle OAIQ098G007 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.Numerical.FiniteIndex`, `OAI.SharpPlanar.Numerical.finiteIndex`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Indices`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Indices.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G010` and `OAIQ098G1694`; the statements `OAI.SharpPlanar.Numerical.finiteIndex_bound_g`, `OAI.SharpPlanar.Numerical.finiteIndex_cover_check_g`, `OAI.SharpPlanar.Numerical.finiteIndex_injective_g` and `OAI.SharpPlanar.Numerical.finiteIndex_range_g`; the proofs of `OAI.SharpPlanar.Numerical.finiteIndex_bound_g`, `OAI.SharpPlanar.Numerical.finiteIndex_cover_check_g`, `OAI.SharpPlanar.Numerical.finiteIndex_injective_g`, `OAI.SharpPlanar.Numerical.finiteIndex_range_g` and `OAI.SharpPlanar.tableCoords_mem_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G006

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Indices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite node coordinates

These coordinates enumerate the value and derivative data on the first
triangular shell nodes in the planar Fourier interpolation problem.
-/

namespace SharpPlanar.Numerical

open scoped BigOperators
abbrev FiniteIndex := Fin 6 ⊕ (Fin 48 × Fin 2)
def finiteIndex : FiniteIndex → Node × Bool := Sum.elim centralIndex exteriorIndex
end SharpPlanar.Numerical

end OAI
end


