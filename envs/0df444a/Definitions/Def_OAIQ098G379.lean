-- Prove2me | Definitions.Def_OAIQ098G379
-- name    : OAIQ098G379
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T19:21:31.164952+00:00
-- url     : https://prove2.me/theorems/f0763786-38aa-45e3-9e80-5e3a697dde95
-- title:
--   Definitions bundle OAIQ098G379 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 6 definitions. The definitions and types are `OAI.SharpPlanar.factorRational`, `OAI.SharpPlanar.pieceRational`, `OAI.SharpPlanar.rowFactor`, `OAI.SharpPlanar.rowPiece`, `OAI.SharpPlanar.rowTable`, `OAI.SharpPlanar.tableRational`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_CanonicalRows`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G362` and `OAIQ098G365` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SharpPlanar.rowTable_bounds_g`, `OAI.SharpPlanar.rowTable_le_g`, `OAI.SharpPlanar.sharp_S_tail_g`, `OAI.SharpPlanar.tableRational_hundred_g` and `OAI.SharpPlanar.tableRational_sixteen_g`; the proofs of `OAI.SharpPlanar.Numerical.exterior_exterior_norm_g`, `OAI.SharpPlanar.Numerical.finiteA_bijective_g`, `OAI.SharpPlanar.Numerical.interpolation_exists_unique_g`, `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.exact_head_lower_g`, `OAI.SharpPlanar.rowTable_bounds_g`, `OAI.SharpPlanar.rowTable_le_g`, `OAI.SharpPlanar.sharp_S_tail_g`, `OAI.SharpPlanar.tableRational_hundred_g`, `OAI.SharpPlanar.tableRational_sixteen_g` and `OAI.SharpPlanar.tail_second_bound_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G362
import Definitions.Def_OAIQ098G365

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open IntegerBasis


noncomputable def rowFactor (j : Fin 6) (n : ℕ) : ℝ :=
  (1+|D n|+Real.pi*zCap ⟨j.val,by omega⟩)/Q n*densityCap j
noncomputable def rowPiece (j : Fin 6) (n : ℕ) : ℝ :=
  if n%12 ∈ residues then rowFactor j n * pieceL j n else 0
noncomputable def rowTable (N : ℕ) : ℝ :=
  ∑ j : Fin 6, (∑ a : Fin 12, rowPiece j (N+1+a.val)) /
    (1-Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩))

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

noncomputable def factorRational (j : Fin 6) (n : ℕ) : ℝ :=
  (1+rowDUpper n+(31416/10000:ℝ)*zCap ⟨j.val,by omega⟩)/rowQLower n*densityCap j
noncomputable def pieceRational (j : Fin 6) (n : ℕ) : ℝ :=
  if n%12 ∈ residues then factorRational j n *
    (lambdaCap ⟨j.val,by omega⟩*pieceBase j^n*massRational j n) else 0
noncomputable def tableRational (N : ℕ) : ℝ :=
  ∑ j : Fin 6, (∑ a : Fin 12, pieceRational j (N+1+a.val))/(1-pieceBase j^12)
end SharpPlanar

end OAI
end


