-- Prove2me | Definitions.Def_OAIQ098E010
-- name    : OAIQ098E010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T04:39:38.767299+00:00
-- url     : https://prove2.me/theorems/59f5db5d-7d72-4f5c-85d8-2afa4482c6fb
-- title:
--   Definitions bundle OAIQ098E010 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 6 definitions. The definitions and types are `OAI.SharpPlanar.Numerical.IF`, `OAI.SharpPlanar.Numerical.RF`, `OAI.SharpPlanar.Numerical.finiteA`, `OAI.SharpPlanar.Numerical.signedS`, `OAI.SharpPlanar.finiteEmbedding`, `OAI.SharpPlanar.finiteRestriction`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_FiniteCoordinates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FiniteCoordinates.lean), [`PlanarPacking_FiniteFull`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FiniteFull.lean), [`PlanarPacking_FiniteProjection`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FiniteProjection.lean).
--
--   **Imports.** It imports the bundles `OAIQ098E007`, `OAIQ098E008` and `OAIQ098E009` of this split; the published statements `OAI.SharpPlanar.Numerical.finiteIndex_injective_e`, `OAI.SharpPlanar.finiteEmbedding_bound_e` and `OAI.SharpPlanar.finiteRestriction_bound_e`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098E059`, `OAIQ098E066`, `OAIQ098E075`, `OAIQ098E077`, `OAIQ098E105`, `OAIQ098E111`, `OAIQ098E127` and `OAIQ098E237`; the statements `OAI.SharpPlanar.Numerical.finiteA_bijective_e`, `OAI.SharpPlanar.Numerical.interpolation_exists_unique_e`, `OAI.SharpPlanar.finiteEmbedding_apply_e`, `OAI.SharpPlanar.finiteEmbedding_norm_e`, `OAI.SharpPlanar.finiteRestriction_apply_e` and `OAI.SharpPlanar.finiteRestriction_embedding_e`; the proofs of `OAI.SharpPlanar.finiteEmbedding_apply_e`, `OAI.SharpPlanar.finiteEmbedding_norm_e`, `OAI.SharpPlanar.finiteRestriction_apply_e` and `OAI.SharpPlanar.finiteRestriction_embedding_e`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098E007
import Definitions.Def_OAIQ098E008
import Definitions.Def_OAIQ098E009
import Theorems.Thm_OAI_SharpPlanar_Numerical_finiteIndex_injective_e
import Theorems.Thm_OAI_SharpPlanar_finiteEmbedding_bound_e
import Theorems.Thm_OAI_SharpPlanar_finiteRestriction_bound_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
namespace SharpPlanar
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
noncomputable def finiteRestriction : X →L[ℝ] L1Finite ι :=
  (finiteRestrictionLinear e).mkContinuous 1 (finiteRestriction_bound_e e he)
noncomputable def finiteEmbedding : L1Finite ι →L[ℝ] X :=
  (finiteEmbeddingLinear e).mkContinuous 1 (finiteEmbedding_bound_e e)
end
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite coordinate projections

Restriction and extension identify the first shell coordinates with a finite
subspace of the absolutely summable interpolation space.
-/

namespace SharpPlanar.Numerical
open scoped BigOperators
noncomputable abbrev RF := finiteRestriction finiteIndex finiteIndex_injective_e
noncomputable abbrev IF := finiteEmbedding finiteIndex
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite interpolation system

Schur complements give existence, uniqueness and norm bounds for the finite system.
-/

namespace SharpPlanar.Numerical
noncomputable def signedS (neg : Bool) : X →L[ℝ] X := if neg then -S else S
noncomputable def finiteA (neg : Bool) : L1Finite FiniteIndex →L[ℝ] L1Finite FiniteIndex :=
  1-RF.comp ((signedS neg).comp IF)
end SharpPlanar.Numerical

end OAI
end


