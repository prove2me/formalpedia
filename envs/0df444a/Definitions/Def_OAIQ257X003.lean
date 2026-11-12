-- Prove2me | Definitions.Def_OAIQ257X003
-- name    : OAIQ257X003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T03:33:20.910961+00:00
-- url     : https://prove2.me/theorems/5876a952-75bb-4986-a01d-cacb13ef9bae
-- title:
--   Definitions bundle OAIQ257X003 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.AtomicTriangular.Construction.tailBase`, `OAI.AtomicTriangular.Construction.tailEnvelopeSum`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Envelope_EnvelopeBoxes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeBoxes.lean), [`Triangular_Envelope_EnvelopeSumsBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSumsBase.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundle `OAIQ257X000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ257X004`, `OAIQ257X005` and `OAIQ257X030`; the statement `OAI.AtomicTriangular.Construction.tail_atom_column_bounds_x`; the proofs of `OAI.AtomicTriangular.Construction.Ckernel_summable_x`, `OAI.AtomicTriangular.Construction.actualFiniteError_norm_x` and `OAI.AtomicTriangular.Construction.actualTail_norm_x`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X000

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def tailBase (a : Fin 15) : ℤ := residue a + if residue a < 25 then 36 else 0
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeSumsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def tailEnvelopeSum (q v : Fin 2) (j : Fin 31) : ℝ :=
  (∑ a : Fin 15, normJetEnvelope (damping q) (damping v) (tailBase a) (frequency j)) *
    (1-Real.exp (-frequencyDecay (damping q) (damping v) (frequency j)*36))⁻¹

end AtomicTriangular.Construction
end

end OAI
end


