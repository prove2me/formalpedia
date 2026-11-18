-- Prove2me | Definitions.Def_OAIQ368Chrom071
-- name    : OAIQ368Chrom071
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:06:04.671382+00:00
-- url     : https://prove2.me/theorems/18b79e7e-7a39-43cd-bce3-af0f45b26c80
-- title:
--   Definitions bundle OAIQ368Chrom071 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 instance.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_QuantumTorus_QuantumTorus`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/QuantumTorus.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom001` of this split.
--
--   **Imported by** (directly, in this split): none.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom001

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_QuantumTorus
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus

variable {R M : Type*} [CommRing R] [AddCommGroup M]

namespace Torus
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)

noncomputable instance instModule : Module R (Torus v Ω) := inferInstanceAs (Module R (M →₀ R))

end Torus
end ElementaryPositivity.QuantumTorus
end
end

end OAI
end


