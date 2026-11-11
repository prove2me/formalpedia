-- Prove2me | Definitions.Def_OAIQ241TT003
-- name    : OAIQ241TT003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:46:23.198197+00:00
-- url     : https://prove2.me/theorems/6d8f5a0f-5358-4bb6-98cd-462e063d9352
-- title:
--   Definitions bundle OAIQ241TT003 of the split of OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.StrongThinTree.Spectral.block`, `OAI.StrongThinTree.Spectral.tail`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`ThinTrees_SpectralPacking`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/SpectralPacking.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proof of `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.capturePackage`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ241_TT.ThinTrees_SpectralPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι uι2 uV uι3 uV2 uV3 uV4 uV5 uV6 uι4 uη

section
open scoped Classical
open Matrix

namespace StrongThinTree.Spectral
noncomputable section
open Finset LinearMap
open scoped InnerProductSpace
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def tail {d : ℕ} (s : Fin d → ℝ) (p : ℕ) := ∑i with p ≤ i.val + 1, s i
def block {d : ℕ} (s : Fin d → ℝ) (p : ℕ) := ∑i with p ≤ i.val + 1 ∧ i.val + 1 < 2*p, s i

end
end StrongThinTree.Spectral

end

end OAI
end


