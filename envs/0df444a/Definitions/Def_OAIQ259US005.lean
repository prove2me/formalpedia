-- Prove2me | Definitions.Def_OAIQ259US005
-- name    : OAIQ259US005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:06:20.491262+00:00
-- url     : https://prove2.me/theorems/529bcb5f-d0a2-4e6a-a648-d0d0af5d40f7
-- title:
--   Definitions bundle OAIQ259US005 of the split of OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.UniversalTensorSquare.smallT13_5`, `OAI.UniversalTensorSquare.smallT13_6`, `OAI.UniversalTensorSquare.smallT13_7`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`UniversalSquare_Finite_SmallContracts13_1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_1.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the statements `OAI.UniversalTensorSquare.smallCert13_5`, `OAI.UniversalTensorSquare.smallCert13_6` and `OAI.UniversalTensorSquare.smallCert13_7`; the proofs of `OAI.UniversalTensorSquare.smallCert13_5`, `OAI.UniversalTensorSquare.smallCert13_6`, `OAI.UniversalTensorSquare.smallCert13_7`, `OAI.UniversalTensorSquare.smallSupport13_5`, `OAI.UniversalTensorSquare.smallSupport13_6` and `OAI.UniversalTensorSquare.smallSupport13_7`.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 1. -/

section

noncomputable section
namespace UniversalTensorSquare
def smallT13_5 : Equiv.Perm (Fin 13) := Equiv.swap 10 4 * (Equiv.swap 10 2 * (Equiv.swap 7 6 * (Equiv.swap 6 9 * (Equiv.swap 4 12 * (Equiv.swap 4 0 * (Equiv.swap 0 1 * (Equiv.swap 2 11 * (Equiv.swap 1 5 * (Equiv.swap 0 3)))))))))
def smallT13_6 : Equiv.Perm (Fin 13) := Equiv.swap 10 11 * (Equiv.swap 7 0 * (Equiv.swap 7 3 * (Equiv.swap 0 2 * (Equiv.swap 2 9 * (Equiv.swap 3 8 * (Equiv.swap 2 4 * (Equiv.swap 0 5)))))))
def smallT13_7 : Equiv.Perm (Fin 13) := Equiv.swap 6 9 * (Equiv.swap 9 3 * (Equiv.swap 8 7 * (Equiv.swap 7 11 * (Equiv.swap 6 10 * (Equiv.swap 3 2 * (Equiv.swap 3 5 * (Equiv.swap 3 4 * (Equiv.swap 2 12))))))))

end UniversalTensorSquare
end
end

end OAI
end


