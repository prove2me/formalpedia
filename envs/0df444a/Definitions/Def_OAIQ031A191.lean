-- Prove2me | Definitions.Def_OAIQ031A191
-- name    : OAIQ031A191
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T17:44:51.335631+00:00
-- url     : https://prove2.me/theorems/30b97f3c-f6f3-498d-8a5d-8c2e6f7bfe50
-- title:
--   Definitions bundle OAIQ031A191 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.ArExplicit.counterexample`, `OAI.ArExplicit.explicitConclusionProof`, `OAI.ArExplicit.verifiedCounterexample`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Main`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Main.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A189` and `OAIQ031A190` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.ArExplicit.Statement.main`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A189
import Definitions.Def_OAIQ031A190

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit
universe v

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

attribute [local instance] OAI.ArExplicit.instHasDerivedCategoryModuleCatTBaseFieldQ
attribute [local instance] OAI.ArExplicit.instHasDerivedCategoryModuleCatABaseFieldQ
abbrev explicitConclusionProof :=
  let hspan := fun z =>
    Exists.elim (T.fiberDiagonalClass_spans q q_ne_zero one_add_q_ne_zero
      q_noPositivePowerOne (parameterUnit 1) (parameterUnit 2) z)
      (fun a ha => Exists.intro a ha.symm)
  T.explicit_mainConclusions q (parameterUnit 1) (parameterUnit 2)
    diagonalClass q_ne_zero one_add_q_ne_zero q_noPositivePowerOne
    (T.fiberDiagonalClass_image q q_ne_zero one_add_q_ne_zero q_noPositivePowerOne
      (parameterUnit 1) (parameterUnit 2))
    hspan
    (T.fiberPositiveRhoPair_bijective q q_ne_zero one_add_q_ne_zero q_noPositivePowerOne
      (parameterUnit 1) (parameterUnit 2))
    parameterUnit_twist_ne

def verifiedCounterexample := verifiedCandidate explicitConclusionProof

def counterexample : Candidate := verifiedCounterexample.val

end ArExplicit

end

end OAI
end


