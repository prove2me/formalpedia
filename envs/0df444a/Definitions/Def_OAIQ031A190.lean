-- Prove2me | Definitions.Def_OAIQ031A190
-- name    : OAIQ031A190
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T17:19:56.022383+00:00
-- url     : https://prove2.me/theorems/579a0a54-df7b-4ecf-b7bb-91708ae626f5
-- title:
--   Definitions bundle OAIQ031A190 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Fibers_ConcreteFiberProfile`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberProfile.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A187` and `OAIQ031A188` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A191`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A187
import Definitions.Def_OAIQ031A188

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberProfile
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : Resolution.NoPositivePowerOne q)
variable (H₁ H₂ : kˣ)

include hq hq1 h

theorem fiberPositiveRhoPair_bijective (n : ℤ) (hn : 0 < n) :
    Function.Bijective (fiberFullRhoPair q H₁ H₂ n) :=
  fiberFullRhoPair_positive_bijective q H₁ H₂ hq1 (branchZeroScalarEquiv q hq hq1 h)
    (normalizedBranches_equal q hq hq1 h H₁ H₂)
    (normalizedBranch_ne_zero q hq hq1 h H₁)
    (fun a ha => branchHom_subsingleton q hq hq1 h a (by omega) (by omega)) n hn

end ArExplicit.T

end

end OAI
end


