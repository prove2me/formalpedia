-- Prove2me | Definitions.Def_OAIQ031A173
-- name    : OAIQ031A173
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:23:31.611977+00:00
-- url     : https://prove2.me/theorems/3db982d2-775e-43f6-a014-993a33e35286
-- title:
--   Definitions bundle OAIQ031A173 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Coordinates_ConcreteMainCriterion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ConcreteMainCriterion.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A163` and `OAIQ031A167` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A189`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A163
import Definitions.Def_OAIQ031A167

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ConcreteMainCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.A k q))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

local instance instFiniteAEnvelopingBimoduleCarrierTensorProductMulOppositeFiniteFiber_1 : Module.Finite (A k q)
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier) := by
  simpa only [explicitBimodule, BimoduleFiber.bimodule, BimoduleFiber.finiteModule, finiteFiber]
    using (explicitBimodule_left q H₁ H₂).1
local instance instProjectiveAEnvelopingBimoduleCarrierTensorProductMulOppositeFiniteFiber_1 : Module.Projective (A k q)
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier) := by
  simpa only [explicitBimodule, BimoduleFiber.bimodule, BimoduleFiber.finiteModule, finiteFiber]
    using (explicitBimodule_left q H₁ H₂).2
local instance instFiniteMulOppositeAEnvelopingBimoduleCarrierTensorProductFiniteFiber_1 : Module.Finite (A k q)ᵐᵒᵖ
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier) := by
  simpa only [explicitBimodule, BimoduleFiber.bimodule, BimoduleFiber.finiteModule, finiteFiber]
    using (explicitBimodule_right q H₁ H₂).1

end ArExplicit.T

end

end OAI
end


