-- Prove2me | Definitions.Def_OAIQ031A189
-- name    : OAIQ031A189
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T17:28:30.42199+00:00
-- url     : https://prove2.me/theorems/aa4e39b1-358e-4ebb-b631-648437bf6a75
-- title:
--   Definitions bundle OAIQ031A189 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Coordinates_ConcreteMainCriterion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ConcreteMainCriterion.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A138`, `OAIQ031A173`, `OAIQ031A174` and `OAIQ031A187` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A191`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A138
import Definitions.Def_OAIQ031A173
import Definitions.Def_OAIQ031A174
import Definitions.Def_OAIQ031A187

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

variable (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0)

attribute [local instance] OAI.ArExplicit.T.instFiniteAEnvelopingBimoduleCarrierTensorProductMulOppositeFiniteFiber_1
attribute [local instance] OAI.ArExplicit.T.instProjectiveAEnvelopingBimoduleCarrierTensorProductMulOppositeFiniteFiber_1
attribute [local instance] OAI.ArExplicit.T.instFiniteMulOppositeAEnvelopingBimoduleCarrierTensorProductFiniteFiber_1
attribute [local instance] OAI.ArExplicit.T.instProjectiveMulOppositeAEnvelopingBimoduleCarrierTensorProductFiniteFiber_1
theorem explicit_mainConclusions (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (hp : Resolution.NoPositivePowerOne q)
    (hg : fiberFullRhoPair q H₁ H₂ 0 g =
      (CompleteComparison.fullHomIdentity (A.simpleComplete q),
        CompleteComparison.fullHomIdentity (A.simpleComplete q)))
    (hspan : ∀ z, ∃ a : k, a • g = z)
    (hrho : ∀ n : ℤ, 0 < n → Function.Bijective (fiberFullRhoPair q H₁ H₂ n))
    (hsep : ∀ m : ℕ, 0 < m → (((H₁⁻¹ : kˣ) : k)^m) ≠ (((H₂⁻¹ : kˣ) : k)^m)) :
    MainConclusions k (explicitAlgebra q H₁ H₂) (explicitLeftModule q H₁ H₂ g) := by
  apply convertedTensorCone_mainConclusions q
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier)
    (A.simpleComplete q) (tensorFiberMap q H₁ H₂ g) hq hq1
    ((A.simpleFiniteModule q).completeCochain_totallyAcyclic (AFrobeniusTrace k q))
  · intro n hn
    exact (tensorFiberComparison_positive_bijective q H₁ H₂ hq hq1 hp g hg hrho hsep n hn).1
  · intro n
    rcases n with _ | n
    · exact tensorFiberMap_zero_surjective q H₁ H₂ g hspan
    · exact (tensorFiberComparison_positive_bijective q H₁ H₂ hq hq1 hp g hg hrho hsep
        (n+1) (by omega)).2
  · exact tensorFiberMap_zero_nonzero_kernel q H₁ H₂ hq1 g

end ArExplicit.T

end

end OAI
end


