-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
-- name    : OAI_Probability_ThorpShuffle_TaggedCompletion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:38:28.84785+00:00
-- url     : https://prove2.me/theorems/70afc539-47e9-4cb1-a8f5-1f28b41ae13e
-- title:
--   Free points: the complement of a finite list of exposed points
-- statement:
--   Let $\alpha$ be a set with decidable equality, and let $e=(e_0,\dots,e_{k-1})$ be a finite sequence of points of $\alpha$ (repetitions allowed). The free marker of $e$ is the indicator $\phi_e:\alpha\to\{0,1\}$ of the points not in the list:
--   $$
--   \phi_e(y)=1\iff y\ne e_i\ \text{for every } i\in\{0,\dots,k-1\}.
--   $$
--   The module records the two basic facts: $\phi_e(e_i)=0$ for every $i$, and $\phi_e(y)=1$ exactly when no $e_i$ equals $y$.
--
--   In the analysis of the Thorp shuffle, $e$ lists the positions of a set of exposed cards. The free marker then singles out the remaining positions, over which the position of a tagged card is compared with the uniform distribution.
--
--   **Formalization Note** The definition is `Conditional.freeOf e`, the Boolean `decide (∀ i, e i ≠ y)`, and the lemmas are `freeOf_exposed` and `freeOf_true`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/TaggedCompletion.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/TaggedCompletion.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def freeOf {α : Type uα} [DecidableEq α] {k : ℕ} (e : Fin k → α) : α → Bool :=
  fun y => decide (∀ i, e i ≠ y)

@[simp] theorem freeOf_exposed {α : Type uα} [DecidableEq α] {k : ℕ}
    (e : Fin k → α) (i : Fin k) : freeOf e (e i) = false := by
  simp [freeOf]

@[simp] theorem freeOf_true {α : Type uα} [DecidableEq α] {k : ℕ}
    (e : Fin k → α) (y : α) : freeOf e y = true ↔ ∀ i, e i ≠ y := by
  simp [freeOf]

end Conditional

end Thorp

end

end OAI


