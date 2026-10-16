-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_Subcube
-- name    : OAI_Probability_SATVariance_Subcube
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:16:57.624432+00:00
-- url     : https://prove2.me/theorems/f7b6406b-24a5-405c-a756-71534fe096fb
-- title:
--   Subcube of assignments that are false on the first $b$ variables
-- statement:
--   For $u,b\in\mathbb N$, let $Q_{u,b}$ be the set of assignments $a:[u]\to\{\mathrm T,\mathrm F\}$ of the variables $[u]=\{0,\dots,u-1\}$ that are false on every variable with index below $b$:
--   $$
--   Q_{u,b}=\big\{a\in\{\mathrm T,\mathrm F\}^{[u]} : a(v)=\mathrm F\ \text{for all } v\in[u] \text{ with } v<b\big\}.
--   $$
--
--   When $b\le u$ this is a subcube of dimension $u-b$: the first $b$ coordinates are fixed and the remaining $u-b$ are free. It always contains the all-false assignment, and its frozen variables (those on which all its members agree) are exactly the variables with index below $b$. It is therefore the simplest nonempty solution set with a prescribed number of frozen variables, and it serves as the test set when the probability that one random clause of width $k-1$ kills a solution set is compared with the probability that a block of random clauses of width $k$ does.
--
--   **Formalization Note** If $b\ge u$, the condition constrains every variable and $Q_{u,b}$ consists of the all-false assignment only.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/Subcube.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/Subcube.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SATSharpness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace RandomKSAT

def subcube (u b : ℕ) : Finset (Assignment u) :=
  Finset.univ.filter fun a => ∀ v : Fin u, (v : ℕ) < b → a v = false

end RandomKSAT

end

end OAI


