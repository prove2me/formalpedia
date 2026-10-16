-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_ShuffleAverages
-- name    : OAI_Probability_SATVariance_ShuffleAverages
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:43:24.604261+00:00
-- url     : https://prove2.me/theorems/b9fca544-74d7-42db-b707-3333fc276b87
-- title:
--   Averages over a list and over all rearrangements of a list
-- statement:
--   Let $\alpha$ be a set and $l=(x_1,\dots,x_N)$ a finite list of elements of $\alpha$, repetitions allowed.
--
--   1. **List average.** For $f:\alpha\to\mathbb R$,
--   $$
--   \operatorname{avg}_l f=\frac1N\sum_{i=1}^N f(x_i),
--   $$
--   the average of $f$ over the entries of $l$ counted with multiplicity; it is $0$ for the empty list.
--   2. **Shuffle average.** For a real function $f$ on lists over $\alpha$,
--   $$
--   \operatorname{Sh}_l f=\frac1{N!}\sum_{\pi\in\mathfrak S_N} f\big(x_{\pi(1)},\dots,x_{\pi(N)}\big),
--   $$
--   the expected value of $f$ at a uniformly random rearrangement of the positions of $l$. It is the list average of $f$ over the list of all $N!$ rearrangements of $l$.
--
--   Shuffle averages are invariant under permuting $l$, linear and monotone in $f$, and satisfy $(\operatorname{Sh}_l f)^2\le\operatorname{Sh}_l(f^2)$. They can be computed recursively: shuffling a list $c$ followed by $l$ is the same as shuffling $l$ and then inserting $c$ at a uniformly random one of the $N+1$ positions. Most importantly, if $w$ is a uniformly random word of length $M$ over a finite nonempty set, averaging $f(w)$ over random rearrangements does not change its mean. This lets a uniform random clause word be viewed as a random ordering of its clauses, which is how the lower bound on the variance of the first unsatisfiability time of random $k$-SAT exploits the randomness in the positions of special clauses.
--
--   **Formalization Note** `shuffleAvg l f` is `listAvg` over `l.permutations'`; Mathlib's `List.permutations'` lists all $N!$ positional rearrangements, with repetitions when $l$ has repeated entries. `listAvg` divides by the length, so it is $0$ on the empty list.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/ShuffleAverages.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/ShuffleAverages.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SATVariance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression
import Definitions.Def_OAI_Probability_SATVariance_CapBridge

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def listAvg.{u_1} {α : Type u_1} (l : List α) (f : α → ℝ) : ℝ :=
  (l.map f).sum / l.length

def shuffleAvg.{u_1} {α : Type u_1} (l : List α) (f : List α → ℝ) : ℝ := listAvg l.permutations' f

end RandomKSAT

end

end OAI


