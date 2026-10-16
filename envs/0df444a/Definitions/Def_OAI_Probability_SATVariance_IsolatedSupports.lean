-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_IsolatedSupports
-- name    : OAI_Probability_SATVariance_IsolatedSupports
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:49:57.855096+00:00
-- url     : https://prove2.me/theorems/88cfce3e-e200-46d8-9b09-300438f18e0f
-- title:
--   Isolated clauses of a clause word
-- statement:
--   A $k$-clause on $n$ Boolean variables is a set $\operatorname{supp}c$ of $k$ distinct variables in $[n]=\{0,\dots,n-1\}$ together with a sign for each; an assignment satisfies it if it agrees with at least one of these signs. Let $w=(w_0,\dots,w_{M-1})$ be a word of $k$-clauses.
--
--   1. **Isolated position.** A position $i<M$ is isolated in $w$ if the support of $w_i$ is disjoint from the support of every other clause of the word:
--   $$
--   \operatorname{supp}w_i\cap\operatorname{supp}w_j=\emptyset\qquad\text{for all } j<M,\ j\ne i.
--   $$
--   2. **Isolated set.** $\operatorname{Iso}(w)=\{i<M:\ i\text{ is isolated in }w\}$.
--
--   An isolated clause shares no variable with any other clause of the word, so for $k\ge1$ it can always be satisfied independently of the others; it acts as a bystander that can shift the first unsatisfiability time only through its position. For a uniformly random word with $1\le k\le n$, $2k^2\le n$ and $M\le2Rn$, the expected number of isolated positions is at least $Me^{-4Rk^2}$. This linear supply of bystander clauses is the basis of the linear lower bound on the variance of the first unsatisfiability time of random $k$-SAT.
--
--   **Formalization Note** `isolated w i` states that the support of `w i` is `Disjoint` from the support of `w j` for every index $j\ne i$; `isolateSet w` is the corresponding `Finset (Fin M)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/IsolatedSupports.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/IsolatedSupports.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_SATVariance_ShuffleAverages
import Definitions.Def_OAI_Probability_SATVariance_BystanderStops
import Definitions.Def_OAI_Probability_SATVariance_InsertionVariance

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def isolated {n k M : ℕ} (w : Fin M → Clause n k) (i : Fin M) : Prop :=
  ∀ j, j ≠ i → Disjoint (w i).1.1 (w j).1.1

def isolateSet {n k M : ℕ} (w : Fin M → Clause n k) : Finset (Fin M) :=
  Finset.univ.filter (isolated w)

end RandomKSAT

end

end OAI


