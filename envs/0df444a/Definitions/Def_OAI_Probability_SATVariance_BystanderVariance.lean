-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_BystanderVariance
-- name    : OAI_Probability_SATVariance_BystanderVariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:51:22.971901+00:00
-- url     : https://prove2.me/theorems/b7590d8f-5534-4e17-a802-e0df4f0a8748
-- title:
--   Shuffle variance, the stopping window, and a choice of isolated bystander clauses
-- statement:
--   For a finite list $l$ of length $N$ over a set and a real function $f$ on lists, $\operatorname{Sh}_l f$ denotes the average of $f$ over all $N!$ rearrangements of the positions of $l$. A $k$-clause on $n$ Boolean variables is a set of $k$ distinct variables in $[n]=\{0,\dots,n-1\}$ with a sign for each, satisfied by an assignment that agrees with at least one sign. For a list $r$ of clauses, $\operatorname{stop}(r)$ is the length of the shortest unsatisfiable initial segment of $r$, or $|r|+1$ if $r$ is satisfiable. For a word $w=(w_0,\dots,w_{M-1})$ of $k$-clauses, position $i$ is isolated if the support of $w_i$ is disjoint from the supports of all other $w_j$, and $\operatorname{Iso}(w)$ is the set of isolated positions.
--
--   1. **Shuffle variance.** $\operatorname{SV}_l f=\operatorname{Sh}_l(f^2)-(\operatorname{Sh}_l f)^2$, the variance of $f$ at a uniformly random rearrangement of $l$.
--   2. **Outside-window indicator.** For $Q,V\in\mathbb N$ and a list $r$ of clauses,
--   $$
--   \mathbf 1^{\mathrm{out}}_{Q,V}(r)=\begin{cases}1&\text{if } \operatorname{stop}(r)<2Q \text{ or } \operatorname{stop}(r)>V,\\0&\text{otherwise.}\end{cases}
--   $$
--   3. **Chosen isolates.** For $Q\in\mathbb N$, $\operatorname{Ch}_Q(w)\subseteq\operatorname{Iso}(w)$ is a fixed choice of a subset with exactly $\min\big(Q,|\operatorname{Iso}(w)|\big)$ elements.
--   4. **Bystander and active lists.** The bystander list consists of the clauses $w_i$ with $i\in\operatorname{Ch}_Q(w)$, and the active list of the clauses $w_i$ with $i\notin\operatorname{Ch}_Q(w)$, each listed once in some fixed order.
--
--   The bystander list followed by the active list is a rearrangement of $w$, and for $k\ge1$ the two lists form a bystander configuration, since each chosen clause has a variable occurring in no other clause. The variance of $\operatorname{stop}(w)$ for a uniformly random word dominates its average shuffle variance, and the random insertion positions of the bystanders contribute variance whenever the stopping index lies in the window $[2Q,V]$. For $1\le k\le n$ and $Q+V\le M+1$ this gives
--   $$
--   \frac{Q(M+1-Q-V)}{(M+1)^2}\,\mathbb E\min\big(Q,|\operatorname{Iso}(w)|\big)\le\operatorname{Var}\operatorname{stop}(w)+\frac{Q(M+1-Q-V)}{(M+1)^2}\,Q\,\mathbb E\,\mathbf 1^{\mathrm{out}}_{Q,V}(w),
--   $$
--   where $w$ is a uniformly random word of $M$ clauses. This is the main step toward the linear lower bound on the variance of the first unsatisfiability time of random $k$-SAT.
--
--   **Formalization Note** `chosenIsolates` applies `Classical.choose` to the existence of a subset of the required size. `bystanderList` and `activeList` turn these index sets into lists with `Finset.toList`, whose order is unspecified, and then apply $w$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/BystanderVariance.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/BystanderVariance.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_SATVariance_IsolatedSupports

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def shuffleVar.{u_1} {α : Type u_1} (l : List α) (f : List α → ℝ) : ℝ :=
  shuffleAvg l (fun r => (f r)^2) - (shuffleAvg l f)^2

def outsideWindow {n k : ℕ} (Q V : ℕ) (r : List (Clause n k)) : ℝ :=
  if listStop r < 2*Q ∨ V < listStop r then 1 else 0

def chosenIsolates {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) : Finset (Fin M) :=
  Classical.choose (Finset.exists_subset_card_eq (s := isolateSet w) (min_le_right Q (isolateSet w).card))

def bystanderList {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) : List (Clause n k) :=
  (chosenIsolates Q w).toList.map w

def activeList {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) : List (Clause n k) :=
  (Finset.univ \ chosenIsolates Q w).toList.map w

end RandomKSAT

end

end OAI


