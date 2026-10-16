-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_BystanderStops
-- name    : OAI_Probability_SATVariance_BystanderStops
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:45:40.18192+00:00
-- url     : https://prove2.me/theorems/b9ab063b-bd81-4604-bc59-78d4cc633a34
-- title:
--   Satisfiability and stopping index of a clause list, and harmless clauses
-- statement:
--   A $k$-clause on $n$ Boolean variables is a set of $k$ distinct variables in $[n]=\{0,\dots,n-1\}$ with a sign for each; an assignment $a:[n]\to\{\mathrm T,\mathrm F\}$ satisfies it if it agrees with at least one of these signs. Let $l=(c_1,\dots,c_N)$ be a finite list of $k$-clauses.
--
--   1. **Satisfiable list.** $l$ is satisfiable if a single assignment satisfies every clause in $l$.
--   2. **Stopping index.**
--   $$
--   \operatorname{stop}(l)=\min\big\{m\in\mathbb N:\ m=N+1\ \text{ or } (c_1,\dots,c_{\min(m,N)}) \text{ is unsatisfiable}\big\}.
--   $$
--   Thus $\operatorname{stop}(l)$ is the length of the shortest unsatisfiable initial segment of $l$, and $\operatorname{stop}(l)=N+1$ if $l$ is satisfiable; always $1\le\operatorname{stop}(l)\le N+1$.
--   3. **Harmless clause.** A clause $c$ is harmless for $l$ if for every sublist $r$ of $l$ (a subsequence with the order preserved), the list $c$ followed by $r$ is satisfiable exactly when $r$ is satisfiable.
--
--   A clause having a variable that occurs in no clause of $l$ is harmless for $l$, since that variable can always be set to satisfy it. If $c$ is harmless for $l$ and is inserted into $l$ at position $i\in\{0,\dots,N\}$, so that $i$ clauses of $l$ precede it, then the stopping index increases by one exactly when $i<\operatorname{stop}(l)$ and is unchanged otherwise. Such bystander clauses therefore move the first unsatisfiability time by an amount that depends only on their random positions, which is the source of the linear lower bound on its variance for random $k$-SAT.
--
--   **Formalization Note** `listStop` is defined with `Nat.find`. Since `l.take m` is the whole list for $m>N$, the alternative $m=N+1$ in the definition matters only when $l$ is satisfiable. `Harmless` quantifies over `List.Sublist`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/BystanderStops.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/BystanderStops.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def listSAT {n k : ℕ} (l : List (Clause n k)) : Prop :=
  ∃ a : Assignment n, ∀ c ∈ l, Satisfies c a

def listStop {n k : ℕ} (l : List (Clause n k)) : ℕ :=
  Nat.find (show ∃ m : ℕ, m = l.length+1 ∨ ¬listSAT (l.take m) from ⟨_,Or.inl rfl⟩)

def Harmless {n k : ℕ} (c : Clause n k) (l : List (Clause n k)) : Prop :=
  ∀ r, r.Sublist l → (listSAT (c::r) ↔ listSAT r)

end RandomKSAT

end

end OAI


