-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_OmissionCompression
-- name    : OAI_Probability_SATVariance_OmissionCompression
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:39:00.081571+00:00
-- url     : https://prove2.me/theorems/c37be076-61f3-48af-a899-1c46b8edaf95
-- title:
--   Joining root and residual assignments, and satisfiability of a clause word with one clause omitted
-- statement:
--   Assignments on $m$ Boolean variables are maps $[m]\to\{\mathrm T,\mathrm F\}$, $[m]=\{0,\dots,m-1\}$. A $k$-clause on $n$ variables is a set of $k$ distinct variables in $[n]$ with a sign for each; an assignment satisfies it if it agrees with at least one of these signs.
--
--   1. **Joined assignment.** Let $e:[k]\sqcup[u]\to[n]$ be a bijection, splitting the variables into root variables $e(j)$, $j\in[k]$, and residual variables $e(\bar\jmath)$, $j\in[u]$, where $\bar\jmath$ is the copy of $j$ in the second summand. For a root assignment $a:[k]\to\{\mathrm T,\mathrm F\}$ and a residual assignment $b:[u]\to\{\mathrm T,\mathrm F\}$, the joined assignment $a\oplus_e b$ on $[n]$ is given by
--   $$
--   (a\oplus_e b)\big(e(j)\big)=a(j),\qquad (a\oplus_e b)\big(e(\bar\jmath)\big)=b(j).
--   $$
--   Every assignment on $[n]$ arises in this way from exactly one pair $(a,b)$.
--   2. **Satisfiability with one clause omitted.** For a word $(c_0,\dots,c_{L-1})$ of $k$-clauses, a position $i<L$ and $m\in\mathbb N$, $\mathrm{SAT}_{-i}(m)$ holds when some assignment satisfies every $c_j$ with $j<m$ and $j\ne i$.
--
--   The joined assignment translates satisfaction of split clauses: the clause obtained by merging a root pattern $t$ on the root variables with a residual clause $c'$ on the residual variables is satisfied by $a\oplus_e b$ exactly when $a$ satisfies one of the root literals of $t$ or $b$ satisfies $c'$. Every clause $c$ admits a split $e$, with the support of $c$ as root variables, and a root assignment $a$ such that $a'\oplus_e b$ falsifies $c$ if and only if $a'=a$. With this presentation, the increase of the truncated failure time caused by omitting the clause $c$ from a clause word is bounded by the forced-reward sum of the pair evolution driven by the remaining clauses, which is the central reduction in the variance upper bound for the first unsatisfiability time.
--
--   **Formalization Note** `joinedAssignment e (a, b)` evaluates `Sum.elim a b` at `e.symm v`. `omittedSAT` is a reducible abbreviation for the predicate inside `omittedTime`, the count of $m<L$ for which $\mathrm{SAT}_{-i}(m)$ holds.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/OmissionCompression.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/OmissionCompression.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def joinedAssignment {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (x : Assignment k × Assignment u) : Assignment n :=
  fun v => Sum.elim x.1 x.2 (e.symm v)

abbrev omittedSAT {n k L : ℕ} (i : Fin L) (cs : Fin L → Clause n k) (m : ℕ) : Prop :=
  ∃ a : Assignment n, ∀ j : Fin L, j.val < m → j ≠ i → Satisfies (cs j) a

end RandomKSAT

end

end OAI


