-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_HiddenTests
-- name    : OAI_Probability_SATVariance_HiddenTests
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:32:58.880614+00:00
-- url     : https://prove2.me/theorems/21dd7add-8534-4ca1-b170-08a1bbe26fe0
-- title:
--   Family-killing indicator and the hidden test positions of a root assignment
-- statement:
--   Assignments on $u$ Boolean variables are maps $[u]\to\{\mathrm T,\mathrm F\}$, $[u]=\{0,\dots,u-1\}$. An $s$-clause on $u$ variables is a set of $s$ distinct variables with a sign for each, satisfied by an assignment that agrees with at least one sign.
--
--   1. **Family-killing indicator.** For a finite set $S$ of assignments and a finite family $(c_i)_{i\in I}$ of $s$-clauses,
--   $$
--   \kappa_S\big((c_i)_{i\in I}\big)=\begin{cases}0&\text{if some } b\in S \text{ satisfies every } c_i,\\1&\text{otherwise.}\end{cases}
--   $$
--   2. **Test indices.** Let $a:[k]\to\{\mathrm T,\mathrm F\}$ be a root assignment and $p_0,\dots,p_{M-1}$ root data, where each $p_i=(t_i,c_i)$ consists of a root type $t_i:[k]\to\{\bot,\mathrm T,\mathrm F\}$ and a residual clause $c_i$ on $u$ variables. For $m\in\mathbb N$ and a root position $j\in[k]$,
--   $$
--   \operatorname{Test}_m(j)=\big\{\,i\in\{0,\dots,M-1\}:\ i<m,\ \ t_i \text{ has exactly one entry different from } \bot,\ \text{and } t_i(j)=a(j)\,\big\}.
--   $$
--
--   For $s\le u$, averaging $\kappa_S$ over $d$ independent uniformly random $s$-clauses gives exactly the block-killing probability, the probability that $d$ random clauses leave no member of $S$ satisfying all of them. In the deletion analysis for random $k$-SAT, if the root assignment $a$ stays forced up to time $m$ (every surviving pair of root and residual assignments has root part $a$), then for every available position $j$ (one that is not the unique root literal satisfied by $a$ in any datum with at least two root entries) the fresh hidden $(k-1)$-clauses that replace the residual parts of the tests in $\operatorname{Test}_m(j)$ must kill the current fibre of residual assignments. Since the hidden clauses at different positions are independent, the average of the forced reward over the hidden clauses is at most $\mathbf 1[F\ne\emptyset]\,R_{u,k-1}(F,d)^{|J|}$, where $F$ is the current fibre, $J$ is a set of available positions, $d$ bounds the number of tests at each position, and $R_{u,k-1}(F,d)$ is the probability that $d$ independent uniform $(k-1)$-clauses kill $F$.
--
--   **Formalization Note** `familyKill` is real-valued, takes the values $0$ and $1$, and accepts any finite index type. `testIndices` returns a `Finset (Fin M)`; the condition that $t_i$ has exactly one entry different from $\bot$ is `rootSize t = 1`, and together with $t_i(j)=a(j)$ it is the predicate `TestAt`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/HiddenTests.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/HiddenTests.lean by skeleton subtraction
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

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def familyKill.{u_1} {u s : ℕ} {ι : Type u_1} [Fintype ι]
    (S : Finset (Assignment u)) (cs : ι → Clause u s) : ℝ :=
  if ∃ b ∈ S, ∀ i, Satisfies (cs i) b then 0 else 1

def testIndices {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (m : ℕ) (j : Fin k) : Finset (Fin M) :=
  Finset.univ.filter fun i => i.val < m ∧ TestAt a (env i) j

end RandomKSAT

end

end OAI


