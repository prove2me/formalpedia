-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement
-- name    : OAI_Probability_SATVariance_MarkovReplacement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:14:29.371575+00:00
-- url     : https://prove2.me/theorems/4a870c80-5625-40dc-bd1d-b8fe8cc312d8
-- title:
--   Residual solution set after a family of clauses
-- statement:
--   Let $u,s\in\mathbb N$. An assignment is a map $a:[u]\to\{\mathrm T,\mathrm F\}$ on the variables $[u]=\{0,\dots,u-1\}$, and a clause of width $s$ is a pair $c=(V,\beta)$ of an $s$-element set $V\subseteq[u]$ and signs $\beta:V\to\{\mathrm T,\mathrm F\}$; the assignment $a$ satisfies $c$ if $a(v)=\beta(v)$ for some $v\in V$. Given a finite set $S$ of assignments and a family $\mathbf c=(c_i)_{i\in I}$ of width-$s$ clauses indexed by a finite set $I$, the *residual* of $S$ under $\mathbf c$ is
--   $$
--   S\langle\mathbf c\rangle=\{a\in S : a \text{ satisfies } c_i \text{ for every } i\in I\}.
--   $$
--
--   It is the part of the candidate solution set $S$ that survives the formula consisting of the clauses $c_i$. In particular $S\langle\mathbf c\rangle\neq\emptyset$ exactly when some member of $S$ satisfies every clause of the family, and adding clauses one at a time corresponds to filtering $S$ successively. This is what allows the step-by-step clause-filtering process on solution sets to be rewritten as a single average over tuples of clauses.
--
--   **Formalization Note** `residual S cs` is the filter of the `Finset` $S$ by the predicate that every clause `cs i` is satisfied; the index type is any type with a `Fintype` instance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/MarkovReplacement.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/MarkovReplacement.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SATSharpness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def residual.{u_1} {u s : ℕ} {ι : Type u_1} [Fintype ι]
    (S : Finset (Assignment u)) (cs : ι → Clause u s) : Finset (Assignment u) :=
  S.filter fun a => ∀ i, Satisfies (cs i) a

end RandomKSAT

end

end OAI


