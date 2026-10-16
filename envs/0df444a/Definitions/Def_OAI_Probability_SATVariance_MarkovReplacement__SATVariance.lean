-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
-- name    : OAI_Probability_SATVariance_MarkovReplacement__SATVariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:24:52.286663+00:00
-- url     : https://prove2.me/theorems/4dba5773-028a-442a-9812-ba4b408a9ffa
-- title:
--   Uniform averages, the one-clause Markov operator, survival probabilities and expected lifetimes of solution sets
-- statement:
--   Assignments on $u$ Boolean variables are maps $[u]\to\{\mathrm T,\mathrm F\}$ with $[u]=\{0,\dots,u-1\}$. An $s$-clause is a set of $s$ distinct variables with a sign for each, satisfied by an assignment that agrees with at least one sign. Write $\mathcal C_{u,s}$ for the finite set of $s$-clauses on $u$ variables and $\mathrm{Sat}(c)$ for the set of assignments satisfying $c$. Throughout, $S$ is a finite set of assignments.
--
--   1. **Uniform average.** For a real function $f$ on a finite set $A$, $\operatorname{avg}_A f=\frac1{|A|}\sum_{x\in A}f(x)$.
--   2. **Residual set.** For a finite family $(c_i)_{i\in I}$ of clauses, $\operatorname{res}\big(S,(c_i)\big)=\{a\in S:\ a\text{ satisfies } c_i \text{ for every } i\in I\}$.
--   3. **One-clause operator.** For a real function $f$ on sets of assignments,
--   $$
--   (P_{u,s}f)(S)=\operatorname{avg}_{c\in\mathcal C_{u,s}} f\big(S\cap\mathrm{Sat}(c)\big).
--   $$
--   This is the transition operator of the Markov chain that adds one uniformly random $s$-clause and keeps the surviving assignments.
--   4. **Alive indicator and survival.** $\operatorname{alive}(S)=1$ if $S\ne\emptyset$ and $0$ otherwise, and $\operatorname{surv}_{u,s}(S,m)=\big(P_{u,s}^{\,m}\operatorname{alive}\big)(S)$. Equivalently, it is the average over all $m$-tuples of $s$-clauses of the indicator that the residual set is nonempty; for $s\le u$ it is the probability that some member of $S$ satisfies $m$ independent uniformly random $s$-clauses.
--   5. **Lifetime.**
--   $$
--   \operatorname{life}_{u,s}(S)=\sum_{m=0}^{\infty}\operatorname{surv}_{u,s}(S,m),
--   $$
--   the expected number of steps during which $S$ still has a surviving member, i.e. the expected time at which a stream of independent uniform $s$-clauses kills $S$.
--   6. **Lifetime exponent and constant.** For $k\in\mathbb N$,
--   $$
--   \beta_k=\frac{k}{k-1},\qquad C_k=4\,\big(2K_k\big)^{1/(k-1)},
--   $$
--   where $K_k=\big(2^k(k-1)\big)^{k-1}$ is the clause-replacement constant.
--
--   The operators $P_{u,s}$ for different clause lengths commute, and for lengths at most $u$ they fix constant functions; this lets single-clause replacements be telescoped into a comparison of $d$ random clauses of length $r$ with $dg$ random clauses of length $r+1$. The resulting lifetime-killing trade-off reads, for $2\le r$, $r+1\le u$ and $d\ge1$,
--   $$
--   \operatorname{life}_{u,r+1}(S)\;R_{u,r}(S,d)^{\beta_{r+1}}\le C_{r+1}\,d^{\beta_{r+1}},
--   $$
--   where $R_{u,r}(S,d)$ is the probability that $d$ independent uniform $r$-clauses leave no member of $S$ satisfying all of them. It bounds how long a solution set that short clauses would easily kill can survive under clauses of the next length, and is reused in the variance estimates for the first unsatisfiability time of random $k$-SAT.
--
--   **Formalization Note** `favg` divides by the cardinality, so it returns $0$ on an empty type (for example $s$-clauses when $s>u$). `lifetime` is a `tsum`, which Lean sets to $0$ for a non-summable series; the series is summable when $s\le u$. In `lifetimeBeta` and `lifetimeC`, $k-1$ is natural-number subtraction and the reciprocal is taken in $\mathbb R$ with $1/0=0$, so $\beta_0=\beta_1=0$ and $C_1=4$; the power in $C_k$ is the real power.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/MarkovReplacement.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/MarkovReplacement.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SATVariance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def favg.{u_1} {α : Type u_1} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

def residual.{u_1} {u s : ℕ} {ι : Type u_1} [Fintype ι]
    (S : Finset (Assignment u)) (cs : ι → Clause u s) : Finset (Assignment u) :=
  S.filter fun a => ∀ i, Satisfies (cs i) a

def clauseStep (u s : ℕ) (f : Finset (Assignment u) → ℝ)
    (S : Finset (Assignment u)) : ℝ :=
  favg fun c : Clause u s => f (S.filter (Satisfies c))

def alive (u : ℕ) (S : Finset (Assignment u)) : ℝ := if S.Nonempty then 1 else 0

def survival (u s : ℕ) (S : Finset (Assignment u)) (m : ℕ) : ℝ :=
  (clauseStep u s)^[m] (alive u) S

def lifetime (u s : ℕ) (S : Finset (Assignment u)) : ℝ := ∑' m, survival u s S m

def lifetimeBeta (k : ℕ) : ℝ := (k : ℝ) / ((k-1 : ℕ) : ℝ)

def lifetimeC (k : ℕ) : ℝ := 4 * (2*replacementK k)^(((k-1 : ℕ) : ℝ)⁻¹)

end RandomKSAT

end

end OAI


