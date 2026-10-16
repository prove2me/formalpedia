-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_BlockKilling
-- name    : OAI_Probability_SATVariance_BlockKilling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:23:18.341626+00:00
-- url     : https://prove2.me/theorems/040093b8-f4ff-47e3-9de7-2458d76f12f8
-- title:
--   Block-killing probability of a set of assignments and the clause-replacement constant
-- statement:
--   Fix $u,s\in\mathbb N$ and write $[u]=\{0,\dots,u-1\}$. Assignments on $u$ Boolean variables are maps $[u]\to\{\mathrm T,\mathrm F\}$. An $s$-clause is a set of $s$ distinct variables with a sign for each; an assignment satisfies it if it agrees with at least one of these signs. A *clause stream* is an infinite sequence $\omega=(\omega_0,\omega_1,\dots)$ of $s$-clauses, and $\mathbb P_{u,s}$ denotes the product law under which the $\omega_i$ are independent and uniform over all $\binom us2^s$ clauses.
--
--   1. **Joint satisfiability within a set.** For a finite set $S$ of assignments and $g\in\mathbb N$, $\mathrm{SAT}_S(\omega,g)$ holds when some $a\in S$ satisfies each of the first $g$ clauses $\omega_0,\dots,\omega_{g-1}$.
--   2. **Block-killing probability.**
--   $$
--   R_{u,s}(S,g)=\mathbb P_{u,s}\big[\text{no } a\in S \text{ satisfies all of } \omega_0,\dots,\omega_{g-1}\big],
--   $$
--   the probability that a block of $g$ independent uniform $s$-clauses eliminates every assignment in $S$. When $s\le u$ it equals $1$ for $S=\emptyset$, and for nonempty $S$ and $g=1$ it is the kill ratio $\binom bs/(2^s\binom us)$, where $b$ is the number of variables on which all members of $S$ agree.
--   3. **Replacement constant.** For $k\in\mathbb N$,
--   $$
--   K_k=\big(2^k\,(k-1)\big)^{k-1}.
--   $$
--
--   The constant $K_k$ measures the cost of replacing one random clause of length $r=k-1$ by a block of $g$ random clauses of length $k$: for $2\le r$, $r+1\le u$ and $g\ge1$ one has $R_{u,r}(S,1)-K_{r+1}/g^r\le R_{u,r+1}(S,g)$ for every set $S$. Iterating this comparison along a sequence of clauses is the basis of the lifetime bounds for solution sets used in the variance analysis of the first unsatisfiability time of random $k$-SAT.
--
--   **Formalization Note** `blockKill u s S g` is the real number obtained from the stream-law measure of the event that `SetSAT S ω g` fails. The stream law is a probability measure when $s\le u$, which the lemmas about `blockKill` assume. In `replacementK` the exponent and the factor $k-1$ use natural-number subtraction, so $K_0=K_1=1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/BlockKilling.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/BlockKilling.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SATVariance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def SetSAT {u s : ℕ} (S : Finset (Assignment u)) (ω : Stream u s) (g : ℕ) : Prop :=
  ∃ a ∈ S, ∀ i < g, Satisfies (ω i) a

def blockKill (u s : ℕ) (S : Finset (Assignment u)) (g : ℕ) : ℝ :=
  (streamLaw u s {ω | ¬ SetSAT S ω g}).toReal

def replacementK (k : ℕ) : ℝ := ((2 : ℝ)^k * ((k-1 : ℕ) : ℝ))^(k-1)

end RandomKSAT

end

end OAI


