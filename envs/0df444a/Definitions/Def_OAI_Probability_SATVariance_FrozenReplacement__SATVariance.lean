-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
-- name    : OAI_Probability_SATVariance_FrozenReplacement__SATVariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:22:05.572547+00:00
-- url     : https://prove2.me/theorems/063dc588-7a31-43f7-adbf-64779d9a8fa4
-- title:
--   Kill ratio $\binom{b}{s}/(2^s\binom{u}{s})$ of a solution set with $b$ frozen variables
-- statement:
--   For natural numbers $u,b,s$ the *kill ratio* is the real number
--   $$
--   \kappa(u,b,s)=\frac{\binom bs}{2^s\binom us}.
--   $$
--
--   Its meaning is the following. Let $S$ be a nonempty set of assignments $[u]\to\{\mathrm T,\mathrm F\}$ on $u$ Boolean variables, $[u]=\{0,\dots,u-1\}$, and suppose that exactly $b$ variables are *frozen* in $S$, i.e. all members of $S$ take the same value there. An $s$-clause on $u$ variables is a set of $s$ distinct variables with a prescribed sign for each; an assignment satisfies it if it agrees with at least one of these signs, and the clause *kills* $S$ if no member of $S$ satisfies it. The killing clauses are exactly those whose $s$ variables are all frozen and whose signs all oppose the common values, so there are $\binom bs$ of them among the $2^s\binom us$ clauses. Hence, for $s\le u$, $\kappa(u,b,s)$ is the probability that a uniformly random $s$-clause kills $S$. For example $\kappa(u,b,0)=1$, and $\kappa(u,b,s)=0$ whenever $s>b$.
--
--   The kill ratio is the one-clause quantity in the comparison between clauses of consecutive lengths. Estimates for it, such as $\kappa(u,b,s)\le\big(b/(2u)\big)^s$ for $b,s\le u$ and the frozen-power inequality $\kappa(u,b,r)^{(r+1)/r}/(r+1)\le\kappa(u,b,r+1)$ for $1\le r$ and $r+1\le b\le u$, are what allow a random clause of length $r$ to be traded for a block of random clauses of length $r+1$ in the study of random $k$-SAT.
--
--   **Formalization Note** `killRatio u b s` uses real division, so by Lean's convention it equals $0$ when $s>u$, where the denominator $\binom us$ vanishes.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FrozenReplacement.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FrozenReplacement.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SATVariance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def killRatio (u b s : ℕ) : ℝ := (b.choose s : ℝ) / (2 ^ s * u.choose s)

end RandomKSAT

end

end OAI


