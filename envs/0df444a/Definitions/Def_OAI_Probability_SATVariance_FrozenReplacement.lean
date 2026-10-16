-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
-- name    : OAI_Probability_SATVariance_FrozenReplacement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:13:47.151469+00:00
-- url     : https://prove2.me/theorems/831f908f-1630-46e6-88a9-ebff499fcd68
-- title:
--   Kill ratio $\binom bs/(2^s\binom us)$ of a random clause
-- statement:
--   For natural numbers $u,b,s$ the *kill ratio* is the real number
--   $$
--   \kappa(u,b,s)=\frac{\binom bs}{2^s\binom us}.
--   $$
--
--   Its meaning comes from random clauses. Consider assignments $a:[u]\to\{\mathrm T,\mathrm F\}$ of the variables $[u]=\{0,\dots,u-1\}$, and clauses of width $s$, i.e. pairs $(V,\beta)$ of a set $V\subseteq[u]$ with $|V|=s$ and signs $\beta:V\to\{\mathrm T,\mathrm F\}$, satisfied by $a$ when $a(v)=\beta(v)$ for some $v\in V$; there are $\binom us2^s$ of them. If $S$ is a nonempty set of assignments whose members all agree on exactly $b$ variables (its frozen variables), then exactly $\binom bs$ clauses are violated by every member of $S$, namely those whose $s$ variables are all frozen and whose signs oppose the common values. Hence $\kappa(u,b,s)$ is the probability that one uniformly random clause of width $s$ kills $S$. For example $\kappa(u,b,0)=1$, and $\kappa(u,b,s)=0$ when $s>b$.
--
--   **Formalization Note** `killRatio u b s` uses real division, so by Lean's convention it equals $0$ when $s>u$ (then $\binom us=0$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FrozenReplacement.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FrozenReplacement.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SATSharpness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def killRatio (u b s : ℕ) : ℝ := (b.choose s : ℝ) / (2 ^ s * u.choose s)

end RandomKSAT

end

end OAI


