-- Prove2me | Definitions.Def_OAI_Probability_RandomSAT_Main
-- name    : OAI_Probability_RandomSAT_Main
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:47:45.17499+00:00
-- url     : https://prove2.me/theorems/5b0b00d0-9346-4565-b3b9-c35a56fe108b
-- title:
--   The limiting center: limit superior of the normalized centers
-- statement:
--   For a clause size $k$, the limiting center is
--   $$
--   \alpha_k=\limsup_{n\to\infty}c_k(n),
--   $$
--   where $c_k(n)$ is the normalized capped center: $1/n$ times the expected number of the first $2^{k+1}n$ uniformly random proper $k$-clauses on $n$ variables for which the corresponding prefix of the formula is still satisfiable.
--
--   For every $k\ge3$ the centers converge to $\alpha_k$, and $e^{-2}/16\le\alpha_k\le2^k+1$. The number $\alpha_k$ is the positive finite threshold in the main theorem: for every fixed real $c$ with $0\le c<\alpha_k$, a uniformly random formula of $\lfloor cn\rfloor$ proper $k$-clauses on $n$ variables is satisfiable with probability tending to $1$, and for every fixed $c>\alpha_k$ this probability tends to $0$. Nothing is asserted at $c=\alpha_k$.
--
--   **Formalization Note** `limitingCenter k` is `Filter.limsup (fun n => center n k) Filter.atTop` in $\mathbb{R}$. This is the genuine limit superior here because the centers are bounded (between $0$ and $2^{k+1}$); for an unbounded sequence Lean's real `limsup` would return a junk value.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Main.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Main.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FixedClauseThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
import Definitions.Def_OAI_Probability_RandomSAT_Interpolation
import Definitions.Def_OAI_Probability_RandomSAT_Transfer
import Definitions.Def_OAI_Probability_RandomSAT_CenterComparison
import Definitions.Def_OAI_Probability_RandomSAT_Convergence

namespace OAI

/-!
For every fixed clause size at least three, the proper-clause satisfiability
probability has a positive finite limiting threshold. No conclusion is asserted
at the critical density.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def limitingCenter (k : ℕ) : ℝ := Filter.limsup (fun n : ℕ => center n k) Filter.atTop

end

end FixedClauseThreshold

end OAI


