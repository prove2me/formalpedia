-- Prove2me | Definitions.Def_OAI_Probability_RandomSAT_Convergence
-- name    : OAI_Probability_RandomSAT_Convergence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:46:06.524905+00:00
-- url     : https://prove2.me/theorems/febb269a-95c9-4517-b98f-f786685fcd1e
-- title:
--   The balanced-block constant $3^\beta/((3/2)^\beta-1)$
-- statement:
--   For a real number $\beta$ the module defines
--   $$
--   K(\beta)=\frac{3^\beta}{(3/2)^\beta-1}.
--   $$
--   For $\beta>0$ the denominator is positive, so $K(\beta)$ is a positive finite constant.
--
--   $K(\beta)$ is the constant of a geometric potential over balanced block decompositions. Let $A\ge0$ and $\beta>0$, and suppose a real sequence $u$ satisfies the near-superadditive comparison $\min(u_r,u_t)-A\min(r,t)^{-\beta}\le u_{r+t}$ for all $r,t\ge N$, and $u_s-As^{-\beta}\le u_{s+1}$ for some $s\ge N$ with $s\ge1$. Splitting an index into $q$ nearly equal blocks then gives
--   $$
--   u_{qs+r}\ge u_s-A\,s^{-\beta}-A\,K(\beta)\,s^{-\beta}\big(1-q^{-\beta}\big)\qquad(q\ge1,\ 0\le r\le q),
--   $$
--   for every number $q$ of blocks, including numbers that are not powers of two. For bounded sequences satisfying such comparisons for all large $s$, this yields convergence to the limit superior, which is how the normalized centers are shown to converge.
--
--   **Formalization Note** The powers are real powers. For $\beta=0$ the denominator vanishes and Lean's convention gives $K(0)=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Convergence.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Convergence.lean by skeleton subtraction
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

namespace OAI

/-!
A balanced-block geometric potential proves convergence from boundedness and
summable-min comparisons, including block counts that are not powers of two.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def balanceConstant (β : ℝ) : ℝ := (3 : ℝ)^β / ((3 / 2 : ℝ)^β - 1)

end

end FixedClauseThreshold

end OAI


