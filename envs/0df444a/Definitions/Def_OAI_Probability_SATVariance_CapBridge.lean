-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_CapBridge
-- name    : OAI_Probability_SATVariance_CapBridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:41:47.717815+00:00
-- url     : https://prove2.me/theorems/26a80883-af48-432f-9f09-10fd31f545bc
-- title:
--   The cap-bridge constant $q^{-2}\sum_j j^2 q^j$ with $q=1-2^{-k}$
-- statement:
--   For $k\in\mathbb N$ put $q=1-2^{-k}$, the probability that a uniformly random $k$-clause is satisfied by a fixed assignment (a $k$-clause on $n\ge k$ Boolean variables being a set of $k$ distinct variables with a sign for each, satisfied when the assignment agrees with at least one sign). The *cap-bridge constant* is
--   $$
--   C^{\mathrm{br}}_k=\frac{1}{q^{2}}\sum_{j=0}^{\infty}j^2q^j .
--   $$
--   For $k\ge1$ one has $\tfrac12\le q<1$, the series converges to $q(1+q)/(1-q)^3$, and hence $C^{\mathrm{br}}_k=(1+q)/\big(q(1-q)^3\big)$ depends only on $k$.
--
--   Let $H$ be the first time $m$ at which the first $m$ clauses of a stream of independent uniformly random $k$-clauses on $n$ variables are not simultaneously satisfiable (almost surely finite), let $T_B=\min\big(H,\lfloor Bn\rfloor\big)$ be its truncation, and let $U(k)=\log2/\big(-\log(1-2^{-k})\big)$. For $1\le k\le n$ and $B\ge U(k)$ the mean squared truncation error satisfies $\mathbb E\big[(H-T_B)^2\big]\le C^{\mathrm{br}}_k$, uniformly in $n$. Consequently $\operatorname{Var}H\le 2\operatorname{Var}T_B+2C^{\mathrm{br}}_k$ and $\operatorname{Var}T_B\le2\operatorname{Var}H+2C^{\mathrm{br}}_k$, so variance bounds transfer between the uncapped and the capped failure times.
--
--   **Formalization Note** The Lean definition `bridgeC k` uses the reciprocal of $1-2^{-k}$ in $\mathbb R$, with $0^{-1}=0$, and the unconditional sum `tsum`, which would be $0$ for a non-summable series. The series is summable for every $k$; for $k=0$ one has $q=0$ and the constant is $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/CapBridge.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/CapBridge.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def bridgeC (k : ℕ) : ℝ := (1-((2 : ℝ)^k)⁻¹)⁻¹^2 *
  ∑' j : ℕ, (j : ℝ)^2*(1-((2 : ℝ)^k)⁻¹)^j

end RandomKSAT

end

end OAI


