-- Prove2me | Definitions.Def_OpRiskInspection_Hybrid_Strategy
-- name    : OpRiskInspection_Hybrid_Strategy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:17.985435+00:00
-- url     : https://prove2.me/theorems/9111fbcb-e121-48a2-b139-619d3981d2f3
-- title:
--   §4.2, p. 14 — an optimal inspection strategy $S^*_I=(v^*_I,P^*_I,w^*_I)$ with its best response
-- statement:
--   Fix a model, an inspection cost $K$ and a family of inspection laws $v\mapsto F_v$ (one inspection policy $I$). A triple $(v,P,w)$ together with an effort path $a$ is an **optimal inspection strategy attained with best response $a$** if
--
--   1. $v>0$, $P\ge0$ and $w\ge0$;
--   2. $a$ is an optimal effort of the agent for $(F_v,P)$;
--   3. the agent participates: $\pi(a;v,P,w)\ge\bar\pi$;
--   4. the principal's payoff is maximal among achievable payoffs:
--   $$
--   x\le \Pi(v,P,w)\quad\text{for every achievable payoff }x\text{ of policy }I .
--   $$
--
--   This is the meaning of the paper's "the optimal strategy under policy $I$ is $S^*_I=(v^*_I,P^*_I,w^*_I)$", used in Lemma EC.3 and Proposition 1.
--
--   **Formalization Note** The best response is carried as a witness because the payoff (3) depends on it; any two optimal efforts agree almost everywhere where they matter and give the same payoff.
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), p. 14, §4.2, first paragraph (definition of S*_I); (4)–(5), p. 10

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_Setting

namespace OpRiskInspection.Hybrid

/-- `(v, P, w)` is an optimal inspection strategy under the family of inspection laws `law`,
attained with the agent's best response `a`: the strategy is feasible for (4)–(5), `a` is an
optimal effort for the agent, the agent participates, and the resulting principal payoff (3)
is at least every achievable payoff. -/
def OptimalStrategyWith (p : OpRiskInspection.RandomVsPeriodic.Params) (K : ℝ) (law : ℝ → MeasureTheory.Measure ℝ)
    (v P w : ℝ) (a : OpRiskInspection.RandomVsPeriodic.Effort) : Prop :=
  0 < v ∧ 0 ≤ P ∧ 0 ≤ w ∧
    OpRiskInspection.RandomVsPeriodic.AgentOptimal p (law v) P a ∧
    p.pibar ≤ OpRiskInspection.RandomVsPeriodic.agentPayoff p (law v) a P w ∧
    ∀ x, OpRiskInspection.RandomVsPeriodic.Achievable p K law x → x ≤ OpRiskInspection.RandomVsPeriodic.principalPayoff p K v (law v) a P w

end OpRiskInspection.Hybrid


