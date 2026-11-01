-- Prove2me | Definitions.Def_SelfGuidedALP_IsOptimalValue
-- name    : SelfGuidedALP_IsOptimalValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:20.03951+00:00
-- url     : https://prove2.me/theorems/4253edea-c999-4faf-96a5-12ec755849ba
-- title:
--   The MDP value function $V^*$: continuous solution of the optimality equations
-- statement:
--   A function $V$ is the **MDP value function** $V^*$ when it is continuous on $\mathcal S$ and solves the optimality equations
--   $$
--   V(s)=\min_{a\in\mathcal A_s}\bigl\{c(s,a)+\gamma\,\mathbb E[V(s')\mid s,a]\bigr\}\qquad\text{for every }s\in\mathcal S,
--   $$
--   with the minimum attained.
--
--   This pins down $V^*$ without policies: all the mission's statements use $V^*$ only through these equations.
--
--   **Formalization Note** The paper defines $V^*:=\mathrm{PC}(\cdot,\pi^*)$ for an optimal stationary policy and uses it through these equations. Because $\gamma<1$, the Bellman operator is a sup-norm contraction, so the continuous solution is unique; under Assumption EC.1 it is the optimal value (Hernández-Lerma–Lasserre, Theorem 4.2.3). The expectation is automatically finite, since $V$ is continuous on the compact set that carries $P(\cdot\mid s,a)$.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Assumption 1, p.7, and p.8

import Mathlib
import Definitions.Def_SelfGuidedALP_MDP

open MeasureTheory

namespace SelfGuidedALP

/-- `V` is the MDP value function `V*`: it is continuous on `𝒮` and solves the optimality equations
`V(s) = min_{a ∈ 𝒜ₛ} {c(s,a) + γ E[V(s') | s,a]}` for every `s ∈ 𝒮`, the minimum being attained
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Assumption 1, p.7, and p.8).

**Formalization Note.** The paper defines `V* := PC(·,π*)` and uses it only through these equations.
Since `γ < 1`, the Bellman operator is a sup-norm contraction, so a function continuous on the
compact `𝒮` that solves the equations is unique; under Assumption EC.1 it is the optimal value
(Hernández-Lerma–Lasserre, Thm 4.2.3). The expectation is integrable automatically: `V` is continuous
on the compact set `𝒮`, which carries all of `P s a`. -/
def IsOptimalValue {d m : ℕ} (M : MDP d m) (V : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContinuousOn V M.S ∧
    ∀ s ∈ M.S, IsLeast ((fun a => M.c s a + M.γ * ∫ s', V s' ∂(M.P s a)) '' M.A s) (V s)

end SelfGuidedALP


