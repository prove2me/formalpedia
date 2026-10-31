-- Prove2me | Definitions.Def_ParamSDPTraj_IsContinuousBifurcationPoint
-- name    : ParamSDPTraj_IsContinuousBifurcationPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:14:57.555983+00:00
-- url     : https://prove2.me/theorems/6cdf6174-74bc-469f-9c4d-235571616209
-- title:
--   Continuous bifurcation point
-- statement:
--   A pair $(X^*,t^*)$ is a **continuous bifurcation point** of $F$ if $F(t^*)=\{X^*\}$ and there is $\varepsilon>0$ such that:
--
--   1. $F$ is continuous at every $t\in(t^*-\varepsilon,t^*+\varepsilon)$;
--   2. $F$ is single-valued at every $t\in(t^*-\varepsilon,t^*]$;
--   3. $F$ is multi-valued at every $t\in(t^*,t^*+\varepsilon)$.
--
--   **Formalization Note** The definition is the three bullets. The later sentence on p.14 about two distinct continuous curves is a claimed consequence and is not part of it. The interval lies in $T$.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Definition 3.10, p.14

import Mathlib
import Definitions.Def_ParamSDPTraj_SingleValuedAt
import Definitions.Def_ParamSDPTraj_PKContinuousAt
import Definitions.Def_ParamSDPTraj_MultiValuedAt

namespace ParamSDPTraj

/-- **Continuous bifurcation point.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Definition 3.10, p.14: "At a continuous bifurcation point (X∗, t∗), P∗(t∗) = {X∗} and there
exists ε > 0 such that • P∗(t) is continuous at any t ∈ (t∗ − ε, t∗ + ε), • P∗(t) is single-valued
for every t ∈ (t∗ − ε, t∗], • P∗(t) is multi-valued for every t ∈ (t∗, t∗ + ε)."

**Formalization Note** The three bullets. The sentence that follows them on p.14 ("In particular,
there exist at least two distinct continuous curves …") is a claimed consequence, not part of
the definition. The interval lies in `T`, as in `IsRegularPoint`. -/
def IsContinuousBifurcationPoint {n : ℕ} (T : Set ℝ) (F : ℝ → Set (Matrix (Fin n) (Fin n) ℝ)) (X : Matrix (Fin n) (Fin n) ℝ)
    (tstar : ℝ) : Prop :=
  F tstar = {X} ∧ ∃ ε > 0, Set.Ioo (tstar - ε) (tstar + ε) ⊆ T ∧
    (∀ t ∈ Set.Ioo (tstar - ε) (tstar + ε), PKContinuousAt T F t) ∧
    (∀ t ∈ Set.Ioc (tstar - ε) tstar, SingleValuedAt F t) ∧
    (∀ t ∈ Set.Ioo tstar (tstar + ε), MultiValuedAt F t)

end ParamSDPTraj


