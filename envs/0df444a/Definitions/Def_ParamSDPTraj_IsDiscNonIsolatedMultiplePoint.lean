-- Prove2me | Definitions.Def_ParamSDPTraj_IsDiscNonIsolatedMultiplePoint
-- name    : ParamSDPTraj_IsDiscNonIsolatedMultiplePoint
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:09.835385+00:00
-- url     : https://prove2.me/theorems/76cd2c58-b6a1-48aa-90df-498bb559fa45
-- title:
--   Discontinuous non-isolated multiple point
-- statement:
--   A pair $(X^*,t^*)$ is a **discontinuous non-isolated multiple point** of $F$ if $X^*\in F(t^*)$ and there is $\varepsilon>0$ such that:
--
--   1. $F$ is continuous at every $t\in(t^*-\varepsilon,t^*)\cup(t^*,t^*+\varepsilon)$;
--   2. $F$ is single-valued at every $t\in(t^*-\varepsilon,t^*)$;
--   3. $F$ is multi-valued at every $t\in[t^*,t^*+\varepsilon)$.
--
--   **Formalization Note** The interval lies in $T$.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Definition 3.8, p.13

import Mathlib
import Definitions.Def_ParamSDPTraj_SingleValuedAt
import Definitions.Def_ParamSDPTraj_PKContinuousAt
import Definitions.Def_ParamSDPTraj_MultiValuedAt

namespace ParamSDPTraj

/-- **Discontinuous non-isolated multiple point.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Definition 3.8, p.13: "At a discontinuous non-isolated multiple point (X∗, t∗), X∗ ∈ P∗(t∗)
and there exists ε > 0 such that • P∗(t) is continuous at any t ∈ (t∗ − ε, t∗) ∪ (t∗, t∗ + ε),
• P∗(t) is single-valued for every t ∈ (t∗ − ε, t∗), • P∗(t) is multi-valued for every
t ∈ [t∗, t∗ + ε)."

**Formalization Note** The interval lies in `T`, as in `IsRegularPoint`. -/
def IsDiscNonIsolatedMultiplePoint {n : ℕ} (T : Set ℝ) (F : ℝ → Set (Matrix (Fin n) (Fin n) ℝ)) (X : Matrix (Fin n) (Fin n) ℝ)
    (tstar : ℝ) : Prop :=
  X ∈ F tstar ∧ ∃ ε > 0, Set.Ioo (tstar - ε) (tstar + ε) ⊆ T ∧
    (∀ t ∈ Set.Ioo (tstar - ε) tstar ∪ Set.Ioo tstar (tstar + ε), PKContinuousAt T F t) ∧
    (∀ t ∈ Set.Ioo (tstar - ε) tstar, SingleValuedAt F t) ∧
    (∀ t ∈ Set.Ico tstar (tstar + ε), MultiValuedAt F t)

end ParamSDPTraj


