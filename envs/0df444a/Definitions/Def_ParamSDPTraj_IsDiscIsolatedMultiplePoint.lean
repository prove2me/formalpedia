-- Prove2me | Definitions.Def_ParamSDPTraj_IsDiscIsolatedMultiplePoint
-- name    : ParamSDPTraj_IsDiscIsolatedMultiplePoint
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:14:51.131815+00:00
-- url     : https://prove2.me/theorems/af1cac1d-bd22-46e8-8279-9a2326993233
-- title:
--   Discontinuous isolated multiple point
-- statement:
--   A pair $(X^*,t^*)$ is a **discontinuous isolated multiple point** of $F$ if $X^*\in F(t^*)$ and there is $\varepsilon>0$ such that:
--
--   1. $F$ is single-valued and continuous at every $t\in(t^*-\varepsilon,t^*)\cup(t^*,t^*+\varepsilon)$;
--   2. $F$ is multi-valued at $t^*$.
--
--   **Formalization Note** The interval lies in $T$.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Definition 3.7, p.13

import Mathlib
import Definitions.Def_ParamSDPTraj_SingleValuedAt
import Definitions.Def_ParamSDPTraj_PKContinuousAt
import Definitions.Def_ParamSDPTraj_MultiValuedAt

namespace ParamSDPTraj

/-- **Discontinuous isolated multiple point.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Definition 3.7, p.13: "At a discontinuous isolated multiple point (X∗, t∗), X∗ ∈ P∗(t∗) and
there exists ε > 0 such that • P∗(t) is single-valued and continuous for every
t ∈ (t∗ − ε, t∗) ∪ (t∗, t∗ + ε), • P∗(t) is multi-valued at t∗."

**Formalization Note** The interval lies in `T`, as in `IsRegularPoint`. -/
def IsDiscIsolatedMultiplePoint {n : ℕ} (T : Set ℝ) (F : ℝ → Set (Matrix (Fin n) (Fin n) ℝ)) (X : Matrix (Fin n) (Fin n) ℝ) (tstar : ℝ) :
    Prop :=
  X ∈ F tstar ∧ ∃ ε > 0, Set.Ioo (tstar - ε) (tstar + ε) ⊆ T ∧
    (∀ t ∈ Set.Ioo (tstar - ε) tstar ∪ Set.Ioo tstar (tstar + ε),
      SingleValuedAt F t ∧ PKContinuousAt T F t) ∧
    MultiValuedAt F tstar

end ParamSDPTraj


