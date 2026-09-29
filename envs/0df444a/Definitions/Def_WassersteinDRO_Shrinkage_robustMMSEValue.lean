-- Prove2me | Definitions.Def_WassersteinDRO_Shrinkage_robustMMSEValue
-- name    : WassersteinDRO_Shrinkage_robustMMSEValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:49:37.519529+00:00
-- url     : https://prove2.me/theorems/fee19377-0049-49c3-92e7-cee1b1108071
-- title:
--   Optimal value of the distributionally robust MMSE estimation problem
-- statement:
--   The optimal value of problem (35) is $\inf_{\psi\in\Psi} \sup_{Q\in B_{\varepsilon,2}(\hat
--   P_N)} E_Q[\|x-\psi(y)\|_2^2]$, $\Psi$ the family of measurable estimators, valued in the
--   extended reals and restricted to distributions under which the loss is integrable.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, eq. (35), p. 29

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_ambiguitySet
import Definitions.Def_WassersteinDRO_Shrinkage_nominalRisk
import Definitions.Def_WassersteinDRO_Shrinkage_estimationLoss

open MeasureTheory

namespace WassersteinDRO.Shrinkage

/-- The optimal value of the distributionally robust MMSE estimation problem (35), Kuhn et
al. 2019, p. 29: `inf_{ψ∈Ψ} sup_{Q∈B_{ε,2}(P̂N)} E_Q[‖x-ψ(y)‖₂²]`, `Ψ` the family of measurable
estimators. The `Measurable ψ` guard on the outer infimum's binder is the paper's own `Ψ`: p. 29
defines "an estimator" as *a measurable function* `ψ(y)` before denoting by `Ψ` "the family of
all possible [measurable] estimators" — an earlier draft's binder ranged over every function of
the type with no measurability constraint, an infimum over a strictly larger candidate set that
can only be `≤` the paper's own value and was flagged by moderation as a silently dropped
hypothesis (fixed this revision). Valued in `EReal`, guarded by `Integrable`, matching the
series' worst-case-risk convention. -/
noncomputable def robustMMSEValue {mx my : ℕ} (ε : ℝ) (PN : Measure (EuclideanSpace ℝ (Fin mx ⊕ Fin my))) :
    EReal :=
  ⨅ (ψ : EuclideanSpace ℝ (Fin my) → EuclideanSpace ℝ (Fin mx)) (_ : Measurable ψ),
    ⨆ (Q : Measure (EuclideanSpace ℝ (Fin mx ⊕ Fin my)))
      (_ : Q ∈ ambiguitySet ε 2 Set.univ PN) (_ : Integrable (estimationLoss ψ) Q),
      (nominalRisk Q (estimationLoss ψ) : EReal)

end WassersteinDRO.Shrinkage


