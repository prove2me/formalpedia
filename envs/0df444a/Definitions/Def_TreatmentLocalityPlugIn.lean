-- Prove2me | Definitions.Def_TreatmentLocalityPlugIn
-- name    : TreatmentLocalityPlugIn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-22T00:35:01.183141+00:00
-- url     : https://prove2.me/theorems/ed37e44d-dd2e-4f38-9a21-33047333d1be
-- title:
--   The model-based plug-in estimator and its Bellman system
-- statement:
--   **The model-based (plug-in) estimator, and the linear system it solves.** In the information-sharing scheme of arXiv:2407.19618 the estimator is a plug-in: from the statistics $v = (K^t, R^t, K^c, R^c)$ one forms, for each arm $a$, the visit counts $N^a_i = \sum_k K^a_{ik}$, the estimated transition matrix and mean rewards
--   $$\hat P^a_{ij} = K^a_{ij}/N^a_i, \qquad \hat r^a_i = R^a_i/N^a_i,$$
--   and the estimated value function $\hat V^a = (I - \gamma \hat P^a)^{-1} \hat r^a$, so that the ATE estimator is $\hat\Delta = \hat V^t - \hat V^c$ (`mbATE`).
--
--   Multiplying the plug-in Bellman equation $\hat V^a = \hat r^a + \gamma \hat P^a \hat V^a$ through by the visit counts clears both divisions: $\hat V^a$ is the solution of the linear system
--   $$\bigl(\mathrm{Diag}(N^a) - \gamma K^a\bigr)\, \hat V^a = R^a .$$
--   This is the form in which the estimator is actually computed (arXiv:2407.19618, eq. (EC.4)), and it is the useful one for analysis: the system matrix `mbSystem` depends **linearly** on the raw statistics, whereas $\hat P^a$ and $\hat r^a$ do not. Differentiating the estimator with respect to the statistics — the gradient the delta method needs — therefore reduces to differentiating a matrix inverse composed with a linear map.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, Section 2 (the Bellman equation V = (I - γP)⁻¹ r), Remark 1 and Proposition 5 (the model-based plug-in estimators P̂, r̂, V̂), and Appendix EC.6, eq. (EC.4) (the visit-count-weighted form Diag(N)·(V̂ - r̂ + γP̂V̂)).

import Definitions.Def_TreatmentLocalityEstimator

/-!
The model-based (plug-in) estimator of arXiv:2407.19618, Remark 1 and Proposition 5,
written so that its dependence on the raw statistics is transparent.

From the statistics `v = (K^t, R^t, K^c, R^c)` one forms, for each arm `a`, the visit
counts `N^a i = ∑ k, K^a i k`, the plug-in transition matrix `P̂^a i j = K^a i j / N^a i`,
the plug-in mean rewards `r̂^a i = R^a i / N^a i`, and the plug-in value function
`V̂^a = (I - γ P̂^a)⁻¹ r̂^a`, so that `mbATE = V̂^t - V̂^c`.

Multiplying the plug-in Bellman equation through by the visit counts removes both
divisions: `V̂^a` is the solution of the linear system `(Diag(N^a) - γ K^a) V̂^a = R^a`,
whose matrix `mbSystem` is a *linear* function of the statistics.  This is the form in
which the plug-in estimator is actually solved (arXiv:2407.19618, eq. (EC.4)).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- The plug-in transition matrix `P̂^a i j = K^a i j / N^a i` of arm `a`. -/
noncomputable def mbTrans (v : EstInput S) (a : Bool) : Matrix S S ℝ :=
  Matrix.of fun i j => (v a).1 i j / ∑ k, (v a).1 i k

/-- The plug-in mean-reward vector `r̂^a i = R^a i / N^a i` of arm `a`. -/
noncomputable def mbReward (v : EstInput S) (a : Bool) : S → ℝ :=
  fun i => (v a).2 i / ∑ k, (v a).1 i k

/-- The plug-in value function `V̂^a = (I - γ P̂^a)⁻¹ r̂^a` of arm `a`. -/
noncomputable def mbValue (M : Model S) (v : EstInput S) (a : Bool) : S → ℝ :=
  (((1 : Matrix S S ℝ) - M.γdisc • mbTrans v a)⁻¹).mulVec (mbReward v a)

/-- The plug-in Bellman system matrix `Diag(N^a) - γ K^a` of arm `a`: the plug-in value
function is the solution of `(Diag(N^a) - γ K^a) V̂^a = R^a`.  Unlike `mbTrans` and
`mbReward` it depends *linearly* on the statistics. -/
noncomputable def mbSystem (M : Model S) (v : EstInput S) (a : Bool) : Matrix S S ℝ :=
  Matrix.of fun i j => (if i = j then ∑ k, (v a).1 i k else 0) - M.γdisc * (v a).1 i j

lemma mbSystem_apply (M : Model S) (v : EstInput S) (a : Bool) (i j : S) :
    mbSystem M v a i j = (if i = j then ∑ k, (v a).1 i k else 0) - M.γdisc * (v a).1 i j := rfl

/-- The model-based ATE estimator is the difference of the two plug-in value functions. -/
lemma mbATE_eq_mbValue (M : Model S) (v : EstInput S) :
    mbATE M v = mbValue M v true - mbValue M v false := rfl

end TreatmentLocality


