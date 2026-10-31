-- Prove2me | Definitions.Def_AdaDiscRL_Assumption2
-- name    : AdaDiscRL_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:40.314026+00:00
-- url     : https://prove2.me/theorems/61dd6879-65d1-46cd-893c-8390cd07453a
-- title:
--   Assumption 2 (model-based Lipschitz): $r_h$ is $L_r$-Lipschitz and $T_h$ is $L_T$-Lipschitz in $d_W$
-- statement:
--   **Assumption 2 (Model-Based Lipschitz).** For every $x,x',a,a'$ and $h$,
--   $$
--   |r_h(x,a)-r_h(x',a')|\le L_r\,\mathcal D((x,a),(x',a')),\qquad d_W\big(T_h(\cdot\mid x,a),T_h(\cdot\mid x',a')\big)\le L_T\,\mathcal D((x,a),(x',a')),
--   $$
--   where $d_W$ is the 1-Wasserstein distance on $(\mathcal S,\mathcal D_{\mathcal S})$. AdaMB is analysed under this assumption.
--
--   **Formalization Note** $d_W$ is the platform definition `WassersteinLinOpt.Ball.wassersteinDist 1` (infimum over couplings of $\int \mathcal D_{\mathcal S}$, valued in $[0,\infty]$); the right-hand side is cast with `ENNReal.ofReal`.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Assumption 2, p.10

import Mathlib
import Definitions.Def_AdaDiscRL_EpisodicMDP
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist

open MeasureTheory ProbabilityTheory

namespace AdaDiscRL

/-- **Assumption 2 (Model-Based Lipschitz)** (arXiv:2110.15843v3, p.10): the mean reward is
`L_r`-Lipschitz with respect to `D`, and the transition kernels are `L_T`-Lipschitz in the
1-Wasserstein metric `d_W` (on `S` with its metric `D_S`): for every `x, x′, a, a′, h`,
`|r_h(x,a) − r_h(x′,a′)| ≤ L_r D((x,a),(x′,a′))`,
`d_W(T_h(·|x,a), T_h(·|x′,a′)) ≤ L_T D((x,a),(x′,a′))`.

**Formalization Note.** `d_W` is the platform's `WassersteinLinOpt.Ball.wassersteinDist 1`
(infimum over couplings of `∫ dist`, valued in `ℝ≥0∞`); the right-hand side is cast with
`ENNReal.ofReal`. -/
def Assumption2 {S A : Type*} [MetricSpace S] [MeasurableSpace S] [MeasurableSpace A] {H : ℕ}
    (M : EpisodicMDP S A H) (D : S × A → S × A → ℝ) (Lr LT : ℝ) : Prop :=
  (∀ h p q, |M.meanReward h p - M.meanReward h q| ≤ Lr * D p q) ∧
  (∀ h p q,
    haveI := M.isMarkov_T h
    WassersteinLinOpt.Ball.wassersteinDist 1 ⟨M.T h p, inferInstance⟩ ⟨M.T h q, inferInstance⟩ ≤
      ENNReal.ofReal (LT * D p q))

end AdaDiscRL


