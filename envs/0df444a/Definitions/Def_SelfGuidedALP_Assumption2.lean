-- Prove2me | Definitions.Def_SelfGuidedALP_Assumption2
-- name    : SelfGuidedALP_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:28:32.227614+00:00
-- url     : https://prove2.me/theorems/76a63421-18f7-4d77-ba0b-03d4a12d964a
-- title:
--   Assumption 2: $V^*\in\mathcal R$, universality, second moment, regularity of $\varphi$
-- statement:
--   **Assumption 2** for a value function $V$ and a Lipschitz constant $L$ says:
--
--   1. $V\in\mathcal R$;
--   2. the class of random basis functions is universal;
--   3. the sampling distribution has a finite second moment, $\mathbb E_\rho[\|\theta\|_2^2]<\infty$;
--   4. $L>0$ and $|\varphi(x)-\varphi(y)|\le L|x-y|$;
--   5. $\|\varphi\|_\infty\le1$ and $\varphi(0)=0$.
--
--   The paper imposes this for all the results from p.10 on, and for all proofs in the e-companion (p.ec1).
--
--   **Formalization Note** $\|\varphi\|_\infty$ is the supremum over all of $\mathbb R$, as $\varphi:\mathbb R\to\mathbb R$ on p.8. The constant $L$ is any Lipschitz constant, not necessarily the least.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Assumption 2, p.10

import Mathlib
import Definitions.Def_SelfGuidedALP_InClassR
import Definitions.Def_SelfGuidedALP_IsUniversal
import Definitions.Def_SelfGuidedALP_samplingMeasure

open MeasureTheory

namespace SelfGuidedALP

/-- Assumption 2 of the paper, for the value function `V` and the Lipschitz constant `L`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Assumption 2, p.10): `V ∈ ℛ`; the class is universal; the sampling distribution has a finite
second moment; `ϕ` has Lipschitz constant `L > 0`, `‖ϕ‖_∞ ≤ 1` and `ϕ(0) = 0`. -/
structure Assumption2 {d m : ℕ} (M : MDP d m) (R : RBClass d) (L : ℝ)
    (V : EuclideanSpace ℝ (Fin d) → ℝ) : Prop where
  mem_R : InClassR M R V
  universal : IsUniversal M R
  secondMoment : Integrable (fun θ : EuclideanSpace ℝ (Fin (d + 1)) => ‖θ‖ ^ 2) (samplingMeasure R)
  L_pos : 0 < L
  lipschitz : ∀ x y, |R.ϕ x - R.ϕ y| ≤ L * |x - y|
  bounded : ∀ x, |R.ϕ x| ≤ 1
  map_zero : R.ϕ 0 = 0

end SelfGuidedALP


