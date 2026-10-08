-- Prove2me | Definitions.Def_OptimalSGD_Smooth_Model
-- name    : OptimalSGD_Smooth_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:20:22.053745+00:00
-- url     : https://prove2.me/theorems/88cc469c-9073-42a6-b6bd-d923fb9e6eae
-- title:
--   $\mu$-smoothness with respect to $w^*$ (§2, p. 3, (2))
-- statement:
--   Let $W \subseteq \mathbb R^d$ be the domain and $F : \mathbb R^d \to \mathbb R$ the objective.
--
--   **$\mu$-smoothness with respect to $w^*$** (equation (2) of the paper). For $\mu \in \mathbb R$ and a point $w^*$, the function $F$ is $\mu$-smooth with respect to $w^*$ on $W$ if
--   $$F(w) - F(w^*) \ \le\ \frac{\mu}{2}\,\|w - w^*\|^2 \qquad \text{for all } w \in W.$$
--
--   The stochastic subgradient oracle relative to $W$ (§2, p. 2) used with this condition is the series' shared predicate `OptimalSGD.Suffix.IsSubgradientOracleOn`, which this module imports. Condition (2) only bounds the growth of $F$ away from the optimum; it does not require $F$ to be differentiable and is weaker than a Lipschitz-gradient assumption.
--
--   **Formalization Note** The paper's Hilbert space is specialised to $\mathbb R^d$ with the Euclidean norm (`UnderstandingML.Vec d`). Smoothness is required only at points of $W$, exactly as in (2); no sign of $\mu$ is built in (the theorems that use it assume $0 \le \mu$).
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, pp. 2–3, §2 (stochastic gradient oracle, p. 2) and Eq. (2), p. 3

import Definitions.Def_UnderstandingML_SGD
import Definitions.Def_OptimalSGD_Suffix_Model

/-!
# Rakhlin–Shamir–Sridharan (2012), §2: the stochastic gradient oracle relative to `W`
# and µ-smoothness with respect to the optimum

Rakhlin, Shamir, Sridharan, *Making Gradient Descent Optimal for Strongly Convex Stochastic
Optimization*, arXiv:1109.5647v7, pp. 2–3.

* **Oracle (p. 2).** Given `w ∈ W` the oracle produces a random vector `ĝ` whose expectation
  `E[ĝ] = g` is a subgradient of `F` at `w`. The randomness is a sample `z ∼ D` and `ĝ = g(w, z)`.
  The subgradient is taken relative to the domain `W`: `F(u) ≥ F(w) + ⟨u − w, g⟩` for `u ∈ W`.
* **(2), p. 3.** `F` is `µ`-smooth with respect to `w*` if `F(w) − F(w*) ≤ µ/2 ‖w − w*‖²` for all
  `w ∈ W`.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace OptimalSGD.Smooth

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

/-- **µ-smoothness with respect to `w*`**, (2) p. 3: `F(w) − F(w*) ≤ µ/2 ‖w − w*‖²` for all
`w ∈ W`. -/
def IsSmoothWrt (W : Set (UnderstandingML.Vec d)) (F : UnderstandingML.Vec d → ℝ) (μ : ℝ)
    (wstar : UnderstandingML.Vec d) : Prop :=
  ∀ w ∈ W, F w - F wstar ≤ μ / 2 * ‖w - wstar‖ ^ 2

end OptimalSGD.Smooth


