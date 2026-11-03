-- Prove2me | Definitions.Def_PLIAG_AssumptionB2
-- name    : PLIAG_AssumptionB2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:51.916037+00:00
-- url     : https://prove2.me/theorems/898f7f7d-64c7-4fce-a4cb-949a05d1b5a2
-- title:
--   Assumption B2: $\operatorname{dom}h\cap\operatorname{int}\operatorname{dom}w\ne\emptyset$ and $h$ subdifferentiable there
-- statement:
--   **Assumption B2.** $\operatorname{dom}h\cap\operatorname{int}\operatorname{dom}w\neq\emptyset$, and $h$ is subdifferentiable at every point of $\operatorname{dom}h\cap\operatorname{int}\operatorname{dom}w$: for each such $x$ there is $g\in\mathbb R^d$ with
--
--   $$
--   h(y)\ \ge\ h(x)+\langle g,\,y-x\rangle\qquad\text{for all }y\in\mathbb R^d .
--   $$
--
--   The first clause makes the subproblems of the method attain their minimum inside $\operatorname{int}\operatorname{dom}w$; the second is used through Fermat's rule.
--
--   **Formalization Note** The subgradient inequality is stated in `EReal`.
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, Assumption B2, §2.3, p.7

import Mathlib
import Definitions.Def_AubinLipschitz_effDom

namespace PLIAG

/-- **Assumption B2** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, §2.3, p.7):
`dom h ∩ int dom w ≠ ∅`, and `h` is subdifferentiable at every point of `dom h ∩ int dom w`.

**Formalization Note.** Subdifferentiability of the extended function `h` at `x` is the existence of
a subgradient `g`: `h(x) + ⟨g, y − x⟩ ≤ h(y)` for all `y`, in `EReal`. -/
def AssumptionB2 {d : ℕ} (w h : EuclideanSpace ℝ (Fin d) → EReal) : Prop :=
  (AubinLipschitz.effDom h ∩ interior (AubinLipschitz.effDom w)).Nonempty ∧
    ∀ x ∈ AubinLipschitz.effDom h ∩ interior (AubinLipschitz.effDom w), ∃ g : EuclideanSpace ℝ (Fin d),
      ∀ y, h x + ((inner ℝ g (y - x) : ℝ) : EReal) ≤ h y

end PLIAG


