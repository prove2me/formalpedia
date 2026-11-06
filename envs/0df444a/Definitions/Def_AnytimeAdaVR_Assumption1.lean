-- Prove2me | Definitions.Def_AnytimeAdaVR_Assumption1
-- name    : AnytimeAdaVR_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:36.062485+00:00
-- url     : https://prove2.me/theorems/504620f1-4441-42e2-b962-f0c2517c4955
-- title:
--   Assumption 1 — objective smoothness and initial gap
-- statement:
--   **Assumption 1** holds for $f:\mathbb R^d\to\mathbb R$, constants $L,\Delta_f$ and an initial point $x_{\mathrm{init}}$ if:
--
--   1. $f$ is differentiable and its gradient is $L$-Lipschitz: $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ for all $x,y$;
--   2. $L>0$;
--   3. $f$ is bounded below, i.e. $f^*>-\infty$;
--   4. $\Delta_f\ge 0$ and $f(x_{\mathrm{init}})-f^*\le\Delta_f$.
--
--   The norm is Euclidean. This is the first of the two assumptions that apply throughout the paper.
--
--   **Formalization Note** Item 1 is the platform definition `HomotopyProxVM.IsSmoothParam f L` (which also records $L\ge0$). Boundedness below is `BddBelow (Set.range f)`, and $f^*$ is `AnytimeAdaVR.fStar f`.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §2, Assumption 1, p.3

import Mathlib
import Definitions.Def_HomotopyProxVM_IsSmoothParam
import Definitions.Def_AnytimeAdaVR_fStar

namespace AnytimeAdaVR

/-- **Assumption 1 (objective smoothness and initial gap).** Jiang–Wang–Yang–Zhang–Li, *Adaptive
Variance Reduction across Smoothness and Noise Conditions* (preprint, 2026), §2, p.3: "The function
f is differentiable, f∗ > −∞, and, for all x, y ∈ ℝ^d, ‖∇f(x) − ∇f(y)‖ ≤ L‖x − y‖. The initial point
satisfies f(xinit) − f∗ ≤ ∆f, where L > 0 and ∆f ≥ 0."

**Formalization Note.** Differentiability and the Lipschitz gradient are the platform definition
`HomotopyProxVM.IsSmoothParam f L` (it also records `0 ≤ L`, implied by `0 < L`). `f∗ > −∞` is
`BddBelow (Set.range f)`, under which `fStar f` is the true infimum. `∇f` is Mathlib's `gradient`. -/
def Assumption1 {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (L Δf : ℝ)
    (xinit : EuclideanSpace ℝ (Fin d)) : Prop :=
  HomotopyProxVM.IsSmoothParam f L ∧ 0 < L ∧ BddBelow (Set.range f) ∧ 0 ≤ Δf ∧
    f xinit - fStar f ≤ Δf

end AnytimeAdaVR


