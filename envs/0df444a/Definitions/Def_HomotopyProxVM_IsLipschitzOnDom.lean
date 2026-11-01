-- Prove2me | Definitions.Def_HomotopyProxVM_IsLipschitzOnDom
-- name    : HomotopyProxVM_IsLipschitzOnDom
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:51.130478+00:00
-- url     : https://prove2.me/theorems/7f5e1ce9-e803-407f-854e-fa0cc8fc5891
-- title:
--   $L_g$-Lipschitz continuity of $g$ on $\operatorname{dom}(g)$
-- statement:
--   A function $g$ with effective domain $D$ is **Lipschitz continuous on $\operatorname{dom}(g)$ with constant $L_g\in[0,+\infty)$** if
--
--   $$
--   |g(x)-g(y)|\le L_g\|y-x\|_2\qquad\text{for all }x,y\in D .
--   $$
--
--   This is the assumption on $g$ in Assumption 2.
--
--   **Formalization Note** The bound is on $D$ only. Indicator functions of nonempty sets are covered, with $L_g=0$, and subgradients at the boundary of $D$ may be arbitrarily large.
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, §2.1, p.5

import Mathlib

namespace HomotopyProxVM

/-- `g` is Lipschitz continuous on `dom(g)` with a constant `Lg ∈ [0,+∞)`:
`|g(x) − g(y)| ≤ Lg‖y − x‖₂` for all `x, y ∈ dom(g)` (Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, §2.1, p.5).

**Formalization Note.** `dom(g)` is the set `D` of the encoding of `g` by its domain and its values
on the domain (`OneStepProx.IsProperConvex`). The bound is on `D` only, so indicator functions are
covered, with `Lg = 0`. -/
def IsLipschitzOnDom {p : ℕ} (D : Set (EuclideanSpace ℝ (Fin p)))
    (g : EuclideanSpace ℝ (Fin p) → ℝ) (Lg : ℝ) : Prop :=
  0 ≤ Lg ∧ ∀ x ∈ D, ∀ y ∈ D, |g x - g y| ≤ Lg * ‖y - x‖

end HomotopyProxVM


