-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSetsB_IsConvexWithTop
-- name    : DiscreteConvex_MConvexSetsB_IsConvexWithTop
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:28:59.061184+00:00
-- url     : https://prove2.me/theorems/233ce333-2fc8-4c94-b413-1603332bc29a
-- title:
--   IsConvexWithTop
-- statement:
--   $f : \mathbb R^V \to \mathbb R \cup \{+\infty\}$ is **convex**: for every $x,y$ and $t \in [0,1]$, $f(tx+(1-t)y) \le t\bullet f(x) + (1-t)\bullet f(y)$.
--
--   **Formalization Note.** `WithTop ℝ` carries no `Module ℝ` structure (there is no consistent scalar action of negative reals on $\top$), so convexity is stated directly via the `ScalarWithTop` scalar action (always applied here with nonnegative weights) and the native order on `WithTop ℝ`, rather than via Mathlib's `ConvexOn`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting Theorem 4.16, p.111.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting Theorem 4.16, p.111

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ScalarWithTop

/-!
Convexity of an `R ∪ {+∞}`-valued function on `Rⱽ`, used to state Theorem 4.16 (Murota,
*Discrete Convex Analysis*, SIAM 2003, p.111), in `DiscreteConvex.MConvexSetsB`. `WithTop ℝ`
carries no `Module ℝ` structure (there is no consistent scalar action of negative reals on
`⊤`), so convexity is stated directly via `ScalarWithTop` (always applied with nonnegative
weights here) and the native order on `WithTop ℝ`, rather than via `Mathlib`'s `ConvexOn`. -/

namespace DiscreteConvex.MConvexSetsB

/-- `f : Rⱽ → R ∪ \{+∞\}` is **convex**: for every `x, y` and `t ∈ [0,1]`,
`f(tx + (1-t)y) ≤ t • f(x) + (1-t) • f(y)`. -/
def IsConvexWithTop {V : Type*} (f : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x y : V → ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (fun v => t * x v + (1 - t) * y v) ≤ ScalarWithTop t (f x) + ScalarWithTop (1 - t) (f y)

end DiscreteConvex.MConvexSetsB


