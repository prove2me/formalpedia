-- Prove2me | Definitions.Def_BinaryQueryLB_IsCanonicalChart
-- name    : BinaryQueryLB_IsCanonicalChart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:48:46.315794+00:00
-- url     : https://prove2.me/theorems/783d3fcf-9fc8-465e-a010-9b9e2da639ac
-- title:
--   Canonical chart $G_{\mathrm{can}}$
-- statement:
--   A chart $G$ is **canonical** if it is a first-order chart and
--   $$
--   G(F_W,y)=g_W(y)\qquad\text{for all }W\in\mathcal W,\ y\in X .
--   $$
--   For $f\in F(d,R,M)\setminus\mathcal H$, $G(f,y)$ is a fixed element of $\partial f(y)$; any such choice gives a canonical chart, and the arguments of the paper use only the values on $\mathcal H$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.7, p.13

import Mathlib
import Definitions.Def_BinaryQueryLB_IsChart
import Definitions.Def_BinaryQueryLB_gW
import Definitions.Def_BinaryQueryLB_FW__386b32
import Definitions.Def_BinaryQueryLB_Wset

namespace BinaryQueryLB

/-- **Canonical chart `Gcan` (Definition 2.7).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.7, p.13: "The chart `Gcan` is
given by `Gcan(F_W, y) = g_W(y)` for `W ∈ 𝒲` and `y ∈ X`. For `f ∈ F(d, R, M) \ ℋ`, the vector
`Gcan(f, y)` is a fixed element of `∂f(y)`."

`IsCanonicalChart d R M G` says that `G` is a first-order chart and agrees with `g_W` on the hard
family. Every choice of the fixed elements outside `ℋ` gives such a chart; the paper's arguments
use only the values on `ℋ`. -/
def IsCanonicalChart (d : ℕ) (R M : ℝ) (G : Chart d) : Prop :=
  IsChart d R M G ∧ ∀ W ∈ Wset (d / 2), ∀ y ∈ Box d R, G (FW d R M W) y = gW d R M W y

end BinaryQueryLB


