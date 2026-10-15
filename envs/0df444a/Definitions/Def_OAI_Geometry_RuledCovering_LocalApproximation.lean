-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
-- name    : OAI_Geometry_RuledCovering_LocalApproximation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:18:35.193132+00:00
-- url     : https://prove2.me/theorems/cc6dfbe8-a802-4595-9a79-44e438234e36
-- title:
--   Exact affine lattice template for covering ruling segments by sliding square cells
-- statement:
--   Let $\mathbb{R}^2_\infty$ denote the coordinate plane of pairs of reals with the maximum norm $\|x\|_\infty=\max(|x_1|,|x_2|)$ and the associated distance, and let $\Lambda_n=\tfrac1n\mathbb{Z}^2$ be the grid of mesh $1/n$.
--
--   1. **Parameter space.** The space $\mathbb{R}^2_\infty$ itself, under the name of parameter plane.
--   2. **Lattice model.** For a linear map $A:\mathbb{R}^2_\infty\to\mathbb{R}^2_\infty$ and reals $L,R$, the property $\mathrm{LM}(A,L,R)$ holds when for every integer $n\ge 1$, every $p\in\mathbb{R}^2_\infty$ and every $r\in\mathbb{R}$ with $|r|\le L$ there is a grid point $b\in\Lambda_n$ such that
--   $$\|b-p\|_\infty\le\frac{R}{n}\qquad\text{and}\qquad\bigl\|(p-b)+r\,A(p-b)\bigr\|_\infty\le\frac{1}{2n}.$$
--
--   The template describes covering by a lattice of square cells, each sliding along its own straight line. If a field $v$ is exactly affine with linear part $A$, i.e. $v(p)-v(b)=A(p-b)$, then the point $p+r\,v(p)$ at time $r$ on the line through $p$ with direction $v(p)$ differs from $b+r\,v(b)$ by $(p-b)+rA(p-b)$. So $\mathrm{LM}(A,L,R)$ says that at every scale $1/n$ and every time $|r|\le L$, the square of side $1/n$ centred at $b+r\,v(b)$ for a suitable grid point $b$ contains $p+r\,v(p)$, and that this $b$ can be chosen within distance $R/n$ of $p$; the uniform radius is what allows only finitely many centres to be retained over a compact set of base points. Combined with a $C^1$ remainder estimate for a nonlinear field, the template yields, at a suitable scale $1/n$, a finite set of grid centres $b$ such that every point $p+r\,v(p)$ with $p$ in a given compact set and $|r|\le L$ lies in a slightly enlarged square around some $b+r\,v(b)$, and whose weighted count approximates the corresponding integral. It is verified later for the hyperbolic template $A=\lambda S$ ($S$ the coordinate swap, $L>0$, $0<L\lambda<1$) and for the shear template $A=dN$.
--
--   **Formalization Note** `Parameter` is the abbreviation `Fin 2 → ℝ` (the same type as `Coordinates`), so `dist` and the norm are the supremum ones. In `LatticeModel A L R`, `A` is a continuous linear map, `coordinateGrid n` is $\Lambda_n$, and no sign condition is imposed on $L$ or $R$ (for $L<0$ the condition is vacuous).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/LocalApproximation.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/LocalApproximation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RuledCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

abbrev Parameter := Fin 2 → ℝ

/-- Exact affine lattice template. The uniform bound retains finitely many centers. -/
def LatticeModel (A : Parameter →L[ℝ] Parameter) (L R : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ p : Parameter, ∀ r : ℝ, |r| ≤ L →
    ∃ b ∈ coordinateGrid n, dist b p ≤ R / n ∧
      ‖p - b + r • A (p - b)‖ ≤ 1 / (2 * n)

end RuledApproximation

end

end OAI


