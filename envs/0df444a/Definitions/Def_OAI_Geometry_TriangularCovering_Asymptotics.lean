-- Prove2me | Definitions.Def_OAI_Geometry_TriangularCovering_Asymptotics
-- name    : OAI_Geometry_TriangularCovering_Asymptotics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:42:33.184218+00:00
-- url     : https://prove2.me/theorems/60eb5492-983b-4347-b080-83db5c594d4a
-- title:
--   Limiting area density and mesh coefficient sum for the second-order area expansion
-- statement:
--   Use the coordinate-cover notation $\eta=1/1000$, $\alpha(a,b)=\frac{1+ab}4$, $\beta(a,b)=\frac{a+b}4$, $d(q)=\frac{q^2(1+q^2)}{16}$, $M(a,b)=\eta+\max\{d(a),d(b)\}$, $S(a,b)=\alpha(a,b)^2+2\beta(a,b)^2$, and the uniform mesh $m_{N,j}=-1+j\,h_N$ of $[-1,1]$ with step $h_N=2/N$.
--
--   1. **Area density.** For $q\in\mathbb{R}$,
--   $$
--   \varphi(q)=\eta+d(q)-\frac18\left[\Big(\frac{1+q^2}{4}\Big)^2+2\Big(\frac q2\Big)^2\right]=\eta-\frac1{128}-\frac{q^2}{64}+\frac{7q^4}{128}.
--   $$
--   Here $\eta+d(q)$ and the bracket are the pointwise limits of $M(a,b)$ and $S(a,b)$ as the mesh cell $[a,b]$ shrinks to $q$ (since $\alpha(a,b)\to\frac{1+q^2}4$ and $\beta(a,b)\to\frac q2$). A direct computation gives $\int_{-1}^1\varphi(q)\,dq=-\frac{13}{6000}$.
--   2. **Coefficient sum.** For $N\in\mathbb{N}$,
--   $$
--   \Sigma_N=\sum_{j=0}^{N-1}h_N\left(M(m_{N,j},m_{N,j+1})-\frac{S(m_{N,j},m_{N,j+1})}{8}\right).
--   $$
--
--   These two objects organize the second-order term of the area of the tilted-cylinder covering. Expanding $T_\varepsilon(a,b)^2/\sqrt{1+\varepsilon^2S(a,b)}$ with $T_\varepsilon(a,b)=\frac12+\varepsilon^2M(a,b)$ gives $\frac14+\varepsilon^2\big(M(a,b)-S(a,b)/8\big)+O(\varepsilon^4)$, so the normalized total base area is $\frac12+\varepsilon^2\Sigma_N+O(\varepsilon^4)$. Since $\Sigma_N$ is a Riemann-type sum for $\int_{-1}^1\varphi=-\frac{13}{6000}$, this is the source of the coefficient $-\frac{13}{6000}$ in the asymptotic formula $\frac12-\frac{13}{6000}\varepsilon^2+O(\varepsilon^4)$.
--
--   **Formalization Note** The Lean names are `areaDensity` ($\varphi$) and `coefficientSum` ($\Sigma_N$); $M$, $S$, $h_N$ and the mesh are `cutoffCoeff`, `speedSq`, `step` and `mesh`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/Asymptotics.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/Asymptotics.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection
import Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily
import Definitions.Def_OAI_Geometry_TriangularCovering_Tetrahedron
import Definitions.Def_OAI_Geometry_TriangularCovering_Shadows

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

end TriangularCovering

namespace TriangularCovering

/-- The limiting polynomial for the second-order area coefficient. -/
def areaDensity (q : ℝ) : ℝ :=
  η+d q-(((1+q^2)/4)^2+2*(q/2)^2)/8

end TriangularCovering

namespace TriangularCovering

def coefficientSum (N : ℕ) : ℝ := ∑ j : Fin N,
  step N*(cutoffCoeff (mesh N j) (mesh N (j+1))-speedSq (mesh N j) (mesh N (j+1))/8)

end TriangularCovering

end

end OAI


