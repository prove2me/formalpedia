-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_CapAsymptotics
-- name    : OAI_Geometry_RuledCovering_CapAsymptotics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:33:13.951472+00:00
-- url     : https://prove2.me/theorems/c6c735e7-3ffb-409c-875f-d47a63a5a77c
-- title:
--   Normalized cap increment of the singular parameter domain
-- statement:
--   Let $P_p(b)=b^2\bigl(\tfrac{p}{4}+(2-p)\,b^2\bigr)$ be the ceiling polynomial of the singular construction and write $x_+=\max(x,0)$. For real $p,c,b$ the cap increment quotient is
--   $$Q_p(c,b)=\frac{\bigl(\tfrac12+c^2P_p(b)+c^{5/2}-|b|\bigr)_+-\bigl(\tfrac12-|b|\bigr)_+}{c^2}.$$
--
--   The singular parameter domain is $\Omega_c=\{b:\ c^{\gamma}\le b_2\le 2,\ |b_1|\le b_2,\ b_2\le \tfrac12+c^2P_p(b_1)+c^{5/2}\}$, a slightly raised version of the triangle $\{|b_1|\le b_2\le\tfrac12\}$ with a small tip removed. For fixed abscissa $b$, the numerator of $Q_p(c,b)$ is the length of the vertical slice of $\{|b|\le r\le \tfrac12+c^2P_p(b)+c^{5/2}\}$ minus that of $\{|b|\le r\le\tfrac12\}$, so $Q_p(c,b)$ is the extra slice length gained by raising the ceiling, measured in units of $c^2$. The same module shows that, for $0\le p\le 2$ and $c>0$, $0\le Q_p(c,b)\le P_p(b)+c^{1/2}$ with equality when $|b|\le\tfrac12$, and that $Q_p(c,b)\to\mathbf{1}_{[-1/2,1/2]}(b)\,P_p(b)$ as $c\to0^+$. By dominated convergence this yields the second-order area expansion $(|\Omega_c|-\tfrac14)/c^2\to\int_{-1/2}^{1/2}P_p(b)\,db$ as $c\to0^+$, for $0\le p\le 2$ and $\gamma>1$.
--
--   **Formalization Note** `capIncrementQuotient p c b` uses `ceilingPolynomial p b`, which is `b ^ 2 * ((1/2) * p / 2 + (2 - p) / (2 * (1/2)) * b ^ 2)`, and the real power `c ^ (5/2 : ℝ)`. At $c=0$ Lean's convention $x/0=0$ makes the quotient $0$; only $c>0$ is relevant.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/CapAsymptotics.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/CapAsymptotics.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RuledCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField
import Definitions.Def_OAI_Geometry_RuledCovering_PlanarIntegration
import Definitions.Def_OAI_Geometry_RuledCovering_ConeVolume

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def capIncrementQuotient (p c b : ℝ) : ℝ :=
  (max ((1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ)-|b|) 0 -
    max ((1/2:ℝ)-|b|) 0)/c^2

end RuledApproximation

end

end OAI


