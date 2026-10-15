-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_SingularEnergy
-- name    : OAI_Geometry_RuledCovering_SingularEnergy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:35:32.275261+00:00
-- url     : https://prove2.me/theorems/ba7d4e42-8165-440c-9f9a-55b5368d77c9
-- title:
--   Anisotropic energy of the singular field and its weight correction
-- statement:
--   For $p\in\mathbb{R}$ let $W_p=(W_{p,1},W_{p,2})$ be the singular field on the plane,
--   $$W_p(z)=\Bigl(\tfrac14\,(2z_2)^{p-1}\bigl(p+(2-p)(z_1/z_2)^2\bigr),\ (2z_2)^{p-2}\,z_1\Bigr).$$
--
--   1. **Singular energy.** $\mathcal{E}_p(z)=W_{p,1}(z)^2+2\,W_{p,2}(z)^2$.
--   2. **Energy correction.** For $c\in\mathbb{R}$,
--   $$\rho_{p,c}(z)=-\frac{\mathcal{E}_p(z)}{\sqrt{1+c^2\mathcal{E}_p(z)}\,\Bigl(\sqrt{1+c^2\mathcal{E}_p(z)}+1\Bigr)}.$$
--
--   The physical weight with vertical scale $\sqrt2$ of a vector $w$ is $1/\sqrt{1+w_1^2+2w_2^2}$, so for the scaled field $cW_p$ it equals $1/\sqrt{1+c^2\mathcal{E}_p}$, and the correction term is exactly the coefficient in
--   $$\frac{1}{\sqrt{1+c^2\mathcal{E}_p(z)}}=1+c^2\rho_{p,c}(z).$$
--   The same module shows $|\rho_{p,c}|\le\mathcal{E}_p/2$ and $\rho_{p,c}(z)\to-\mathcal{E}_p(z)/2$ as $c\to0^+$. Hence the weighted cost integral over the singular parameter domain $\Omega_c$ equals $|\Omega_c|+c^2\int_{\Omega_c}\rho_{p,c}$, and by dominated convergence the last integral tends to $-\tfrac12\int_{\Delta(1/2)}\mathcal{E}_p$ as $c\to0^+$, for $1<p\le 2$ and $\gamma>0$, where $\Delta(1/2)=\{0\le z_2\le\tfrac12,\ |z_1|\le z_2\}$.
--
--   **Formalization Note** `singularEnergy p z` is `singularField p z 0 ^ 2 + 2 * singularField p z 1 ^ 2` and `energyCorrection p c z` is the displayed quotient. The powers of $2z_2$ are real powers, written in Lean as `(z 1 / (1/2)) ^ (p - 1)`; the formulas are meaningful for $z_2>0$, and elsewhere Lean's conventions (such as division by zero giving $0$) apply.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SingularEnergy.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SingularEnergy.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_RuledCovering_CapAsymptotics

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def singularEnergy (p : ℝ) (z : Plane) : ℝ :=
  singularField p z 0^2+2*singularField p z 1^2

def energyCorrection (p c : ℝ) (z : Plane) : ℝ :=
  -singularEnergy p z /
    (Real.sqrt (1+c^2*singularEnergy p z)*(Real.sqrt (1+c^2*singularEnergy p z)+1))

end RuledApproximation

end

end OAI


