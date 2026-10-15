-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_EnergyIntegral
-- name    : OAI_Geometry_RuledCovering_EnergyIntegral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:36:51.590982+00:00
-- url     : https://prove2.me/theorems/ab07b662-b3b0-4298-8e75-094b69c69f2d
-- title:
--   Angular profile of the singular energy
-- statement:
--   For real $p$ and $\eta$, the angular energy is the polynomial
--   $$A_p(\eta)=\tfrac14\bigl(p+(2-p)\,\eta^2\bigr)^2+2\,\eta^2 .$$
--
--   It is the angular profile of the singular energy $\mathcal{E}_p=W_{p,1}^2+2W_{p,2}^2$ of the singular field $W_p(z)=\bigl(\tfrac14(2z_2)^{p-1}(p+(2-p)(z_1/z_2)^2),\ (2z_2)^{p-2}z_1\bigr)$: along rays one has $\mathcal{E}_p(r\eta,r)=\tfrac14(2r)^{2p-2}A_p(\eta)$ for $r>0$. The same module computes $\int_{-1}^{1}A_p(\eta)\,d\eta=\tfrac{2(2p^2+2p+13)}{15}$, deduces $\int_{\Delta(1/2)}\mathcal{E}_p=\tfrac{2p^2+2p+13}{240p}$ for $p>1$ over the triangle $\Delta(1/2)=\{0\le z_2\le\tfrac12,\ |z_1|\le z_2\}$, and combines it with $\int_{-1/2}^{1/2}P_p=\tfrac{p+3}{120}$ for the ceiling polynomial to obtain the explicit second-order coefficient
--   $$\frac{p+3}{120}-\frac12\cdot\frac{2p^2+2p+13}{240p}=\Bigl(\frac12\Bigr)^4\frac{2p^2+10p-13}{30p}.$$
--
--   **Formalization Note** `angularEnergy p eta` is `(1/4) * (p + (2 - p) * eta ^ 2) ^ 2 + 2 * eta ^ 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/EnergyIntegral.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/EnergyIntegral.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_RuledCovering_SingularEnergy

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def angularEnergy (p eta : ℝ) : ℝ :=
  (1/4:ℝ)*(p+(2-p)*eta^2)^2+2*eta^2

end RuledApproximation

end

end OAI


