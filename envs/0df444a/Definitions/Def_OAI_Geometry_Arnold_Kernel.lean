-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Kernel
-- name    : OAI_Geometry_Arnold_Kernel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T09:14:27.592988+00:00
-- url     : https://prove2.me/theorems/aa0e720c-f405-4b76-b7d6-09b25b452e5e
-- title:
--   A distinguished direction at the lift $\zeta_0$ and the line through it
-- statement:
--   Let $\zeta_0=\bigl(0,\tfrac12,-\tfrac i2,\tfrac12,\tfrac i2\bigr)\in\mathbb{C}^5$. The file defines the vector and the line
--   $$
--   \kappa=\Bigl(0,-\tfrac14,\tfrac i4,\tfrac14,\tfrac i4\Bigr),\qquad \ell(t)=\zeta_0+t\,\kappa\quad(t\in\mathbb{R}).
--   $$
--
--   $\kappa$ is the candidate eigenvector with eigenvalue $1$ in the linearization of the counterexample map at its fixed point $[\zeta_0]$. The line $\ell$ is used to compute that derivative, exhibiting the degenerate fixed point required by the main theorem.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Kernel.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Kernel.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ArnoldCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume
import Definitions.Def_OAI_Geometry_Arnold_Obstruction
import Definitions.Def_OAI_Geometry_Arnold_ThreePoints
import Definitions.Def_OAI_Geometry_Arnold_Factors
import Definitions.Def_OAI_Geometry_Arnold_Field
import Definitions.Def_OAI_Geometry_Arnold_CompactField
import Definitions.Def_OAI_Geometry_Arnold_Midpoint
import Definitions.Def_OAI_Geometry_Arnold_MidpointGeometry
import Definitions.Def_OAI_Geometry_Arnold_Parameter
import Definitions.Def_OAI_Geometry_Arnold_Quotient
import Definitions.Def_OAI_Geometry_Arnold_Hamiltonian
import Definitions.Def_OAI_Geometry_Arnold_CriticalLifts

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

def kernelVector : CV := ![0,-1/4,Complex.I/4,1/4,Complex.I/4]

def kernelCurve (t : ℝ) : CV := zeroVector + t • kernelVector
end ArnoldCounterexample.Construction

end

end OAI


