-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
-- name    : OAI_Analysis_CoulombTransport_StationaryMap
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T19:07:34.247987+00:00
-- url     : https://prove2.me/theorems/e66d4caf-9fb4-45c2-911d-84f61bb8597a
-- title:
--   The local three-body potential and its stationarity map
-- statement:
--   Let $\phi(x)=|x|^{-1}$, with Hessian $D^2\phi$. For an axis vector $a$, a parameter $y$ (the outer point near $a$) and a state $s=(s_1,s_2)$ (the central point near $0$ and the other outer point near $-a$):
--
--   1. the state potential is
--   $$
--   \phi(s_1-y)+\phi(s_1-s_2)+\phi(s_2-y)-\Bigl(\tfrac52-10|s_1|^2\Bigr)-\Bigl(\tfrac54\langle a,s_2+a\rangle-10|s_2+a|^2\Bigr);
--   $$
--   2. the stationary map is its state gradient,
--   $$
--   \bigl(\nabla\phi(s_1-y)+\nabla\phi(s_1-s_2)+20s_1,\ \nabla\phi(s_2-s_1)+\nabla\phi(s_2-y)-\tfrac54a+20(s_2+a)\bigr);
--   $$
--   3. the joint potential bundles the parameter and the state, and the state differential is the linear form $(u,v)\mapsto\langle G_1,u\rangle+\langle G_2,v\rangle$.
--
--   Minimizing the Coulomb cost minus the two prescribed potentials over the state defines the supporting potential at the moving outer point.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/StationaryMap.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/StationaryMap.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CoulombCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate

namespace OAI

universe uE

noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.StationaryMap

open CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The state potential with the explicit common central quadratic, K = 20. -/
def statePotential (a y : E) (s : E × E) : ℝ :=
  pairCost (s.1 - y) + pairCost (s.1 - s.2) + pairCost (s.2 - y) -
    ((5 : ℝ) / 2 - 10 * ‖s.1‖ ^ 2) -
    ((5 : ℝ) / 4 * ⟪a, s.2 + a⟫ - 10 * ‖s.2 + a‖ ^ 2)

/-- The concrete stationary equation, with parameter first and state second. -/
def stationary (a : E) (p : E × (E × E)) : E × E :=
  (pairGradient (p.2.1 - p.1) + pairGradient (p.2.1 - p.2.2) + (20 : ℝ) • p.2.1,
   pairGradient (p.2.2 - p.2.1) + pairGradient (p.2.2 - p.1) -
     (5 / 4 : ℝ) • a + (20 : ℝ) • (p.2.2 + a))

/-- The scalar potential with parameter and state bundled together. -/
def jointPotential (a : E) (p : E × (E × E)) : ℝ := statePotential a p.1 p.2

/-- The linear form represented by the two components of the stationary map. -/
def stateDifferential (a y : E) (s : E × E) : E × E →L[ℝ] ℝ :=
  (innerSL ℝ (stationary a (y, s)).1).comp (ContinuousLinearMap.fst ℝ E E) +
    (innerSL ℝ (stationary a (y, s)).2).comp (ContinuousLinearMap.snd ℝ E E)

end Problem356.StationaryMap

end

end OAI


