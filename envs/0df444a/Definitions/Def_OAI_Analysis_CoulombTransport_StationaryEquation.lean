-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
-- name    : OAI_Analysis_CoulombTransport_StationaryEquation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:59:14.753827+00:00
-- url     : https://prove2.me/theorems/3c863dfe-8f84-4ce4-bb89-3d53c7a718bb
-- title:
--   The stationarity equation of the regularized local problem
-- statement:
--   Let $\phi(x)=|x|^{-1}$, $K\in\mathbb{R}$ and a vector $a$. For a parameter $p$ (the moving outer point) and a state $(z,w)$ (the central point and the negated other outer point),
--   $$
--   G(p,(z,w))=\Bigl(\nabla\phi(z-p)+\nabla\phi(z-w)+Kz,\ -\nabla\phi(z-w)-\nabla\phi(p-w)-\tfrac54a+K(w+a)\Bigr).
--   $$
--   At the center its state derivative has blocks $2Q+K$, $-Q$, $-Q$, $\frac98Q+K$, and its parameter derivative is $v\mapsto(-Qv,-\frac18Qv)$, where $Q$ is the unit-vector Hessian.
--
--   Solutions of $G=0$ are the stationary points along which the local branches are defined.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/StationaryEquation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/StationaryEquation.lean by skeleton subtraction
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

namespace OAI

universe uE

noncomputable section

namespace Problem356.GeometryJets

open CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The state gradient of the regularized three-body Coulomb cost.
The input is `(parameter, (central point, negative outer point))`. -/
def stationaryEquation (K : ℝ) (a : E) (p : E × (E × E)) : E × E :=
  (pairGradient (p.2.1 - p.1) + pairGradient (p.2.1 - p.2.2) + K • p.2.1,
   -pairGradient (p.2.1 - p.2.2) - pairGradient (p.1 - p.2.2) -
     (5 / 4 : ℝ) • a + K • (p.2.2 + a))

/-- The center state Hessian, expressed using the single-pair unit-center Hessian. -/
def centerStateHessian (K : ℝ) (Q : E →L[ℝ] E) : (E × E) →L[ℝ] (E × E) :=
  (((2 : ℝ) • Q + K • ContinuousLinearMap.id ℝ E).comp
      (ContinuousLinearMap.fst ℝ E E) - Q.comp (ContinuousLinearMap.snd ℝ E E)).prod
    (-(Q.comp (ContinuousLinearMap.fst ℝ E E)) +
      ((9 / 8 : ℝ) • Q + K • ContinuousLinearMap.id ℝ E).comp
        (ContinuousLinearMap.snd ℝ E E))

/-- The center derivative with respect to the moving positive outer point. -/
def centerParameterDerivative (Q : E →L[ℝ] E) : E →L[ℝ] (E × E) :=
  (-Q).prod ((-1 / 8 : ℝ) • Q)

/-- Total differential with the parameter block followed by the state block. -/
def centerTotalDerivative (K : ℝ) (Q : E →L[ℝ] E) :
    (E × (E × E)) →L[ℝ] (E × E) :=
  (centerParameterDerivative Q).comp (ContinuousLinearMap.fst ℝ E (E × E)) +
    (centerStateHessian K Q).comp (ContinuousLinearMap.snd ℝ E (E × E))

end Problem356.GeometryJets

end

end OAI


