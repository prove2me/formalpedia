-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
-- name    : OAI_Analysis_CoulombTransport_CoulombCoercivity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T19:03:00.707972+00:00
-- url     : https://prove2.me/theorems/83855953-7bd3-4eb6-9a94-038867ced267
-- title:
--   The regularized state Jacobian of the local problem
-- statement:
--   Let $\phi(x)=|x|^{-1}$, with Hessian $D^2\phi$. For points $a,b,c$ of a real inner product space $E$, the regularized state Jacobian is the linear map on $E\times E$
--   $$
--   (u,v)\mapsto\Bigl(D^2\phi(a)u+D^2\phi(b)(u-v)+20u,\ -D^2\phi(b)(u-v)+D^2\phi(c)v+20v\Bigr).
--   $$
--
--   It is the derivative of the stationarity equation in the state variables, with regularization constant $K=20$. Its invertibility near the centers makes the local branches smooth.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CoulombCoercivity.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CoulombCoercivity.lean by skeleton subtraction
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

namespace OAI

universe uE

noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The regularized state-Jacobian, written in component form suitable for the
parameter/state stationarity equation. -/
def regularizedStateHessian (a b c : E) : (E × E) →L[ℝ] E × E :=
  (((pairHessian a).comp (ContinuousLinearMap.fst ℝ E E) +
      (pairHessian b).comp
        (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E)) +
      (20 : ℝ) • ContinuousLinearMap.fst ℝ E E).prod
    ((-((pairHessian b).comp
        (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E)) +
      (pairHessian c).comp (ContinuousLinearMap.snd ℝ E E)) +
      (20 : ℝ) • ContinuousLinearMap.snd ℝ E E)

@[simp] theorem regularizedStateHessian_apply (a b c u v : E) :
    regularizedStateHessian a b c (u, v) =
      (pairHessian a u + pairHessian b (u - v) + (20 : ℝ) • u,
        -(pairHessian b (u - v)) + pairHessian c v + (20 : ℝ) • v) := rfl

end Problem356.CoulombCalculus

end

end OAI


