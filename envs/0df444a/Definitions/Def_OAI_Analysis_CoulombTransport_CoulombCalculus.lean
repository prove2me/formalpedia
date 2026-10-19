-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
-- name    : OAI_Analysis_CoulombTransport_CoulombCalculus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:57:52.62707+00:00
-- url     : https://prove2.me/theorems/b3c9bf48-8363-4088-891d-d55eae3e92bc
-- title:
--   Derivatives of the radial Coulomb interaction
-- statement:
--   In a real inner product space, away from the origin:
--
--   1. the pair interaction is $\phi(x)=|x|^{-1}$;
--   2. its gradient is $\nabla\phi(x)=-x/|x|^3$;
--   3. its Hessian is
--   $$
--   D^2\phi(x)=-\frac{I}{|x|^3}+\frac{3\,x\otimes x}{|x|^5} .
--   $$
--   The interaction and Hessian are even, $\phi(-x)=\phi(x)$, and the gradient is odd.
--
--   At a unit vector $e_k$ the Hessian has eigenvalue $2$ along $e_k$ and $-1$ transversely.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CoulombCalculus.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CoulombCalculus.lean by skeleton subtraction
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

namespace OAI

universe uE

noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real-valued radial Coulomb interaction, used only away from the origin. -/
def pairCost (x : E) : ℝ := ‖x‖⁻¹

/-- The gradient of the real radial Coulomb interaction. -/
def pairGradient (x : E) : E := -(‖x‖ ^ 3)⁻¹ • x

/-- The Hessian of the real radial Coulomb interaction. -/
def pairHessian (x : E) : E →L[ℝ] E :=
  -(‖x‖ ^ 3)⁻¹ • ContinuousLinearMap.id ℝ E +
    (3 * (‖x‖ ^ 5)⁻¹) • (innerSL ℝ x).smulRight x

omit [InnerProductSpace ℝ E] in
@[simp] lemma pairCost_neg (x : E) : pairCost (-x) = pairCost x := by
  simp [pairCost]

@[simp] lemma pairGradient_neg (x : E) : pairGradient (-x) = -pairGradient x := by
  simp [pairGradient]

@[simp] lemma pairHessian_neg (x : E) : pairHessian (-x) = pairHessian x := by
  ext y
  simp [pairHessian]

end Problem356.CoulombCalculus

end

end OAI


