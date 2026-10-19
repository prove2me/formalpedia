-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
-- name    : OAI_Analysis_CoulombTransport_DensityMeasure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:47:12.37059+00:00
-- url     : https://prove2.me/theorems/68ab6175-b8ee-4d37-8ce3-c2d6f264dac0
-- title:
--   Density measures have no atoms
-- statement:
--   For any function $\rho$ on $\mathbb{R}^3$, the density measure $\mu_\rho=\rho^+\,dx$ (Lebesgue measure weighted by $\max(\rho,0)$) gives measure zero to every point:
--   $$
--   \mu_\rho(\{x\})=0\quad\text{for all }x .
--   $$
--
--   No regularity of $\rho$ is needed. Atomlessness is what allows measure-preserving maps to approximate couplings.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/DensityMeasure.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/DensityMeasure.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A density measure has no point atoms, without any regularity assumption on the density. -/
instance densityMeasure_nullSingletonClass (rho : E3 → ℝ) :
    NullSingletonClass (densityMeasure rho) := by
  unfold densityMeasure
  infer_instance

end Problem356

end

end OAI


