-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
-- name    : OAI_Analysis_CoulombTransport_CenterCertificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:44:51.208985+00:00
-- url     : https://prove2.me/theorems/17ab51ab-2494-4c6e-b904-aebecc94b459
-- title:
--   The five centers and their supporting potential
-- statement:
--   The five centers in $\mathbb{R}^3$ are $P_0=0$, $P_1=e_1$, $P_2=-e_1$, $P_3=e_2$, $P_4=-e_2$.
--
--   1. The potential is $\frac52$ at $P_0$ and $0$ at the other centers.
--   2. A triple of center indices is good if, as a set, it is $\{0,1,2\}$ or $\{0,3,4\}$.
--   3. The center distances are $1$ to $P_0$, $2$ between opposite outer centers, and $\sqrt2$ between adjacent outer centers:
--   $$
--   c(P_0,\pm e_1)=1+1+\tfrac12=\tfrac52 .
--   $$
--
--   The potential is a dual certificate on the centers: the potential sum is at most the Coulomb cost, with equality exactly on the two good families. Two distinct optimal contact families are what prevents a Monge optimizer.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CenterCertificate.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CenterCertificate.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped ENNReal

namespace Problem356.CenterCertificate

/-- The center and the two opposite pairs used in the local construction. -/
def point : Fin 5 → E3 :=
  ![0, !₂[1, 0, 0], !₂[-1, 0, 0], !₂[0, 1, 0], !₂[0, -1, 0]]

/-- The prescribed value of the supporting potential at each center. -/
def potential (i : Fin 5) : ℝ≥0∞ := if i = 0 then 5 / 2 else 0

/-- A center triple belongs to one of the two intended contact families. -/
def Good (i j k : Fin 5) : Prop :=
  ({i, j, k} : Finset (Fin 5)) = {0, 1, 2} ∨
    ({i, j, k} : Finset (Fin 5)) = {0, 3, 4}

/-- The pairwise distances of the five centers. -/
def distance (i j : Fin 5) : ℝ :=
  if i = j then 0 else
  if i = 0 ∨ j = 0 then 1 else
  if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) then 2 else Real.sqrt 2

end Problem356.CenterCertificate

end

end OAI


