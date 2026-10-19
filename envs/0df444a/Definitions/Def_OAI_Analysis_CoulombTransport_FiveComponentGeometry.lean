-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_FiveComponentGeometry
-- name    : OAI_Analysis_CoulombTransport_FiveComponentGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T19:32:13.479763+00:00
-- url     : https://prove2.me/theorems/c99c8ef2-71ff-4418-b409-e14a84eed223
-- title:
--   The five local potentials of the Coulomb construction
-- statement:
--   Let $C_1$ and $C_2$ be local supporting charts for the local problem at the outer centers $P_1=(1,0,0)$ and $P_3=(0,1,0)$, with value functions $V_1,V_2$ and branches $y\mapsto(\mathrm{central}(y),\mathrm{opposite}(y))$.
--
--   1. The five potentials are
--   $$
--   v_0(x)=\tfrac52-10|x|^2,\quad v_1=V_1,\quad v_2(z)=\tfrac54\langle P_1,z+P_1\rangle-10|z+P_1|^2,\quad v_3=V_2,\quad v_4(z)=\tfrac54\langle P_3,z+P_3\rangle-10|z+P_3|^2 .
--   $$
--   2. Their preliminary domains are all of $\mathbb{R}^3$ for the polynomial potentials and the chart sources for $V_1,V_2$.
--   3. A triple is a branch contact if it is a permutation of $(\mathrm{central}(y),y,\mathrm{opposite}(y))$ for some $y$ in the source of $C_1$ or of $C_2$.
--
--   At the centers these potentials take the values $\frac52$ and $0$ of the finite certificate. Their contact set is the union of the two branch graphs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/FiveComponentGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/FiveComponentGeometry.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open Set Filter Metric
open scoped ENNReal InnerProductSpace

namespace Problem356.FiveComponentGeometry

open LocalGeometry StationaryMap CenterCertificate

abbrev ChartsAt (a : E3) :=
  LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a)

/-- The actual five local potentials of the Coulomb construction, with the
same central quadratic for both branches. -/
def potentials (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    Fin 5 → E3 → ℝ :=
  ![fun x => (5 : ℝ) / 2 - 10 * ‖x‖ ^ 2,
    C₁.value,
    fun z => (5 : ℝ) / 4 * ⟪point 1, z + point 1⟫_ℝ - 10 * ‖z + point 1‖ ^ 2,
    C₂.value,
    fun z => (5 : ℝ) / 4 * ⟪point 3, z + point 3⟫_ℝ - 10 * ‖z + point 3‖ ^ 2]

/-- Preliminary domains are unrestricted for the polynomial potentials and
are the actual chart sources for the two supporting-value potentials. -/
def domains (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) : Fin 5 → Set E3 :=
  ![univ, C₁.charts.central.source, univ, C₂.charts.central.source, univ]

/-- Symmetric union of the two actual local branch graphs. The parameter
remains in the corresponding chart source. -/
def branchContact (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) (t : Triple) : Prop :=
  (∃ y ∈ C₁.charts.central.source,
    List.Perm [t.1, t.2.1, t.2.2] [C₁.charts.central y, y, C₁.charts.opposite y]) ∨
  (∃ y ∈ C₂.charts.central.source,
    List.Perm [t.1, t.2.1, t.2.2] [C₂.charts.central y, y, C₂.charts.opposite y])

end Problem356.FiveComponentGeometry

end

end OAI


