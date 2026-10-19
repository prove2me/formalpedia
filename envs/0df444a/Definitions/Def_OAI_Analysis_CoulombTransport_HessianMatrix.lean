-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
-- name    : OAI_Analysis_CoulombTransport_HessianMatrix
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T19:02:06.733168+00:00
-- url     : https://prove2.me/theorems/08edb3cd-7975-4165-a9a2-2720a9770ed8
-- title:
--   Unit axis vectors in $\mathbb{R}^3$
-- statement:
--   For $k\in\{0,1,2\}$ the axis vector $e_k\in\mathbb{R}^3$ is the $k$-th standard basis vector. It satisfies
--   $$
--   |e_k|=1,\qquad\langle e_k,v\rangle=v_k,\qquad e_k\ne0 .
--   $$
--
--   The local Coulomb branches are attached to the axis vectors $(1,0,0)$ and $(0,1,0)$, which are outer centers of the construction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/HessianMatrix.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/HessianMatrix.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped RealInnerProductSpace
open Matrix

namespace Problem356.CoulombCalculus

/-- Unit coordinate vector for either local Coulomb branch. -/
def axisVector (k : Fin 3) : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single k 1

@[simp] theorem norm_axisVector (k : Fin 3) : ‖axisVector k‖ = 1 := by
  simp [axisVector]

@[simp] theorem inner_axisVector (k : Fin 3) (v : EuclideanSpace ℝ (Fin 3)) :
    ⟪axisVector k, v⟫ = v k := by
  simp [axisVector, EuclideanSpace.inner_single_left]

@[simp] theorem axisVector_ne_zero (k : Fin 3) : axisVector k ≠ 0 := by
  intro h
  have hn := norm_axisVector k
  rw [h, norm_zero] at hn
  norm_num at hn

end Problem356.CoulombCalculus

namespace Problem356.GeometryJets

open CoulombCalculus

end Problem356.GeometryJets

end

end OAI


