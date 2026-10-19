-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
-- name    : OAI_Analysis_CoulombTransport_IsometryTransport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T19:23:30.565985+00:00
-- url     : https://prove2.me/theorems/9c5d0350-b391-469f-bf8c-08b956581305
-- title:
--   Isometries act on triples and preserve the Coulomb cost
-- statement:
--   Work in $\mathbb{R}^3$. The three-body Coulomb cost of a triple $(x,y,z)$ is $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$.
--
--   1. An isometry $e$ of $\mathbb{R}^3$ lifts to the measurable equivalence $(x,y,z)\mapsto(ex,ey,ez)$ of triples. It preserves all inverse distances, hence
--   $$
--   c(ex,ey,ez)=c(x,y,z) .
--   $$
--   2. The axis swap is the linear isometry exchanging the first two coordinate axes and fixing the third; it fixes $0$ and exchanges $(1,0,0)$ and $(0,1,0)$.
--
--   The axis swap maps the first local branch onto the second. So the analysis of one branch transfers to the other.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/IsometryTransport.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/IsometryTransport.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.IsometryTransport

/-- Apply the same spatial isometry to each particle. -/
def lift (e : E3 ≃ᵢ E3) : Triple ≃ᵐ Triple :=
  e.toHomeomorph.toMeasurableEquiv.prodCongr
    (e.toHomeomorph.toMeasurableEquiv.prodCongr e.toHomeomorph.toMeasurableEquiv)

@[simp] theorem lift_apply (e : E3 ≃ᵢ E3) (t : Triple) :
    lift e t = (e t.1, (e t.2.1, e t.2.2)) := rfl

@[simp] theorem invDistance_apply (e : E3 ≃ᵢ E3) (x y : E3) :
    invDistance (e x) (e y) = invDistance x y := by
  simp only [invDistance, ← dist_eq_norm, e.dist_eq]

@[simp] theorem cost_lift (e : E3 ≃ᵢ E3) (t : Triple) :
    coulombCost (lift e t) = coulombCost t := by
  simp only [coulombCost, lift_apply, tripleFst, tripleSnd, tripleThd,
    invDistance_apply]

/-- Exchange the first and second Euclidean axes, leaving the third fixed. -/
def axisSwap : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 3) 1)

@[simp] theorem axisSwap_single (i : Fin 3) (a : ℝ) :
    axisSwap (PiLp.single 2 i a) = PiLp.single 2 (Equiv.swap 0 1 i) a := by
  exact LinearIsometryEquiv.piLpCongrLeft_single _ _ _

@[simp] theorem axisSwap_zero : axisSwap (0 : E3) = 0 := map_zero axisSwap

@[simp] theorem axisSwap_first :
    axisSwap (PiLp.single 2 (0 : Fin 3) (1 : ℝ)) = PiLp.single 2 (1 : Fin 3) (1 : ℝ) := by
  simp

@[simp] theorem axisSwap_second :
    axisSwap (PiLp.single 2 (1 : Fin 3) (1 : ℝ)) = PiLp.single 2 (0 : Fin 3) (1 : ℝ) := by
  simp

end Problem356.IsometryTransport

end

end OAI


