-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
-- name    : OAI_Analysis_CoulombTransport_HessianCLM
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:54:00.927854+00:00
-- url     : https://prove2.me/theorems/ff6d6897-0003-4a82-ab45-c0dbfec8afb4
-- title:
--   Linear operators of the local stationarity problem
-- statement:
--   In the local construction the five centers are $0,\pm e_1,\pm e_2$, and a local Coulomb branch is attached to each unit axis vector $e_k$. On the axis space $\mathbb{R}^3$ and the state space $\mathbb{R}^3\times\mathbb{R}^3$:
--
--   1. the state operator is the regularized $6\times6$ Hessian for axis $k$, transported to product coordinates;
--   2. the parameter operator is
--   $$
--   v\mapsto\Bigl(-Q_kv,\ -\tfrac18Q_kv\Bigr),\qquad Q_k=\mathrm{diag}(\lambda_k),
--   $$
--      the derivative in the moving outer point;
--   3. the branch operator is $v\mapsto(A_kv,B_kv)$ with $A_k,B_k$ the central and opposite branch derivatives.
--
--   These are the operators to which the implicit function theorem is applied.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/HessianCLM.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/HessianCLM.lean by skeleton subtraction
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

namespace OAI

universe uN

noncomputable section

namespace Problem356.LocalHessian

open Matrix
open scoped RealInnerProductSpace

abbrev AxisSpace := EuclideanSpace ℝ (Fin 3)
abbrev StateSpace := AxisSpace × AxisSpace
abbrev JointSpace := EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)

/-- Passing from sum coordinates to the product coordinates used by the implicit function theorem. -/
def stateCoordinates : JointSpace ≃L[ℝ] StateSpace := EuclideanSpace.sumEquivProd

/-- The regularized state derivative as a continuous linear map on product space. -/
def stateOperator (k : Fin 3) : StateSpace →L[ℝ] StateSpace :=
  stateCoordinates.toContinuousLinearMap ∘L
    (Matrix.toEuclideanCLM (n := Fin 3 ⊕ Fin 3) (𝕜 := ℝ) (regularizedHessian k)) ∘L
      stateCoordinates.symm.toContinuousLinearMap

@[simp] lemma stateCoordinates_symm_inl (v : StateSpace) (i : Fin 3) :
    stateCoordinates.symm v (Sum.inl i) = v.1 i := rfl

@[simp] lemma stateCoordinates_symm_inr (v : StateSpace) (i : Fin 3) :
    stateCoordinates.symm v (Sum.inr i) = v.2 i := rfl

/-- The derivative in the parameter variable at the center. -/
def parameterOperator (k : Fin 3) : AxisSpace →L[ℝ] StateSpace :=
  let Q := Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (pairHessian k)
  (-Q).prod ((-(1 / 8 : ℝ)) • Q)

/-- The derivative of the stationary branch: central and opposite components. -/
def branchOperator (k : Fin 3) : AxisSpace →L[ℝ] StateSpace :=
  (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (centralDerivative k)).prod
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (oppositeDerivative k))

@[simp] lemma branchOperator_fst_apply (k : Fin 3) (v : AxisSpace) (i : Fin 3) :
    (branchOperator k v).1 i = (if i = k then 9 / 106 else -15 / 271) * v i := by
  change ((centralDerivative k) *ᵥ WithLp.ofLp v) i = _
  simp [centralDerivative, mulVec_diagonal]

@[simp] lemma branchOperator_snd_apply (k : Fin 3) (v : AxisSpace) (i : Fin 3) :
    (branchOperator k v).2 i = (if i = k then 1 / 53 else -1 / 271) * v i := by
  change ((oppositeDerivative k) *ᵥ WithLp.ofLp v) i = _
  simp [oppositeDerivative, mulVec_diagonal]

@[simp] lemma parameterOperator_fst_apply (k : Fin 3) (v : AxisSpace) (i : Fin 3) :
    (parameterOperator k v).1 i = -eigenvalue k i * v i := by
  change -(((pairHessian k) *ᵥ WithLp.ofLp v) i) = _
  simp [pairHessian, mulVec_diagonal]

@[simp] lemma parameterOperator_snd_apply (k : Fin 3) (v : AxisSpace) (i : Fin 3) :
    (parameterOperator k v).2 i = -(eigenvalue k i * v i) / 8 := by
  change (-(1 / 8 : ℝ)) * (((pairHessian k) *ᵥ WithLp.ofLp v) i) = _
  simp [pairHessian, mulVec_diagonal]
  ring

end Problem356.LocalHessian

end

end OAI


