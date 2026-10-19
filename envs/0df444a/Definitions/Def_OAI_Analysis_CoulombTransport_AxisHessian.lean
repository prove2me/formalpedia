-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
-- name    : OAI_Analysis_CoulombTransport_AxisHessian
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:29:28.763459+00:00
-- url     : https://prove2.me/theorems/aa91b4fc-0028-451e-964c-f54bc3a85062
-- title:
--   Explicit Hessian data for the two local Coulomb branches
-- statement:
--   In the local construction the five centers are $0,\pm e_1,\pm e_2$, and a local Coulomb branch is attached to each unit axis vector $e_k$. For an axis $k\in\{0,1,2\}$:
--
--   1. The Hessian of $x\mapsto|x|^{-1}$ at $e_k$ is diagonal with eigenvalues $\lambda_k(i)=2$ for $i=k$ and $-1$ otherwise.
--   2. The first derivatives of the central and opposite stationary branches are the diagonal matrices
--   $$
--   \mathrm{diag}\Bigl(\tfrac9{106}\text{ at }k,\ -\tfrac{15}{271}\text{ elsewhere}\Bigr),\qquad\mathrm{diag}\Bigl(\tfrac1{53}\text{ at }k,\ -\tfrac1{271}\text{ elsewhere}\Bigr).
--   $$
--   3. With regularization $K=20$, the regularized $6\times6$ Hessian has diagonal blocks $20+2\lambda_k$ and $20+\frac98\lambda_k$ and off-diagonal blocks $-\lambda_k$.
--
--   These explicit matrices certify that the stationarity equations of the two branches are nondegenerate. The implicit function theorem then yields smooth local branches.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/AxisHessian.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/AxisHessian.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CoulombCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CoulombCounterexample

namespace OAI

/-! Explicit nondegeneracy algebra for the two local Coulomb branches.
The Hessian eigenvalues are 2 in the axial direction and -1 transversely.
A common regularization parameter K = 20 works in every direction. -/

noncomputable section

namespace Problem356.LocalHessian

open Matrix

/-- Eigenvalue of the inverse-distance Hessian at a unit coordinate vector. -/
def eigenvalue (k i : Fin 3) : ℝ := if i = k then 2 else -1

/-- The inverse-distance Hessian at either chosen unit coordinate vector. -/
def pairHessian (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal (eigenvalue k)

/-- First derivative of the central stationary branch for K = 20. -/
def centralDerivative (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun i => if i = k then 9 / 106 else -15 / 271

/-- First derivative of the opposite stationary branch for K = 20. -/
def oppositeDerivative (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun i => if i = k then 1 / 53 else -1 / 271

/-- Upper diagonal block of the regularized Hessian. -/
def upperBlock (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun i => 20 + 2 * eigenvalue k i

/-- Lower diagonal block of the regularized Hessian. -/
def lowerBlock (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun i => 20 + (9 / 8) * eigenvalue k i

/-- Mixed block of the regularized Hessian. -/
def mixedBlock (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun i => -eigenvalue k i

/-- The full six-dimensional regularized Hessian. -/
def regularizedHessian (k : Fin 3) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  fromBlocks (upperBlock k) (mixedBlock k) (mixedBlock k) (lowerBlock k)

end Problem356.LocalHessian

end

end OAI


