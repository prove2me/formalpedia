-- Prove2me | Definitions.Def_NewtonianLipschitz_JacobianMatrix
-- name    : NewtonianLipschitz_JacobianMatrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:22:23.184231+00:00
-- url     : https://prove2.me/theorems/e7e80caf-3337-409f-946b-81c7c5a5048a
-- title:
--   Jacobian Matrix
-- statement:
--   Definitions and structural lemmas for Jacobian Matrix, from alexodas and contributors's pinned Sharp Newtonian field Lipschitz bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianMatrix.lean

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_JacobianRows
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Matrix WithLp
open scoped NNReal Topology InnerProductSpace
namespace NewtonianLipschitz
noncomputable def newtonianJacobianMatrix
    (μ : ℝ) (x : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  (μ / euclideanRadius x ^ 5) •
    ((3 : ℝ) • Matrix.vecMulVec x x -
      (euclideanRadius x ^ 2) •
        (1 : Matrix (Fin 3) (Fin 3) ℝ))
def normalizedVector (u v : ℝ) : Vec3 :=
  ![(1 : ℝ), u, v]
end NewtonianLipschitz


