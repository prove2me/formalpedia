-- Prove2me | Definitions.Def_NewtonianLipschitz_ConvexBaseline
-- name    : NewtonianLipschitz_ConvexBaseline
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:23:20.043233+00:00
-- url     : https://prove2.me/theorems/32de5b2b-62a7-4963-a921-4a606caf7ad6
-- title:
--   Convex Baseline
-- statement:
--   Definitions and structural lemmas for Convex Baseline, from alexodas and contributors's pinned Sharp Newtonian field Lipschitz bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexBaseline.lean

module
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
public import Definitions.Def_NewtonianLipschitz_Clearance
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open scoped NNReal Topology InnerProductSpace
namespace NewtonianLipschitz
noncomputable def NewtonianPointSource.clearanceLipschitzCoefficient
    (d : ℝ) (M : ℝ≥0) (hd : 0 < d) : ℝ≥0 :=
  Real.toNNReal (((10 : ℕ) : ℝ) * (M : ℝ) / d ^ 3)
end NewtonianLipschitz


