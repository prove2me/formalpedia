-- Prove2me | Definitions.Def_NewtonianLipschitz_ConvexImproved
-- name    : NewtonianLipschitz_ConvexImproved
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:24:46.99918+00:00
-- url     : https://prove2.me/theorems/365761db-2d59-4f25-8a67-5394b3a7c69b
-- title:
--   Convex Improved
-- statement:
--   Definitions and structural lemmas for Convex Improved, from alexodas and contributors's pinned Sharp Newtonian field Lipschitz bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexImproved.lean

module
public import Definitions.Def_NewtonianLipschitz_ImprovedBounds
public import Definitions.Def_NewtonianLipschitz_Clearance
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open scoped NNReal Topology InnerProductSpace
namespace NewtonianLipschitz
noncomputable def NewtonianPointSource.sevenLipschitzCoefficient
    (d : ℝ) (M : ℝ≥0) (hd : 0 < d) : ℝ≥0 :=
  Real.toNNReal (((7 : ℕ) : ℝ) * (M : ℝ) / d ^ 3)
end NewtonianLipschitz


