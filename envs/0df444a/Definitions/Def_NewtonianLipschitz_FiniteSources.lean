-- Prove2me | Definitions.Def_NewtonianLipschitz_FiniteSources
-- name    : NewtonianLipschitz_FiniteSources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:21:17.466164+00:00
-- url     : https://prove2.me/theorems/128a28f2-5e2c-4bda-b5ff-40c72f6597a0
-- title:
--   Finite Sources
-- statement:
--   Definitions and structural lemmas for Finite Sources, from alexodas and contributors's pinned Sharp Newtonian field Lipschitz bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/FiniteSources.lean

module
public import Definitions.Def_NewtonianLipschitz_Field
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NewtonianLipschitz
noncomputable def NewtonianPointSource.finiteDifferentialAcceleration
    (sources : List (ℝ → NewtonianPointSource)) (t : ℝ) (q : Vec3) : Vec3 :=
  (sources.map (fun source =>
    (source t).exactDifferentialAcceleration q)).sum
end NewtonianLipschitz


