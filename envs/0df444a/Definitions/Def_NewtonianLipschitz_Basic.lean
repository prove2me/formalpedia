-- Prove2me | Definitions.Def_NewtonianLipschitz_Basic
-- name    : NewtonianLipschitz_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:19:42.813271+00:00
-- url     : https://prove2.me/theorems/8abec807-27df-4e80-9efa-872ca1ef7392
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from alexodas and contributors's pinned Sharp Newtonian field Lipschitz bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Basic.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NewtonianLipschitz
abbrev Vec3 := Fin 3 → ℝ
noncomputable def euclideanRadius (x : Vec3) : ℝ :=
  Real.sqrt (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)
abbrev PhysicalVec3 := EuclideanSpace ℝ (Fin 3)
def toPhysicalVec3 (q : Vec3) : PhysicalVec3 := WithLp.toLp ((2 : ℕ) : ENNReal) q
end NewtonianLipschitz


