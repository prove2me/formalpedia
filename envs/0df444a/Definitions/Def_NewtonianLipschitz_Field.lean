-- Prove2me | Definitions.Def_NewtonianLipschitz_Field
-- name    : NewtonianLipschitz_Field
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:20:27.560369+00:00
-- url     : https://prove2.me/theorems/f70f1558-2d98-416f-bf07-a69b0eee29ac
-- title:
--   Field
-- statement:
--   Definitions and structural lemmas for Field, from alexodas and contributors's pinned Sharp Newtonian field Lipschitz bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Field.lean

module
public import Definitions.Def_NewtonianLipschitz_Basic
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NewtonianLipschitz
noncomputable def newtonianAcceleration (μ : ℝ) (x : Vec3) : Vec3 :=
  (-(μ) / euclideanRadius x ^ 3) • x
structure NewtonianPointSource where
  gravitationalParameter : ℝ
  gravitationalParameter_nonneg : 0 ≤ gravitationalParameter
  displacement : Vec3
  displacement_ne_zero : displacement ≠ 0
noncomputable def NewtonianPointSource.accelerationField
    (c : NewtonianPointSource) (x : Vec3) : Vec3 :=
  (-(c.gravitationalParameter) / euclideanRadius x ^ 3) • x
noncomputable def NewtonianPointSource.exactDifferentialAcceleration
    (c : NewtonianPointSource) (q : Vec3) : Vec3 :=
  c.accelerationField (c.displacement + q) -
    c.accelerationField c.displacement
def NewtonianPointSource.unitAxis : NewtonianPointSource where
  gravitationalParameter := 1
  gravitationalParameter_nonneg := by norm_num
  displacement := ![(1 : ℝ), 0, 0]
  displacement_ne_zero := by
    intro h
    have h0 := congrArg (fun q : Vec3 => q 0) h
    norm_num at h0
end NewtonianLipschitz


