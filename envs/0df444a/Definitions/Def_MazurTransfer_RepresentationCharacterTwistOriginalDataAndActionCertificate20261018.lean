-- Prove2me | Definitions.Def_MazurTransfer_RepresentationCharacterTwistOriginalDataAndActionCertificate20261018
-- name    : MazurTransfer_RepresentationCharacterTwistOriginalDataAndActionCertificate20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T00:06:51.07015+00:00
-- url     : https://prove2.me/theorems/789993fb-f834-4eaa-b21b-609f422883b8
-- title:
--   Original character twist and literal action certificate
-- statement:
--   The original scalar-twist representation and its literal action formula. Both full declaration types and the whole representation value are checked in their original universe levels. Named downstream consumer: the actual norm-kernel quotient paired against a character eigenvector. Bilinear equivariance remains a separate proof obligation.
-- source:
--   MazurTheorem original declarations and immediately necessary constructor certificates; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: scalar twisting of a representation and the equivariance
of an invariant bilinear pairing evaluated on a character eigenvector.
Named downstream consumer: the complementary quotient of the actual
order-13 norm factor containing the rational fixed line.
-/
import Mathlib.RepresentationTheory.Intertwining

noncomputable section
universe u v w x y
namespace MazurTransfer.RepresentationCharacterTwist
variable {k : Type u} [Field k] {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

def twist (χ : G →* kˣ) (ρ : Representation k G V) : Representation k G V where
  toFun g := (χ g : k) • ρ g
  map_one' := by
    rw [map_one, map_one, Units.val_one, one_smul]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    simp only [map_mul, Units.val_mul, LinearMap.smul_apply, Module.End.mul_apply,
      map_smul, smul_smul, mul_comm]

theorem twist_apply (χ : G →* kˣ) (ρ : Representation k G V) (g : G) (v : V) :
    twist χ ρ g v = (χ g : k) • ρ g v := rfl

end MazurTransfer.RepresentationCharacterTwist
#print axioms MazurTransfer.RepresentationCharacterTwist.twist


