-- Prove2me | Definitions.Def_MazurTransfer_OriginalRepresentationCanonicalDistribMulActionData20261020
-- name    : MazurTransfer_OriginalRepresentationCanonicalDistribMulActionData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T01:58:32.978776+00:00
-- url     : https://prove2.me/theorems/64a5eec7-170b-4c38-928d-d5e91cda0398
-- title:
--   Original distributive multiplicative action of the same fixed representation
-- statement:
--   Retain the exact distributive multiplicative action of the same original representation on the same module. Its complete original type and whole value, with every generated structural certificate, are independently checked. The action formula is a separate theorem interface. Named downstream consumer: selected ordered arithmetic character quotients in the finite-flat Hopf quotient construction.
-- source:
--   MazurTheorem RepresentationCanonicalDistribMulAction by Vas and contributors; complete original types and whole action value, preserving Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: expose the action of a FIXED representation as a
DistribMulAction, definitionally its original linear operators.
Named downstream consumer: selected ordered arithmetic character
quotients in the finite-flat Hopf quotient construction.
-/
import Mathlib.RepresentationTheory.Basic

namespace MazurTransfer.RepresentationCanonicalDistribMulAction
universe u v w
variable {k : Type u} [Semiring k] {G : Type v} [Monoid G]
variable {V : Type w} [AddCommMonoid V] [Module k V]

abbrev ofRepresentation (ρ : Representation k G V) : DistribMulAction G V where
  smul g v := ρ g v
  one_smul v := LinearMap.congr_fun (map_one ρ) v
  mul_smul g h v := LinearMap.congr_fun (map_mul ρ g h) v
  smul_zero g := map_zero (ρ g)
  smul_add g x y := map_add (ρ g) x y

variable (ρ : Representation k G V)


end MazurTransfer.RepresentationCanonicalDistribMulAction
#print axioms MazurTransfer.RepresentationCanonicalDistribMulAction.ofRepresentation


