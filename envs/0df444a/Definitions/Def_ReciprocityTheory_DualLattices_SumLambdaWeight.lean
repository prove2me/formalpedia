-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
-- name    : ReciprocityTheory_DualLattices_SumLambdaWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:11.141791+00:00
-- url     : https://prove2.me/theorems/2654609e-ad6f-435e-a01e-7cc0e806f32f
-- title:
--   Sum Lambda Weight
-- statement:
--   Definitions and structural lemmas for Sum Lambda Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLambdaWeight.lean

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
structure IsTeich (v : Valuation C NNReal) (ω : ZMod p → C) : Prop where
  pow : ∀ a, ω a ^ p = ω a
  cong : ∀ a, v (ω a - (a.val : C)) < 1
  zero : ω 0 = 0
  one : ω 1 = 1
  mul : ∀ a b, ω (a * b) = ω a * ω b
  sep : ∀ a b, a ≠ b → v (ω a - ω b) = 1
namespace IsTeich
variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω
end IsTeich
def wt (ω : ZMod p → C) (a : ZMod p) : C := ω a ^ (2 * p - 3)
def sS (ω : ZMod p → C) : C := ∑ b, wt ω b
def u0 (ω : ZMod p → C) (a : ZMod p) : C := wt ω a - if a = 0 then sS ω else 0
def lam (ω : ZMod p → C) (f : ZMod p → C) : C := ∑ a, u0 ω a * f a
section wt
namespace IsTeich
variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω
end IsTeich
end wt
section hopf
variable (hv : v.Integers R)
include hv
variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω
end hopf
end ReciprocityTheory.PGsh.Up.U3


