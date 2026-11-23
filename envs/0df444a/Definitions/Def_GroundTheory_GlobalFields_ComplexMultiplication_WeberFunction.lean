-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:07.996319+00:00
-- url     : https://prove2.me/theorems/944fe8e1-3874-40ea-946f-6cf0e943c8bb
-- title:
--   Weber Function
-- statement:
--   Definitions and structural lemmas for Weber Function, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Global
open WeierstrassCurve OnePoint
variable {F : Type*} [Field F]
structure IsShortForm (W : WeierstrassCurve F) : Prop where
  a₁_eq : W.a₁ = 0
  a₂_eq : W.a₂ = 0
  a₃_eq : W.a₃ = 0
namespace ShortWeierstrass
def g₂ (W : WeierstrassCurve F) : F := -4 * W.a₄
def g₃ (W : WeierstrassCurve F) : F := -4 * W.a₆
end ShortWeierstrass
open ShortWeierstrass
open scoped Classical in

noncomputable def weberValue (W : WeierstrassCurve F) (x : F) : F :=
  if W.a₆ = 0 then g₂ W ^ 2 / W.Δ * x ^ 2
  else if W.a₄ = 0 then g₃ W / W.Δ * x ^ 3
  else g₂ W * g₃ W / W.Δ * x
noncomputable def weberFunction (W : WeierstrassCurve F) : W.toAffine.Point → OnePoint F
  | .zero => ∞
  | .some x _ _ => OnePoint.some (weberValue W x)
section Isomorphism
variable [CharZero F]
end Isomorphism
section FieldOfDefinition
variable {L : Type*} [Field L]
def pointMapOfRingHom (φ : F →+* L) {W : WeierstrassCurve F} :
    W.toAffine.Point → (W.map φ).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (φ x) (φ y) ((W.toAffine.map_nonsingular φ.injective x y).mpr h)
end FieldOfDefinition
end GroundTheory.Global


