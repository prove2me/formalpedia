-- Prove2me | Definitions.Def_MazurTransfer_NineteenRootsGaloisRepresentationOriginalData20261018
-- name    : MazurTransfer_NineteenRootsGaloisRepresentationOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T15:14:02.558616+00:00
-- url     : https://prove2.me/theorems/28c75156-4b82-460c-b0f7-e3258e829bde
-- title:
--   Original one-dimensional F19 representation of literal nineteen-th roots of unity
-- statement:
--   The original roots-of-unity type, canonical exponent-nineteen F19 module, and literal field Galois representation, with the original evaluation, cardinality and rank-one laws. All six complete original declaration types and three constructor values are checked, together with three provider types and one module-provider value. The named downstream consumers are the actual norm-kernel cyclotomic characters and their quotient representations.
-- source:
--   MazurTheorem NineteenRootsGaloisRepresentation, exact original declarations and constructors; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: nineteen-th roots of unity carry their literal field
Galois action as a one-dimensional F19 representation.
Named downstream consumer: actual norm-kernel cyclotomic quotient maps.
-/
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Module.ZMod

noncomputable section
namespace MazurTransfer.NineteenRootsGaloisRepresentation
variable (K : Type) [Field K] [CharZero K]
local instance rootsOriginalPrimeProvider20261018 : Fact (Nat.Prime 19) := ⟨by decide⟩
abbrev Roots := rootsOfUnity 19 K

def rootsZModModule : Module (ZMod 19) (Additive (Roots K)) :=
  AddCommGroup.zmodModule (fun x => by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact x.toMul.property)
local instance rootsOriginalModuleProvider20261018 : Module (ZMod 19) (Additive (Roots K)) := rootsZModModule K

def rootsRepresentation : Representation (ZMod 19) (K ≃ₐ[ℚ] K) (Additive (Roots K)) where
  toFun σ := (restrictRootsOfUnity σ.toRingHom 19).toAdditive.toZModLinearMap 19
  map_one' := by
    apply LinearMap.ext
    intro z
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' σ τ := by
    apply LinearMap.ext
    intro z
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl

theorem rootsRepresentation_apply (σ : K ≃ₐ[ℚ] K) (z : Additive (Roots K)) :
    rootsRepresentation K σ z = Additive.ofMul (restrictRootsOfUnity σ.toRingHom 19 z.toMul) := rfl

variable [IsAlgClosed K]
local instance rootsOriginalNeZeroProvider20261018 : NeZero (19 : K) := ⟨by norm_num⟩

theorem roots_card : Nat.card (Roots K) = 19 := HasEnoughRootsOfUnity.natCard_rootsOfUnity K 19

theorem roots_finrank_one : Module.finrank (ZMod 19) (Additive (Roots K)) = 1 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 19) (V := Additive (Roots K))
  have hc : Nat.card (Additive (Roots K)) = 19 := roots_card K
  simp only [Nat.card_zmod] at h
  apply Nat.pow_right_injective (by decide : 2 ≤ 19)
  exact h.symm.trans hc

end MazurTransfer.NineteenRootsGaloisRepresentation
#print axioms MazurTransfer.NineteenRootsGaloisRepresentation.rootsRepresentation
#print axioms MazurTransfer.NineteenRootsGaloisRepresentation.roots_finrank_one


