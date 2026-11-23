-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsHomDivMulRefine
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsHomDivMulRefine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:26:21.633587+00:00
-- url     : https://prove2.me/theorems/384f2362-9240-44a7-864f-62dd661e1020
-- title:
--   Exists Hom Div Mul Refine
-- statement:
--   Definitions and structural lemmas for Exists Hom Div Mul Refine, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsHomDivMulRefine.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
namespace QuadRefinement
section Additive
variable {O Y M : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y]
  [AddCommGroup M]
def addRefine (τ : Y →+ Y →+ M) (w : O) (y : Y) : M := τ y (w • y)
variable {τ : Y →+ Y →+ M} {w : O}
def subHom {ψ ψ' : Y → M} (hψ : ∀ y y', ψ (y + y') = ψ y + ψ y' + τ y y')
    (hψ' : ∀ y y', ψ' (y + y') = ψ' y + ψ' y' + τ y y') : Y →+ M :=
  AddMonoidHom.mk' (fun y => ψ y - ψ' y) fun y y' => by
    rw [hψ, hψ']; abel
@[simp] theorem subHom_apply {ψ ψ' : Y → M} (hψ : ∀ y y', ψ (y + y') = ψ y + ψ y' + τ y y')
    (hψ' : ∀ y y', ψ' (y + y') = ψ' y + ψ' y' + τ y y') (y : Y) :
    subHom hψ hψ' y = ψ y - ψ' y := rfl
end Additive
section Multiplicative
variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A]
def mulRefine (τ : Y →+ Y →+ Additive A) (w : O) (y : Y) : A := (τ y (w • y)).toMul
variable {τ : Y →+ Y →+ Additive A} {w : O}
end Multiplicative
section HalfElement
variable {K : Type*} [Field K] [CharZero K] [StarRing K] {d : ℤ} {s : K}
end HalfElement
section Example
open QuadraticAlgebra
def traceFormSeven :
    QuadraticAlgebra ℤ (-2) 1 →+ QuadraticAlgebra ℤ (-2) 1 →+ Additive (Multiplicative ℤ) :=
  AddMonoidHom.mk'
    (fun y => AddMonoidHom.mk'
      (fun y' => Additive.ofMul (Multiplicative.ofAdd
        (2 * y.re * y'.re + y.re * y'.im + y.im * y'.re + 4 * y.im * y'.im)))
      fun a b => by
        rw [← ofMul_mul, ← ofAdd_add]; congr 2; simp only [re_add, im_add]; ring)
    fun a b => by
      ext y'
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [← ofMul_mul, ← ofAdd_add]; simp only [re_add, im_add]; ring_nf
end Example
end QuadRefinement
end GlobalTheory


