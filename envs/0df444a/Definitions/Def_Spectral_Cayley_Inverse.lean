-- Prove2me | Definitions.Def_Spectral_Cayley_Inverse
-- name    : Spectral_Cayley_Inverse
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:53:11.192202+00:00
-- url     : https://prove2.me/theorems/e238aab2-2e5c-5345-9494-7a1cf8a64667
-- title:
--   Inverse
-- statement:
--   Definitions and structural lemmas for Inverse, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Inverse.lean

import Definitions.Def_Spectral_Cayley_Unitary
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
def oneSub (U : E →L[ℂ] E) : E →ₗ[ℂ] E :=
  LinearMap.id - U.toLinearMap
def oneAdd (U : E →L[ℂ] E) : E →ₗ[ℂ] E :=
  LinearMap.id + U.toLinearMap
omit [CompleteSpace E] in
theorem oneSub_injective (U : E →L[ℂ] E)
    (hInj : ∀ x, U x = x → x = 0) : Function.Injective (oneSub U) := by
  intro x y hxy
  have hfixed : U (x - y) = x - y := by
    change x - U x = y - U y at hxy
    rw [map_sub]
    rw [sub_eq_sub_iff_add_eq_add] at hxy ⊢
    simpa only [add_comm] using hxy.symm
  exact sub_eq_zero.mp (hInj (x - y) hfixed)
noncomputable def inverseCayley
    (U : E →L[ℂ] E) (_hU : U ∈ unitary (E →L[ℂ] E))
    (hInj : ∀ x, U x = x → x = 0)
    (_hDense : DenseRange (fun x => x - U x)) : E →ₗ.[ℂ] E :=
  let e : E ≃ₗ[ℂ] LinearMap.range (oneSub U) :=
    LinearEquiv.ofInjective (oneSub U) (oneSub_injective U hInj)
  { domain := LinearMap.range (oneSub U)
    toFun := Complex.I • (oneAdd U).comp e.symm.toLinearMap }


