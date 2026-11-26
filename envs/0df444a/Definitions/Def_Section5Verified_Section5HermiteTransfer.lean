-- Prove2me | Definitions.Def_Section5Verified_Section5HermiteTransfer
-- name    : Section5Verified_Section5HermiteTransfer
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T12:17:52.16465+00:00
-- url     : https://prove2.me/theorems/727f429f-8ad9-4927-8842-37f1354332ed
-- title:
--   Section5HermiteTransfer — verified interface
-- statement:
--   Genuine rectangular tensor powers on finite Euclidean spaces, product-state action, operator-norm hybrid bound, adjoint stability, and tensor inverse coefficient error transfer.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5HermiteTransfer; mechanically extracted with exact Lean declaration spans.

import Mathlib
section
set_option autoImplicit false

/-!
The operator-norm transfer in the proof of Theorem 5.2, Eqs. (162)--(166).
The synthesis maps have the clean ancilla subspace as their domain; taking
their adjoints therefore gives the projected inverse coefficients.
-/















noncomputable def section5_isometry_transport
    {E E' F F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup F'] [NormedSpace ℂ F']
    (e : E ≃ₗᵢ[ℂ] E') (f : F ≃ₗᵢ[ℂ] F') (A : E →L[ℂ] F) : E' →L[ℂ] F' :=
  f.toLinearIsometry.toContinuousLinearMap ∘L A ∘L
    e.symm.toLinearIsometry.toContinuousLinearMap





noncomputable def section5_tensor_matrix
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (B : EuclideanSpace ℂ γ →L[ℂ] EuclideanSpace ℂ δ) :
    EuclideanSpace ℂ (α×γ) →L[ℂ] EuclideanSpace ℂ (β×δ) :=
  section5_isometry_transport
    ((EuclideanSpace.basisFun α ℂ).tensorProduct (EuclideanSpace.basisFun γ ℂ)).repr
    ((EuclideanSpace.basisFun β ℂ).tensorProduct (EuclideanSpace.basisFun δ ℂ)).repr
    (TensorProduct.mapL A B)









def section5_tuple_cons_equiv (α : Type*) (n : ℕ) :
    (Fin (n+1) → α) ≃ α×(Fin n → α) where
  toFun x := (x 0, Fin.tail x)
  invFun p := Fin.cons p.1 p.2
  left_inv := Fin.cons_self_tail
  right_inv p := by apply Prod.ext <;> simp

def section5_empty_tuple_equiv (α β : Type*) : (Fin 0 → α) ≃ (Fin 0 → β) where
  toFun _ := Fin.elim0
  invFun _ := Fin.elim0
  left_inv x := by funext i; exact Fin.elim0 i
  right_inv x := by funext i; exact Fin.elim0 i

noncomputable def section5_tensor_cons
    {α β : Type*} [Fintype α] [Fintype β] (n : ℕ)
    (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (B : EuclideanSpace ℂ (Fin n → α) →L[ℂ] EuclideanSpace ℂ (Fin n → β)) :
    EuclideanSpace ℂ (Fin (n+1) → α) →L[ℂ] EuclideanSpace ℂ (Fin (n+1) → β) :=
  section5_isometry_transport
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (section5_tuple_cons_equiv α n).symm)
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (section5_tuple_cons_equiv β n).symm)
    (section5_tensor_matrix A B)









noncomputable def section5_tensor_power {α β : Type*} [Fintype α] [Fintype β]
    (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β) :
    (n : ℕ) → EuclideanSpace ℂ (Fin n → α) →L[ℂ] EuclideanSpace ℂ (Fin n → β)
  | 0 => (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (section5_empty_tuple_equiv α β)).toLinearIsometry.toContinuousLinearMap
  | n+1 => section5_tensor_cons n A (section5_tensor_power A n)









end


