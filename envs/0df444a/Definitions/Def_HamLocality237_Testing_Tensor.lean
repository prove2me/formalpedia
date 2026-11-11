-- Prove2me | Definitions.Def_HamLocality237_Testing_Tensor
-- name    : HamLocality237_Testing_Tensor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:30.629197+00:00
-- url     : https://prove2.me/theorems/0c543273-6007-46ff-b1c1-c13e88d627c1
-- title:
--   Completed finite Hilbert tensor powers and one-factor actions
-- statement:
--   For a complex inner-product space $E$ and a natural number $m$, recursively form the algebraic tensor product with $m$ factors and scalar empty tensor product. Its Hilbert completion is
--
--   $$\mathcal H_m(E)=\overline{E\otimes_{\mathrm{alg}}\cdots\otimes_{\mathrm{alg}}E}.$$
--
--   The product vector associated with $u_0,\ldots,u_{m-1}$ is the canonical image of the corresponding pure algebraic tensor. A bounded operator on any selected factor acts by the algebraic tensor map and then its continuous extension to the completion. The file proves
--
--   $$\left\langle\bigotimes_j u_j,\bigotimes_j v_j\right\rangle=\prod_j\langle u_j,v_j\rangle.$$
--
--   This is infrastructure for the input register of Equation (11). It includes no commutation, spectral, or progress facts as fields. The Adversary definition instantiates these completed tensor powers at the actual single input register and labels factors by computational bit strings. Density of algebraic tensors follows from completion, and one-factor actions are genuine continuous extensions.
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), §3.2.1, Eq. (11), p.16 (tensor construction infrastructure). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Mathlib

open scoped TensorProduct
noncomputable section

namespace HamLocality237.Testing

/-- A bundled inner product space, used to build the recursive tensor carrier. -/
structure InnerSpace where
  carrier : Type
  normed : NormedAddCommGroup carrier
  inner : InnerProductSpace ℂ carrier

attribute [instance] InnerSpace.normed InnerSpace.inner

/-- Algebraic precursor of the finite Hilbert tensor product in Eq. (11), p.16. -/
@[reducible] def powerSpace (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] : ℕ → InnerSpace
  | 0 => ⟨ℂ, inferInstance, inferInstance⟩
  | m + 1 => ⟨E ⊗[ℂ] (powerSpace E m).carrier, inferInstance, inferInstance⟩

abbrev AlgebraicPower (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (m : ℕ) :=
  (powerSpace E m).carrier

abbrev HilbertPower (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (m : ℕ) :=
  UniformSpace.Completion (AlgebraicPower E m)

def algebraicProduct {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    (m : ℕ) → (Fin m → E) → AlgebraicPower E m
  | 0, _ => (1 : ℂ)
  | m + 1, u => u 0 ⊗ₜ[ℂ] algebraicProduct m (fun j => u j.succ)

def hilbertProduct {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {m : ℕ} (u : Fin m → E) : HilbertPower E m :=
  (algebraicProduct m u : UniformSpace.Completion (AlgebraicPower E m))

/-- Genuine bounded action on one tensor factor, before completion. -/
def algebraicLift {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    (m : ℕ) → Fin m → (E →L[ℂ] E) →
      (AlgebraicPower E m →L[ℂ] AlgebraicPower E m)
  | 0, j, _ => Fin.elim0 j
  | m + 1, j, a => Fin.cases
      (TensorProduct.mapL a (ContinuousLinearMap.id ℂ (AlgebraicPower E m)))
      (fun i => TensorProduct.mapL (ContinuousLinearMap.id ℂ E) (algebraicLift m i a)) j

def hilbertLift {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {m : ℕ} (j : Fin m) (a : E →L[ℂ] E) : HilbertPower E m →L[ℂ] HilbertPower E m :=
  (algebraicLift m j a).completion

/-- Product inner products: no spectral or progress facts are assumed. -/
theorem algebraicProduct_inner {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (m : ℕ) (u v : Fin m → E) :
    inner ℂ (algebraicProduct m u) (algebraicProduct m v) =
      ∏ j, inner ℂ (u j) (v j) := by
  induction m with
  | zero => simp [algebraicProduct]
  | succ m ih =>
    rw [algebraicProduct, algebraicProduct, TensorProduct.inner_tmul, ih]
    exact (Fin.prod_univ_succ (fun j => inner ℂ (u j) (v j))).symm

theorem hilbertProduct_inner {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {m : ℕ} (u v : Fin m → E) :
    inner ℂ (hilbertProduct u) (hilbertProduct v) = ∏ j, inner ℂ (u j) (v j) := by
  rw [hilbertProduct, hilbertProduct, UniformSpace.Completion.inner_coe]
  exact algebraicProduct_inner m u v

end HamLocality237.Testing


