-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
-- name    : ReciprocityTheory_DualLattices_RidConvolutionDerivation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:48.540175+00:00
-- url     : https://prove2.me/theorems/b89dc1fc-f96b-4ce3-8a92-742dfc861433
-- title:
--   Rid Convolution Derivation
-- statement:
--   Definitions and structural lemmas for Rid Convolution Derivation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
namespace ReciprocityTheory.PGsh
section Bialg
variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
def IsPtDer (δ : A →ₗ[R] R) : Prop :=
  ∀ f g : A, δ (f * g) = Coalgebra.counit (R := R) f * δ g + Coalgebra.counit (R := R) g * δ f
def convD (δ : A →ₗ[R] R) : A →ₗ[R] A :=
  (TensorProduct.rid R A).toLinearMap ∘ₗ δ.lTensor A ∘ₗ Coalgebra.comul
end Bialg
section Chain
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
end Chain
section Coeff
variable {R : Type*} [CommRing R] {d p : ℕ}
def LowRed (p m : ℕ) (P : MvPolynomial (Fin d) R) : Prop :=
  ∀ β : Fin d →₀ ℕ, (∀ j, β j < p) → β.degree < m → coeff β P = 0
end Coeff
section Bialg2
variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
end Bialg2
section Core
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {d p : ℕ}
end Core
end ReciprocityTheory.PGsh


