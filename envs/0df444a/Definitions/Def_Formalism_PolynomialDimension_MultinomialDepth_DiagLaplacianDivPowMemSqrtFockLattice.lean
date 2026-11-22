-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
-- name    : Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:36.997474+00:00
-- url     : https://prove2.me/theorems/d517fb05-a29a-4c5d-99d2-e19ce13779ea
-- title:
--   Diag Laplacian Div Pow Mem Sqrt Fock Lattice
-- statement:
--   Definitions and structural lemmas for Diag Laplacian Div Pow Mem Sqrt Fock Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/DiagLaplacianDivPowMemSqrtFockLattice.lean

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.CountingSumsFrames
section DivPow
variable {K E : Type*} [Field K] [CharZero K] [Ring E] [Algebra K E]
def stabilizerSubsemiring {V : Type*} [AddCommGroup V] [Module K V] (L : Set V)
    (hadd : ∀ f g, f ∈ L → g ∈ L → f + g ∈ L) (h0 : (0 : V) ∈ L) : Subsemiring (Module.End K V) where
  carrier := {T | ∀ f ∈ L, T f ∈ L}
  mul_mem' := by
    intro S T hS hT f hf
    exact hS _ (hT _ hf)
  one_mem' := by
    intro f hf
    exact hf
  add_mem' := by
    intro S T hS hT f hf
    exact hadd _ _ (hS _ hf) (hT _ hf)
  zero_mem' := by
    intro f _
    exact h0
end DivPow
section Coeff
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
def h3s (i : Fin k) (n : ℕ) : XY k →₀ ℕ := Finsupp.single (Sum.inl i) n + Finsupp.single (Sum.inr i) n
def h3e (K : Type) [Field K] {k : ℕ} (i : Fin k) : Module.End K (PolXY K k) :=
  LinearMap.mulLeft K (X (Sum.inl i) * X (Sum.inr i))
def h3d (K : Type) [Field K] {k : ℕ} (i : Fin k) : Module.End K (PolXY K k) :=
  (pderiv (R := K) (Sum.inl i : XY k)).toLinearMap ∘ₗ (pderiv (R := K) (Sum.inr i : XY k)).toLinearMap
end Coeff
section Std
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
end Std
section SubstGL
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
end SubstGL
section Proj
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
end Proj
end Formalism.CountingSumsFrames


