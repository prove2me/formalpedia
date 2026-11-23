-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIff
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:14.020642+00:00
-- url     : https://prove2.me/theorems/aef1916b-66a4-4621-994f-9339ab7319eb
-- title:
--   Preirreducible Space Fibre Hypersurface Spectrum Iff
-- statement:
--   Definitions and structural lemmas for Preirreducible Space Fibre Hypersurface Spectrum Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleSpaceFibreHypersurfaceSpectrumIff.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
noncomputable section
namespace GlobalTheory.FibreHyp
section defs
variable {A : Type} [CommRing A] {σ : Type} (f g : MvPolynomial σ A) (k : Type) [Field k] [Algebra A k]
abbrev Ik : Ideal (MvPolynomial σ k) := Ideal.span {MvPolynomial.map (algebraMap A k) f}
abbrev Lk := Localization.Away (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g))
abbrev LA := Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g)
def rhoK : MvPolynomial σ k →ₐ[k] Lk f g k :=
  (IsScalarTower.toAlgHom k (MvPolynomial σ k ⧸ Ik f k) (Lk f g k)).comp (Ideal.Quotient.mkₐ k (Ik f k))
def rhoA : MvPolynomial σ A →ₐ[A] LA f g :=
  (IsScalarTower.toAlgHom A (MvPolynomial σ A ⧸ Ideal.span {f}) (LA f g)).comp
    (Ideal.Quotient.mkₐ A (Ideal.span {f}))
lemma rhoK_apply (p : MvPolynomial σ k) :
    rhoK f g k p = algebraMap (MvPolynomial σ k ⧸ Ik f k) (Lk f g k) (Ideal.Quotient.mk (Ik f k) p) := rfl
lemma rhoA_apply (p : MvPolynomial σ A) :
    rhoA f g p = algebraMap (MvPolynomial σ A ⧸ Ideal.span {f}) (LA f g) (Ideal.Quotient.mk _ p) := rfl
def fwd0 : MvPolynomial σ A →ₐ[A] Lk f g k :=
  MvPolynomial.aeval (fun i => rhoK f g k (MvPolynomial.X i))
lemma fibreHypersurfaceForwardPolynomial_apply (p : MvPolynomial σ A) :
    fwd0 f g k p = rhoK f g k (MvPolynomial.map (algebraMap A k) p) := by
  rw [fwd0, ← MvPolynomial.aeval_map_algebraMap k]
  conv_rhs => rw [MvPolynomial.aeval_unique (rhoK f g k)]
  rfl
def fwd1 : (MvPolynomial σ A ⧸ Ideal.span {f}) →ₐ[A] Lk f g k :=
  Ideal.Quotient.liftₐ (Ideal.span {f}) (fwd0 f g k) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, fibreHypersurfaceForwardPolynomial_apply f g k f]
    have : rhoK f g k (MvPolynomial.map (algebraMap A k) f) = 0 := by
      simp [rhoK, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
    rw [this, mul_zero])
lemma fibreHypersurfaceForwardQuotient_mk (p : MvPolynomial σ A) :
    fwd1 f g k (Ideal.Quotient.mk _ p) = rhoK f g k (MvPolynomial.map (algebraMap A k) p) := by
  rw [← fibreHypersurfaceForwardPolynomial_apply]; rfl
def fwd2 : LA f g →ₐ[A] Lk f g k :=
  IsLocalization.Away.liftAlgHom (S := LA f g) (Ideal.Quotient.mk (Ideal.span {f}) g) (f := fwd1 f g k) (by
    rw [fibreHypersurfaceForwardQuotient_mk, rhoK_apply]
    exact IsLocalization.Away.algebraMap_isUnit (S := Lk f g k)
      (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g)))
def fwd : k ⊗[A] LA f g →ₐ[k] Lk f g k :=
  Algebra.TensorProduct.lift (Algebra.ofId k _) (fwd2 f g k) (fun _ _ => Commute.all _ _)
def bwd0 : MvPolynomial σ k →ₐ[k] k ⊗[A] LA f g :=
  MvPolynomial.aeval (fun i => Algebra.TensorProduct.includeRight (rhoA f g (MvPolynomial.X i)))
lemma fibreHypersurfaceBackwardPolynomial_map (p : MvPolynomial σ A) :
    bwd0 f g k (MvPolynomial.map (algebraMap A k) p) =
      Algebra.TensorProduct.includeRight (R := A) (A := k) (rhoA f g p) := by
  rw [bwd0, MvPolynomial.aeval_map_algebraMap]
  change _ = ((Algebra.TensorProduct.includeRight (R := A) (A := k)).comp (rhoA f g)) p
  conv_rhs => rw [MvPolynomial.aeval_unique ((Algebra.TensorProduct.includeRight (R := A) (A := k)).comp (rhoA f g))]
  rfl
def bwd1 : (MvPolynomial σ k ⧸ Ik f k) →ₐ[k] k ⊗[A] LA f g :=
  Ideal.Quotient.liftₐ _ (bwd0 f g k) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, fibreHypersurfaceBackwardPolynomial_map]
    have : rhoA f g f = 0 := by
      simp [rhoA, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
    rw [this, map_zero, mul_zero])
lemma fibreHypersurfaceBackwardQuotient_mk (p : MvPolynomial σ k) : bwd1 f g k (Ideal.Quotient.mk _ p) = bwd0 f g k p := rfl
def bwd2 : Lk f g k →ₐ[k] k ⊗[A] LA f g :=
  IsLocalization.Away.liftAlgHom (S := Lk f g k) (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g)) (f := bwd1 f g k) (by
    rw [fibreHypersurfaceBackwardQuotient_mk, fibreHypersurfaceBackwardPolynomial_map, rhoA_apply]
    exact (IsLocalization.Away.algebraMap_isUnit (S := LA f g)
      (Ideal.Quotient.mk (Ideal.span {f}) g)).map (Algebra.TensorProduct.includeRight (R := A) (A := k)))
end defs
end GlobalTheory.FibreHyp


