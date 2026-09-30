-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_InterfaceSpectralResolution
-- name    : WeierstrassEllipticZeta_InterfaceSpectralResolution
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-12T20:52:48.938974+00:00
-- url     : https://prove2.me/theorems/d9d31aa4-6d9e-4d83-9789-43adb50e72db
-- title:
--   Spectral projectors and product certificates
-- statement:
--   For multiplication by a polynomial on a finite contact quotient, these certificates record the generalized eigenspace decomposition, its commuting projections, the corresponding orthogonal idempotents, and the quotient's product decomposition. The projections and idempotents sum to the identity. Each component has a named individual factor certificate.
--
--   The fields preserve the original witnesses and coordinate identities; the accompanying equivalences are their constructor APIs.
-- source:
--   Structural reorganization of the exact open frontier WeierstrassEllipticZeta.spectral_factor_nilradical_multiplicity_obstruction, https://prove2.me/theorems/39b4eb14-daee-45cf-8bec-ecd2560be211. The mathematical setting is Senthil Kumar K (2026), Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The interfaces and equivalence proofs are derived here, rather than quoted from the article.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceSpectralFactor

open WeierstrassEllipticZeta TranscendenceTheory
open scoped Pointwise Classical

namespace WeierstrassEllipticZeta.Frontier

/-- Named fields for the inherited SpectralProduct certificate. -/
structure SpectralProduct
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I))
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ)
    (p : MvPolynomial (Fin 4) ℂ)
    (W : Finset ℂ)
    (ε : W → MvPolynomial (Fin 4) ℂ ⧸ I)
    (Φ : (MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₐ[ℂ] (∀ z : W, ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸ Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))))) : Prop where
  quotient_coordinates :
    (∀ a z, Φ a z =
    Ideal.Quotient.mk (Ideal.span {1 - ε z}) a)
  idempotent_coordinates :
    (∀ z w, Φ (ε w) z = if z = w then 1 else 0)
  factors :
    ∀ z : W, ∃ ψ : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
        Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) ≃ₗ[ℂ]
      Module.End.maxGenEigenspace (ρ p).mulVecLin z.val,
    SpectralFactor U V I M β ρ p W ε z ψ

theorem SpectralProduct.iff_fields
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I))
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ)
    (p : MvPolynomial (Fin 4) ℂ)
    (W : Finset ℂ)
    (ε : W → MvPolynomial (Fin 4) ℂ ⧸ I)
    (Φ : (MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₐ[ℂ] (∀ z : W, ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸ Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))))) :
    SpectralProduct U V I M β ρ p W ε Φ ↔
      (∀ a z, Φ a z =
        Ideal.Quotient.mk (Ideal.span {1 - ε z}) a) ∧
      (∀ z w, Φ (ε w) z = if z = w then 1 else 0) ∧
      ∀ z : W, ∃ ψ : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
            Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) ≃ₗ[ℂ]
          Module.End.maxGenEigenspace (ρ p).mulVecLin z.val,
        SpectralFactor U V I M β ρ p W ε z ψ := by
  constructor
  · intro h
    exact ⟨h.quotient_coordinates, h.idempotent_coordinates, h.factors⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, h1, h2⟩

/-- Named fields for the inherited SpectralIdempotents certificate. -/
structure SpectralIdempotents
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I))
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ)
    (p : MvPolynomial (Fin 4) ℂ)
    (W : Finset ℂ)
    (Pr : W → Module.End ℂ (Fin M.natDegree → ℂ))
    (ε : W → MvPolynomial (Fin 4) ℂ ⧸ I) : Prop where
  matrix_action :
    (∀ z, (Algebra.leftMulMatrix β (ε z)).mulVecLin = Pr z)
  formula :
    (∀ z, ε z = β.equivFun.symm (Pr z (β.equivFun 1)))
  idempotent :
    (∀ z, IsIdempotentElem (ε z))
  orthogonal :
    (∀ z w, z ≠ w → ε z * ε w = 0)
  sum_one :
    (∑ z, ε z) = 1
  kernel :
    (∀ z (a : MvPolynomial (Fin 4) ℂ ⧸ I),
    a ∈ Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)) ↔ ε z * a = 0)
  product :
    ∃ Φ : (MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₐ[ℂ]
      (∀ z : W, (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
        Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
    SpectralProduct U V I M β ρ p W ε Φ

theorem SpectralIdempotents.iff_fields
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I))
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ)
    (p : MvPolynomial (Fin 4) ℂ)
    (W : Finset ℂ)
    (Pr : W → Module.End ℂ (Fin M.natDegree → ℂ))
    (ε : W → MvPolynomial (Fin 4) ℂ ⧸ I) :
    SpectralIdempotents U V I M β ρ p W Pr ε ↔
      (∀ z, (Algebra.leftMulMatrix β (ε z)).mulVecLin = Pr z) ∧
      (∀ z, ε z = β.equivFun.symm (Pr z (β.equivFun 1))) ∧
      (∀ z, IsIdempotentElem (ε z)) ∧
      (∀ z w, z ≠ w → ε z * ε w = 0) ∧
      (∑ z, ε z) = 1 ∧
      (∀ z (a : MvPolynomial (Fin 4) ℂ ⧸ I),
        a ∈ Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)) ↔ ε z * a = 0) ∧
      ∃ Φ : (MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₐ[ℂ]
          (∀ z : W, (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
            Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
        SpectralProduct U V I M β ρ p W ε Φ := by
  constructor
  · intro h
    exact ⟨h.matrix_action, h.formula, h.idempotent, h.orthogonal, h.sum_one, h.kernel, h.product⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

/-- Named fields for the inherited SpectralProjectors certificate. -/
structure SpectralProjectors
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I))
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ)
    (p : MvPolynomial (Fin 4) ℂ)
    (W : Finset ℂ)
    (e : (∀ z : W, Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) ≃ₗ[ℂ] (Fin M.natDegree → ℂ))
    (Pr : W → Module.End ℂ (Fin M.natDegree → ℂ)) : Prop where
  coordinates :
    (∀ z x, Pr z x = (e.symm x z : Fin M.natDegree → ℂ))
  idempotent :
    (∀ z, IsIdempotentElem (Pr z))
  orthogonal :
    (∀ z w, z ≠ w → Pr z * Pr w = 0)
  sum_one :
    (∑ z, Pr z) = 1
  range :
    (∀ z, LinearMap.range (Pr z) =
    Module.End.maxGenEigenspace (ρ p).mulVecLin z.val)
  commutes :
    (∀ (q : MvPolynomial (Fin 4) ℂ) (z : W),
    Commute (Pr z) (ρ q).mulVecLin)
  idempotents :
    ∃ ε : W → MvPolynomial (Fin 4) ℂ ⧸ I,
    SpectralIdempotents U V I M β ρ p W Pr ε

theorem SpectralProjectors.iff_fields
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I))
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ)
    (p : MvPolynomial (Fin 4) ℂ)
    (W : Finset ℂ)
    (e : (∀ z : W, Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) ≃ₗ[ℂ] (Fin M.natDegree → ℂ))
    (Pr : W → Module.End ℂ (Fin M.natDegree → ℂ)) :
    SpectralProjectors U V I M β ρ p W e Pr ↔
      (∀ z x, Pr z x = (e.symm x z : Fin M.natDegree → ℂ)) ∧
      (∀ z, IsIdempotentElem (Pr z)) ∧
      (∀ z w, z ≠ w → Pr z * Pr w = 0) ∧
      (∑ z, Pr z) = 1 ∧
      (∀ z, LinearMap.range (Pr z) =
        Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) ∧
      (∀ (q : MvPolynomial (Fin 4) ℂ) (z : W),
        Commute (Pr z) (ρ q).mulVecLin) ∧
      ∃ ε : W → MvPolynomial (Fin 4) ℂ ⧸ I,
        SpectralIdempotents U V I M β ρ p W Pr ε := by
  constructor
  · intro h
    exact ⟨h.coordinates, h.idempotent, h.orthogonal, h.sum_one, h.range, h.commutes, h.idempotents⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

/-- Named fields for the inherited SpectralDecomposition certificate. -/
structure SpectralDecomposition
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I))
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ)
    (p : MvPolynomial (Fin 4) ℂ)
    (W : Finset ℂ)
    (e : (∀ z : W, Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) ≃ₗ[ℂ] (Fin M.natDegree → ℂ)) : Prop where
  sum_formula :
    (∀ x, e x = ∑ z : W, (x z : Fin M.natDegree → ℂ))
  projectors :
    ∃ Pr : W → Module.End ℂ (Fin M.natDegree → ℂ),
    SpectralProjectors U V I M β ρ p W e Pr

theorem SpectralDecomposition.iff_fields
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I))
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ)
    (p : MvPolynomial (Fin 4) ℂ)
    (W : Finset ℂ)
    (e : (∀ z : W, Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) ≃ₗ[ℂ] (Fin M.natDegree → ℂ)) :
    SpectralDecomposition U V I M β ρ p W e ↔
      (∀ x, e x = ∑ z : W, (x z : Fin M.natDegree → ℂ)) ∧
      ∃ Pr : W → Module.End ℂ (Fin M.natDegree → ℂ),
        SpectralProjectors U V I M β ρ p W e Pr := by
  constructor
  · intro h
    exact ⟨h.sum_formula, h.projectors⟩
  · rintro ⟨h0, h1⟩
    exact ⟨h0, h1⟩

end WeierstrassEllipticZeta.Frontier


