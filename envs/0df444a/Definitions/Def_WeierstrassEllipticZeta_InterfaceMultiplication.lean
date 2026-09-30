-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_InterfaceMultiplication
-- name    : WeierstrassEllipticZeta_InterfaceMultiplication
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-12T20:53:35.408838+00:00
-- url     : https://prove2.me/theorems/c5cb4ccd-75cd-4dbd-b5ca-0538ecdea489
-- title:
--   Weighted basis and multiplication certificates
-- statement:
--   Let $I$ be a finite contact ideal with monic time polynomial $M$ and triangular coordinates $r$. These certificates record a weighted basis of the quotient, polynomial coordinates, and its regular matrix representation. They include the inherited determinant, characteristic polynomial, trace, rank, Fitting decomposition, generalized inverse, and spectral resolution identities.
--
--   The dimension remains $\deg M$, and the representation remains multiplication in the same quotient algebra. Named projections make individual identities available without unpacking the entire geometric hypothesis.
-- source:
--   Structural reorganization of the exact open frontier WeierstrassEllipticZeta.spectral_factor_nilradical_multiplicity_obstruction, https://prove2.me/theorems/39b4eb14-daee-45cf-8bec-ecd2560be211. The mathematical setting is Senthil Kumar K (2026), Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The interfaces and equivalence proofs are derived here, rather than quoted from the article.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceSpectralResolution

open WeierstrassEllipticZeta TranscendenceTheory
open scoped Pointwise Classical

namespace WeierstrassEllipticZeta.Frontier

/-- Named fields for the inherited MultiplicationCertificate certificate. -/
structure MultiplicationCertificate
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I))
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ) : Prop where
  regular_representation :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    ρ p = Algebra.leftMulMatrix β (Ideal.Quotient.mk I p))
  entries :
    (∀ (p : MvPolynomial (Fin 4) ℂ) (i j : Fin M.natDegree),
    ρ p i j = ((MvPolynomial.aeval (Fin.cons Polynomial.X r) p *
      Polynomial.X ^ j.val) %ₘ M).coeff i.val)
  kernel :
    (∀ p : MvPolynomial (Fin 4) ℂ, ρ p = 0 ↔ p ∈ I)
  polynomial_action :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    ρ p = Polynomial.aeval (ρ (MvPolynomial.X (0 : Fin 4)))
      (MvPolynomial.aeval (Fin.cons Polynomial.X r) p))
  coordinate_charpoly :
    (ρ (MvPolynomial.X (0 : Fin 4))).charpoly = M
  determinant :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    (ρ p).det = ∏ v : V,
      (MvPolynomial.eval v.val p) ^ (3 * U + 1))
  units :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    IsUnit (ρ p) ↔ ∀ v : V, 0 < 3 * U + 1 →
      MvPolynomial.eval v.val p ≠ 0)
  charpoly :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    (ρ p).charpoly = ∏ v : V,
      (Polynomial.X - Polynomial.C (MvPolynomial.eval v.val p)) ^
        (3 * U + 1))
  trace :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    (ρ p).trace = ∑ v : V,
      ((3 * U + 1 : ℕ) : ℂ) * MvPolynomial.eval v.val p)
  spectrum :
    (∀ (p : MvPolynomial (Fin 4) ℂ) (z : ℂ),
    z ∈ _root_.spectrum ℂ (ρ p) ↔ ∃ v : V,
      0 < 3 * U + 1 ∧ z = MvPolynomial.eval v.val p)
  nilpotence :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    IsNilpotent (ρ p) ↔ ∀ v : V, 0 < 3 * U + 1 →
      MvPolynomial.eval v.val p = 0)
  nilpotence_bound :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    (∀ v : V, 0 < 3 * U + 1 → MvPolynomial.eval v.val p = 0) →
      (ρ p) ^ M.natDegree = 0)
  rank_nullity :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I.colon {p}) ≃ₗ[ℂ]
      LinearMap.range (ρ p).mulVecLin) ∧
    (ρ p).rank = Module.finrank ℂ
      (MvPolynomial (Fin 4) ℂ ⧸ I.colon {p}) ∧
    Module.finrank ℂ (LinearMap.ker (ρ p).mulVecLin) =
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
        (I ⊔ Ideal.span {p})) ∧
    (ρ p).rank + Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
      (I ⊔ Ideal.span {p})) = M.natDegree)
  fitting :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    IsCompl (LinearMap.ker ((ρ p) ^ M.natDegree).mulVecLin)
      (LinearMap.range ((ρ p) ^ M.natDegree).mulVecLin) ∧
    Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₗ[ℂ]
      (LinearMap.ker ((ρ p) ^ M.natDegree).mulVecLin) ×
        (LinearMap.range ((ρ p) ^ M.natDegree).mulVecLin)) ∧
    ∀ N : ℕ, M.natDegree ≤ N →
      LinearMap.ker ((ρ p) ^ N).mulVecLin =
        LinearMap.ker ((ρ p) ^ M.natDegree).mulVecLin ∧
      LinearMap.range ((ρ p) ^ N).mulVecLin =
        LinearMap.range ((ρ p) ^ M.natDegree).mulVecLin ∧
      I.colon {p ^ N} = I.colon {p ^ M.natDegree})
  algebra_split :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    let K := I ⊔ Ideal.span {p ^ M.natDegree}
    let R := I.colon {p ^ M.natDegree}
    K ⊔ R = ⊤ ∧ K ⊓ R = I ∧ K * R = I ∧
    Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₐ[ℂ]
      (MvPolynomial (Fin 4) ℂ ⧸ K) ×
        (MvPolynomial (Fin 4) ℂ ⧸ R)) ∧
    (Ideal.Quotient.mk K p) ^ M.natDegree = 0 ∧
    IsUnit (Ideal.Quotient.mk R p) ∧
    ∃ e : MvPolynomial (Fin 4) ℂ,
      e ∈ K ∧ 1 - e ∈ R ∧ e * e - e ∈ I ∧
      K = I ⊔ Ideal.span {e} ∧ R = I ⊔ Ideal.span {1 - e})
  drazin_inverse :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    ∃! b : MvPolynomial (Fin 4) ℂ ⧸ I,
      Ideal.Quotient.mk I p * b * b = b ∧
      (Ideal.Quotient.mk I p) ^ (M.natDegree + 1) * b =
        (Ideal.Quotient.mk I p) ^ M.natDegree ∧
      (let a := Ideal.Quotient.mk I p
       let f := Algebra.lmul ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) a
       let E := Algebra.lmul ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) (a * b)
       IsIdempotentElem (a * b) ∧ IsIdempotentElem E ∧
         LinearMap.ker E = LinearMap.ker (f ^ M.natDegree) ∧
         LinearMap.range E = LinearMap.range (f ^ M.natDegree) ∧
         ∃ h : IsCompl (LinearMap.range (f ^ M.natDegree))
             (LinearMap.ker (f ^ M.natDegree)),
           E = (LinearMap.range (f ^ M.natDegree)).projection
             (LinearMap.ker (f ^ M.natDegree)) h))
  multiplicative_inverse :
    (∃! G : MvPolynomial (Fin 4) ℂ →*₀
      (MvPolynomial (Fin 4) ℂ ⧸ I),
    ∀ p : MvPolynomial (Fin 4) ℂ,
      Ideal.Quotient.mk I p * G p * G p = G p ∧
      (Ideal.Quotient.mk I p) ^ (M.natDegree + 1) * G p =
        (Ideal.Quotient.mk I p) ^ M.natDegree ∧
      (G p = 0 ↔ p ∈ I.radical) ∧
      (IsUnit (Ideal.Quotient.mk I p) ↔
        Ideal.Quotient.mk I p * G p = 1) ∧
      ∀ r : MvPolynomial (Fin 4) ℂ,
        Ideal.Quotient.mk I r = G p →
          (∀ v : V,
            MvPolynomial.eval v.val r = (MvPolynomial.eval v.val p)⁻¹ ∧
            MvPolynomial.eval v.val (p * r) =
              if MvPolynomial.eval v.val p = 0 then 0 else 1) ∧
          (ρ (p * r)).rank = (3 * U + 1) *
            (Finset.univ.filter (fun v : V =>
              MvPolynomial.eval v.val p ≠ 0)).card ∧
          Module.finrank ℂ (LinearMap.ker (ρ (p * r)).mulVecLin) =
            M.natDegree - (3 * U + 1) *
              (Finset.univ.filter (fun v : V =>
                MvPolynomial.eval v.val p ≠ 0)).card)
  stable_rank :
    (∀ (p : MvPolynomial (Fin 4) ℂ) (N : ℕ), M.natDegree ≤ N →
    ((ρ p) ^ N).rank = (3 * U + 1) *
      (Finset.univ.filter (fun v : V =>
        MvPolynomial.eval v.val p ≠ 0)).card ∧
    Module.finrank ℂ (LinearMap.ker ((ρ p) ^ N).mulVecLin) =
      M.natDegree - (3 * U + 1) *
        (Finset.univ.filter (fun v : V =>
          MvPolynomial.eval v.val p ≠ 0)).card)
  eigenspace_dimension :
    (∀ (p : MvPolynomial (Fin 4) ℂ) (z : ℂ),
    Module.finrank ℂ
      (Module.End.maxGenEigenspace (ρ p).mulVecLin z) =
        (3 * U + 1) * (Finset.univ.filter (fun v : V =>
          MvPolynomial.eval v.val p = z)).card ∧
    ∀ N : ℕ, M.natDegree ≤ N →
      Module.finrank ℂ
        (Module.End.genEigenspace (ρ p).mulVecLin z N) =
          (3 * U + 1) * (Finset.univ.filter (fun v : V =>
            MvPolynomial.eval v.val p = z)).card)
  spectral_decomposition :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    let W := Finset.univ.image (fun v : V => MvPolynomial.eval v.val p)
    DirectSum.IsInternal (fun z : W =>
      Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) ∧
    ∃ e : (∀ z : W,
        Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) ≃ₗ[ℂ]
          (Fin M.natDegree → ℂ),
      SpectralDecomposition U V I M β ρ p W e)

theorem MultiplicationCertificate.iff_fields
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I))
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ) :
    MultiplicationCertificate U V I M r β ρ ↔
      (∀ p : MvPolynomial (Fin 4) ℂ,
        ρ p = Algebra.leftMulMatrix β (Ideal.Quotient.mk I p)) ∧
      (∀ (p : MvPolynomial (Fin 4) ℂ) (i j : Fin M.natDegree),
        ρ p i j = ((MvPolynomial.aeval (Fin.cons Polynomial.X r) p *
          Polynomial.X ^ j.val) %ₘ M).coeff i.val) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ, ρ p = 0 ↔ p ∈ I) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        ρ p = Polynomial.aeval (ρ (MvPolynomial.X (0 : Fin 4)))
          (MvPolynomial.aeval (Fin.cons Polynomial.X r) p)) ∧
      (ρ (MvPolynomial.X (0 : Fin 4))).charpoly = M ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        (ρ p).det = ∏ v : V,
          (MvPolynomial.eval v.val p) ^ (3 * U + 1)) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        IsUnit (ρ p) ↔ ∀ v : V, 0 < 3 * U + 1 →
          MvPolynomial.eval v.val p ≠ 0) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        (ρ p).charpoly = ∏ v : V,
          (Polynomial.X - Polynomial.C (MvPolynomial.eval v.val p)) ^
            (3 * U + 1)) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        (ρ p).trace = ∑ v : V,
          ((3 * U + 1 : ℕ) : ℂ) * MvPolynomial.eval v.val p) ∧
      (∀ (p : MvPolynomial (Fin 4) ℂ) (z : ℂ),
        z ∈ _root_.spectrum ℂ (ρ p) ↔ ∃ v : V,
          0 < 3 * U + 1 ∧ z = MvPolynomial.eval v.val p) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        IsNilpotent (ρ p) ↔ ∀ v : V, 0 < 3 * U + 1 →
          MvPolynomial.eval v.val p = 0) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        (∀ v : V, 0 < 3 * U + 1 → MvPolynomial.eval v.val p = 0) →
          (ρ p) ^ M.natDegree = 0) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I.colon {p}) ≃ₗ[ℂ]
          LinearMap.range (ρ p).mulVecLin) ∧
        (ρ p).rank = Module.finrank ℂ
          (MvPolynomial (Fin 4) ℂ ⧸ I.colon {p}) ∧
        Module.finrank ℂ (LinearMap.ker (ρ p).mulVecLin) =
          Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
            (I ⊔ Ideal.span {p})) ∧
        (ρ p).rank + Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
          (I ⊔ Ideal.span {p})) = M.natDegree) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        IsCompl (LinearMap.ker ((ρ p) ^ M.natDegree).mulVecLin)
          (LinearMap.range ((ρ p) ^ M.natDegree).mulVecLin) ∧
        Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₗ[ℂ]
          (LinearMap.ker ((ρ p) ^ M.natDegree).mulVecLin) ×
            (LinearMap.range ((ρ p) ^ M.natDegree).mulVecLin)) ∧
        ∀ N : ℕ, M.natDegree ≤ N →
          LinearMap.ker ((ρ p) ^ N).mulVecLin =
            LinearMap.ker ((ρ p) ^ M.natDegree).mulVecLin ∧
          LinearMap.range ((ρ p) ^ N).mulVecLin =
            LinearMap.range ((ρ p) ^ M.natDegree).mulVecLin ∧
          I.colon {p ^ N} = I.colon {p ^ M.natDegree}) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        let K := I ⊔ Ideal.span {p ^ M.natDegree}
        let R := I.colon {p ^ M.natDegree}
        K ⊔ R = ⊤ ∧ K ⊓ R = I ∧ K * R = I ∧
        Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₐ[ℂ]
          (MvPolynomial (Fin 4) ℂ ⧸ K) ×
            (MvPolynomial (Fin 4) ℂ ⧸ R)) ∧
        (Ideal.Quotient.mk K p) ^ M.natDegree = 0 ∧
        IsUnit (Ideal.Quotient.mk R p) ∧
        ∃ e : MvPolynomial (Fin 4) ℂ,
          e ∈ K ∧ 1 - e ∈ R ∧ e * e - e ∈ I ∧
          K = I ⊔ Ideal.span {e} ∧ R = I ⊔ Ideal.span {1 - e}) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        ∃! b : MvPolynomial (Fin 4) ℂ ⧸ I,
          Ideal.Quotient.mk I p * b * b = b ∧
          (Ideal.Quotient.mk I p) ^ (M.natDegree + 1) * b =
            (Ideal.Quotient.mk I p) ^ M.natDegree ∧
          (let a := Ideal.Quotient.mk I p
           let f := Algebra.lmul ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) a
           let E := Algebra.lmul ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) (a * b)
           IsIdempotentElem (a * b) ∧ IsIdempotentElem E ∧
             LinearMap.ker E = LinearMap.ker (f ^ M.natDegree) ∧
             LinearMap.range E = LinearMap.range (f ^ M.natDegree) ∧
             ∃ h : IsCompl (LinearMap.range (f ^ M.natDegree))
                 (LinearMap.ker (f ^ M.natDegree)),
               E = (LinearMap.range (f ^ M.natDegree)).projection
                 (LinearMap.ker (f ^ M.natDegree)) h)) ∧
      (∃! G : MvPolynomial (Fin 4) ℂ →*₀
          (MvPolynomial (Fin 4) ℂ ⧸ I),
        ∀ p : MvPolynomial (Fin 4) ℂ,
          Ideal.Quotient.mk I p * G p * G p = G p ∧
          (Ideal.Quotient.mk I p) ^ (M.natDegree + 1) * G p =
            (Ideal.Quotient.mk I p) ^ M.natDegree ∧
          (G p = 0 ↔ p ∈ I.radical) ∧
          (IsUnit (Ideal.Quotient.mk I p) ↔
            Ideal.Quotient.mk I p * G p = 1) ∧
          ∀ r : MvPolynomial (Fin 4) ℂ,
            Ideal.Quotient.mk I r = G p →
              (∀ v : V,
                MvPolynomial.eval v.val r = (MvPolynomial.eval v.val p)⁻¹ ∧
                MvPolynomial.eval v.val (p * r) =
                  if MvPolynomial.eval v.val p = 0 then 0 else 1) ∧
              (ρ (p * r)).rank = (3 * U + 1) *
                (Finset.univ.filter (fun v : V =>
                  MvPolynomial.eval v.val p ≠ 0)).card ∧
              Module.finrank ℂ (LinearMap.ker (ρ (p * r)).mulVecLin) =
                M.natDegree - (3 * U + 1) *
                  (Finset.univ.filter (fun v : V =>
                    MvPolynomial.eval v.val p ≠ 0)).card) ∧
      (∀ (p : MvPolynomial (Fin 4) ℂ) (N : ℕ), M.natDegree ≤ N →
        ((ρ p) ^ N).rank = (3 * U + 1) *
          (Finset.univ.filter (fun v : V =>
            MvPolynomial.eval v.val p ≠ 0)).card ∧
        Module.finrank ℂ (LinearMap.ker ((ρ p) ^ N).mulVecLin) =
          M.natDegree - (3 * U + 1) *
            (Finset.univ.filter (fun v : V =>
              MvPolynomial.eval v.val p ≠ 0)).card) ∧
      (∀ (p : MvPolynomial (Fin 4) ℂ) (z : ℂ),
        Module.finrank ℂ
          (Module.End.maxGenEigenspace (ρ p).mulVecLin z) =
            (3 * U + 1) * (Finset.univ.filter (fun v : V =>
              MvPolynomial.eval v.val p = z)).card ∧
        ∀ N : ℕ, M.natDegree ≤ N →
          Module.finrank ℂ
            (Module.End.genEigenspace (ρ p).mulVecLin z N) =
              (3 * U + 1) * (Finset.univ.filter (fun v : V =>
                MvPolynomial.eval v.val p = z)).card) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        let W := Finset.univ.image (fun v : V => MvPolynomial.eval v.val p)
        DirectSum.IsInternal (fun z : W =>
          Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) ∧
        ∃ e : (∀ z : W,
            Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) ≃ₗ[ℂ]
              (Fin M.natDegree → ℂ),
          SpectralDecomposition U V I M β ρ p W e) := by
  constructor
  · intro h
    exact ⟨h.regular_representation, h.entries, h.kernel, h.polynomial_action, h.coordinate_charpoly, h.determinant, h.units, h.charpoly, h.trace, h.spectrum, h.nilpotence, h.nilpotence_bound, h.rank_nullity, h.fitting, h.algebra_split, h.drazin_inverse, h.multiplicative_inverse, h.stable_rank, h.eigenspace_dimension, h.spectral_decomposition⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩

/-- Named fields for the inherited WeightedBasisCertificate certificate. -/
structure WeightedBasisCertificate
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ)
    (q : MvPolynomial (Fin 4) ℂ)
    (T : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I)) : Prop where
  vectors :
    (∀ i : Fin M.natDegree,
    β i = Ideal.Quotient.mk I ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q) ∧
    ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q).totalDegree ≤
      M.natDegree - 1 + q.totalDegree)
  coordinates :
    (∀ (p : MvPolynomial (Fin 4) ℂ) (i : Fin M.natDegree),
    β.repr (Ideal.Quotient.mk I p) i = (T p).coeff i.val)
  reconstruction :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    Ideal.Quotient.mk I p = ∑ i : Fin M.natDegree,
      (T p).coeff i.val • Ideal.Quotient.mk I
        ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q))
  dimension :
    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) = M.natDegree
  multiplication :
    ∃ ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ]
      Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ,
    MultiplicationCertificate U V I M r β ρ

theorem WeightedBasisCertificate.iff_fields
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ)
    (q : MvPolynomial (Fin 4) ℂ)
    (T : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I)) :
    WeightedBasisCertificate U V I M r q T β ↔
      (∀ i : Fin M.natDegree,
        β i = Ideal.Quotient.mk I ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q) ∧
        ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q).totalDegree ≤
          M.natDegree - 1 + q.totalDegree) ∧
      (∀ (p : MvPolynomial (Fin 4) ℂ) (i : Fin M.natDegree),
        β.repr (Ideal.Quotient.mk I p) i = (T p).coeff i.val) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        Ideal.Quotient.mk I p = ∑ i : Fin M.natDegree,
          (T p).coeff i.val • Ideal.Quotient.mk I
            ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q)) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) = M.natDegree ∧
      ∃ ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ]
          Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ,
        MultiplicationCertificate U V I M r β ρ := by
  constructor
  · intro h
    exact ⟨h.vectors, h.coordinates, h.reconstruction, h.dimension, h.multiplication⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨h0, h1, h2, h3, h4⟩

end WeierstrassEllipticZeta.Frontier


