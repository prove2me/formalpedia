-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_InterfaceDivision
-- name    : WeierstrassEllipticZeta_InterfaceDivision
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-12T20:54:41.979097+00:00
-- url     : https://prove2.me/theorems/bcfc4018-f460-439a-a71d-fd60efd62984
-- title:
--   Bounded division and inverse certificates
-- statement:
--   At a positive derivative prefix whose ideal is the unit ideal, a bounded generic combination is invertible modulo the contact ideal. These certificates record its chosen index, its polynomial inverse, the unique bounded division operator, and the resulting weighted basis.
--
--   The original degree bounds and uniqueness quantifiers are preserved. The constructor equivalences expose exactly the former conjunctions, while applications use their named fields.
-- source:
--   Structural reorganization of the exact open frontier WeierstrassEllipticZeta.spectral_factor_nilradical_multiplicity_obstruction, https://prove2.me/theorems/39b4eb14-daee-45cf-8bec-ecd2560be211. The mathematical setting is Senthil Kumar K (2026), Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The interfaces and equivalence proofs are derived here, rather than quoted from the article.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceMultiplication

open WeierstrassEllipticZeta TranscendenceTheory
open scoped Pointwise Classical

namespace WeierstrassEllipticZeta.Frontier

/-- Named fields for the inherited DivisionCertificate certificate. -/
structure DivisionCertificate
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ)
    (q : MvPolynomial (Fin 4) ℂ)
    (b : Polynomial ℂ)
    (T : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ) : Prop where
  normal_form :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    T p = (MvPolynomial.aeval (Fin.cons Polynomial.X r)
      (p * Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b)) %ₘ M ∧
    (T p).degree < (M.natDegree : ℕ) ∧
    (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (T p)).totalDegree ≤
      M.natDegree - 1 ∧
    p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T p) * q ∈ I ∧
    (p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T p) * q).totalDegree ≤
      max p.totalDegree (M.natDegree - 1 + q.totalDegree) ∧
    (∀ b' : Polynomial ℂ, b'.degree < (M.natDegree : ℕ) →
      (p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b' * q ∈ I ↔ b' = T p)))
  kernel :
    (∀ p : MvPolynomial (Fin 4) ℂ, T p = 0 ↔ p ∈ I)
  unique :
    (∀ T' : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ,
    (∀ p : MvPolynomial (Fin 4) ℂ, (T' p).degree < (M.natDegree : ℕ) ∧
      p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T' p) * q ∈ I) → T' = T)
  basis :
    ∃ β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I),
    WeightedBasisCertificate U V I M r q T β

theorem DivisionCertificate.iff_fields
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ)
    (q : MvPolynomial (Fin 4) ℂ)
    (b : Polynomial ℂ)
    (T : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ) :
    DivisionCertificate U V I M r q b T ↔
      (∀ p : MvPolynomial (Fin 4) ℂ,
        T p = (MvPolynomial.aeval (Fin.cons Polynomial.X r)
          (p * Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b)) %ₘ M ∧
        (T p).degree < (M.natDegree : ℕ) ∧
        (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (T p)).totalDegree ≤
          M.natDegree - 1 ∧
        p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T p) * q ∈ I ∧
        (p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T p) * q).totalDegree ≤
          max p.totalDegree (M.natDegree - 1 + q.totalDegree) ∧
        (∀ b' : Polynomial ℂ, b'.degree < (M.natDegree : ℕ) →
          (p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b' * q ∈ I ↔ b' = T p))) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ, T p = 0 ↔ p ∈ I) ∧
      (∀ T' : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ,
        (∀ p : MvPolynomial (Fin 4) ℂ, (T' p).degree < (M.natDegree : ℕ) ∧
          p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T' p) * q ∈ I) → T' = T) ∧
      ∃ β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I),
        WeightedBasisCertificate U V I M r q T β := by
  constructor
  · intro h
    exact ⟨h.normal_form, h.kernel, h.unique, h.basis⟩
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨h0, h1, h2, h3⟩

/-- Named fields for the inherited InverseCertificate certificate. -/
structure InverseCertificate
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ)
    (q : MvPolynomial (Fin 4) ℂ)
    (b : Polynomial ℂ) : Prop where
  degree :
    b.degree < (M.natDegree : ℕ)
  total_degree :
    (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) b).totalDegree ≤
    M.natDegree - 1
  inverse :
    1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q ∈ I
  inverse_degree :
    (1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q).totalDegree ≤
    M.natDegree - 1 + q.totalDegree
  unique :
    (∀ b' : Polynomial ℂ, b'.degree < (M.natDegree : ℕ) →
    1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b' * q ∈ I → b' = b)
  cancellation :
    (∀ f : MvPolynomial (Fin 4) ℂ, f * q ∈ I ↔ f ∈ I)
  unit_ideal :
    I ⊔ Ideal.span {q} = ⊤
  division :
    ∃ T : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ,
    DivisionCertificate U V I M r q b T

theorem InverseCertificate.iff_fields
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ)
    (q : MvPolynomial (Fin 4) ℂ)
    (b : Polynomial ℂ) :
    InverseCertificate U V I M r q b ↔
      b.degree < (M.natDegree : ℕ) ∧
      (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) b).totalDegree ≤
        M.natDegree - 1 ∧
      1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q ∈ I ∧
      (1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q).totalDegree ≤
        M.natDegree - 1 + q.totalDegree ∧
      (∀ b' : Polynomial ℂ, b'.degree < (M.natDegree : ℕ) →
        1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b' * q ∈ I → b' = b) ∧
      (∀ f : MvPolynomial (Fin 4) ℂ, f * q ∈ I ↔ f ∈ I) ∧
      I ⊔ Ideal.span {q} = ⊤ ∧
      ∃ T : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ,
        DivisionCertificate U V I M r q b T := by
  constructor
  · intro h
    exact ⟨h.degree, h.total_degree, h.inverse, h.inverse_degree, h.unique, h.cancellation, h.unit_ideal, h.division⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

/-- Named fields for the inherited GenericCertificate certificate. -/
structure GenericCertificate
    (L : PeriodPair)
    (m : ℕ)
    (n : ℕ)
    (U : ℕ)
    (s : ℕ)
    (a : ℕ)
    (Q : MvPolynomial (Fin 7) ℂ)
    (c : Fin 2)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) : Prop where
  index_bound :
    a ≤ V.card * (s - 1)
  data :
    let q := ∑ j : Fin s, MvPolynomial.C ((a : ℂ) ^ j.val) *
      ((extensionChartDerivation L.g₂ L.g₃ c)^[j.val] (extensionChartNormalize c Q))
    (∀ v : V, MvPolynomial.eval v.val q ≠ 0) ∧
    q.totalDegree ≤ m + 2 * n + (s - 1) ∧
    ∃ b : Polynomial ℂ,
      InverseCertificate U V I M r q b

theorem GenericCertificate.iff_fields
    (L : PeriodPair)
    (m : ℕ)
    (n : ℕ)
    (U : ℕ)
    (s : ℕ)
    (a : ℕ)
    (Q : MvPolynomial (Fin 7) ℂ)
    (c : Fin 2)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) :
    GenericCertificate L m n U s a Q c V I M r ↔
      a ≤ V.card * (s - 1) ∧
      let q := ∑ j : Fin s, MvPolynomial.C ((a : ℂ) ^ j.val) *
        ((extensionChartDerivation L.g₂ L.g₃ c)^[j.val] (extensionChartNormalize c Q))
      (∀ v : V, MvPolynomial.eval v.val q ≠ 0) ∧
      q.totalDegree ≤ m + 2 * n + (s - 1) ∧
      ∃ b : Polynomial ℂ,
        InverseCertificate U V I M r q b := by
  constructor
  · intro h
    exact ⟨h.index_bound, h.data⟩
  · rintro ⟨h0, h1⟩
    exact ⟨h0, h1⟩

end WeierstrassEllipticZeta.Frontier


