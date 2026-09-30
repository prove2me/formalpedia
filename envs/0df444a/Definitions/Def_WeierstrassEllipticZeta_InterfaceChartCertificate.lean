-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_InterfaceChartCertificate
-- name    : WeierstrassEllipticZeta_InterfaceChartCertificate
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-12T20:57:55.957498+00:00
-- url     : https://prove2.me/theorems/8e635874-1779-4a65-a3c3-6fe97f833a12
-- title:
--   Finite chart contact certificates
-- statement:
--   Fix a chart, a finite set $Z$ of parameters, its coordinate image $V$, and contact weight $3U+1$. The chart certificate records vanishing in the common contact ideal, a Bezout certificate, finite dimensionality, and dimension $(3U+1)\#Z$. Its monic time polynomial is the product of the local factors with this weight.
--
--   A triangular certificate supplies the coordinate polynomials, derivative-prefix certificates, bounded Bezout coefficients, and hypersurface intersection data. These named components preserve the original witnesses and bounds.
-- source:
--   Structural reorganization of the exact open frontier WeierstrassEllipticZeta.spectral_factor_nilradical_multiplicity_obstruction, https://prove2.me/theorems/39b4eb14-daee-45cf-8bec-ecd2560be211. The mathematical setting is Senthil Kumar K (2026), Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The interfaces and equivalence proofs are derived here, rather than quoted from the article.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceContactPrefixes

open WeierstrassEllipticZeta TranscendenceTheory
open scoped Pointwise Classical

namespace WeierstrassEllipticZeta.Frontier

/-- Named fields for the inherited TriangularCertificate certificate. -/
structure TriangularCertificate
    (L : PeriodPair)
    (B : ℕ → ℕ)
    (m : ℕ)
    (n : ℕ)
    (U : ℕ)
    (Q : MvPolynomial (Fin 7) ℂ)
    (c : Fin 2)
    (Z : Finset ℂ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) : Prop where
  degree :
    (∀ i, (r i).degree < ((3 * U + 1) * Z.card : ℕ))
  generators :
    I = Ideal.span (insert (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) M)
    (Set.range (fun i : Fin 3 => MvPolynomial.X i.succ -
      Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (r i))))
  membership :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
  orders :
    (∃ t : V → ℕ,
    (∀ v : V, 3 * U + 1 ≤ t v ∧ t v < B (m + 2 * n) ∧
      MvPolynomial.eval v.val
        ((extensionChartDerivation L.g₂ L.g₃ c)^[t v] (extensionChartNormalize c Q)) ≠ 0 ∧
      ∀ j < t v, MvPolynomial.eval v.val
        ((extensionChartDerivation L.g₂ L.g₃ c)^[j] (extensionChartNormalize c Q)) = 0) ∧
    ∀ s : ℕ, 0 < s →
      let J := I ⊔ Ideal.span (Set.range (fun i : Fin s =>
        (extensionChartDerivation L.g₂ L.g₃ c)^[i.val] (extensionChartNormalize c Q)))
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) =
        ∑ v : V, min (3 * U + 1) (t v + 1 - s) ∧
      (J = ⊤ ↔ ∀ v : V, t v < s) ∧
      (B (m + 2 * n) ≤ s → J = ⊤))
  prefixes :
    (∀ s : ℕ,
    let J := I ⊔ Ideal.span (Set.range (fun i : Fin s =>
      (extensionChartDerivation L.g₂ L.g₃ c)^[i.val] (extensionChartNormalize c Q)))
    PrefixCertificate L m n U s Q c V I M r J)
  bezout :
    (∃ b : Fin (B (m + 2 * n)) → Polynomial ℂ,
    (∀ k : Fin (B (m + 2 * n)),
      (b k).degree < ((3 * U + 1) * Z.card : ℕ) ∧
      (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (b k)).totalDegree ≤
        (3 * U + 1) * Z.card - 1) ∧
    (1 - ∑ k : Fin (B (m + 2 * n)),
      Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b k) *
        ((extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q))) ∈ I ∧
    (1 - ∑ k : Fin (B (m + 2 * n)),
      Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b k) *
        ((extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q))).totalDegree ≤
      ((3 * U + 1) * Z.card - 1) + (m + 2 * n + (B (m + 2 * n) - 1)))
  hypersurfaces :
    ∀ p : MvPolynomial (Fin 4) ℂ,
    let q := MvPolynomial.aeval (Fin.cons Polynomial.X r) p
    let J := I ⊔ Ideal.span {p}
    Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ]
      (Polynomial ℂ ⧸ Ideal.span {gcd M q})) ∧
    FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = (gcd M q).natDegree ∧
    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ M.natDegree ∧
    (q ≠ 0 → Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ q.natDegree) ∧
    (let R := I.colon {p}
     let G := M / gcd M q
     (∀ f : MvPolynomial (Fin 4) ℂ,
       f ∈ R ↔ G ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
     Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ R) ≃ₐ[ℂ]
       (Polynomial ℂ ⧸ Ideal.span {G})) ∧
     FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
     Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) = G.natDegree ∧
     Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) +
       Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = M.natDegree ∧
     I.colon (R : Set (MvPolynomial (Fin 4) ℂ)) = J ∧
     I.colon (J : Set (MvPolynomial (Fin 4) ℂ)) = R) ∧
    ∃ e : V → ℕ,
      (∀ v : V, e v ≤ 3 * U + 1 ∧ ∀ k ≤ 3 * U + 1,
        k ≤ e v ↔ ∀ j < k,
          MvPolynomial.eval v.val
            ((extensionChartDerivation L.g₂ L.g₃ c)^[j] p) = 0) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = ∑ v : V, e v ∧
      I.colon {p} =
        (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (3 * U + 1 - e v)) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I.colon {p}) =
        ∑ v : V, (3 * U + 1 - e v)

theorem TriangularCertificate.iff_fields
    (L : PeriodPair)
    (B : ℕ → ℕ)
    (m : ℕ)
    (n : ℕ)
    (U : ℕ)
    (Q : MvPolynomial (Fin 7) ℂ)
    (c : Fin 2)
    (Z : Finset ℂ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) :
    TriangularCertificate L B m n U Q c Z V I M r ↔
      (∀ i, (r i).degree < ((3 * U + 1) * Z.card : ℕ)) ∧
      I = Ideal.span (insert (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) M)
        (Set.range (fun i : Fin 3 => MvPolynomial.X i.succ -
          Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (r i)))) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p) ∧
      (∃ t : V → ℕ,
        (∀ v : V, 3 * U + 1 ≤ t v ∧ t v < B (m + 2 * n) ∧
          MvPolynomial.eval v.val
            ((extensionChartDerivation L.g₂ L.g₃ c)^[t v] (extensionChartNormalize c Q)) ≠ 0 ∧
          ∀ j < t v, MvPolynomial.eval v.val
            ((extensionChartDerivation L.g₂ L.g₃ c)^[j] (extensionChartNormalize c Q)) = 0) ∧
        ∀ s : ℕ, 0 < s →
          let J := I ⊔ Ideal.span (Set.range (fun i : Fin s =>
            (extensionChartDerivation L.g₂ L.g₃ c)^[i.val] (extensionChartNormalize c Q)))
          FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
          Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) =
            ∑ v : V, min (3 * U + 1) (t v + 1 - s) ∧
          (J = ⊤ ↔ ∀ v : V, t v < s) ∧
          (B (m + 2 * n) ≤ s → J = ⊤)) ∧
      (∀ s : ℕ,
        let J := I ⊔ Ideal.span (Set.range (fun i : Fin s =>
          (extensionChartDerivation L.g₂ L.g₃ c)^[i.val] (extensionChartNormalize c Q)))
        PrefixCertificate L m n U s Q c V I M r J) ∧
      (∃ b : Fin (B (m + 2 * n)) → Polynomial ℂ,
        (∀ k : Fin (B (m + 2 * n)),
          (b k).degree < ((3 * U + 1) * Z.card : ℕ) ∧
          (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (b k)).totalDegree ≤
            (3 * U + 1) * Z.card - 1) ∧
        (1 - ∑ k : Fin (B (m + 2 * n)),
          Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b k) *
            ((extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q))) ∈ I ∧
        (1 - ∑ k : Fin (B (m + 2 * n)),
          Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b k) *
            ((extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q))).totalDegree ≤
          ((3 * U + 1) * Z.card - 1) + (m + 2 * n + (B (m + 2 * n) - 1))) ∧
      ∀ p : MvPolynomial (Fin 4) ℂ,
        let q := MvPolynomial.aeval (Fin.cons Polynomial.X r) p
        let J := I ⊔ Ideal.span {p}
        Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ]
          (Polynomial ℂ ⧸ Ideal.span {gcd M q})) ∧
        FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = (gcd M q).natDegree ∧
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ M.natDegree ∧
        (q ≠ 0 → Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ q.natDegree) ∧
        (let R := I.colon {p}
         let G := M / gcd M q
         (∀ f : MvPolynomial (Fin 4) ℂ,
           f ∈ R ↔ G ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
         Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ R) ≃ₐ[ℂ]
           (Polynomial ℂ ⧸ Ideal.span {G})) ∧
         FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
         Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) = G.natDegree ∧
         Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) +
           Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = M.natDegree ∧
         I.colon (R : Set (MvPolynomial (Fin 4) ℂ)) = J ∧
         I.colon (J : Set (MvPolynomial (Fin 4) ℂ)) = R) ∧
        ∃ e : V → ℕ,
          (∀ v : V, e v ≤ 3 * U + 1 ∧ ∀ k ≤ 3 * U + 1,
            k ≤ e v ↔ ∀ j < k,
              MvPolynomial.eval v.val
                ((extensionChartDerivation L.g₂ L.g₃ c)^[j] p) = 0) ∧
          Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = ∑ v : V, e v ∧
          I.colon {p} =
            (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (3 * U + 1 - e v)) ∧
          Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I.colon {p}) =
            ∑ v : V, (3 * U + 1 - e v) := by
  constructor
  · intro h
    exact ⟨h.degree, h.generators, h.membership, h.orders, h.prefixes, h.bezout, h.hypersurfaces⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

/-- Named fields for the inherited ContactCertificate certificate. -/
structure ContactCertificate
    (L : PeriodPair)
    (B : ℕ → ℕ)
    (m : ℕ)
    (n : ℕ)
    (U : ℕ)
    (Q : MvPolynomial (Fin 7) ℂ)
    (c : Fin 2)
    (Z : Finset ℂ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ) : Prop where
  monic :
    M.Monic
  degree :
    M.degree = ((3 * U + 1) * Z.card : ℕ)
  triangular :
    ∃ r : Fin 3 → Polynomial ℂ,
    TriangularCertificate L B m n U Q c Z V I M r

theorem ContactCertificate.iff_fields
    (L : PeriodPair)
    (B : ℕ → ℕ)
    (m : ℕ)
    (n : ℕ)
    (U : ℕ)
    (Q : MvPolynomial (Fin 7) ℂ)
    (c : Fin 2)
    (Z : Finset ℂ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ) :
    ContactCertificate L B m n U Q c Z V I M ↔
      M.Monic ∧ M.degree = ((3 * U + 1) * Z.card : ℕ) ∧
      ∃ r : Fin 3 → Polynomial ℂ,
        TriangularCertificate L B m n U Q c Z V I M r := by
  constructor
  · intro h
    exact ⟨h.monic, h.degree, h.triangular⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, h1, h2⟩

/-- Named fields for the inherited ChartCertificate certificate. -/
structure ChartCertificate
    (L : PeriodPair)
    (B : ℕ → ℕ)
    (m : ℕ)
    (n : ℕ)
    (U : ℕ)
    (Q : MvPolynomial (Fin 7) ℂ)
    (c : Fin 2)
    (Z : Finset ℂ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) : Prop where
  vanishing :
    extensionChartNormalize c Q ∈ I
  bezout :
    (∃ a : Fin (B (m + 2 * n)) → MvPolynomial (Fin 4) ℂ,
    1 - ∑ k : Fin (B (m + 2 * n)), a k *
      ((extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q)) ∈ I ∧
    I ⊔ Ideal.span (Set.range (fun k : Fin (B (m + 2 * n)) =>
      (extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q))) = ⊤)
  finite :
    FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ I)
  dimension :
    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) = (3 * U + 1) * Z.card
  polynomial :
    let M : Polynomial ℂ :=
      ∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ (3 * U + 1)
    ContactCertificate L B m n U Q c Z V I M

theorem ChartCertificate.iff_fields
    (L : PeriodPair)
    (B : ℕ → ℕ)
    (m : ℕ)
    (n : ℕ)
    (U : ℕ)
    (Q : MvPolynomial (Fin 7) ℂ)
    (c : Fin 2)
    (Z : Finset ℂ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) :
    ChartCertificate L B m n U Q c Z V I ↔
      extensionChartNormalize c Q ∈ I ∧
      (∃ a : Fin (B (m + 2 * n)) → MvPolynomial (Fin 4) ℂ,
        1 - ∑ k : Fin (B (m + 2 * n)), a k *
          ((extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q)) ∈ I ∧
        I ⊔ Ideal.span (Set.range (fun k : Fin (B (m + 2 * n)) =>
          (extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q))) = ⊤) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) = (3 * U + 1) * Z.card ∧
      let M : Polynomial ℂ :=
        ∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ (3 * U + 1)
      ContactCertificate L B m n U Q c Z V I M := by
  constructor
  · intro h
    exact ⟨h.vanishing, h.bezout, h.finite, h.dimension, h.polynomial⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨h0, h1, h2, h3, h4⟩

end WeierstrassEllipticZeta.Frontier


