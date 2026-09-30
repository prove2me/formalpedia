-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_InterfaceContactPrefixes
-- name    : WeierstrassEllipticZeta_InterfaceContactPrefixes
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-12T20:57:20.324236+00:00
-- url     : https://prove2.me/theorems/dbeccfe4-541a-4a73-937d-982f5253fd5c
-- title:
--   Contact prefix and intersection certificates
-- statement:
--   For each derivative prefix of the normalized polynomial, these certificates record the residual ideal, sparse generators, canonical time polynomial, derivative escape, and local intersection multiplicities. If the local orders are $e_v$, the quotient dimension is $\sum_v e_v$, and the differentiated prefix has local orders $\max(e_v-k,0)$.
--
--   All inherited order comparisons, radical and prime-support formulas, residual identities, and saturation formulas remain fields of this fixed interface.
-- source:
--   Structural reorganization of the exact open frontier WeierstrassEllipticZeta.spectral_factor_nilradical_multiplicity_obstruction, https://prove2.me/theorems/39b4eb14-daee-45cf-8bec-ecd2560be211. The mathematical setting is Senthil Kumar K (2026), Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The interfaces and equivalence proofs are derived here, rather than quoted from the article.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceDivision

open WeierstrassEllipticZeta TranscendenceTheory
open scoped Pointwise Classical

namespace WeierstrassEllipticZeta.Frontier

/-- Named fields for the inherited IntersectionCertificate certificate. -/
structure IntersectionCertificate
    (L : PeriodPair)
    (U : ℕ)
    (s : ℕ)
    (Q : MvPolynomial (Fin 7) ℂ)
    (c : Fin 2)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (J : Ideal (MvPolynomial (Fin 4) ℂ))
    (e : V → ℕ) : Prop where
  orders :
    (∀ v : V, e v ≤ 3 * U + 1 ∧ ∀ k ≤ 3 * U + 1,
    k ≤ e v ↔ ∀ i : Fin s, ∀ j < k,
      MvPolynomial.eval v.val
        ((extensionChartDerivation L.g₂ L.g₃ c)^[j + i.val]
          (extensionChartNormalize c Q)) = 0)
  ideal :
    J = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v))
  generator_derivatives :
    (∀ (r₀ : ℕ) (f : Fin r₀ → MvPolynomial (Fin 4) ℂ),
    J = Ideal.span (Set.range f) → ∀ k : ℕ,
    let K := Ideal.span (Set.range (fun i : Fin (k + 1) × Fin r₀ =>
      (extensionChartDerivation L.g₂ L.g₃ c)^[i.1.val] (f i.2)))
    K = J ⊔ Ideal.span ((extensionChartDerivation L.g₂ L.g₃ c)^[k] ''
      (J : Set (MvPolynomial (Fin 4) ℂ))) ∧
      K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v - k)) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = ∑ v : V, (e v - k) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        p ∈ K ↔ ∃ q : MvPolynomial (Fin 4) ℂ, q ∈ J ∧
          p - (extensionChartDerivation L.g₂ L.g₃ c)^[k] q ∈ J) ∧
      (K = ⊤ ↔ ∀ v : V, e v ≤ k) ∧
      (let K' := Ideal.span (Set.range
         (fun i : Fin (k + 1 + 1) × Fin r₀ =>
           (extensionChartDerivation L.g₂ L.g₃ c)^[i.1.val] (f i.2)))
       K ≤ K' ∧
       (K = K' ↔ K = ⊤) ∧
       (K < K' ↔ ∃ v : V, k < e v) ∧
       Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) =
         Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K') +
           (Finset.univ.filter (fun v : V => k < e v)).card))
  derivatives :
    (∀ k : ℕ,
    let K := J ⊔ Ideal.span ((extensionChartDerivation L.g₂ L.g₃ c)^[k] ''
      (J : Set (MvPolynomial (Fin 4) ℂ)))
    K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v - k)) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = ∑ v : V, (e v - k) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        p ∈ K ↔ ∃ q : MvPolynomial (Fin 4) ℂ, q ∈ J ∧
          p - (extensionChartDerivation L.g₂ L.g₃ c)^[k] q ∈ J) ∧
      (K = ⊤ ↔ ∀ v : V, e v ≤ k))
  order_comparison :
    (∀ f : V → ℕ,
    let K : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (f v)
    (J ≤ K ↔ ∀ v : V, f v ≤ e v) ∧
    (J = K ↔ e = f) ∧
    (J < K ↔ (∀ v : V, f v ≤ e v) ∧ ∃ v : V, f v < e v))
  product :
    Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ]
    ((v : V) → Polynomial ℂ ⧸
      Ideal.span {(Polynomial.X - Polynomial.C (v.val 0)) ^ e v}))
  radical :
    J.radical = (⨅ v : V, if e v = 0 then ⊤ else RingHom.ker (MvPolynomial.eval v.val))
  prime_support :
    (∀ P' : Ideal (MvPolynomial (Fin 4) ℂ), P'.IsPrime →
    (J ≤ P' ↔ ∃! v : V, 0 < e v ∧ P' = RingHom.ker (MvPolynomial.eval v.val)))
  dimension :
    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = ∑ v : V, e v
  residual :
    I.colon (J : Set (MvPolynomial (Fin 4) ℂ)) =
    (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (3 * U + 1 - e v))
  residual_dimension :
    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
    I.colon (J : Set (MvPolynomial (Fin 4) ℂ))) =
    ∑ v : V, (3 * U + 1 - e v)
  complement :
    (let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
    J ⊔ R = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val
      (min (e v) (3 * U + 1 - e v))) ∧
    FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) ∧
    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) =
      ∑ v : V, min (e v) (3 * U + 1 - e v) ∧
    (J ⊔ R = ⊤ ↔ ∀ v : V, e v = 0 ∨ e v = 3 * U + 1) ∧
    ((∀ v : V, e v = 0 ∨ e v = 3 * U + 1) →
      J ⊓ R = I ∧ J * R = I ∧
      Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₐ[ℂ]
        (MvPolynomial (Fin 4) ℂ ⧸ J) × (MvPolynomial (Fin 4) ℂ ⧸ R)) ∧
      ∃ p : MvPolynomial (Fin 4) ℂ,
        p ∈ J ∧ 1 - p ∈ R ∧ p * p - p ∈ I ∧
        J = I ⊔ Ideal.span {p} ∧ R = I ⊔ Ideal.span {1 - p}) ∧
    (let K := J ⊓ R
     I ≤ K ∧ K ^ 2 ≤ I ∧
     K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val
       (max (e v) (3 * U + 1 - e v))) ∧
     FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
     Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) =
       ∑ v : V, max (e v) (3 * U + 1 - e v) ∧
     Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) +
       Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) =
       Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) ∧
     (K = I ↔ J ⊔ R = ⊤)))
  saturation :
    (∀ p : MvPolynomial (Fin 4) ℂ,
    let K := J.colon {p ^ (3 * U + 1)}
    let e' : V → ℕ := fun v => if MvPolynomial.eval v.val p = 0 then 0 else e v
    K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e' v)) ∧
    (∀ q : MvPolynomial (Fin 4) ℂ, (∃ r : ℕ, q * p ^ r ∈ J) ↔ q ∈ K) ∧
    FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = ∑ v : V, e' v)

theorem IntersectionCertificate.iff_fields
    (L : PeriodPair)
    (U : ℕ)
    (s : ℕ)
    (Q : MvPolynomial (Fin 7) ℂ)
    (c : Fin 2)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (J : Ideal (MvPolynomial (Fin 4) ℂ))
    (e : V → ℕ) :
    IntersectionCertificate L U s Q c V I J e ↔
      (∀ v : V, e v ≤ 3 * U + 1 ∧ ∀ k ≤ 3 * U + 1,
        k ≤ e v ↔ ∀ i : Fin s, ∀ j < k,
          MvPolynomial.eval v.val
            ((extensionChartDerivation L.g₂ L.g₃ c)^[j + i.val]
              (extensionChartNormalize c Q)) = 0) ∧
      J = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v)) ∧
      (∀ (r₀ : ℕ) (f : Fin r₀ → MvPolynomial (Fin 4) ℂ),
        J = Ideal.span (Set.range f) → ∀ k : ℕ,
        let K := Ideal.span (Set.range (fun i : Fin (k + 1) × Fin r₀ =>
          (extensionChartDerivation L.g₂ L.g₃ c)^[i.1.val] (f i.2)))
        K = J ⊔ Ideal.span ((extensionChartDerivation L.g₂ L.g₃ c)^[k] ''
          (J : Set (MvPolynomial (Fin 4) ℂ))) ∧
          K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v - k)) ∧
          FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
          Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = ∑ v : V, (e v - k) ∧
          (∀ p : MvPolynomial (Fin 4) ℂ,
            p ∈ K ↔ ∃ q : MvPolynomial (Fin 4) ℂ, q ∈ J ∧
              p - (extensionChartDerivation L.g₂ L.g₃ c)^[k] q ∈ J) ∧
          (K = ⊤ ↔ ∀ v : V, e v ≤ k) ∧
          (let K' := Ideal.span (Set.range
             (fun i : Fin (k + 1 + 1) × Fin r₀ =>
               (extensionChartDerivation L.g₂ L.g₃ c)^[i.1.val] (f i.2)))
           K ≤ K' ∧
           (K = K' ↔ K = ⊤) ∧
           (K < K' ↔ ∃ v : V, k < e v) ∧
           Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) =
             Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K') +
               (Finset.univ.filter (fun v : V => k < e v)).card)) ∧
      (∀ k : ℕ,
        let K := J ⊔ Ideal.span ((extensionChartDerivation L.g₂ L.g₃ c)^[k] ''
          (J : Set (MvPolynomial (Fin 4) ℂ)))
        K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v - k)) ∧
          FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
          Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = ∑ v : V, (e v - k) ∧
          (∀ p : MvPolynomial (Fin 4) ℂ,
            p ∈ K ↔ ∃ q : MvPolynomial (Fin 4) ℂ, q ∈ J ∧
              p - (extensionChartDerivation L.g₂ L.g₃ c)^[k] q ∈ J) ∧
          (K = ⊤ ↔ ∀ v : V, e v ≤ k)) ∧
      (∀ f : V → ℕ,
        let K : Ideal (MvPolynomial (Fin 4) ℂ) :=
          ⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (f v)
        (J ≤ K ↔ ∀ v : V, f v ≤ e v) ∧
        (J = K ↔ e = f) ∧
        (J < K ↔ (∀ v : V, f v ≤ e v) ∧ ∃ v : V, f v < e v)) ∧
      Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ]
        ((v : V) → Polynomial ℂ ⧸
          Ideal.span {(Polynomial.X - Polynomial.C (v.val 0)) ^ e v})) ∧
      J.radical = (⨅ v : V, if e v = 0 then ⊤ else RingHom.ker (MvPolynomial.eval v.val)) ∧
      (∀ P' : Ideal (MvPolynomial (Fin 4) ℂ), P'.IsPrime →
        (J ≤ P' ↔ ∃! v : V, 0 < e v ∧ P' = RingHom.ker (MvPolynomial.eval v.val))) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = ∑ v : V, e v ∧
      I.colon (J : Set (MvPolynomial (Fin 4) ℂ)) =
        (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (3 * U + 1 - e v)) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
        I.colon (J : Set (MvPolynomial (Fin 4) ℂ))) =
        ∑ v : V, (3 * U + 1 - e v) ∧
      (let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
       J ⊔ R = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val
         (min (e v) (3 * U + 1 - e v))) ∧
       FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) ∧
       Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) =
         ∑ v : V, min (e v) (3 * U + 1 - e v) ∧
       (J ⊔ R = ⊤ ↔ ∀ v : V, e v = 0 ∨ e v = 3 * U + 1) ∧
       ((∀ v : V, e v = 0 ∨ e v = 3 * U + 1) →
         J ⊓ R = I ∧ J * R = I ∧
         Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₐ[ℂ]
           (MvPolynomial (Fin 4) ℂ ⧸ J) × (MvPolynomial (Fin 4) ℂ ⧸ R)) ∧
         ∃ p : MvPolynomial (Fin 4) ℂ,
           p ∈ J ∧ 1 - p ∈ R ∧ p * p - p ∈ I ∧
           J = I ⊔ Ideal.span {p} ∧ R = I ⊔ Ideal.span {1 - p}) ∧
       (let K := J ⊓ R
        I ≤ K ∧ K ^ 2 ≤ I ∧
        K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val
          (max (e v) (3 * U + 1 - e v))) ∧
        FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) =
          ∑ v : V, max (e v) (3 * U + 1 - e v) ∧
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) +
          Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) =
          Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) ∧
        (K = I ↔ J ⊔ R = ⊤))) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        let K := J.colon {p ^ (3 * U + 1)}
        let e' : V → ℕ := fun v => if MvPolynomial.eval v.val p = 0 then 0 else e v
        K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e' v)) ∧
        (∀ q : MvPolynomial (Fin 4) ℂ, (∃ r : ℕ, q * p ^ r ∈ J) ↔ q ∈ K) ∧
        FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = ∑ v : V, e' v) := by
  constructor
  · intro h
    exact ⟨h.orders, h.ideal, h.generator_derivatives, h.derivatives, h.order_comparison, h.product, h.radical, h.prime_support, h.dimension, h.residual, h.residual_dimension, h.complement, h.saturation⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- Named fields for the inherited PrefixCertificate certificate. -/
structure PrefixCertificate
    (L : PeriodPair)
    (m : ℕ)
    (n : ℕ)
    (U : ℕ)
    (s : ℕ)
    (Q : MvPolynomial (Fin 7) ℂ)
    (c : Fin 2)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ)
    (J : Ideal (MvPolynomial (Fin 4) ℂ)) : Prop where
  generic :
    (0 < s → J = ⊤ → ∃ a : ℕ, GenericCertificate L m n U s a Q c V I M r)
  residual_duality :
    (let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
    I ≤ R ∧
    I.colon (R : Set (MvPolynomial (Fin 4) ℂ)) = J ∧
    FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) +
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = M.natDegree ∧
    (∀ K : Ideal (MvPolynomial (Fin 4) ℂ), I ≤ K →
      (J ≤ K ↔ I.colon (K : Set (MvPolynomial (Fin 4) ℂ)) ≤ R)))
  sparse_generators :
    (let p : ℕ → MvPolynomial (Fin 4) ℂ := fun j =>
      (extensionChartDerivation L.g₂ L.g₃ c)^[j] (extensionChartNormalize c Q)
    let T := (Finset.range s).filter (fun j =>
      p j ∉ (I ⊔ Ideal.span (Set.range (fun i : Fin j => p i.val))))
    J = I ⊔ Ideal.span (p '' (T : Set ℕ)) ∧
    T.card + Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ M.natDegree ∧
    (J = ⊤ → ∃ b : T → Polynomial ℂ,
      (∀ j : T, (b j).degree < (M.natDegree : ℕ) ∧
        (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (b j)).totalDegree ≤
          M.natDegree - 1) ∧
      1 - ∑ j : T,
        Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * p j.val ∈ I ∧
      ∀ D : ℕ, (∀ j : T, (p j.val).totalDegree ≤ D) →
        (1 - ∑ j : T,
          Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * p j.val).totalDegree ≤
            M.natDegree - 1 + D))
  canonical_polynomial :
    (∃ g : Polynomial ℂ,
    g.Monic ∧ g ∣ M ∧ g.natDegree ≤ M.natDegree ∧
    g = Nat.rec M (fun j h => gcd h
      (MvPolynomial.aeval (Fin.cons Polynomial.X r)
        ((extensionChartDerivation L.g₂ L.g₃ c)^[j]
          (extensionChartNormalize c Q)))) s ∧
    J = I ⊔ Ideal.span {Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g} ∧
    (let f : Fin 4 → MvPolynomial (Fin 4) ℂ :=
       Fin.cons (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g)
         (fun i : Fin 3 => MvPolynomial.X i.succ -
           Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (r i))
     J = Ideal.span (Set.range f) ∧
     (∀ i : Fin 4, (f i).totalDegree ≤ max 1 M.natDegree) ∧
     (∀ (k : ℕ) (i : Fin (k + 1) × Fin 4),
       ((extensionChartDerivation L.g₂ L.g₃ c)^[i.1.val] (f i.2)).totalDegree ≤
         max 1 M.natDegree + k)) ∧
    (∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ J ↔ g ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = g.natDegree ∧
    (∀ p : MvPolynomial (Fin 4) ℂ,
      let h := gcd g (MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
      let K := J ⊔ Ideal.span {p}
      h.Monic ∧ h ∣ g ∧
      (∀ f : MvPolynomial (Fin 4) ℂ,
        f ∈ K ↔ h ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = h.natDegree ∧
      h.natDegree ≤ g.natDegree ∧
      (h = g ↔ p ∈ J) ∧
      (h.natDegree < g.natDegree ↔ p ∉ J) ∧
      (Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) <
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ↔ p ∉ J) ∧
      (∀ q : Polynomial ℂ, q.Monic →
        (∀ f : MvPolynomial (Fin 4) ℂ,
          f ∈ K ↔ q ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) → q = h)) ∧
    (let δ := extensionChartDerivation L.g₂ L.g₃ c
     let p := Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g
     (∀ k : ℕ, δ^[k] p = Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
       (Polynomial.derivative^[k] g)) ∧
     δ^[g.natDegree] p = algebraMap ℂ (MvPolynomial (Fin 4) ℂ)
       (g.natDegree.factorial : ℂ) ∧
     (g.natDegree.factorial : ℂ)⁻¹ • δ^[g.natDegree] p = 1 ∧
     (∀ k : ℕ, g.natDegree < k → δ^[k] p = 0) ∧
     (∀ k : ℕ, Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ k →
       Ideal.span (Set.range (fun i : Fin (k + 1) => δ^[i.val] p)) = ⊤)) ∧
    (∀ e : V → ℕ,
      J = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v)) →
      g = (∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ e v) ∧
        ∀ z : ℂ, g.eval z = 0 ↔ ∃ v : V, 0 < e v ∧ z = v.val 0) ∧
    (∀ h : Polynomial ℂ, h.Monic →
      (∀ f : MvPolynomial (Fin 4) ℂ,
        f ∈ J ↔ h ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) → h = g))
  finite :
    FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J)
  escape :
    (J ≠ ⊤ → ∃ p : MvPolynomial (Fin 4) ℂ,
    p ∈ J ∧ extensionChartDerivation L.g₂ L.g₃ c p ∉ J)
  time_escape :
    (J ≠ ⊤ → ∃ g : Polynomial ℂ,
    g.Monic ∧ 0 < g.natDegree ∧
    g.natDegree ≤ Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
    (∀ q : Polynomial ℂ, Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) q ∈ J ↔ g ∣ q) ∧
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g ∈ J ∧
    extensionChartDerivation L.g₂ L.g₃ c (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g) =
      Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g.derivative ∧
    g.derivative.natDegree < g.natDegree ∧
    extensionChartDerivation L.g₂ L.g₃ c (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g) ∉ J)
  intersection :
    ∃ e : V → ℕ,
    IntersectionCertificate L U s Q c V I J e

theorem PrefixCertificate.iff_fields
    (L : PeriodPair)
    (m : ℕ)
    (n : ℕ)
    (U : ℕ)
    (s : ℕ)
    (Q : MvPolynomial (Fin 7) ℂ)
    (c : Fin 2)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ)
    (J : Ideal (MvPolynomial (Fin 4) ℂ)) :
    PrefixCertificate L m n U s Q c V I M r J ↔
      (0 < s → J = ⊤ → ∃ a : ℕ, GenericCertificate L m n U s a Q c V I M r) ∧
      (let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
       I ≤ R ∧
       I.colon (R : Set (MvPolynomial (Fin 4) ℂ)) = J ∧
       FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
       Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) +
         Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = M.natDegree ∧
       (∀ K : Ideal (MvPolynomial (Fin 4) ℂ), I ≤ K →
         (J ≤ K ↔ I.colon (K : Set (MvPolynomial (Fin 4) ℂ)) ≤ R))) ∧
      (let p : ℕ → MvPolynomial (Fin 4) ℂ := fun j =>
         (extensionChartDerivation L.g₂ L.g₃ c)^[j] (extensionChartNormalize c Q)
       let T := (Finset.range s).filter (fun j =>
         p j ∉ (I ⊔ Ideal.span (Set.range (fun i : Fin j => p i.val))))
       J = I ⊔ Ideal.span (p '' (T : Set ℕ)) ∧
       T.card + Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ M.natDegree ∧
       (J = ⊤ → ∃ b : T → Polynomial ℂ,
         (∀ j : T, (b j).degree < (M.natDegree : ℕ) ∧
           (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (b j)).totalDegree ≤
             M.natDegree - 1) ∧
         1 - ∑ j : T,
           Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * p j.val ∈ I ∧
         ∀ D : ℕ, (∀ j : T, (p j.val).totalDegree ≤ D) →
           (1 - ∑ j : T,
             Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * p j.val).totalDegree ≤
               M.natDegree - 1 + D)) ∧
      (∃ g : Polynomial ℂ,
        g.Monic ∧ g ∣ M ∧ g.natDegree ≤ M.natDegree ∧
        g = Nat.rec M (fun j h => gcd h
          (MvPolynomial.aeval (Fin.cons Polynomial.X r)
            ((extensionChartDerivation L.g₂ L.g₃ c)^[j]
              (extensionChartNormalize c Q)))) s ∧
        J = I ⊔ Ideal.span {Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g} ∧
        (let f : Fin 4 → MvPolynomial (Fin 4) ℂ :=
           Fin.cons (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g)
             (fun i : Fin 3 => MvPolynomial.X i.succ -
               Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (r i))
         J = Ideal.span (Set.range f) ∧
         (∀ i : Fin 4, (f i).totalDegree ≤ max 1 M.natDegree) ∧
         (∀ (k : ℕ) (i : Fin (k + 1) × Fin 4),
           ((extensionChartDerivation L.g₂ L.g₃ c)^[i.1.val] (f i.2)).totalDegree ≤
             max 1 M.natDegree + k)) ∧
        (∀ f : MvPolynomial (Fin 4) ℂ,
          f ∈ J ↔ g ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = g.natDegree ∧
        (∀ p : MvPolynomial (Fin 4) ℂ,
          let h := gcd g (MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
          let K := J ⊔ Ideal.span {p}
          h.Monic ∧ h ∣ g ∧
          (∀ f : MvPolynomial (Fin 4) ℂ,
            f ∈ K ↔ h ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
          FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
          Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = h.natDegree ∧
          h.natDegree ≤ g.natDegree ∧
          (h = g ↔ p ∈ J) ∧
          (h.natDegree < g.natDegree ↔ p ∉ J) ∧
          (Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) <
            Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ↔ p ∉ J) ∧
          (∀ q : Polynomial ℂ, q.Monic →
            (∀ f : MvPolynomial (Fin 4) ℂ,
              f ∈ K ↔ q ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) → q = h)) ∧
        (let δ := extensionChartDerivation L.g₂ L.g₃ c
         let p := Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g
         (∀ k : ℕ, δ^[k] p = Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
           (Polynomial.derivative^[k] g)) ∧
         δ^[g.natDegree] p = algebraMap ℂ (MvPolynomial (Fin 4) ℂ)
           (g.natDegree.factorial : ℂ) ∧
         (g.natDegree.factorial : ℂ)⁻¹ • δ^[g.natDegree] p = 1 ∧
         (∀ k : ℕ, g.natDegree < k → δ^[k] p = 0) ∧
         (∀ k : ℕ, Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ k →
           Ideal.span (Set.range (fun i : Fin (k + 1) => δ^[i.val] p)) = ⊤)) ∧
        (∀ e : V → ℕ,
          J = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v)) →
          g = (∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ e v) ∧
            ∀ z : ℂ, g.eval z = 0 ↔ ∃ v : V, 0 < e v ∧ z = v.val 0) ∧
        (∀ h : Polynomial ℂ, h.Monic →
          (∀ f : MvPolynomial (Fin 4) ℂ,
            f ∈ J ↔ h ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) → h = g)) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
      (J ≠ ⊤ → ∃ p : MvPolynomial (Fin 4) ℂ,
        p ∈ J ∧ extensionChartDerivation L.g₂ L.g₃ c p ∉ J) ∧
      (J ≠ ⊤ → ∃ g : Polynomial ℂ,
        g.Monic ∧ 0 < g.natDegree ∧
        g.natDegree ≤ Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
        (∀ q : Polynomial ℂ, Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) q ∈ J ↔ g ∣ q) ∧
        Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g ∈ J ∧
        extensionChartDerivation L.g₂ L.g₃ c (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g) =
          Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g.derivative ∧
        g.derivative.natDegree < g.natDegree ∧
        extensionChartDerivation L.g₂ L.g₃ c (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g) ∉ J) ∧
      ∃ e : V → ℕ,
        IntersectionCertificate L U s Q c V I J e := by
  constructor
  · intro h
    exact ⟨h.generic, h.residual_duality, h.sparse_generators, h.canonical_polynomial, h.finite, h.escape, h.time_escape, h.intersection⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

end WeierstrassEllipticZeta.Frontier


