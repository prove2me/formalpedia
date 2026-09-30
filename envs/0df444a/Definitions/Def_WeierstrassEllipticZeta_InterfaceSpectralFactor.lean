-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_InterfaceSpectralFactor
-- name    : WeierstrassEllipticZeta_InterfaceSpectralFactor
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-12T20:51:30.855742+00:00
-- url     : https://prove2.me/theorems/66e04ffc-bb1a-4c89-8574-52db478ec1ee
-- title:
--   Individual spectral factor certificates
-- statement:
--   Fix a finite contact quotient with weighted basis, regular representation, and a selected spectral idempotent. This certificate records an equivalence of the selected quotient factor with its generalized eigenspace, its dimension and nilpotence bounds, its resolvent, and its polynomial calculus. For the finite point set $V$ and contact weight $3U+1$, the factor dimension is
--   $$d_z=(3U+1)\#\{v\in V:p(v)=z\}.$$
--   The final field contains the named polynomial-calculus certificate for this factor.
-- source:
--   Structural reorganization of the exact open frontier WeierstrassEllipticZeta.spectral_factor_nilradical_multiplicity_obstruction, https://prove2.me/theorems/39b4eb14-daee-45cf-8bec-ecd2560be211. The mathematical setting is Senthil Kumar K (2026), Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The interfaces and equivalence proofs are derived here, rather than quoted from the article.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceSpectralCalculus

open WeierstrassEllipticZeta TranscendenceTheory
open scoped Pointwise Classical

namespace WeierstrassEllipticZeta.Frontier

/-- Named fields for the inherited SpectralFactor certificate. -/
structure SpectralFactor
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I))
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ)
    (p : MvPolynomial (Fin 4) ℂ)
    (W : Finset ℂ)
    (ε : W → MvPolynomial (Fin 4) ℂ ⧸ I)
    (z : W)
    (ψ : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸ Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) ≃ₗ[ℂ] Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) : Prop where
  equivalence_action :
    (∀ a : MvPolynomial (Fin 4) ℂ ⧸ I,
    (ψ (Ideal.Quotient.mk (Ideal.span {1 - ε z}) a) : Fin M.natDegree → ℂ) =
      β.equivFun (ε z * a))
  dimension :
    Module.finrank ℂ
    ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
      Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) =
    (3 * U + 1) * (Finset.univ.filter (fun v : V =>
      MvPolynomial.eval v.val p = z.val)).card
  nilpotence :
    (Ideal.Quotient.mk
    (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))
    (Ideal.Quotient.mk I (p - MvPolynomial.C z.val))) ^
      M.natDegree = 0
  dimension_nilpotence :
    (∀ N : ℕ, (3 * U + 1) *
    (Finset.univ.filter (fun v : V =>
      MvPolynomial.eval v.val p = z.val)).card ≤ N →
    (Ideal.Quotient.mk
      (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))
      (Ideal.Quotient.mk I (p - MvPolynomial.C z.val))) ^ N = 0)
  resolvent :
    (∀ w : ℂ, w ≠ z.val →
    let π := (Ideal.Quotient.mk
      (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))).comp
        (Ideal.Quotient.mk I)
    let d := (3 * U + 1) *
      (Finset.univ.filter (fun v : V =>
        MvPolynomial.eval v.val p = z.val)).card
    let b := π (MvPolynomial.C ((z.val - w)⁻¹)) *
      ∑ k ∈ Finset.range d,
        (-(π (MvPolynomial.C ((z.val - w)⁻¹)) *
          π (p - MvPolynomial.C z.val))) ^ k
    π (p - MvPolynomial.C w) * b = 1 ∧
      b * π (p - MvPolynomial.C w) = 1 ∧
      IsUnit (π (p - MvPolynomial.C w)))
  polynomial_calculus :
    (∀ q : Polynomial ℂ,
    let π := (Ideal.Quotient.mk
      (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))).comp
        (Ideal.Quotient.mk I)
    let d := (3 * U + 1) *
      (Finset.univ.filter (fun v : V =>
        MvPolynomial.eval v.val p = z.val)).card
    (q.eval₂ (π.comp MvPolynomial.C) (π p) -
      π (MvPolynomial.C (q.eval z.val))) ^ d = 0 ∧
    (IsUnit (q.eval₂ (π.comp MvPolynomial.C) (π p)) ↔
      q.eval z.val ≠ 0) ∧
    (IsNilpotent (q.eval₂ (π.comp MvPolynomial.C) (π p)) ↔
      q.eval z.val = 0) ∧
    (q ≠ 0 →
      ∃ u : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
        Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))ˣ,
        q.eval₂ (π.comp MvPolynomial.C) (π p) =
          (π p - π (MvPolynomial.C z.val)) ^ q.rootMultiplicity z.val * ↑u ∧
        (∀ k : ℕ,
          (q.eval₂ (π.comp MvPolynomial.C) (π p)) ^ k = 0 ↔
            (π p - π (MvPolynomial.C z.val)) ^
              (q.rootMultiplicity z.val * k) = 0) ∧
        ∀ k : ℕ, d ≤ q.rootMultiplicity z.val * k →
          (q.eval₂ (π.comp MvPolynomial.C) (π p)) ^ k = 0))
  calculus :
    let π := (Ideal.Quotient.mk
      (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))).comp
        (Ideal.Quotient.mk I)
    let d := (3 * U + 1) *
      (Finset.univ.filter (fun v : V =>
        MvPolynomial.eval v.val p = z.val)).card
    let n := nilpotencyClass (π p - π (MvPolynomial.C z.val))
    SpectralCalculus n d I M ρ p W ε z ψ π

theorem SpectralFactor.iff_fields
    (U : ℕ)
    (V : Finset (Fin 4 → ℂ))
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I))
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ)
    (p : MvPolynomial (Fin 4) ℂ)
    (W : Finset ℂ)
    (ε : W → MvPolynomial (Fin 4) ℂ ⧸ I)
    (z : W)
    (ψ : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸ Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) ≃ₗ[ℂ] Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) :
    SpectralFactor U V I M β ρ p W ε z ψ ↔
      (∀ a : MvPolynomial (Fin 4) ℂ ⧸ I,
        (ψ (Ideal.Quotient.mk (Ideal.span {1 - ε z}) a) : Fin M.natDegree → ℂ) =
          β.equivFun (ε z * a)) ∧
      Module.finrank ℂ
        ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) =
        (3 * U + 1) * (Finset.univ.filter (fun v : V =>
          MvPolynomial.eval v.val p = z.val)).card ∧
      (Ideal.Quotient.mk
        (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))
        (Ideal.Quotient.mk I (p - MvPolynomial.C z.val))) ^
          M.natDegree = 0 ∧
      (∀ N : ℕ, (3 * U + 1) *
        (Finset.univ.filter (fun v : V =>
          MvPolynomial.eval v.val p = z.val)).card ≤ N →
        (Ideal.Quotient.mk
          (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))
          (Ideal.Quotient.mk I (p - MvPolynomial.C z.val))) ^ N = 0) ∧
      (∀ w : ℂ, w ≠ z.val →
        let π := (Ideal.Quotient.mk
          (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))).comp
            (Ideal.Quotient.mk I)
        let d := (3 * U + 1) *
          (Finset.univ.filter (fun v : V =>
            MvPolynomial.eval v.val p = z.val)).card
        let b := π (MvPolynomial.C ((z.val - w)⁻¹)) *
          ∑ k ∈ Finset.range d,
            (-(π (MvPolynomial.C ((z.val - w)⁻¹)) *
              π (p - MvPolynomial.C z.val))) ^ k
        π (p - MvPolynomial.C w) * b = 1 ∧
          b * π (p - MvPolynomial.C w) = 1 ∧
          IsUnit (π (p - MvPolynomial.C w))) ∧
      (∀ q : Polynomial ℂ,
        let π := (Ideal.Quotient.mk
          (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))).comp
            (Ideal.Quotient.mk I)
        let d := (3 * U + 1) *
          (Finset.univ.filter (fun v : V =>
            MvPolynomial.eval v.val p = z.val)).card
        (q.eval₂ (π.comp MvPolynomial.C) (π p) -
          π (MvPolynomial.C (q.eval z.val))) ^ d = 0 ∧
        (IsUnit (q.eval₂ (π.comp MvPolynomial.C) (π p)) ↔
          q.eval z.val ≠ 0) ∧
        (IsNilpotent (q.eval₂ (π.comp MvPolynomial.C) (π p)) ↔
          q.eval z.val = 0) ∧
        (q ≠ 0 →
          ∃ u : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
            Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))ˣ,
            q.eval₂ (π.comp MvPolynomial.C) (π p) =
              (π p - π (MvPolynomial.C z.val)) ^ q.rootMultiplicity z.val * ↑u ∧
            (∀ k : ℕ,
              (q.eval₂ (π.comp MvPolynomial.C) (π p)) ^ k = 0 ↔
                (π p - π (MvPolynomial.C z.val)) ^
                  (q.rootMultiplicity z.val * k) = 0) ∧
            ∀ k : ℕ, d ≤ q.rootMultiplicity z.val * k →
              (q.eval₂ (π.comp MvPolynomial.C) (π p)) ^ k = 0)) ∧
      let π := (Ideal.Quotient.mk
        (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))).comp
          (Ideal.Quotient.mk I)
      let d := (3 * U + 1) *
        (Finset.univ.filter (fun v : V =>
          MvPolynomial.eval v.val p = z.val)).card
      let n := nilpotencyClass (π p - π (MvPolynomial.C z.val))
      SpectralCalculus n d I M ρ p W ε z ψ π := by
  constructor
  · intro h
    exact ⟨h.equivalence_action, h.dimension, h.nilpotence, h.dimension_nilpotence, h.resolvent, h.polynomial_calculus, h.calculus⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

end WeierstrassEllipticZeta.Frontier


