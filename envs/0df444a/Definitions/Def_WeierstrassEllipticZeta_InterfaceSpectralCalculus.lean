-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_InterfaceSpectralCalculus
-- name    : WeierstrassEllipticZeta_InterfaceSpectralCalculus
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-12T20:49:40.298282+00:00
-- url     : https://prove2.me/theorems/d187177f-4974-48b2-a9d1-ef59c135eb69
-- title:
--   Spectral polynomial calculus certificates
-- statement:
--   Let $I$ be an ideal of a complex polynomial algebra, and let $A$ be a quotient factor selected by an idempotent $\varepsilon_z$. Fix its coordinate map $\pi$, spectral value $z$, nilpotency index $n$, and dimension bound $d$. This certificate records the inherited evaluation kernel, normal forms, Taylor expansions, generation criteria, centralizers, trace formulas, residue character, and nilradical powers.
--
--   Every named field is equivalent to its original conjunct. The constructor interface packages these facts without deriving them or adding assumptions. Subsequent results about this data are separate theorems.
-- source:
--   Structural reorganization of the exact open frontier WeierstrassEllipticZeta.spectral_factor_nilradical_multiplicity_obstruction, https://prove2.me/theorems/39b4eb14-daee-45cf-8bec-ecd2560be211. The mathematical setting is Senthil Kumar K (2026), Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The interfaces and equivalence proofs are derived here, rather than quoted from the article.

import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Trace.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.RingTheory.Ideal.IsPrimary
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartNormalization
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartCalculus
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionChartLocus
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionLocus
import Mathlib.LinearAlgebra.Projectivization.Basic
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card

open WeierstrassEllipticZeta TranscendenceTheory
open scoped Pointwise Classical

namespace WeierstrassEllipticZeta.Frontier

/-- Named fields for the inherited SpectralCalculus certificate. -/
structure SpectralCalculus
    (n : ℕ)
    (d : ℕ)
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ)
    (p : MvPolynomial (Fin 4) ℂ)
    (W : Finset ℂ)
    (ε : W → MvPolynomial (Fin 4) ℂ ⧸ I)
    (z : W)
    (ψ : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸ Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) ≃ₗ[ℂ] Module.End.maxGenEigenspace (ρ p).mulVecLin z.val)
    (π : MvPolynomial (Fin 4) ℂ →+* ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸ Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))) : Prop where
  index_le_dimension :
    n ≤ d
  evaluation_zero :
    (∀ q : Polynomial ℂ,
    q.eval₂ (π.comp MvPolynomial.C) (π p) = 0 ↔
      (Polynomial.X - Polynomial.C z.val) ^ n ∣ q)
  evaluation_kernel :
    RingHom.ker (Polynomial.eval₂RingHom (π.comp MvPolynomial.C) (π p)) =
    Ideal.span ({(Polynomial.X - Polynomial.C z.val) ^ n} : Set (Polynomial ℂ))
  normal_form :
    (∀ q : Polynomial ℂ,
    let r := q %ₘ ((Polynomial.X - Polynomial.C z.val) ^ n)
    r.degree < (n : WithBot ℕ) ∧
      r.eval₂ (π.comp MvPolynomial.C) (π p) =
        q.eval₂ (π.comp MvPolynomial.C) (π p) ∧
      ∀ s : Polynomial ℂ, s.degree < (n : WithBot ℕ) →
        s.eval₂ (π.comp MvPolynomial.C) (π p) =
          q.eval₂ (π.comp MvPolynomial.C) (π p) → s = r)
  normal_form_equality :
    (∀ q r : Polynomial ℂ,
    q.eval₂ (π.comp MvPolynomial.C) (π p) =
      r.eval₂ (π.comp MvPolynomial.C) (π p) ↔
        q %ₘ ((Polynomial.X - Polynomial.C z.val) ^ n) =
          r %ₘ ((Polynomial.X - Polynomial.C z.val) ^ n))
  hasse_expansion :
    (∀ q : Polynomial ℂ,
    q.eval₂ (π.comp MvPolynomial.C) (π p) =
      ∑ i ∈ Finset.range n,
        π (MvPolynomial.C ((Polynomial.hasseDeriv i q).eval z.val)) *
          (π p - π (MvPolynomial.C z.val)) ^ i)
  hasse_zero :
    (∀ q : Polynomial ℂ,
    q.eval₂ (π.comp MvPolynomial.C) (π p) = 0 ↔
      ∀ i < n, (Polynomial.hasseDeriv i q).eval z.val = 0)
  hasse_equality :
    (∀ q r : Polynomial ℂ,
    q.eval₂ (π.comp MvPolynomial.C) (π p) =
      r.eval₂ (π.comp MvPolynomial.C) (π p) ↔
        ∀ i < n, (Polynomial.hasseDeriv i q).eval z.val =
          (Polynomial.hasseDeriv i r).eval z.val)
  derivative_expansion :
    (∀ q : Polynomial ℂ,
    q.eval₂ (π.comp MvPolynomial.C) (π p) =
      ∑ i ∈ Finset.range n,
        π (MvPolynomial.C (((Polynomial.derivative^[i]) q).eval z.val /
          (i.factorial : ℂ))) *
            (π p - π (MvPolynomial.C z.val)) ^ i)
  derivative_zero :
    (∀ q : Polynomial ℂ,
    q.eval₂ (π.comp MvPolynomial.C) (π p) = 0 ↔
      ∀ i < n, ((Polynomial.derivative^[i]) q).eval z.val = 0)
  derivative_equality :
    (∀ q r : Polynomial ℂ,
    q.eval₂ (π.comp MvPolynomial.C) (π p) =
      r.eval₂ (π.comp MvPolynomial.C) (π p) ↔
        ∀ i < n, ((Polynomial.derivative^[i]) q).eval z.val =
          ((Polynomial.derivative^[i]) r).eval z.val)
  root_multiplicity :
    (∀ q : Polynomial ℂ, q ≠ 0 →
    (∀ k : ℕ,
      (q.eval₂ (π.comp MvPolynomial.C) (π p)) ^ k = 0 ↔
        n ≤ q.rootMultiplicity z.val * k) ∧
    (0 < q.rootMultiplicity z.val →
      IsNilpotent (q.eval₂ (π.comp MvPolynomial.C) (π p)) ∧
        nilpotencyClass (q.eval₂ (π.comp MvPolynomial.C) (π p)) =
          (n + q.rootMultiplicity z.val - 1) /
            q.rootMultiplicity z.val))
  power_basis :
    (minpoly ℂ (π p) = (Polynomial.X - Polynomial.C z.val) ^ n ∧
    (∃ b : PowerBasis ℂ (Algebra.adjoin ℂ ({π p} : Set _)),
      (b.gen : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
        Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))) = π p ∧
        b.dim = n) ∧
    FiniteDimensional ℂ (Algebra.adjoin ℂ ({π p} : Set _)) ∧
    Module.finrank ℂ (Algebra.adjoin ℂ ({π p} : Set _)) = n ∧
    LinearIndependent ℂ (fun i : Fin n => (π p) ^ (i : ℕ)))
  adjoin_equivalence :
    (∃! e : (Polynomial ℂ ⧸
      Ideal.span {(Polynomial.X - Polynomial.C z.val) ^ n}) ≃ₐ[ℂ]
        Algebra.adjoin ℂ ({π p} : Set _),
    ∀ q : Polynomial ℂ,
      (e (Ideal.Quotient.mk
          (Ideal.span {(Polynomial.X - Polynomial.C z.val) ^ n}) q) :
        ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))) =
            q.eval₂ (π.comp MvPolynomial.C) (π p))
  generation :
    ((n = d ↔ Algebra.adjoin ℂ ({π p} : Set _) = ⊤) ∧
    (n = d ↔ Function.Surjective
      (fun q : Polynomial ℂ => q.eval₂ (π.comp MvPolynomial.C) (π p))) ∧
    (n < d ↔ ∃ y : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
        Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
      ∀ q : Polynomial ℂ,
        q.eval₂ (π.comp MvPolynomial.C) (π p) ≠ y))
  cyclic_vectors :
    (∀ y : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
      Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
    Function.Surjective (fun q : Polynomial ℂ =>
      q.eval₂ (π.comp MvPolynomial.C) (π p) * y) ↔
      n = d ∧ IsUnit y)
  commutant :
    (n = d → ∀ T : Module.End ℂ
      ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
        Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
    (∀ a, T (π p * a) = π p * T a) ↔
      ∃! b, T = Algebra.lmul ℂ
        ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) b)
  unit_commutant :
    (n = d → ∀ T : Module.End ℂ
      ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
        Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
    ((∀ a, T (π p * a) = π p * T a) ∧ Function.Bijective T) ↔
      ∃! u : (((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))ˣ),
        T = Algebra.lmul ℂ
          ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
            Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) ↑u)
  commutant_normal_form :
    (n = d → ∀ T : Module.End ℂ
      ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
        Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
    (∀ a, T (π p * a) = π p * T a) ↔
      ∃! q : Polynomial ℂ, q.degree < (n : WithBot ℕ) ∧
        T = Algebra.lmul ℂ
          ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
            Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))
          (q.eval₂ (π.comp MvPolynomial.C) (π p)))
  centralizer_algebra :
    (n = d →
    let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
      Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
    let C := Subalgebra.centralizer ℂ
      ({Algebra.lmul ℂ A (π p)} : Set (Module.End ℂ A))
    (∃! e : A ≃ₐ[ℂ] C, ∀ a : A,
      (e a : Module.End ℂ A) = Algebra.lmul ℂ A a) ∧
      Module.finrank ℂ C = d)
  double_centralizer :
    (n = d →
    let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
      Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
    let C := Subalgebra.centralizer ℂ
      ({Algebra.lmul ℂ A (π p)} : Set (Module.End ℂ A))
    C = Algebra.adjoin ℂ
        ({Algebra.lmul ℂ A (π p)} : Set (Module.End ℂ A)) ∧
      Subalgebra.centralizer ℂ (C : Set (Module.End ℂ A)) = C)
  charpoly :
    (let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
       Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
    let : FiniteDimensional ℂ A := ψ.symm.finiteDimensional
    ∀ q : Polynomial ℂ,
      (Algebra.lmul ℂ A
        (q.eval₂ (π.comp MvPolynomial.C) (π p))).charpoly =
          (Polynomial.X - Polynomial.C (q.eval z.val)) ^ d)
  trace_det :
    (let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
       Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
    let : FiniteDimensional ℂ A := ψ.symm.finiteDimensional
    ∀ q : Polynomial ℂ,
      LinearMap.trace ℂ A (Algebra.lmul ℂ A
        (q.eval₂ (π.comp MvPolynomial.C) (π p))) =
          (d : ℂ) * q.eval z.val ∧
      (Algebra.lmul ℂ A
        (q.eval₂ (π.comp MvPolynomial.C) (π p))).det =
          (q.eval z.val) ^ d)
  trace_radical :
    (n = d →
    let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
      Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
    (∀ a : A, (∀ b : A, Algebra.traceForm ℂ A a b = 0) ↔
      IsNilpotent a) ∧
    ((Algebra.traceForm ℂ A).Nondegenerate ↔ IsReduced A))
  reduced_criterion :
    (n = d →
    let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
      Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
    ((Algebra.traceForm ℂ A).Nondegenerate ↔ d = 1) ∧
      (IsReduced A ↔ d = 1))
  residue_character :
    (n = d →
    let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
      Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
    ∃! χ : A →ₐ[ℂ] ℂ,
      (∀ q : Polynomial ℂ,
        χ (q.eval₂ (π.comp MvPolynomial.C) (π p)) =
          q.eval z.val) ∧
      (∀ a : A, χ a = 0 ↔ IsNilpotent a) ∧
        Function.Surjective χ)
  local_residue :
    (n = d →
    let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
      Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
    let _ : CommRing A := inferInstance
    let _ : Algebra ℂ A := inferInstance
    let N : Ideal A := nilradical A
    IsLocalRing A ∧ (nilradical A).IsMaximal ∧
      (∀ J : Ideal A, J.IsPrime ↔ J = nilradical A) ∧
      ∃ e : (A ⧸ N) ≃ₐ[ℂ] ℂ,
        ∀ q : Polynomial ℂ,
          e (Ideal.Quotient.mk N
            (q.eval₂ (algebraMap ℂ A) (π p))) =
              q.eval z.val)
  nilradical_powers :
    (n = d →
    let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
      Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
    let _ : CommRing A := inferInstance
    let _ : Algebra ℂ A := inferInstance
    let t : A := π p - algebraMap ℂ A z.val
    nilradical A = Ideal.span {t} ∧
      ∀ k : ℕ,
        (nilradical A) ^ k = Ideal.span {t ^ k} ∧
        ((nilradical A) ^ k = ⊥ ↔ d ≤ k))
  embedding :
    ∃ f : (Polynomial ℂ ⧸
      Ideal.span {(Polynomial.X - Polynomial.C z.val) ^ n}) →+*
    ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
      Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
    Function.Injective f ∧ ∀ q : Polynomial ℂ,
      f (Ideal.Quotient.mk
        (Ideal.span {(Polynomial.X - Polynomial.C z.val) ^ n}) q) =
          q.eval₂ (π.comp MvPolynomial.C) (π p)

theorem SpectralCalculus.iff_fields
    (n : ℕ)
    (d : ℕ)
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (M : Polynomial ℂ)
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ)
    (p : MvPolynomial (Fin 4) ℂ)
    (W : Finset ℂ)
    (ε : W → MvPolynomial (Fin 4) ℂ ⧸ I)
    (z : W)
    (ψ : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸ Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) ≃ₗ[ℂ] Module.End.maxGenEigenspace (ρ p).mulVecLin z.val)
    (π : MvPolynomial (Fin 4) ℂ →+* ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸ Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))) :
    SpectralCalculus n d I M ρ p W ε z ψ π ↔
      n ≤ d ∧
      (∀ q : Polynomial ℂ,
        q.eval₂ (π.comp MvPolynomial.C) (π p) = 0 ↔
          (Polynomial.X - Polynomial.C z.val) ^ n ∣ q) ∧
      RingHom.ker (Polynomial.eval₂RingHom (π.comp MvPolynomial.C) (π p)) =
        Ideal.span ({(Polynomial.X - Polynomial.C z.val) ^ n} : Set (Polynomial ℂ)) ∧
      (∀ q : Polynomial ℂ,
        let r := q %ₘ ((Polynomial.X - Polynomial.C z.val) ^ n)
        r.degree < (n : WithBot ℕ) ∧
          r.eval₂ (π.comp MvPolynomial.C) (π p) =
            q.eval₂ (π.comp MvPolynomial.C) (π p) ∧
          ∀ s : Polynomial ℂ, s.degree < (n : WithBot ℕ) →
            s.eval₂ (π.comp MvPolynomial.C) (π p) =
              q.eval₂ (π.comp MvPolynomial.C) (π p) → s = r) ∧
      (∀ q r : Polynomial ℂ,
        q.eval₂ (π.comp MvPolynomial.C) (π p) =
          r.eval₂ (π.comp MvPolynomial.C) (π p) ↔
            q %ₘ ((Polynomial.X - Polynomial.C z.val) ^ n) =
              r %ₘ ((Polynomial.X - Polynomial.C z.val) ^ n)) ∧
      (∀ q : Polynomial ℂ,
        q.eval₂ (π.comp MvPolynomial.C) (π p) =
          ∑ i ∈ Finset.range n,
            π (MvPolynomial.C ((Polynomial.hasseDeriv i q).eval z.val)) *
              (π p - π (MvPolynomial.C z.val)) ^ i) ∧
      (∀ q : Polynomial ℂ,
        q.eval₂ (π.comp MvPolynomial.C) (π p) = 0 ↔
          ∀ i < n, (Polynomial.hasseDeriv i q).eval z.val = 0) ∧
      (∀ q r : Polynomial ℂ,
        q.eval₂ (π.comp MvPolynomial.C) (π p) =
          r.eval₂ (π.comp MvPolynomial.C) (π p) ↔
            ∀ i < n, (Polynomial.hasseDeriv i q).eval z.val =
              (Polynomial.hasseDeriv i r).eval z.val) ∧
      (∀ q : Polynomial ℂ,
        q.eval₂ (π.comp MvPolynomial.C) (π p) =
          ∑ i ∈ Finset.range n,
            π (MvPolynomial.C (((Polynomial.derivative^[i]) q).eval z.val /
              (i.factorial : ℂ))) *
                (π p - π (MvPolynomial.C z.val)) ^ i) ∧
      (∀ q : Polynomial ℂ,
        q.eval₂ (π.comp MvPolynomial.C) (π p) = 0 ↔
          ∀ i < n, ((Polynomial.derivative^[i]) q).eval z.val = 0) ∧
      (∀ q r : Polynomial ℂ,
        q.eval₂ (π.comp MvPolynomial.C) (π p) =
          r.eval₂ (π.comp MvPolynomial.C) (π p) ↔
            ∀ i < n, ((Polynomial.derivative^[i]) q).eval z.val =
              ((Polynomial.derivative^[i]) r).eval z.val) ∧
      (∀ q : Polynomial ℂ, q ≠ 0 →
        (∀ k : ℕ,
          (q.eval₂ (π.comp MvPolynomial.C) (π p)) ^ k = 0 ↔
            n ≤ q.rootMultiplicity z.val * k) ∧
        (0 < q.rootMultiplicity z.val →
          IsNilpotent (q.eval₂ (π.comp MvPolynomial.C) (π p)) ∧
            nilpotencyClass (q.eval₂ (π.comp MvPolynomial.C) (π p)) =
              (n + q.rootMultiplicity z.val - 1) /
                q.rootMultiplicity z.val)) ∧
      (minpoly ℂ (π p) = (Polynomial.X - Polynomial.C z.val) ^ n ∧
        (∃ b : PowerBasis ℂ (Algebra.adjoin ℂ ({π p} : Set _)),
          (b.gen : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
            Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))) = π p ∧
            b.dim = n) ∧
        FiniteDimensional ℂ (Algebra.adjoin ℂ ({π p} : Set _)) ∧
        Module.finrank ℂ (Algebra.adjoin ℂ ({π p} : Set _)) = n ∧
        LinearIndependent ℂ (fun i : Fin n => (π p) ^ (i : ℕ))) ∧
      (∃! e : (Polynomial ℂ ⧸
          Ideal.span {(Polynomial.X - Polynomial.C z.val) ^ n}) ≃ₐ[ℂ]
            Algebra.adjoin ℂ ({π p} : Set _),
        ∀ q : Polynomial ℂ,
          (e (Ideal.Quotient.mk
              (Ideal.span {(Polynomial.X - Polynomial.C z.val) ^ n}) q) :
            ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
              Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))) =
                q.eval₂ (π.comp MvPolynomial.C) (π p)) ∧
      ((n = d ↔ Algebra.adjoin ℂ ({π p} : Set _) = ⊤) ∧
        (n = d ↔ Function.Surjective
          (fun q : Polynomial ℂ => q.eval₂ (π.comp MvPolynomial.C) (π p))) ∧
        (n < d ↔ ∃ y : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
            Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
          ∀ q : Polynomial ℂ,
            q.eval₂ (π.comp MvPolynomial.C) (π p) ≠ y)) ∧
      (∀ y : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
        Function.Surjective (fun q : Polynomial ℂ =>
          q.eval₂ (π.comp MvPolynomial.C) (π p) * y) ↔
          n = d ∧ IsUnit y) ∧
      (n = d → ∀ T : Module.End ℂ
          ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
            Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
        (∀ a, T (π p * a) = π p * T a) ↔
          ∃! b, T = Algebra.lmul ℂ
            ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
              Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) b) ∧
      (n = d → ∀ T : Module.End ℂ
          ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
            Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
        ((∀ a, T (π p * a) = π p * T a) ∧ Function.Bijective T) ↔
          ∃! u : (((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
              Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))ˣ),
            T = Algebra.lmul ℂ
              ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
                Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) ↑u) ∧
      (n = d → ∀ T : Module.End ℂ
          ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
            Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
        (∀ a, T (π p * a) = π p * T a) ↔
          ∃! q : Polynomial ℂ, q.degree < (n : WithBot ℕ) ∧
            T = Algebra.lmul ℂ
              ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
                Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))
              (q.eval₂ (π.comp MvPolynomial.C) (π p))) ∧
      (n = d →
        let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
        let C := Subalgebra.centralizer ℂ
          ({Algebra.lmul ℂ A (π p)} : Set (Module.End ℂ A))
        (∃! e : A ≃ₐ[ℂ] C, ∀ a : A,
          (e a : Module.End ℂ A) = Algebra.lmul ℂ A a) ∧
          Module.finrank ℂ C = d) ∧
      (n = d →
        let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
        let C := Subalgebra.centralizer ℂ
          ({Algebra.lmul ℂ A (π p)} : Set (Module.End ℂ A))
        C = Algebra.adjoin ℂ
            ({Algebra.lmul ℂ A (π p)} : Set (Module.End ℂ A)) ∧
          Subalgebra.centralizer ℂ (C : Set (Module.End ℂ A)) = C) ∧
      (let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
       let : FiniteDimensional ℂ A := ψ.symm.finiteDimensional
       ∀ q : Polynomial ℂ,
         (Algebra.lmul ℂ A
           (q.eval₂ (π.comp MvPolynomial.C) (π p))).charpoly =
             (Polynomial.X - Polynomial.C (q.eval z.val)) ^ d) ∧
      (let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
       let : FiniteDimensional ℂ A := ψ.symm.finiteDimensional
       ∀ q : Polynomial ℂ,
         LinearMap.trace ℂ A (Algebra.lmul ℂ A
           (q.eval₂ (π.comp MvPolynomial.C) (π p))) =
             (d : ℂ) * q.eval z.val ∧
         (Algebra.lmul ℂ A
           (q.eval₂ (π.comp MvPolynomial.C) (π p))).det =
             (q.eval z.val) ^ d) ∧
      (n = d →
        let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
        (∀ a : A, (∀ b : A, Algebra.traceForm ℂ A a b = 0) ↔
          IsNilpotent a) ∧
        ((Algebra.traceForm ℂ A).Nondegenerate ↔ IsReduced A)) ∧
      (n = d →
        let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
        ((Algebra.traceForm ℂ A).Nondegenerate ↔ d = 1) ∧
          (IsReduced A ↔ d = 1)) ∧
      (n = d →
        let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
        ∃! χ : A →ₐ[ℂ] ℂ,
          (∀ q : Polynomial ℂ,
            χ (q.eval₂ (π.comp MvPolynomial.C) (π p)) =
              q.eval z.val) ∧
          (∀ a : A, χ a = 0 ↔ IsNilpotent a) ∧
            Function.Surjective χ) ∧
      (n = d →
        let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
        let _ : CommRing A := inferInstance
        let _ : Algebra ℂ A := inferInstance
        let N : Ideal A := nilradical A
        IsLocalRing A ∧ (nilradical A).IsMaximal ∧
          (∀ J : Ideal A, J.IsPrime ↔ J = nilradical A) ∧
          ∃ e : (A ⧸ N) ≃ₐ[ℂ] ℂ,
            ∀ q : Polynomial ℂ,
              e (Ideal.Quotient.mk N
                (q.eval₂ (algebraMap ℂ A) (π p))) =
                  q.eval z.val) ∧
      (n = d →
        let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
        let _ : CommRing A := inferInstance
        let _ : Algebra ℂ A := inferInstance
        let t : A := π p - algebraMap ℂ A z.val
        nilradical A = Ideal.span {t} ∧
          ∀ k : ℕ,
            (nilradical A) ^ k = Ideal.span {t ^ k} ∧
            ((nilradical A) ^ k = ⊥ ↔ d ≤ k)) ∧
      ∃ f : (Polynomial ℂ ⧸
          Ideal.span {(Polynomial.X - Polynomial.C z.val) ^ n}) →+*
        ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
        Function.Injective f ∧ ∀ q : Polynomial ℂ,
          f (Ideal.Quotient.mk
            (Ideal.span {(Polynomial.X - Polynomial.C z.val) ^ n}) q) =
              q.eval₂ (π.comp MvPolynomial.C) (π p) := by
  constructor
  · intro h
    exact ⟨h.index_le_dimension, h.evaluation_zero, h.evaluation_kernel, h.normal_form, h.normal_form_equality, h.hasse_expansion, h.hasse_zero, h.hasse_equality, h.derivative_expansion, h.derivative_zero, h.derivative_equality, h.root_multiplicity, h.power_basis, h.adjoin_equivalence, h.generation, h.cyclic_vectors, h.commutant, h.unit_commutant, h.commutant_normal_form, h.centralizer_algebra, h.double_centralizer, h.charpoly, h.trace_det, h.trace_radical, h.reduced_criterion, h.residue_character, h.local_residue, h.nilradical_powers, h.embedding⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩

end WeierstrassEllipticZeta.Frontier


