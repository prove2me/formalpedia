-- Prove2me | Definitions.Def_N25_CanonicalConePolynomial
-- name    : N25_CanonicalConePolynomial
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:17:43.145627+00:00
-- url     : https://prove2.me/theorems/7ed50acb-91ae-413b-9a6f-583e9b461722
-- title:
--   A polynomial realization of the graded canonical cone
-- statement:
--   For a homogeneous element $f$ of degree $n$, defines the normalized coefficient $f/A^n$ in the degree-zero $A$-chart and records its original degree as the monomial $(f/A^n)T^n$. These maps are assembled through the graded direct sum into a ring homomorphism from the canonical cone to a polynomial ring over the $A$-chart, providing a technical model for later domain arguments.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalPrincipalOpenChart
/-! Graded polynomial realization of the canonical cone after dividing by powers of A. -/

noncomputable section

universe u

namespace N25

open HomogeneousLocalization DirectSum

variable (K : Type u) [Field K]

/-- Divide a degree-n cone element by A^n in the actual degree-zero A-chart. -/
def canonicalConeFractionPiece25 (n : ℕ) :
    canonicalConePiece25 K n →+ CanonicalAProjRing25 K where
  toFun x := Away.mk (canonicalConePiece25 K) (canonicalConeA25_mem K) n x.val (by simpa using x.property)
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp only [Away.val_mk, HomogeneousLocalization.val_zero, ZeroMemClass.coe_zero, Localization.mk_zero]
  map_add' x y := by
    apply HomogeneousLocalization.val_injective
    simp only [Away.val_mk, HomogeneousLocalization.val_add, Submodule.coe_add, Localization.add_mk]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    use 1
    simp only [Submonoid.coe_one, one_mul, Submonoid.coe_mul]
    ring

theorem canonicalConeFractionPiece25_one :
    canonicalConeFractionPiece25 K 0 (GradedMonoid.GOne.one (A := fun n : ℕ => canonicalConePiece25 K n)) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [canonicalConeFractionPiece25, Away.val_mk, HomogeneousLocalization.val_one]

theorem canonicalConeFractionPiece25_mul {n m : ℕ}
    (x : canonicalConePiece25 K n) (y : canonicalConePiece25 K m) :
    canonicalConeFractionPiece25 K (n+m) (GradedMonoid.GMul.mul (A := fun n : ℕ => canonicalConePiece25 K n) x y) =
      canonicalConeFractionPiece25 K n x * canonicalConeFractionPiece25 K m y := by
  apply HomogeneousLocalization.val_injective
  simp only [canonicalConeFractionPiece25, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Away.val_mk, HomogeneousLocalization.val_mul]
  change Localization.mk (x.val*y.val) _ = Localization.mk x.val _ * Localization.mk y.val _
  rw [Localization.mk_mul]
  congr 1
  apply Subtype.ext
  exact pow_add _ n m

/-- Retain the original degree as a polynomial power after normalizing the coefficient by A. -/
def canonicalConePolynomialPiece25 (n : ℕ) :
    canonicalConePiece25 K n →+ Polynomial (CanonicalAProjRing25 K) :=
  (Polynomial.monomial n).toAddMonoidHom.comp (canonicalConeFractionPiece25 K n)

theorem canonicalConePolynomialPiece25_one :
    canonicalConePolynomialPiece25 K 0 (GradedMonoid.GOne.one (A := fun n : ℕ => canonicalConePiece25 K n)) = 1 := by
  change Polynomial.monomial 0 (canonicalConeFractionPiece25 K 0 (GradedMonoid.GOne.one (A := fun n : ℕ => canonicalConePiece25 K n))) = 1
  rw [canonicalConeFractionPiece25_one, Polynomial.monomial_zero_one]

theorem canonicalConePolynomialPiece25_mul {n m : ℕ}
    (x : canonicalConePiece25 K n) (y : canonicalConePiece25 K m) :
    canonicalConePolynomialPiece25 K (n+m) (GradedMonoid.GMul.mul (A := fun n : ℕ => canonicalConePiece25 K n) x y) =
      canonicalConePolynomialPiece25 K n x * canonicalConePolynomialPiece25 K m y := by
  change Polynomial.monomial (n+m) (canonicalConeFractionPiece25 K (n+m) _) =
    Polynomial.monomial n (canonicalConeFractionPiece25 K n x) *
      Polynomial.monomial m (canonicalConeFractionPiece25 K m y)
  rw [canonicalConeFractionPiece25_mul, Polynomial.monomial_mul_monomial]

/-- The polynomial realization of the direct sum of all cone degrees. -/
def canonicalConeDirectSumPolynomial25 :
    (⨁ n, canonicalConePiece25 K n) →+* Polynomial (CanonicalAProjRing25 K) :=
  DirectSum.toSemiring (canonicalConePolynomialPiece25 K)
    (canonicalConePolynomialPiece25_one K) (canonicalConePolynomialPiece25_mul K)

/-- A graded polynomial map out of the actual cone, before any domain assertion. -/
def canonicalConePolynomial25 : CanonicalConeRing25 K →+* Polynomial (CanonicalAProjRing25 K) :=
  (canonicalConeDirectSumPolynomial25 K).comp (DirectSum.decomposeRingEquiv (canonicalConePiece25 K)).toRingHom

end N25


