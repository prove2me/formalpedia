-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P03
-- name    : QAlgorithms_Papers_Independent_Next46_P03
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T12:34:03.940992+00:00
-- url     : https://prove2.me/theorems/91ac8a81-3dcd-4d71-8053-ca956379f4a1
-- title:
--   Definitions for A First Complete Algorithm for Real Quantifier Elimination in Isabelle/HOL
-- statement:
--   The objects the formalized statements of *A First Complete Algorithm for Real Quantifier Elimination in Isabelle/HOL* (arXiv:2209.10978) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `isolateVariableSparse`: PDF p. 11: the coefficient of the selected variable's power `i`. Each retained exponent vector has coordinate `x` erased, so every monomial in the result has exponent zero at `x`, including at `x = 0`. No condition on the input polynomial is needed for this invariant.
--   - `mpolyToMpolyPolyAlt`: PDF p. 11: the alternate conversion sums powers from zero through `degreeOf x p`, inclusive, with the extracted coefficient at each power.
--   - `mpolyToMpolyPoly`: PDF p. 11: the reference conversion, independently specified by the canonical substitution homomorphism. The selected variable maps to outer `Polynomial.X`; every other variable maps to a coefficient variable with its original index. Thus coefficient monomials contain no selected variable. This definition does not invoke the alternate coefficient-sum conversion.
--   - `univariateIn`: PDF p. 11: convert each polynomial in the given ordered list, retaining order and multiplicities.
--   - `lowerPolyZeroOne`: PDF pp. 11–12: the instance `lowerPoly 0 1` used in the source theorem. It renames every index `j` to `j - 1`. In its use after conversion at zero, coefficients contain no variable zero, so truncated subtraction never identifies two variables that actually occur in those coefficients.
--   - `evalMpoly`: PDF p. 11: the valuation list supplies the value of variable `j` at position `j`, and supplies zero at all positions beyond the list.
--   - `evalMpolyPoly`: PDF p. 11: evaluate the multivariate coefficients, leaving the outer univariate variable untouched.
-- source:
--   A First Complete Algorithm for Real Quantifier Elimination in Isabelle/HOL, arXiv:2209.10978v2, https://arxiv.org/abs/2209.10978v2

import Mathlib

/-!
Polynomial interfaces from Kosaian, Tan and Platzer, arXiv:2209.10978v2,
§3.3, PDF pp. 11–12. The source-dependent algorithmic results are deferred
in this paper's HARD.md. All definitions below belong only to this paper.
-/

namespace QAlgorithms.Papers.Independent.Next46.P03

noncomputable section

/-- PDF p. 11: the coefficient of the selected variable's power `i`.
Each retained exponent vector has coordinate `x` erased, so every monomial
in the result has exponent zero at `x`, including at `x = 0`.
No condition on the input polynomial is needed for this invariant. -/
def isolateVariableSparse {R : Type*} [CommRing R] [Nontrivial R]
    (p : MvPolynomial ℕ R) (x i : ℕ) : MvPolynomial ℕ R :=
  ∑ d ∈ p.support,
    if d x = i then MvPolynomial.monomial (d.erase x) (p.coeff d) else 0

/-- PDF p. 11: the alternate conversion sums powers from zero through
`degreeOf x p`, inclusive, with the extracted coefficient at each power. -/
def mpolyToMpolyPolyAlt {R : Type*} [CommRing R] [Nontrivial R]
    (x : ℕ) (p : MvPolynomial ℕ R) : Polynomial (MvPolynomial ℕ R) :=
  ∑ i ∈ Finset.range (MvPolynomial.degreeOf x p + 1),
    Polynomial.monomial i (isolateVariableSparse p x i)

/-- PDF p. 11: the reference conversion, independently specified by the
canonical substitution homomorphism. The selected variable maps to outer
`Polynomial.X`; every other variable maps to a coefficient variable with its
original index. Thus coefficient monomials contain no selected variable.
This definition does not invoke the alternate coefficient-sum conversion. -/
def mpolyToMpolyPoly {R : Type*} [CommRing R] [Nontrivial R]
    (x : ℕ) (p : MvPolynomial ℕ R) : Polynomial (MvPolynomial ℕ R) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun j => if j = x then Polynomial.X else Polynomial.C (MvPolynomial.X j)) p

/-- PDF p. 11: convert each polynomial in the given ordered list, retaining
order and multiplicities. -/
def univariateIn (qs : List (MvPolynomial ℕ ℝ)) (x : ℕ) :
    List (Polynomial (MvPolynomial ℕ ℝ)) :=
  qs.map (mpolyToMpolyPoly x)

/-- PDF pp. 11–12: the instance `lowerPoly 0 1` used in the source theorem.
It renames every index `j` to `j - 1`. In its use after conversion at zero,
coefficients contain no variable zero, so truncated subtraction never
identifies two variables that actually occur in those coefficients. -/
def lowerPolyZeroOne : MvPolynomial ℕ ℝ →+* MvPolynomial ℕ ℝ :=
  (MvPolynomial.rename (fun j : ℕ => j - 1)).toRingHom

/-- PDF p. 11: the valuation list supplies the value of variable `j` at
position `j`, and supplies zero at all positions beyond the list. -/
def evalMpoly (xs : List ℝ) : MvPolynomial ℕ ℝ →+* ℝ :=
  MvPolynomial.eval (fun j => xs.getD j 0)

/-- PDF p. 11: evaluate the multivariate coefficients, leaving the outer
univariate variable untouched. -/
def evalMpolyPoly (xs : List ℝ) (p : Polynomial (MvPolynomial ℕ ℝ)) :
    Polynomial ℝ :=
  p.map (evalMpoly xs)

/- Sanity examples concern definitions only; the three source results below
remain statement targets. -/

example {R : Type*} [CommRing R] [Nontrivial R] (x i : ℕ) :
    isolateVariableSparse (0 : MvPolynomial ℕ R) x i = 0 := by
  simp [isolateVariableSparse]

example (d : ℕ →₀ ℕ) (x : ℕ) : (d.erase x) x = 0 := by
  simp

example {R : Type*} [CommRing R] [Nontrivial R] (x : ℕ) :
    mpolyToMpolyPolyAlt x (0 : MvPolynomial ℕ R) = 0 := by
  simp [mpolyToMpolyPolyAlt, isolateVariableSparse]

example {R : Type*} [CommRing R] [Nontrivial R] (x : ℕ) :
    mpolyToMpolyPoly x (MvPolynomial.X x : MvPolynomial ℕ R) = Polynomial.X := by
  simp [mpolyToMpolyPoly]

example : univariateIn [] 0 = [] := by
  rfl

example : lowerPolyZeroOne (MvPolynomial.X 1) = MvPolynomial.X 0 := by
  simp [lowerPolyZeroOne]

example (j : ℕ) : evalMpoly [] (MvPolynomial.X j) = 0 := by
  simp [evalMpoly]

example (x : ℝ) : evalMpoly [x] (MvPolynomial.X 0) = x := by
  simp [evalMpoly]

example (xs : List ℝ) : evalMpolyPoly xs 0 = 0 := by
  simp [evalMpolyPoly]

end

end QAlgorithms.Papers.Independent.Next46.P03


