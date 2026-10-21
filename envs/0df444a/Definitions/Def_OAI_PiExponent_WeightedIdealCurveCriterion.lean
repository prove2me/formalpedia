-- Prove2me | Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
-- name    : OAI_PiExponent_WeightedIdealCurveCriterion
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-20T18:18:21.714605+00:00
-- url     : https://prove2.me/theorems/1488f580-223c-4515-9dd6-73cdd74ff290
-- title:
--   Normalized function-field places and weighted affine ideal contact
-- statement:
--   Defines normalized integer-valued places trivial on Complex, weighted coordinate pole degree, affine ideal contact, and a uniform contact-to-degree inequality over all generating function-field curves. Finite-colength and positivity requirements are explicit hypotheses of the proposed general theorem.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Order.Lattice.Nat
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Valuation.Basic

open scoped BigOperators

noncomputable section
namespace OAI.PiExponent.FormalInterpolation

/-- The integer-valued, normalized discrete places trivial on the constant
field. Surjectivity onto the integers excludes the trivial valuation and
excludes multiple rescalings of the same place. -/
def PolynomialCurvePlace (E : Type) [Field E] [Algebra Complex E] :=
  {nu : AddValuation E (WithTop Int) //
    (∀ b : Complex, b ≠ 0 → nu (algebraMap Complex E b) = 0) ∧
    (∀ k : Int, ∃ f : E, nu f = (k : WithTop Int))}

/-- Order with the harmless value zero assigned to the zero function.
Only pole computations use this convention. -/
def polynomialCurveOrder {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (f : E) : Int :=
  (nu.1 f).untop₀

/-- The pole of the rational weighted hyperplane class at a place.
The additional `none` entry contributes zero, including in dimension zero. -/
def polynomialCurvePole {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E) (w : Fin d → Rat) : Real := by
  classical
  exact (Finset.univ : Finset (Option (Fin d))).sup' (by simp)
    (fun i => i.elim 0 (fun j =>
      -(polynomialCurveOrder nu (x j) : Real) / (w j : Real)))

/-- Order of an affine ideal along a curve branch. It is zero away from
its affine chart. At an affine branch it is the least finite order attained
by an element of the ideal. The empty set has infimum zero in `Nat`;
finite colength and a generating nonconstant curve ensure nonemptiness
whenever this definition is used in the curve criterion. -/
def polynomialCurveIdealContact {d : Nat} {E : Type}
    [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Ideal (MvPolynomial (Fin d) Complex)) : Nat := by
  classical
  exact if (∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) then
    sInf {k : Nat | ∃ f : MvPolynomial (Fin d) Complex,
      f ∈ I ∧ nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)}
  else 0

/-- A uniform curve test: total contact with the affine ideal is at most
`rho` times weighted pole degree, for every generating function-field curve.
For such one-variable function fields the pole divisor has finite support;
for a finite-colength ideal the contact divisor does too. -/
def WeightedIdealCurveBound {d : Nat}
    (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (rho : Rat) : Prop :=
  ∀ (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E],
    Algebra.trdeg Complex E = 1 → ∀ x : Fin d → E,
    IntermediateField.adjoin Complex (Set.range x) = ⊤ →
      (∑ᶠ nu : PolynomialCurvePlace E,
        (polynomialCurveIdealContact nu x I : Real)) ≤
      (rho : Real) *
        ∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w

end OAI.PiExponent.FormalInterpolation


