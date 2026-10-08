-- Prove2me | Definitions.Def_Nagata
-- name    : Nagata
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:19.376925+00:00
-- url     : https://prove2.me/theorems/e188b7c1-a774-4015-a14a-102053fe5fb7
-- statement:
--   This block sets up the algebraic and projective-geometric infrastructure for a Nagata-type inequality on configurations of points in the complex projective plane, and states no inequality itself. For a point in K^σ, its point ideal is the kernel of evaluation there, and a polynomial has order at least m at the point if it lies in the m-th power of that ideal. The translation ring homomorphism sends each variable X_i to X_i + point_i and fixes constants; translating by the negated point gives an inverse, so translation is a ring isomorphism and preserves nonzeroness. For nonzero f, the ordinary multiplicity at a point is the least total degree of a monomial in the translated polynomial. Projectively, PlanePoint is a point of the complex projective plane, and OrderedDistinctPoints(n) is an injective n-tuple of such points. A multihomogeneous equation is a polynomial in 3n variables (n triples of coordinates) together with degrees d_i such that every monomial has degree d_i in the i-th triple. It vanishes at a tuple of points if it evaluates to zero at every choice of nonzero representative vectors. A subset of the product of planes is Zariski closed if it is the common zero locus of a set of such equations, and a set of ordered distinct configurations is closed if it is the restriction of such a closed set to the distinct configurations. Dehomogenization in a chart sets the chosen coordinate to 1, and chart coordinates divide the other coordinates of a point by that coordinate. A ternary form has multiplicity at least m at a plane point if, in every chart where the point has a nonzero coordinate, its dehomogenization lies in the m-th power of the point ideal at the chart coordinates; some such chart always exists. Finally, a worker namespace views a ternary polynomial as an element of the associates monoid, takes its irreducible factorization multiplicities, and pushes these forward to a finitely supported function from principal ideals to natural numbers, an ideal cycle recording each irreducible factor's multiplicity.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Nagata.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Nagata.lean; bytes 996..7378
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

namespace OAI

/-!
# Nagata's strict inequality for very general complex plane configurations

The exceptional family is chosen before every curve and multiplicity vector.
Closedness means common multihomogeneous zero loci on the product of projective
planes, restricted to the open set of ordered distinct configurations.
-/

noncomputable section

open scoped BigOperators

namespace Nagata.AffineMultiplicity

variable {σ K : Type*} [CommRing K]

def pointIdeal (point : σ → K) : Ideal (MvPolynomial σ K) :=
  RingHom.ker (MvPolynomial.eval point)

def orderAtLeast (point : σ → K) (multiplicity : ℕ)
    (polynomial : MvPolynomial σ K) : Prop :=
  polynomial ∈ pointIdeal point ^ multiplicity

def translateHom (point : σ → K) : MvPolynomial σ K →+* MvPolynomial σ K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun index => MvPolynomial.X index + MvPolynomial.C (point index))

@[simp] theorem translateHom_C (point : σ → K) (coefficient : K) :
    translateHom point (MvPolynomial.C coefficient) = MvPolynomial.C coefficient := by
  simp [translateHom]

@[simp] theorem translateHom_X (point : σ → K) (index : σ) :
    translateHom point (MvPolynomial.X index) = MvPolynomial.X index + MvPolynomial.C (point index) := by
  simp [translateHom]

theorem translateHom_neg_comp (point : σ → K) :
    (translateHom (-point)).comp (translateHom point) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro coefficient; simp
  · intro index; simp [add_assoc]

theorem translateHom_comp_neg (point : σ → K) :
    (translateHom point).comp (translateHom (-point)) = RingHom.id _ := by
  simpa only [neg_neg] using translateHom_neg_comp (-point)

def translateEquiv (point : σ → K) : MvPolynomial σ K ≃+* MvPolynomial σ K :=
  { translateHom point with
    invFun := translateHom (-point)
    left_inv := fun polynomial => RingHom.congr_fun (translateHom_neg_comp point) polynomial
    right_inv := fun polynomial => RingHom.congr_fun (translateHom_comp_neg point) polynomial }

@[simp] theorem translateEquiv_apply (point : σ → K) (polynomial : MvPolynomial σ K) :
    translateEquiv point polynomial = translateHom point polynomial := rfl

theorem translate_ne_zero (point : σ → K) (polynomial : MvPolynomial σ K)
    (nonzero : polynomial ≠ 0) : translateHom point polynomial ≠ 0 := by
  intro translated_zero
  apply nonzero
  apply (translateEquiv point).injective
  simpa only [translateEquiv_apply, map_zero] using translated_zero

theorem translated_support_nonempty (point : σ → K) (polynomial : MvPolynomial σ K)
    (nonzero : polynomial ≠ 0) : (translateHom point polynomial).support.Nonempty :=
  MvPolynomial.support_nonempty.mpr (translate_ne_zero point polynomial nonzero)

/-- The least total degree of a nonzero Taylor coefficient. -/
def ordinaryMultiplicity (point : σ → K) (polynomial : MvPolynomial σ K)
    (nonzero : polynomial ≠ 0) : ℕ :=
  (translateHom point polynomial).support.inf'
    (translated_support_nonempty point polynomial nonzero) Finsupp.degree

end Nagata.AffineMultiplicity

namespace Nagata.ProjectiveGeometry

abbrev PlanePoint := Projectivization ℂ (Fin 3 → ℂ)

abbrev OrderedDistinctPoints (count : ℕ) :=
  {points : Fin count → PlanePoint // Function.Injective points}

structure MultihomogeneousEquation (count : ℕ) where
  polynomial : MvPolynomial (Fin count × Fin 3) ℂ
  multidegree : Fin count → ℕ
  homogeneous : ∀ exponent ∈ polynomial.support, ∀ index,
    (∑ coordinate : Fin 3, exponent (index, coordinate)) = multidegree index

def equationVanishes {count : ℕ} (equation : MultihomogeneousEquation count)
    (points : Fin count → PlanePoint) : Prop :=
  ∀ (vectors : Fin count → Fin 3 → ℂ) (nonzero : ∀ index, vectors index ≠ 0),
    (∀ index, Projectivization.mk ℂ (vectors index) (nonzero index) = points index) →
    MvPolynomial.eval (fun index => vectors index.1 index.2) equation.polynomial = 0

def IsProductZariskiClosed {count : ℕ} (locus : Set (Fin count → PlanePoint)) : Prop :=
  ∃ equations : Set (MultihomogeneousEquation count),
    ∀ points, points ∈ locus ↔ ∀ equation ∈ equations, equationVanishes equation points

def IsConfigurationZariskiClosed {count : ℕ}
    (locus : Set (OrderedDistinctPoints count)) : Prop :=
  ∃ ambient : Set (Fin count → PlanePoint), IsProductZariskiClosed ambient ∧
    ∀ points, points ∈ locus ↔ points.val ∈ ambient

abbrev ChartVariables (chart : Fin 3) := {coordinate : Fin 3 // coordinate ≠ chart}

def dehomogenize (chart : Fin 3) (polynomial : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (ChartVariables chart) ℂ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun coordinate => if equal : coordinate = chart then 1
      else MvPolynomial.X ⟨coordinate, equal⟩) polynomial

def chartCoordinates (chart : Fin 3) (point : PlanePoint) : ChartVariables chart → ℂ :=
  fun coordinate => point.rep coordinate.val / point.rep chart

/-- Local multiplicity lower bounds are membership in powers of the point ideal. -/
def multiplicityAtLeast (polynomial : MvPolynomial (Fin 3) ℂ)
    (point : PlanePoint) (multiplicity : ℕ) : Prop :=
  ∀ chart : Fin 3, point.rep chart ≠ 0 →
    AffineMultiplicity.orderAtLeast (chartCoordinates chart point) multiplicity
      (dehomogenize chart polynomial)

theorem chart_exists (point : PlanePoint) : ∃ chart : Fin 3, point.rep chart ≠ 0 := by
  by_contra absent
  apply point.rep_nonzero
  funext chart
  exact Classical.not_not.mp (fun nonzero => absent ⟨chart, nonzero⟩)

end Nagata.ProjectiveGeometry

namespace Nagata.Workers.W30

open UniqueFactorizationMonoid

abbrev TernaryPolynomial := MvPolynomial (Fin 3) ℂ

local instance : DecidableEq (Associates TernaryPolynomial) := Classical.decEq _

def equationMultiplicity (polynomial : TernaryPolynomial) :
    Associates TernaryPolynomial →₀ ℕ :=
  factorization (Associates.mk polynomial)

def associatePrincipalIdeal (associate : Associates TernaryPolynomial) :
    Ideal TernaryPolynomial :=
  (Ideal.associatesEquivIsPrincipal TernaryPolynomial associate).val

def equationIdealCycle (polynomial : TernaryPolynomial) : Ideal TernaryPolynomial →₀ ℕ :=
  (equationMultiplicity polynomial).mapDomain associatePrincipalIdeal

attribute [local instance] MvPolynomial.gradedAlgebra



end Nagata.Workers.W30
end
end OAI


