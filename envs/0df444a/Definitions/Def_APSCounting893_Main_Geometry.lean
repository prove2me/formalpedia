-- Prove2me | Definitions.Def_APSCounting893_Main_Geometry
-- name    : APSCounting893_Main_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:00:40.359217+00:00
-- url     : https://prove2.me/theorems/465a45fe-bc32-48d9-a033-e86f760cbfb3
-- title:
--   Affine geometry, Puiseux witnesses and projective degree
-- statement:
--   For a polynomial map $F$, let $Y$ be its Zariski image closure and let $\operatorname{Ann}(F)$ be the kernel of polynomial substitution. Coordinate rings are polynomial rings modulo their pointwise vanishing ideals. An irreducible affine variety is nonempty, closed and not a union of two proper closed subsets. Components are maximal such subsets.
--
--   The Puiseux domain is the union of all positive-denominator ramified Laurent subfields inside rational-exponent Hahn series. Its valuation has $\operatorname{ord}_t(0)=+\infty$, and residue means the coefficient of $t^0$. Approximate vanishing is
--
--   $$\operatorname{AV}(F)=\{x\in\mathcal K^n:\operatorname{ord}_t f_i(x)>0\text{ for every }i\}.$$
--
--   Finite morphisms are expressed as finite generation of the actual coordinate module using polynomial representatives. Normalization has the source formula $\pi_c(y)_i=y_i-c_i y_{n+1}$, with separate injectivity, surjectivity, finiteness and coordinate-integrality predicates. Projective degree is the leading Hilbert-polynomial coefficient times the dimension factorial, using the filtered coordinate-ring Hilbert function. It is not replaced by cumulative component degree. These notions support the geometric milestones.
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), §§3.1–3.2; §3 degree convention, p. 11, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Mathlib
import Definitions.Def_RSCapacity_AffineGeometry
import Definitions.Def_HahnSeries_RamificationBound

set_option autoImplicit false

namespace APSCounting893.Main

abbrev Affine (K : Type) (n : ℕ) := Fin n → K
abbrev Polynomials (K : Type) [CommSemiring K] (n : ℕ) := MvPolynomial (Fin n) K
abbrev PolynomialMap (K : Type) [CommSemiring K] (n m : ℕ) := Fin m → Polynomials K n

noncomputable def evaluate {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (x : Affine K n) : Affine K m :=
  fun j => MvPolynomial.eval x (F j)

noncomputable def imageClosure {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) : Set (Affine K m) := RSCapacity.zClosure (Set.range (evaluate F))

noncomputable def hasAPS {n m : ℕ} (F : PolynomialMap ℂ n m) : Prop :=
  (0 : Affine ℂ m) ∈ imageClosure F

noncomputable def annihilator {n m : ℕ} (F : PolynomialMap ℂ n m) :
    Ideal (Polynomials ℂ m) := RingHom.ker (MvPolynomial.eval₂Hom MvPolynomial.C F)

abbrev PuiseuxAmbient := HahnSeries ℚ ℂ

def IsPuiseux (s : PuiseuxAmbient) : Prop :=
  ∃ (e : ℕ) (he : 0 < e), s ∈ HahnSeries.puiseuxRamSubfield ℂ he

def PuiseuxIntegral (s : PuiseuxAmbient) : Prop := IsPuiseux s ∧ 0 ≤ s.orderTop

noncomputable def residue (s : PuiseuxAmbient) : ℂ := s.coeff 0

noncomputable def approximateVanishing {n m : ℕ} (F : PolynomialMap ℂ n m) :
    Set (Affine PuiseuxAmbient n) :=
  {x | (∀ i, IsPuiseux (x i)) ∧
    ∀ j, 0 < (MvPolynomial.eval₂ HahnSeries.C x (F j)).orderTop}

/-- The ideal of actual pointwise vanishing polynomials defines the coordinate ring. -/
abbrev CoordinateRing {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) :=
  Polynomials K n ⧸ MvPolynomial.vanishingIdeal K X

noncomputable def coordinate {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (i : Fin n) : CoordinateRing X :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- Nonempty irreducible closed sets, without assuming irreducibility of every variety. -/
def IrreducibleAffine {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) : Prop :=
  X.Nonempty ∧ RSCapacity.IsAlgSet X ∧
    ∀ A B : Set (Affine K n), RSCapacity.IsAlgSet A → RSCapacity.IsAlgSet B →
      X ⊆ A ∪ B → X ⊆ A ∨ X ⊆ B

def AffineComponent {K : Type} [Field K] {n : ℕ} (X W : Set (Affine K n)) : Prop :=
  IrreducibleAffine W ∧ W ⊆ X ∧
    ∀ W' : Set (Affine K n), IrreducibleAffine W' → W ⊆ W' → W' ⊆ X → W' = W

def RelativeOpen {K : Type} [Field K] {n : ℕ} (X U : Set (Affine K n)) : Prop :=
  U ⊆ X ∧ RSCapacity.IsAlgSet (X \ U)

/-- Finite generation of the coordinate ring as a module, spelled out using polynomial
representatives. Relations are equalities of functions on X, hence equalities modulo I(X). -/
noncomputable def FiniteMorphism {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) : Prop :=
  ∃ (s : ℕ) (generators : Fin s → Polynomials K n),
    ∀ f : Polynomials K n, ∃ coefficients : Fin s → Polynomials K m,
      ∀ x ∈ X, MvPolynomial.eval x f =
        ∑ i, MvPolynomial.eval (evaluate F x) (coefficients i) *
          MvPolynomial.eval x (generators i)

/-- The prescribed normalization π(y)=(yᵢ−cᵢyₙ₊₁). -/
noncomputable def normalizationPolynomials {n : ℕ} (c : Affine ℂ n) :
    PolynomialMap ℂ (n + 1) n :=
  fun i => MvPolynomial.X i.castSucc - MvPolynomial.C (c i) * MvPolynomial.X (Fin.last n)

noncomputable def normalization {n : ℕ} (c : Affine ℂ n) : Affine ℂ (n + 1) → Affine ℂ n :=
  evaluate (normalizationPolynomials c)

/-- Pullback injectivity is stated on representatives in the two coordinate rings. -/
noncomputable def PullbackInjective {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (Y : Set (Affine K m)) (F : PolynomialMap K n m) : Prop :=
  ∀ f : Polynomials K m,
    (∀ x ∈ X, MvPolynomial.eval (evaluate F x) f = 0) →
      ∀ y ∈ Y, MvPolynomial.eval y f = 0

/-- Coordinate integrality over the actual pullback image: a monic equation, degree ≥1. -/
noncomputable def CoordinatesIntegral {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) : Prop :=
  ∀ j : Fin n, ∃ (d : ℕ) (_ : 0 < d) (coefficients : Fin d → Polynomials K m),
    ∀ x ∈ X, x j ^ d + ∑ i : Fin d,
      MvPolynomial.eval (evaluate F x) (coefficients i) * x j ^ i.val = 0

noncomputable def IsNormalization {n : ℕ} (Y : Set (Affine ℂ (n + 1)))
    (c : Affine ℂ n) : Prop :=
  FiniteMorphism Y (normalizationPolynomials c) ∧ normalization c '' Y = Set.univ ∧
    PullbackInjective Y Set.univ (normalizationPolynomials c) ∧
    CoordinatesIntegral Y (normalizationPolynomials c)

/-- The Hilbert function of the projective closure, in its affine filtration description. -/
noncomputable def affineFilteredPiece {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) : Submodule K (X → K) :=
  Submodule.span K {f | ∃ p : Polynomials K n, p.totalDegree ≤ d ∧
    f = fun x => MvPolynomial.eval x.val p}

noncomputable def affineHilbertFunction {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) : ℕ := Module.finrank K (affineFilteredPiece X d)

/-- The unique eventual polynomial of the filtered coordinate ring. Defining this through
actual Hilbert functions avoids substituting a sum of component degrees for projective degree. -/
noncomputable def affineHilbertPolynomial {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) : Polynomial ℚ :=
  Classical.epsilon (fun p : Polynomial ℚ => ∃ N : ℕ, ∀ d ≥ N,
    p.eval (d : ℚ) = (affineHilbertFunction X d : ℚ))

noncomputable def projectiveDegree {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) : ℕ :=
  let p := affineHilbertPolynomial X
  (p.leadingCoeff * (p.natDegree.factorial : ℚ)).num.natAbs

/-- A line is the whole affine line; its direction is required nonzero by the statements. -/
def affineLine {K : Type} [Field K] {n : ℕ} (base direction : Affine K n) : Set (Affine K n) :=
  Set.range (fun t : K => base + t • direction)

end APSCounting893.Main


