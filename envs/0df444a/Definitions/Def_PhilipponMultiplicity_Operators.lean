-- Prove2me | Definitions.Def_PhilipponMultiplicity_Operators
-- name    : PhilipponMultiplicity_Operators
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-23T20:20:52.667889+00:00
-- url     : https://prove2.me/theorems/6186ecde-559c-4038-9a1c-fe6062c2b983
-- title:
--   Polynomial translation operators and local component retention
-- statement:
--   Actual polynomial translation charts with analytic coefficients, substitution and coefficient-wise iterated differentiation, generated ideals, and intersections of contractions from localization at all homogeneous representatives of group points. The comparison with source primary-component retention and atlas independence remain separate theorem obligations.
--
--   Compiled, admission-free definition bundle. Theorems asserting its substantive properties remain open targets in the full-paper goal.
-- source:
--   Philippon 1986, §§2–5; 1987 corrections/addenda. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_Analytic

/-!
# Philippon's polynomial translation/differentiation operators

The chart coordinates are actual finite polynomials in the projective
coordinates, with actual analytic functions as coefficients. The operators
substitute those polynomials, differentiate their coefficients, and reassemble
the resulting polynomial. No ideal or degree estimate is supplied as data.

The group-retention operation is a literal intersection of contractions of
localized ideals at all homogeneous representatives of group points. Its
comparison with the primary-component presentation in Definition 4.2 is a
separate theorem. It preserves local ideal membership, not just zero loci.
-/

set_option autoImplicit false

open scoped BigOperators Topology
open Filter
noncomputable section

namespace PhilipponMultiplicity

universe u

variable {K : Type u} [NontriviallyNormedField K]

/-- The coefficient ring consists of functions of the analytic parameters. -/
abbrev AnalyticCoefficientRing {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) :=
  A.ParameterSpace → K

/-- Evaluate a polynomial with parameter-function coefficients at an actual
group point and a parameter value. -/
def evaluateCoefficientPolynomial {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G)
    (P : MvPolynomial G.ambient.Variable (AnalyticCoefficientRing A))
    (x : G.Point) (z : A.ParameterSpace) : K :=
  MvPolynomial.eval₂Hom (Pi.evalRingHom (fun _ : A.ParameterSpace => K) z)
    (G.ambient.coordinate (G.embedding x)) P

/-- One Zariski chart for translating by `g` and the local analytic subgroup.
The parameter neighborhood in the representation may depend on `x`.
This is the germwise representation needed to define the source operators;
any stronger uniform product-neighborhood presentation supplies this data. -/
structure TranslationChart {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G)
    (g : G.Point) where
  domain : Set G.Point
  domain_isOpen : @IsOpen _ G.zariskiTopology domain
  degree : G.FactorIndex → ℕ
  coordinates : G.ambient.Variable →
    MvPolynomial G.ambient.Variable (AnalyticCoefficientRing A)
  coefficient_analytic : ∀ v, ∀ e ∈ (coordinates v).support,
    AnalyticAt K ((coordinates v).coeff e) 0
  coordinate_homogeneous : ∀ v, ∀ e ∈ (coordinates v).support,
    (∑ j : Fin (G.ambient.ambientDimension v.1 + 1), e ⟨v.1, j⟩) = degree v.1 ∧
      ∀ i : G.FactorIndex, i ≠ v.1 →
        (∑ j : Fin (G.ambient.ambientDimension i + 1), e ⟨i, j⟩) = 0
  /- Rational translation formulas remain projectively compatible wherever
  they are evaluated, although their entire tuple may vanish off the chart.
  This excludes arbitrary off-chart polynomials (including on other
  connected components) from the global operator ideal. -/
  coordinate_compatible : ∀ x : G.Point, ∀ i : G.FactorIndex,
    ∀ j k : Fin (G.ambient.ambientDimension i + 1),
      ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
        evaluateCoefficientPolynomial A (coordinates ⟨i, j⟩) x z *
            A.lift (g + x) z ⟨i, k⟩ =
          evaluateCoefficientPolynomial A (coordinates ⟨i, k⟩) x z *
            A.lift (g + x) z ⟨i, j⟩
  represents : ∀ x ∈ domain,
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∃ hz : z ∈ A.domain, ∀ i : G.FactorIndex,
        ∃ h : (fun j => evaluateCoefficientPolynomial A (coordinates ⟨i, j⟩) x z) ≠ 0,
          Projectivization.mk K
            (fun j => evaluateCoefficientPolynomial A (coordinates ⟨i, j⟩) x z) h =
              G.embedding (x + g + A.map ⟨z, hz⟩) i

/-- An actual Zariski cover by polynomial translation charts. -/
structure TranslationAtlas {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G)
    (g : G.Point) where
  Index : Type u
  chart : Index → TranslationChart A g
  covers : ∀ x : G.Point, ∃ a : Index, x ∈ (chart a).domain

/-- A coordinatewise bound on the actual chart degrees. The existence of
embedding-dependent bounds for such atlases is a separate geometric theorem. -/
def TranslationAtlas.IsBoundedBy {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}
    {g : G.Point} (atlas : TranslationAtlas A g) (c : G.FactorIndex → ℕ) : Prop :=
  ∀ a : atlas.Index, ∀ i : G.FactorIndex, (atlas.chart a).degree i ≤ c i

/-- Substitute the chart coordinate polynomials into `P`, with constant
coefficients embedded as constant parameter functions. -/
def substitutedPolynomial {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}
    {g : G.Point} (chart : TranslationChart A g) (P : G.CoordinateRing) :
    MvPolynomial G.ambient.Variable (AnalyticCoefficientRing A) :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Pi.constRingHom A.ParameterSpace K)) chart.coordinates P

/-- Source Definition 4.1. An ordered tuple of coordinate directions describes
a mixed partial derivative; repeated directions are allowed. -/
def polynomialOperator {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}
    {g : G.Point} (chart : TranslationChart A g) (order : ℕ)
    (directions : Fin order → Fin A.parameterDimension) (P : G.CoordinateRing) :
    G.CoordinateRing :=
  (AddMonoidAlgebra.coeff (substitutedPolynomial chart P)).sum fun e coefficient =>
    MvPolynomial.monomial e
      (iteratedFDeriv K order coefficient 0
        (fun i => Pi.single (directions i) 1))

/-- A genuine nonzero homogeneous representative of a group point in every
projective factor. Retention ranges over all such representatives. -/
structure GroupHomogeneousRepresentative (G : EmbeddedGroupProduct K) where
  point : G.Point
  coordinates : G.ambient.Variable → K
  nonzero : ∀ i : G.FactorIndex, (fun j => coordinates ⟨i, j⟩) ≠ 0
  represents : ∀ i : G.FactorIndex,
    Projectivization.mk K (fun j => coordinates ⟨i, j⟩) (nonzero i) = G.embedding point i

/-- Every group point has a homogeneous representative; the retention
intersection consequently ranges over a genuine nonempty family. -/
def representativeOfPoint (G : EmbeddedGroupProduct K) (x : G.Point) :
    GroupHomogeneousRepresentative G where
  point := x
  coordinates := G.ambient.coordinate (G.embedding x)
  nonzero i := (G.embedding x i).rep_nonzero
  represents i := (G.embedding x i).mk_rep

def representativeEvaluation (G : EmbeddedGroupProduct K)
    (x : GroupHomogeneousRepresentative G) : G.CoordinateRing →+* K :=
  MvPolynomial.eval x.coordinates

theorem representativeEvaluation_surjective (G : EmbeddedGroupProduct K)
    (x : GroupHomogeneousRepresentative G) :
    Function.Surjective (representativeEvaluation G x) := by
  intro a
  exact ⟨MvPolynomial.C a, MvPolynomial.eval_C (f := x.coordinates) a⟩

/-- The actual maximal ideal of a chosen homogeneous representative. -/
def representativeMaximalIdeal (G : EmbeddedGroupProduct K)
    (x : GroupHomogeneousRepresentative G) : MaximalSpectrum G.CoordinateRing where
  asIdeal := RingHom.ker (representativeEvaluation G x)
  isMaximal := RingHom.ker_isMaximal_of_surjective _ (representativeEvaluation_surjective G x)

/-- Localization at one genuine representative, followed by contraction. -/
def retainAtRepresentative (G : EmbeddedGroupProduct K) (J : Ideal G.CoordinateRing)
    (x : GroupHomogeneousRepresentative G) : Ideal G.CoordinateRing :=
  (J.map (algebraMap G.CoordinateRing
    (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal))).under G.CoordinateRing

/-- Retain precisely the local ideal data on the homogeneous cone above `G`.
For a homogeneous ideal in this Noetherian coordinate ring, comparison with
the intersection of primary components whose projective supports meet `G`
is required separately. Ranging over all representatives avoids relying on
unproved independence from a selected projective representative. -/
def retainOnGroup (G : EmbeddedGroupProduct K) (J : Ideal G.CoordinateRing) :
    Ideal G.CoordinateRing :=
  ⨅ x : GroupHomogeneousRepresentative G, retainAtRepresentative G J x

theorem le_retainOnGroup (G : EmbeddedGroupProduct K) (J : Ideal G.CoordinateRing) :
    J ≤ retainOnGroup G J := by
  apply le_iInf
  intro x
  exact Ideal.le_comap_map

/-- The literal polynomial-generator ideal before the retention operation
in source Definition 4.2. -/
def polynomialOperatorIdeal {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}
    {g : G.Point} (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing) :
    Ideal G.CoordinateRing :=
  G.vanishingIdeal Set.univ ⊔ Ideal.span
    {Q | ∃ P ∈ I, (∃ D, G.ambient.IsHomogeneous P D) ∧
      ∃ a : atlas.Index, ∃ order : ℕ, order ≤ T ∧
        ∃ directions : Fin order → Fin A.parameterDimension,
          Q = polynomialOperator (atlas.chart a) order directions P}

/-- Source Definition 4.2 with a supplied actual chart atlas. Independence
from that atlas, composition, and comparison with the sheaf presentation
are separate theorems, not fields or assumptions here. -/
def retainedPolynomialOperatorIdeal {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}
    {g : G.Point} (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing) :
    Ideal G.CoordinateRing :=
  retainOnGroup G (polynomialOperatorIdeal atlas T I)

end PhilipponMultiplicity


