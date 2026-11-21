-- Prove2me | Definitions.Def_YM_PublicTheory
-- name    : YM_PublicTheory
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T11:36:18.491264+00:00
-- url     : https://prove2.me/theorems/447a4270-602a-405b-9bb6-e1aabd5a3a66
-- title:
--   Gauge groups and Wightman field structures
-- statement:
--   This module fixes the public vocabulary of the construction. A **gauge group** is a compact matrix group: a closed subgroup $G$ of the unitary group $U(n+1)$ together with a real Lie algebra $\mathfrak g\subseteq M_{n+1}(\mathbb C)$ characterized by $X\in\mathfrak g \iff \forall t\in\mathbb R,\ \exp(tX)\in G$. It is **simple** when $\mathfrak g$ is nonabelian and has no nontrivial ideals under the commutator action. Spacetime is $\mathbb R^4$ with time last; test functions are complex Schwartz functions. The module bundles a complex Hilbert space, a field-label space, operator-valued tempered fields on a common dense domain, a strongly continuous translation action, a projection-valued energy-momentum measure, and a proper orthochronous Poincare action, and states the Wightman axioms W0-W3. These definitions are reused by every statement of the mission.
-- source:
--   https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/PublicTheory.lean

import Mathlib

/-! Public gauge and Wightman definitions adapted from an earlier challenge,
commit eea94292e31734d46498be7836d7e8fa50ca8cd2. The symmetry
coordinates cover every proper orthochronous Lorentz transformation and
translation. Their affine action fixes the transformation of test functions. -/
set_option autoImplicit false

noncomputable section

namespace YangMills

open MeasureTheory Set Function
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius

/-! ## Compact simple matrix gauge groups -/

/-- The fixed faithful unitary representation used to describe a gauge
group. -/
abbrev UnitaryRepresentation (n : ℕ) := Matrix.unitaryGroup (Fin (n + 1)) ℂ

/-- A compact matrix gauge group together with its one-parameter Lie
algebra.  The last field prevents the Lie algebra from being arbitrary: it
consists exactly of the matrices whose exponentials stay in the group. -/
structure GaugeGroup where
  n : ℕ
  image : Subgroup (UnitaryRepresentation n)
  imageClosed : IsClosed (image : Set (UnitaryRepresentation n))
  lieAlgebra : Submodule ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  generates : ∀ X,
    X ∈ lieAlgebra ↔
      ∀ t : ℝ, NormedSpace.exp (t • X) ∈
        Set.range (fun u : image ↦ (u.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))

namespace GaugeGroup

/-- Real simplicity of the Lie algebra, including the nonabelian
condition. -/
def IsSimple (gauge : GaugeGroup) : Prop :=
  (∃ X ∈ gauge.lieAlgebra, ∃ Y ∈ gauge.lieAlgebra,
    X * Y - Y * X ≠ 0) ∧
  ∀ ideal : Submodule ℝ (Matrix (Fin (gauge.n + 1)) (Fin (gauge.n + 1)) ℂ),
    ideal ≤ gauge.lieAlgebra →
    (∀ X ∈ gauge.lieAlgebra, ∀ Y ∈ ideal, X * Y - Y * X ∈ ideal) →
    ideal = ⊥ ∨ ideal = gauge.lieAlgebra

end GaugeGroup

/-! ## Spacetime and test functions -/

abbrev Axis := Fin 4
abbrev SpaceAxis := Fin 3
abbrev timeAxis : Axis := Fin.last 3
abbrev Spacetime := EuclideanSpace ℝ Axis
abbrev Space := EuclideanSpace ℝ SpaceAxis

def time (x : Spacetime) : ℝ := x timeAxis

def spatial (x : Spacetime) : Space :=
  WithLp.toLp 2 fun i ↦ x i.castSucc

/-- The closed forward light cone in the convention where time is the final
coordinate. -/
def forwardCone : Set Spacetime := {x | ‖spatial x‖ ≤ time x}

def minkowskiSquare (x : Spacetime) : ℝ := time x ^ 2 - ‖spatial x‖ ^ 2

def spacelike : Set Spacetime := {x | minkowskiSquare x < 0}

abbrev TestFunction := SchwartzMap Spacetime ℂ

/-- Pointwise complex conjugation of a Schwartz test function. -/
def conjugateTest : TestFunction →L[ℝ] TestFunction :=
  SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)

/-! ## Basic quantum-field structures -/

/-- A bundled complex Hilbert space. -/
structure HilbertSpace where
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [innerProductSpace : InnerProductSpace ℂ carrier]
  [completeSpace : CompleteSpace carrier]

attribute [instance] HilbertSpace.normedAddCommGroup
attribute [instance] HilbertSpace.innerProductSpace
attribute [instance] HilbertSpace.completeSpace

namespace HilbertSpace

abbrev Operator (H : HilbertSpace) := H.carrier →L[ℂ] H.carrier

end HilbertSpace

/-- A bundled complex vector space of field labels. -/
structure FieldLabels where
  carrier : Type
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]

attribute [instance] FieldLabels.addCommGroup
attribute [instance] FieldLabels.module

/-- Operator-valued tempered fields on one common invariant domain. -/
structure FieldSystem (H : HilbertSpace) (Labels : FieldLabels) where
  domain : Submodule ℂ H.carrier
  vacuum : domain
  field : Labels.carrier →ₗ[ℂ]
    TestFunction →ₗ[ℂ] (domain →ₗ[ℂ] domain)

namespace FieldSystem

variable {H : HilbertSpace} {Labels : FieldLabels}

def vector (fields : FieldSystem H Labels) :
    List (Labels.carrier × TestFunction) → fields.domain
  | [] => fields.vacuum
  | letter :: word => fields.field letter.1 letter.2 (fields.vector word)

/-- The vacuum expectation of an ordered product of smeared fields. -/
def vacuumExpectation (fields : FieldSystem H Labels) {n : ℕ}
    (labels : Fin n → Labels.carrier) (tests : Fin n → TestFunction) : ℂ :=
  inner ℂ fields.vacuum.1
    (fields.vector (List.ofFn fun i ↦ (labels i, tests i))).1

/-- W1's common-domain, temperedness, and cyclic-vacuum requirements. -/
structure DomainAxioms (fields : FieldSystem H Labels) : Prop where
  normalizedVacuum : ‖fields.vacuum.1‖ = 1
  denseDomain : Dense (fields.domain : Set H.carrier)
  cyclicVacuum : fields.domain =
    Submodule.span ℂ (Set.range fun word ↦ (fields.vector word).1)
  tempered (label : Labels.carrier) (state : fields.domain) :
    Continuous fun test ↦ (fields.field label test state).1

/-- The smeared adjoint identity on the common domain. -/
def AdjointAxiom (fields : FieldSystem H Labels)
    (adjointLabel : Labels.carrier →ₛₗ[starRingEnd ℂ] Labels.carrier) : Prop :=
  ∀ label test (left right : fields.domain),
    inner ℂ (fields.field label test left).1 right.1 =
      inner ℂ left.1
        (fields.field (adjointLabel label) (conjugateTest test) right).1

/-- Two test functions are causally disjoint when every difference of
points in their supports is spacelike. -/
def SpacelikeSeparated (left right : TestFunction) : Prop :=
  ∀ x ∈ tsupport left, ∀ y ∈ tsupport right, x - y ∈ spacelike

/-- W3's local commutativity condition. -/
def LocalCommutativity (fields : FieldSystem H Labels) : Prop :=
  ∀ leftLabel rightLabel leftTest rightTest,
    SpacelikeSeparated leftTest rightTest →
    ∀ state : fields.domain,
      fields.field leftLabel leftTest
          (fields.field rightLabel rightTest state) =
        fields.field rightLabel rightTest
          (fields.field leftLabel leftTest state)

/-- Each nonzero label has a nonzero smeared field operator. -/
def Faithful (fields : FieldSystem H Labels) : Prop :=
  ∀ label : Labels.carrier, label ≠ 0 →
    ∃ test : TestFunction, fields.field label test ≠ 0

end FieldSystem

/-! ## Translations, spectrum, and Poincaré covariance -/

/-- A strongly continuous unitary representation of spacetime
translations. -/
structure TranslationAction (H : HilbertSpace) where
  operator : Spacetime → H.Operator
  identity : operator 0 = ContinuousLinearMap.id ℂ _
  add (x y : Spacetime) :
    (operator x).comp (operator y) = operator (x + y)
  unitary (x : Spacetime) (state : H.carrier) :
    ‖operator x state‖ = ‖state‖
  stronglyContinuous (state : H.carrier) :
    Continuous fun x ↦ operator x state

/-- A projection-valued joint energy–momentum measure. -/
structure EnergyMomentumMeasure (H : HilbertSpace) where
  projection : Set Spacetime → H.Operator
  empty : projection ∅ = 0
  univ : projection Set.univ = ContinuousLinearMap.id ℂ _
  intersection {left right : Set Spacetime} :
    MeasurableSet left → MeasurableSet right →
      (projection left).comp (projection right) = projection (left ∩ right)
  selfAdjoint {region : Set Spacetime} :
    MeasurableSet region →
      (projection region).adjoint = projection region
  countablyAdditive (regions : ℕ → Set Spacetime)
      (measurable : ∀ i, MeasurableSet (regions i))
      (disjoint : Pairwise (Disjoint on regions)) (state : H.carrier) :
    HasSum (fun i ↦ projection (regions i) state)
      (projection (⋃ i, regions i) state)
  diagonal : H.carrier → Measure Spacetime
  finite (state : H.carrier) : IsFiniteMeasure (diagonal state)
  diagonalIdentity {region : Set Spacetime} (measurable : MeasurableSet region)
      (state : H.carrier) :
    ↑((diagonal state).real region) =
      inner ℂ state (projection region state)

namespace EnergyMomentumMeasure

attribute [instance] finite

end EnergyMomentumMeasure

/-- Proper, time-orientation-preserving linear transformations of Minkowski space. -/
abbrev ProperLorentz := {g : (Spacetime →L[ℝ] Spacetime)ˣ //
  LinearMap.det g.val.toLinearMap = 1 ∧
  (∀ x, minkowskiSquare (g.val x) = minkowskiSquare x) ∧
  (∀ x, g.val x ∈ forwardCone ↔ x ∈ forwardCone)}

/-- Standard coordinates on the full proper orthochronous Poincaré group. -/
abbrev PoincareCoordinates := ProperLorentz × Spacetime

/-- An action in any homeomorphic coordinate system, with its group law and
pullback of tests fixed by the ordinary affine action on spacetime. -/
structure PoincareAction (H : HilbertSpace) (Labels : FieldLabels) where
  Symmetry : Type
  [one : One Symmetry]
  [mul : Mul Symmetry]
  [topology : TopologicalSpace Symmetry]
  onStates : Symmetry → H.Operator
  onLabels : Symmetry → Labels.carrier ≃ₗ[ℂ] Labels.carrier
  onTests : Symmetry → TestFunction → TestFunction
  pureTranslation : Spacetime → Symmetry
  identity : onStates 1 = ContinuousLinearMap.id ℂ _
  composition (g h : Symmetry) :
    onStates (g * h) = (onStates g).comp (onStates h)
  unitary (g : Symmetry) (state : H.carrier) :
    ‖onStates g state‖ = ‖state‖
  stronglyContinuous (state : H.carrier) :
    Continuous fun g ↦ onStates g state
  coordinates : Symmetry ≃ₜ PoincareCoordinates
  identityCoordinates : (coordinates 1).1.val = 1 ∧ (coordinates 1).2 = 0
  productCoordinates (g h : Symmetry) :
    (coordinates (g * h)).1.val = (coordinates g).1.val * (coordinates h).1.val ∧
    (coordinates (g * h)).2 = (coordinates g).1.val.val (coordinates h).2 + (coordinates g).2
  translationCoordinates (x : Spacetime) :
    (coordinates (pureTranslation x)).1.val = 1 ∧ (coordinates (pureTranslation x)).2 = x
  pullback (g : Symmetry) (f : TestFunction) (x : Spacetime) :
    onTests g f x = f (((coordinates g).1.val⁻¹).val (x - (coordinates g).2))
  translationZero : pureTranslation 0 = 1
  translationAdd (x y : Spacetime) :
    pureTranslation (x + y) = pureTranslation x * pureTranslation y

attribute [instance] PoincareAction.one
attribute [instance] PoincareAction.mul
attribute [instance] PoincareAction.topology

/-! ## Wightman axioms W0–W3 -/

/-- The observable data of a relativistic quantum field theory. -/
structure WightmanTheory (H : HilbertSpace) (Labels : FieldLabels) where
  fields : FieldSystem H Labels
  adjointLabel : Labels.carrier →ₛₗ[starRingEnd ℂ] Labels.carrier
  translations : TranslationAction H
  energyMomentum : EnergyMomentumMeasure H
  poincare : PoincareAction H Labels
  translationCompatibility (x : Spacetime) :
    poincare.onStates (poincare.pureTranslation x) = translations.operator x

namespace WightmanTheory

variable {H : HilbertSpace} {Labels : FieldLabels}

/-- W0: Hilbert-space covariance, the spectrum condition, and uniqueness of
the invariant vacuum. -/
structure W0 (theory : WightmanTheory H Labels) : Prop where
  spectralRepresentation : ∀ state : H.carrier, ∀ momentum : Spacetime,
    charFun (theory.energyMomentum.diagonal state) momentum =
      inner ℂ state (theory.translations.operator momentum state)
  positiveEnergy :
    theory.energyMomentum.projection forwardConeᶜ = 0
  uniqueVacuum (state : H.carrier) :
    (∀ x, theory.translations.operator x state = state) →
      ∃ scalar : ℂ, scalar • theory.fields.vacuum.1 = state

/-- W1: fields are tempered operator-valued distributions on a common dense
invariant domain, with the vacuum cyclic. -/
structure W1 (theory : WightmanTheory H Labels) : Prop where
  domain : theory.fields.DomainAxioms
  adjoint : theory.fields.AdjointAxiom theory.adjointLabel

/-- W2: Poincaré covariance of the fields and their common domain. -/
structure W2 (theory : WightmanTheory H Labels) : Prop where
  labelIdentity (label : Labels.carrier) :
    theory.poincare.onLabels 1 label = label
  labelComposition (g h : theory.poincare.Symmetry)
      (label : Labels.carrier) :
    theory.poincare.onLabels (g * h) label =
      theory.poincare.onLabels g (theory.poincare.onLabels h label)
  domainInvariant (g : theory.poincare.Symmetry) :
    Set.MapsTo (theory.poincare.onStates g)
      (theory.fields.domain : Set H.carrier) theory.fields.domain
  vacuumInvariant (g : theory.poincare.Symmetry) :
    theory.poincare.onStates g theory.fields.vacuum.1 =
      theory.fields.vacuum.1
  fieldCovariance (g : theory.poincare.Symmetry)
      (label : Labels.carrier) (test : TestFunction)
      (state : theory.fields.domain) :
    theory.poincare.onStates g (theory.fields.field label test state).1 =
      (theory.fields.field (theory.poincare.onLabels g label)
        (theory.poincare.onTests g test)
        ⟨theory.poincare.onStates g state.1,
          domainInvariant g state.2⟩).1

/-- W3: local commutativity at spacelike separation. -/
structure W3 (theory : WightmanTheory H Labels) : Prop where
  locality : theory.fields.LocalCommutativity

/-- The four Wightman axioms are separate fields so the Comparator checks
each one explicitly. -/
structure Axioms (theory : WightmanTheory H Labels) : Prop where
  w0 : W0 theory
  w1 : W1 theory
  w2 : W2 theory
  w3 : W3 theory

end WightmanTheory

end YangMills

end


