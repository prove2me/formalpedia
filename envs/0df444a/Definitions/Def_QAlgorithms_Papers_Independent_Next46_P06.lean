-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06
-- name    : QAlgorithms_Papers_Independent_Next46_P06
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T13:32:41.827835+00:00
-- url     : https://prove2.me/theorems/1ac67017-b0c7-4e4f-8d3d-98825389a9ca
-- title:
--   Definitions for On the Fundamental Principles of Unbounded Functional Calculi
-- statement:
--   The objects the formalized statements of *On the Fundamental Principles of Unbounded Functional Calculi* (arXiv:2009.04733) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Graph`: Operator relations, with the graphDomain retained (PDF p.4).
--   - `identityGraph`: Identity on the full space (PDF p.4).
--   - `banachBoundedGraph`: Graph of an everywhere-defined bounded complex-linear operator (PDF p.4).
--   - `graphRange`: Range of an operator relation (PDF p.4).
--   - `graphAdd`: Sum on the intersection of the domains (PDF p.4).
--   - `graphMul`: Composition AB applies B first (PDF p.4).
--   - `graphScale`: Scalar multiplication retains the graphDomain even at scalar zero (PDF p.4).
--   - `graphInverse`: The inverse relation swaps graph coordinates (PDF p.4).
--   - `BanachClosedOperator`: A closed, single-valued complex-linear graph; no density assumption (PDF p.4).
--   - `Bounded`: Bounded means the full graph of a continuous linear map (PDF pp.4–5).
--   - `InjectiveGraph`: Injectivity on the actual graphDomain (PDF p.5).
--   - `boundedValue`: A bounded-map selector, used only under Bounded (PDF p.5). The zero fallback is never used as a boundedness assertion.
--   - `graphValue`: A graph-value selector, used only on its graphDomain (PDF p.4).
--   - `SubalgebraSet`: Nonunital complex subalgebra, expressed on its ambient carrier (PDF p.13).
--   - `UnitalSubalgebraSet`: A unital complex subalgebra; the ambient algebra need not commute (PDF p.4).
--   - `ProtoOn`: FC1–FC3 on a specified unital subalgebra, with the product-graphDomain equality (PDF p.4). Values outside S are immaterial to this predicate.
--   - `Proto`: A proto-calculus on the whole algebra (PDF p.4).
--   - `boundedElements`: The Phi-bounded symbols (PDF p.5).
--   - `symbolBracket`: The source's symbolBracket [f]_E = {e in E : ef in E} (PDF p.6).
--   - `regularizers`: Regularizers are bounded e with bounded ef (PDF p.6).
--   - `regularizingEquation`: Equality of the two bounded values Phi(ef)x and Phi(e)y (PDF p.6).
--   - `Determines`: Determination is exactly (3.2), including the intersection with reg(f,Phi) (PDF p.6). Empty determining sets are not silently excluded.
--   - `StrongDetermines`: Strong determination uses [f]_E, as in (3.3) (PDF p.6).
--   - `AlgebraicCoreOn`: Algebraic core on a specified subalgebra (PDF p.7).
--   - `CalculusOn`: FC1–FC4 on S, with bounded determination as in FC4 (PDF pp.4,7).
--   - `AbstractCalculus`: A calculus on the whole algebra (PDF p.4).
--   - `PointSeparating`: Common-kernel point separation; the empty family separates only the zero space (PDF p.4).
--   - `AnchorSet`: Anchor sets are nonempty bounded families with trivial common kernel (PDF p.7). This nonempty requirement is retained on the zero Banach space.
--   - `Anchored`: f is anchored in E precisely when [f]_E is an anchor (PDF p.7).
--   - `AnchoredSet`: Every element of S is anchored in E (PDF p.7).
--   - `MulClosedSet`: A multiplicative subset; neither a unit nor nonemptiness is added (PDF p.8).
--   - `setProduct`: Products of two sets, in the displayed order (PDF p.9).
--   - `leftMultipliers`: Left multipliers of E taking E into the bounded part (PDF p.9).
--   - `setCenter`: The center of a subset in the source's sense (PDF p.4).
--   - `CommutativeSet`: Commutativity is imposed exactly when a source clause uses it (PDF p.4).
--   - `pullback`: Pull-back along a unital complex algebra homomorphism (PDF p.11).
--   - `AlgebraRepresentationOn`: A nonunital algebra representation on E (PDF p.13). The total map rho is only constrained and used on E, so no value outside E is prescribed.
--   - `representationGraphs`: The graph-valued bounded representation (PDF p.13).
--   - `canonicalAlgebraicExtension`: The extension constructed by (6.1); functionality and closedness are conclusions under anchoring, not extra premises (PDF p.13).
--   - `maximalAnchored`: The concrete maximal anchored carrier (6.2) (PDF p.15).
--   - `Nondegenerate`: Nondegeneracy means E itself is an anchor (PDF p.15).
--   - `ApproxFor`: Source conditions for an approximate identity for the fixed f. The printed fn on p.18 is corrected to f, as used by the proof on p.19.
--   - `StrongIdentity`: Strong convergence of the bounded Phi(e_n) to I (PDF p.18).
--   - `WeakIdentity`: Weak convergence uses all continuous complex-linear functionals (PDF p.18).
--   - `StrongApprox`: Strong approximate identity for f (PDF p.18).
--   - `WeakApprox`: Weak approximate identity for f (PDF p.18).
--   - `approximateRangeSpan`: The span of all ranges of the approximate identity (PDF p.18).
--   - `transposeGraph`: Complex-linear Banach transpose relation, not a Hilbert adjoint (PDF p.20).
--   - `oppositeBracket`: The opposite-algebra symbolBracket [f]_(B^op), on the original carrier (PDF p.20).
--   - `dualDomain`: Canonical dual extension graphDomain <B^op,F^op,Phi'> (PDF p.20). The order f*b*e is the opposite-algebra instance of formula (6.2).
--   - `dualEvaluation`: The canonical dual calculus constructed from the bounded transposes by (6.1) in the opposite algebra (PDF p.20). Defined as a relation even off its graphDomain; statements use it only on dualDomain.
--   - `dualRangeSpan`: D_f in Theorem 8.1 (PDF p.20).
--   - `dualizableRangeSpan`: D_fb in the dualizability criterion (PDF p.21).
--   - `AlgebraicConvergenceOn`: An algebraic convergence relation on S over an arbitrary index type. Exactly the two source axioms are used: closure as a complex subalgebra of families paired with limits, and convergence of every constant family. No topology, directedness, or eventual-equality axiom is imposed (PDF p.22).
--   - `HausdorffConvergence`: Hausdorff means uniqueness of the limit for a fixed family (PDF p.22).
--   - `JointClosable`: Joint closability is exactly (9.1) (PDF p.22).
--   - `topologicalGraph`: The graph of the topological extension, constructed from simultaneous approximants; it is not an assumed homomorphism (PDF pp.22–23).
--   - `topologicalDomain`: E^tau is the actual graphDomain of simultaneous scalar/operator limits (PDF p.22).
--   - `topologicalValue`: The topological extension value on E^tau (PDF p.23). The zero fallback is outside E^tau and is not used in any assertion about the extension.
--   - `banachResolventShift`: lambda I minus A on dom(A) (PDF p.24).
--   - `banachResolventSet`: Resolvent set of an operator with its actual graphDomain (PDF p.24).
--   - `closedSector`: The closed sector includes zero (PDF p.24).
--   - `Sectorial`: Sectorial operator, with no injectivity or dense-graphDomain assumption (PDF p.24). The resolvent bound is uniform in lambda, on every larger sector.
--   - `onePlusInverse`: R=(I+A)^(-1), only used under sectoriality or the generator hypotheses ensuring the inverse is a full bounded operator (PDF pp.27,35).
--   - `operatorCommutant`: Operator operatorCommutant within bounded operators (PDF p.27).
--   - `OperatorPointSeparating`: Point separation for bounded operator families (PDF p.4). In contrast to an anchor, a point-separating family need not be nonempty on the zero space.
--   - `regularizedStrong`: tau_A^s: strong convergence AFTER multiplication by a common point-separating family in the bicommutant, not ordinary strong convergence (PDF p.27).
--   - `regularizedNorm`: tau_A^n: operator norm convergence AFTER multiplication by a common point-separating family in the bicommutant (PDF p.35).
--   - `BoundedSemigroup`: The paper's bounded semigroup, represented on nonnegative real arguments. Negative arguments of the total function are unused. Strong continuity is required only at positive time, and the semigroup law is for positive s,t (PDF p.33).
--   - `NondegenerateSemigroup`: Nondegeneracy of the positive-time semigroup; exactly the condition that the generator relation is single valued (PDF p.33).
--   - `semigroupResolventOne`: The strong Laplace resolvent at lambda=1, constructed vector by vector (PDF p.33). Under BoundedSemigroup, the vector integrand on (0,infinity) is continuous and dominated by M*exp(-t)*norm(x), hence integrable. The construction is used only under that guard; no norm-Bochner integral of T itself is substituted for a strong operator integral.
--   - `negativeGenerator`: The negative generator A=-B, constructed from the Laplace resolvent at lambda=1 (PDF p.33). If R=(I+A)^(-1), then (x,y) belongs to A precisely when R(x+y)=x. It is a relation before nondegeneracy is imposed.
--   - `MeasurableSymbol`: Finite-valued measurable symbols, with pointwise equality; reused from the accepted measurable-calculus paper (PDF p.39).
--   - `MeasurableAlgebraicCore`: Strong algebraic determination for the accepted measurable-symbol operations, without imposing an algebra instance on their subtype (PDF pp.6,40).
--   - `measurableExtension`: Formula (6.1) for the bounded measurable-symbol algebra (PDF pp.39–40). No free unbounded evaluation is supplied as a parameter.
--   - `BoundedMeasurableRepresentation`: A bounded unital star representation WITH weak bp continuity. Only bounded symbols constrain rho; values outside that algebra are immaterial. This is the bounded input to the measurable extension construction (PDF pp.39–40).
--   - `measurableApproxSequence`: The common identity from p.40, indexed from n+1 so that its denominator is strictly positive even where f=g=0. This is a constructed measurable function.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, https://arxiv.org/abs/2009.04733v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

/-! Haase, arXiv:2009.04733v1. The accepted graphDomain and GraphCore are imported directly.
Paper-local Banach-space definitions preserve actual graph domains, including
non-dense domains, and noncommutative complex algebras. Same-name accepted
Hilbert, measurable, partition and finite-matrix concepts are distinguished
in ASSESSMENT.json; they are not interchangeable with the abstract concepts.
 Compilation is pending the explicitly requested batch handoff. -/

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter
open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Operator relations, with the graphDomain retained (PDF p.4). -/
abbrev Graph (X : Type*) := Set (X × X)

/-- Identity on the full space (PDF p.4). -/
def identityGraph : Graph X := {p | p.2 = p.1}

/-- Graph of an everywhere-defined bounded complex-linear operator (PDF p.4). -/
def banachBoundedGraph (T : X →L[ℂ] X) : Graph X := {p | p.2 = T p.1}

/-- Range of an operator relation (PDF p.4). -/
def graphRange (A : Graph X) : Set X := {y | ∃ x, (x, y) ∈ A}

/-- Sum on the intersection of the domains (PDF p.4). -/
def graphAdd (A B : Graph X) : Graph X :=
  {p | ∃ y z, (p.1, y) ∈ A ∧ (p.1, z) ∈ B ∧ p.2 = y + z}

/-- Composition AB applies B first (PDF p.4). -/
def graphMul (A B : Graph X) : Graph X :=
  {p | ∃ y, (p.1, y) ∈ B ∧ (y, p.2) ∈ A}

/-- Scalar multiplication retains the graphDomain even at scalar zero (PDF p.4). -/
def graphScale (c : ℂ) (A : Graph X) : Graph X :=
  {p | ∃ y, (p.1, y) ∈ A ∧ p.2 = c • y}

/-- The inverse relation swaps graph coordinates (PDF p.4). -/
def graphInverse (A : Graph X) : Graph X := {p | (p.2, p.1) ∈ A}

/-- A closed, single-valued complex-linear graph; no density assumption (PDF p.4). -/
def BanachClosedOperator (A : Graph X) : Prop :=
  IsClosed A ∧ (0, 0) ∈ A ∧
  (∀ x y z w, (x, y) ∈ A → (z, w) ∈ A → (x + z, y + w) ∈ A) ∧
  (∀ (c : ℂ) x y, (x, y) ∈ A → (c • x, c • y) ∈ A) ∧
  (∀ x y z, (x, y) ∈ A → (x, z) ∈ A → y = z)

/-- Bounded means the full graph of a continuous linear map (PDF pp.4–5). -/
def Bounded (A : Graph X) : Prop := ∃ T : X →L[ℂ] X, A = banachBoundedGraph T

/-- Injectivity on the actual graphDomain (PDF p.5). -/
def InjectiveGraph (A : Graph X) : Prop :=
  ∀ x z y, (x, y) ∈ A → (z, y) ∈ A → x = z

/-- A bounded-map selector, used only under Bounded (PDF p.5).
The zero fallback is never used as a boundedness assertion. -/
def boundedValue (A : Graph X) : X →L[ℂ] X :=
  if h : Bounded A then Classical.choose h else 0

/-- A graph-value selector, used only on its graphDomain (PDF p.4). -/
def graphValue (A : Graph X) (x : X) : X :=
  if h : ∃ y, (x, y) ∈ A then Classical.choose h else 0

/-- Nonunital complex subalgebra, expressed on its ambient carrier (PDF p.13). -/
def SubalgebraSet (E : Set F) : Prop :=
  (0 : F) ∈ E ∧
  (∀ f ∈ E, ∀ g ∈ E, f + g ∈ E ∧ f * g ∈ E) ∧
  (∀ (c : ℂ) f, f ∈ E → c • f ∈ E)

/-- A unital complex subalgebra; the ambient algebra need not commute (PDF p.4). -/
def UnitalSubalgebraSet (E : Set F) : Prop := SubalgebraSet E ∧ (1 : F) ∈ E

/-- FC1–FC3 on a specified unital subalgebra, with the product-graphDomain equality
(PDF p.4). Values outside S are immaterial to this predicate. -/
def ProtoOn (Phi : F → Graph X) (S : Set F) : Prop :=
  UnitalSubalgebraSet S ∧ (∀ f ∈ S, BanachClosedOperator (Phi f)) ∧
  Phi 1 = identityGraph ∧
  (∀ (c : ℂ) f, f ∈ S → graphScale c (Phi f) ⊆ Phi (c • f)) ∧
  (∀ f ∈ S, ∀ g ∈ S, graphAdd (Phi f) (Phi g) ⊆ Phi (f + g)) ∧
  (∀ f ∈ S, ∀ g ∈ S,
    graphMul (Phi f) (Phi g) ⊆ Phi (f * g) ∧
    graphDomain (graphMul (Phi f) (Phi g)) = graphDomain (Phi g) ∩ graphDomain (Phi (f * g)))

/-- A proto-calculus on the whole algebra (PDF p.4). -/
def Proto (Phi : F → Graph X) : Prop := ProtoOn Phi Set.univ

/-- The Phi-bounded symbols (PDF p.5). -/
def boundedElements (Phi : F → Graph X) : Set F := {f | Bounded (Phi f)}

/-- The source's symbolBracket [f]_E = {e in E : ef in E} (PDF p.6). -/
def symbolBracket (E : Set F) (f : F) : Set F := {e | e ∈ E ∧ e * f ∈ E}

/-- Regularizers are bounded e with bounded ef (PDF p.6). -/
def regularizers (Phi : F → Graph X) (f : F) : Set F :=
  symbolBracket (boundedElements Phi) f

/-- Equality of the two bounded values Phi(ef)x and Phi(e)y (PDF p.6). -/
def regularizingEquation (Phi : F → Graph X) (f e : F) (x y : X) : Prop :=
  ∃ z, (x, z) ∈ Phi (e * f) ∧ (y, z) ∈ Phi e

/-- Determination is exactly (3.2), including the intersection with reg(f,Phi)
(PDF p.6). Empty determining sets are not silently excluded. -/
def Determines (Phi : F → Graph X) (M : Set F) (f : F) : Prop :=
  M ⊆ boundedElements Phi ∧ ∀ x y,
    ((x, y) ∈ Phi f ↔
      ∀ e ∈ M ∩ regularizers Phi f, regularizingEquation Phi f e x y)

/-- Strong determination uses [f]_E, as in (3.3) (PDF p.6). -/
def StrongDetermines (Phi : F → Graph X) (E : Set F) (f : F) : Prop :=
  E ⊆ boundedElements Phi ∧ Determines Phi (symbolBracket E f) f

/-- Algebraic core on a specified subalgebra (PDF p.7). -/
def AlgebraicCoreOn (Phi : F → Graph X) (E S : Set F) : Prop :=
  E ⊆ S ∩ boundedElements Phi ∧ ∀ f ∈ S, StrongDetermines Phi E f

/-- FC1–FC4 on S, with bounded determination as in FC4 (PDF pp.4,7). -/
def CalculusOn (Phi : F → Graph X) (S : Set F) : Prop :=
  ProtoOn Phi S ∧ ∀ f ∈ S, Determines Phi (S ∩ boundedElements Phi) f

/-- A calculus on the whole algebra (PDF p.4). -/
def AbstractCalculus (Phi : F → Graph X) : Prop := CalculusOn Phi Set.univ

/-- Common-kernel point separation; the empty family separates only the zero
space (PDF p.4). -/
def PointSeparating (Phi : F → Graph X) (E : Set F) : Prop :=
  ∀ x : X, (∀ e ∈ E, (x, 0) ∈ Phi e) → x = 0

/-- Anchor sets are nonempty bounded families with trivial common kernel
(PDF p.7). This nonempty requirement is retained on the zero Banach space. -/
def AnchorSet (Phi : F → Graph X) (E : Set F) : Prop :=
  E.Nonempty ∧ E ⊆ boundedElements Phi ∧ PointSeparating Phi E

/-- f is anchored in E precisely when [f]_E is an anchor (PDF p.7). -/
def Anchored (Phi : F → Graph X) (E : Set F) (f : F) : Prop :=
  AnchorSet Phi (symbolBracket E f)

/-- Every element of S is anchored in E (PDF p.7). -/
def AnchoredSet (Phi : F → Graph X) (E S : Set F) : Prop :=
  ∀ f ∈ S, Anchored Phi E f

/-- A multiplicative subset; neither a unit nor nonemptiness is added (PDF p.8). -/
def MulClosedSet (E : Set F) : Prop := ∀ f ∈ E, ∀ g ∈ E, f * g ∈ E

/-- Products of two sets, in the displayed order (PDF p.9). -/
def setProduct (A B : Set F) : Set F := {f | ∃ a ∈ A, ∃ b ∈ B, f = a * b}

/-- Left multipliers of E taking E into the bounded part (PDF p.9). -/
def leftMultipliers (Phi : F → Graph X) (E : Set F) : Set F :=
  {h | ∀ e ∈ E, h * e ∈ boundedElements Phi}

/-- The center of a subset in the source's sense (PDF p.4). -/
def setCenter (E : Set F) : Set F := {d | d ∈ E ∧ ∀ e ∈ E, d * e = e * d}

/-- Commutativity is imposed exactly when a source clause uses it (PDF p.4). -/
def CommutativeSet (E : Set F) : Prop := ∀ f ∈ E, ∀ g ∈ E, f * g = g * f

/-- Pull-back along a unital complex algebra homomorphism (PDF p.11). -/
def pullback (Phi : F → Graph X) (eta : G →ₐ[ℂ] F) : G → Graph X :=
  fun g => Phi (eta g)

/-- A nonunital algebra representation on E (PDF p.13). The total map rho is
only constrained and used on E, so no value outside E is prescribed. -/
def AlgebraRepresentationOn (rho : F → X →L[ℂ] X) (E : Set F) : Prop :=
  SubalgebraSet E ∧ rho 0 = 0 ∧
  (∀ f ∈ E, ∀ g ∈ E, rho (f + g) = rho f + rho g ∧ rho (f * g) = (rho f).comp (rho g)) ∧
  (∀ (c : ℂ) f, f ∈ E → rho (c • f) = c • rho f)

/-- The graph-valued bounded representation (PDF p.13). -/
def representationGraphs (rho : F → X →L[ℂ] X) : F → Graph X :=
  fun f => banachBoundedGraph (rho f)

/-- The extension constructed by (6.1); functionality and closedness are
conclusions under anchoring, not extra premises (PDF p.13). -/
def canonicalAlgebraicExtension (rho : F → X →L[ℂ] X) (E : Set F) : F → Graph X :=
  fun f => {p | ∀ e ∈ symbolBracket E f, rho (e * f) p.1 = rho e p.2}

/-- The concrete maximal anchored carrier (6.2) (PDF p.15). -/
def maximalAnchored (rho : F → X →L[ℂ] X) (E : Set F) : Set F :=
  {f | ∀ e ∈ E, AnchorSet (representationGraphs rho) (symbolBracket E (e * f))}

/-- Nondegeneracy means E itself is an anchor (PDF p.15). -/
def Nondegenerate (rho : F → X →L[ℂ] X) (E : Set F) : Prop :=
  AnchorSet (representationGraphs rho) E

/-- Source conditions for an approximate identity for the fixed f. The printed
fn on p.18 is corrected to f, as used by the proof on p.19. -/
def ApproxFor (Phi : F → Graph X) (e : ℕ → F) (f : F) : Prop :=
  ∀ n, Bounded (Phi (e n)) ∧ Bounded (Phi (f * e n)) ∧
    graphMul (Phi (e n)) (Phi f) ⊆ graphMul (Phi f) (Phi (e n)) ∧
    graphMul (Phi f) (Phi (e n)) = Phi (f * e n)

/-- Strong convergence of the bounded Phi(e_n) to I (PDF p.18). -/
def StrongIdentity (Phi : F → Graph X) (e : ℕ → F) : Prop :=
  (∀ n, Bounded (Phi (e n))) ∧
  ∀ x, Tendsto (fun n => graphValue (Phi (e n)) x) atTop (𝓝 x)

/-- Weak convergence uses all continuous complex-linear functionals (PDF p.18). -/
def WeakIdentity (Phi : F → Graph X) (e : ℕ → F) : Prop :=
  (∀ n, Bounded (Phi (e n))) ∧
  ∀ (l : X →L[ℂ] ℂ) x,
    Tendsto (fun n => l (graphValue (Phi (e n)) x)) atTop (𝓝 (l x))

/-- Strong approximate identity for f (PDF p.18). -/
def StrongApprox (Phi : F → Graph X) (e : ℕ → F) (f : F) : Prop :=
  ApproxFor Phi e f ∧ StrongIdentity Phi e

/-- Weak approximate identity for f (PDF p.18). -/
def WeakApprox (Phi : F → Graph X) (e : ℕ → F) (f : F) : Prop :=
  ApproxFor Phi e f ∧ WeakIdentity Phi e

/-- The span of all ranges of the approximate identity (PDF p.18). -/
def approximateRangeSpan (Phi : F → Graph X) (e : ℕ → F) : Set X :=
  (Submodule.span ℂ {y | ∃ n, y ∈ graphRange (Phi (e n))} : Set X)

example (A : Graph X) (x : X) : x ∈ graphDomain (graphScale 0 A) ↔ x ∈ graphDomain A := by
  constructor
  · rintro ⟨y, z, hz, _⟩
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨0, z, hz, by simp⟩

example (Phi : F → Graph X) : ¬ AnchorSet Phi (∅ : Set F) := by
  intro h
  exact Set.not_nonempty_empty h.1

example (E : Set F) (f e : F) : e ∈ symbolBracket E f ↔ e ∈ E ∧ e * f ∈ E := Iff.rfl

example (rho : F → X →L[ℂ] X) (E : Set F) (f : F) (x y : X) :
    (x, y) ∈ canonicalAlgebraicExtension rho E f ↔
      ∀ e ∈ symbolBracket E f, rho (e * f) x = rho e y := Iff.rfl

/-- Complex-linear Banach transpose relation, not a Hilbert adjoint (PDF p.20). -/
def transposeGraph (A : Graph X) : Graph (X →L[ℂ] ℂ) :=
  {p | ∀ x y, (x, y) ∈ A → p.1 y = p.2 x}

/-- The opposite-algebra symbolBracket [f]_(B^op), on the original carrier (PDF p.20). -/
def oppositeBracket (Phi : F → Graph X) (f : F) : Set F :=
  {e | e ∈ boundedElements Phi ∧ f * e ∈ boundedElements Phi}

/-- Canonical dual extension graphDomain <B^op,F^op,Phi'> (PDF p.20).
The order f*b*e is the opposite-algebra instance of formula (6.2). -/
def dualDomain (Phi : F → Graph X) : Set F :=
  {f | ∀ b ∈ boundedElements Phi,
    AnchorSet (fun e => transposeGraph (Phi e)) (oppositeBracket Phi (f * b))}

/-- The canonical dual calculus constructed from the bounded transposes by
(6.1) in the opposite algebra (PDF p.20). Defined as a relation even off its
graphDomain; statements use it only on dualDomain. -/
def dualEvaluation (Phi : F → Graph X) (f : F) : Graph (X →L[ℂ] ℂ) :=
  {p | ∀ e ∈ oppositeBracket Phi f, ∀ x : X,
    p.1 (boundedValue (Phi (f * e)) x) = p.2 (boundedValue (Phi e) x)}

/-- D_f in Theorem 8.1 (PDF p.20). -/
def dualRangeSpan (Phi : F → Graph X) (f : F) : Set X :=
  (Submodule.span ℂ {y | ∃ e ∈ oppositeBracket Phi f, y ∈ graphRange (Phi e)} : Set X)

/-- D_fb in the dualizability criterion (PDF p.21). -/
def dualizableRangeSpan (Phi : F → Graph X) (f b : F) : Set X :=
  (Submodule.span ℂ {y | ∃ e ∈ boundedElements Phi,
    f * b * e ∈ boundedElements Phi ∧ y ∈ graphRange (Phi e)} : Set X)

example (A : Graph X) (l m : X →L[ℂ] ℂ) :
    (l, m) ∈ transposeGraph A ↔ ∀ x y, (x, y) ∈ A → l y = m x := Iff.rfl

/-- An algebraic convergence relation on S over an arbitrary index type.
Exactly the two source axioms are used: closure as a complex subalgebra of
families paired with limits, and convergence of every constant family. No
topology, directedness, or eventual-equality axiom is imposed (PDF p.22). -/
def AlgebraicConvergenceOn {I : Type*} (tau : (I → F) → F → Prop) (S : Set F) : Prop :=
  SubalgebraSet S ∧
  (∀ a f, tau a f → (∀ i, a i ∈ S) ∧ f ∈ S) ∧
  (∀ f ∈ S, tau (fun _ => f) f) ∧
  (∀ a b f g, tau a f → tau b g →
    tau (fun i => a i + b i) (f + g) ∧ tau (fun i => a i * b i) (f * g)) ∧
  (∀ (c : ℂ) a f, tau a f → tau (fun i => c • a i) (c • f))

/-- Hausdorff means uniqueness of the limit for a fixed family (PDF p.22). -/
def HausdorffConvergence {I : Type*} (tau : (I → F) → F → Prop) : Prop :=
  ∀ a f g, tau a f → tau a g → f = g

/-- Joint closability is exactly (9.1) (PDF p.22). -/
def JointClosable {I : Type*} (rho : F → X →L[ℂ] X) (E : Set F)
    (tau1 : (I → F) → F → Prop)
    (tau2 : (I → (X →L[ℂ] X)) → (X →L[ℂ] X) → Prop) : Prop :=
  ∀ e : I → F, (∀ i, e i ∈ E) → ∀ T,
    tau1 e 0 → tau2 (fun i => rho (e i)) T → T = 0

/-- The graph of the topological extension, constructed from simultaneous
approximants; it is not an assumed homomorphism (PDF pp.22–23). -/
def topologicalGraph {I : Type*} (rho : F → X →L[ℂ] X) (E : Set F)
    (A : Set (X →L[ℂ] X)) (tau1 : (I → F) → F → Prop)
    (tau2 : (I → (X →L[ℂ] X)) → (X →L[ℂ] X) → Prop)
    (f : F) (T : X →L[ℂ] X) : Prop :=
  T ∈ A ∧ ∃ e : I → F, (∀ i, e i ∈ E) ∧ tau1 e f ∧ tau2 (fun i => rho (e i)) T

/-- E^tau is the actual graphDomain of simultaneous scalar/operator limits (PDF p.22). -/
def topologicalDomain {I : Type*} (rho : F → X →L[ℂ] X) (E : Set F)
    (A : Set (X →L[ℂ] X)) (tau1 : (I → F) → F → Prop)
    (tau2 : (I → (X →L[ℂ] X)) → (X →L[ℂ] X) → Prop) : Set F :=
  {f | ∃ T, topologicalGraph rho E A tau1 tau2 f T}

/-- The topological extension value on E^tau (PDF p.23). The zero fallback
is outside E^tau and is not used in any assertion about the extension. -/
def topologicalValue {I : Type*} (rho : F → X →L[ℂ] X) (E : Set F)
    (A : Set (X →L[ℂ] X)) (tau1 : (I → F) → F → Prop)
    (tau2 : (I → (X →L[ℂ] X)) → (X →L[ℂ] X) → Prop) (f : F) : X →L[ℂ] X :=
  if h : ∃ T, topologicalGraph rho E A tau1 tau2 f T then Classical.choose h else 0

example {I : Type*} (rho : F → X →L[ℂ] X) (E : Set F) (A : Set (X →L[ℂ] X))
    (tau1 : (I → F) → F → Prop)
    (tau2 : (I → (X →L[ℂ] X)) → (X →L[ℂ] X) → Prop) (f : F) :
    f ∈ topologicalDomain rho E A tau1 tau2 ↔
      ∃ T, topologicalGraph rho E A tau1 tau2 f T := Iff.rfl

/-- lambda I minus A on dom(A) (PDF p.24). -/
def banachResolventShift (A : Graph X) (z : ℂ) : Graph X :=
  graphAdd (graphScale z identityGraph) (graphScale (-1) A)

/-- Resolvent set of an operator with its actual graphDomain (PDF p.24). -/
def banachResolventSet (A : Graph X) : Set ℂ :=
  {z | Bounded (graphInverse (banachResolventShift A z))}

/-- The closed sector includes zero (PDF p.24). -/
def closedSector (angle : ℝ) : Set ℂ := {z | z = 0 ∨ |z.arg| ≤ angle}

/-- Sectorial operator, with no injectivity or dense-graphDomain assumption
(PDF p.24). The resolvent bound is uniform in lambda, on every larger sector. -/
def Sectorial (A : Graph X) : Prop :=
  BanachClosedOperator A ∧ ∃ angle : ℝ, 0 ≤ angle ∧ angle < Real.pi ∧
    (banachResolventSet A)ᶜ ⊆ closedSector angle ∧
    ∀ omega : ℝ, angle < omega → omega < Real.pi →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z ∉ closedSector omega →
        z ∈ banachResolventSet A ∧ ‖z • boundedValue (graphInverse (banachResolventShift A z))‖ ≤ C

/-- R=(I+A)^(-1), only used under sectoriality or the generator hypotheses
ensuring the inverse is a full bounded operator (PDF pp.27,35). -/
def onePlusInverse (A : Graph X) : X →L[ℂ] X :=
  boundedValue (graphInverse (graphAdd identityGraph A))

/-- Operator operatorCommutant within bounded operators (PDF p.27). -/
def operatorCommutant (B : Set (X →L[ℂ] X)) : Set (X →L[ℂ] X) :=
  {S | ∀ T ∈ B, S.comp T = T.comp S}

/-- Point separation for bounded operator families (PDF p.4). In contrast
to an anchor, a point-separating family need not be nonempty on the zero space. -/
def OperatorPointSeparating (D : Set (X →L[ℂ] X)) : Prop :=
  ∀ x : X, (∀ d ∈ D, d x = 0) → x = 0

/-- tau_A^s: strong convergence AFTER multiplication by a common
point-separating family in the bicommutant, not ordinary strong convergence
(PDF p.27). -/
def regularizedStrong (R : X →L[ℂ] X) (a : ℕ → (X →L[ℂ] X)) (T : X →L[ℂ] X) : Prop :=
  (∀ n, a n ∈ operatorCommutant {R}) ∧ T ∈ operatorCommutant {R} ∧
  ∃ D : Set (X →L[ℂ] X), D ⊆ operatorCommutant (operatorCommutant {R}) ∧
    OperatorPointSeparating D ∧
    ∀ d ∈ D, ∀ x : X, Tendsto (fun n => d (a n x)) atTop (𝓝 (d (T x)))

/-- tau_A^n: operator norm convergence AFTER multiplication by a common
point-separating family in the bicommutant (PDF p.35). -/
def regularizedNorm (R : X →L[ℂ] X) (a : ℕ → (X →L[ℂ] X)) (T : X →L[ℂ] X) : Prop :=
  (∀ n, a n ∈ operatorCommutant {R}) ∧ T ∈ operatorCommutant {R} ∧
  ∃ D : Set (X →L[ℂ] X), D ⊆ operatorCommutant (operatorCommutant {R}) ∧
    OperatorPointSeparating D ∧
    ∀ d ∈ D, Tendsto (fun n => d.comp (a n)) atTop (𝓝 (d.comp T))

/-- The paper's bounded semigroup, represented on nonnegative real arguments.
Negative arguments of the total function are unused. Strong continuity is
required only at positive time, and the semigroup law is for positive s,t
(PDF p.33). -/
def BoundedSemigroup (T : ℝ → X →L[ℂ] X) : Prop :=
  T 0 = ContinuousLinearMap.id ℂ X ∧
  (∀ s t : ℝ, 0 < s → 0 < t → T (s + t) = (T s).comp (T t)) ∧
  (∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ M) ∧
  (∀ x : X, ContinuousOn (fun t : ℝ => T t x) (Set.Ioi 0))

/-- Nondegeneracy of the positive-time semigroup; exactly the condition
that the generator relation is single valued (PDF p.33). -/
def NondegenerateSemigroup (T : ℝ → X →L[ℂ] X) : Prop :=
  ∀ x : X, (∀ t : ℝ, 0 < t → T t x = 0) → x = 0

/-- The strong Laplace resolvent at lambda=1, constructed vector by vector
(PDF p.33). Under BoundedSemigroup, the vector integrand on (0,infinity)
is continuous and dominated by M*exp(-t)*norm(x), hence integrable. The
construction is used only under that guard; no norm-Bochner integral of T
itself is substituted for a strong operator integral. -/
def semigroupResolventOne (T : ℝ → X →L[ℂ] X) (x : X) : X :=
  ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(t : ℂ)) • T t x

/-- The negative generator A=-B, constructed from the Laplace resolvent at
lambda=1 (PDF p.33). If R=(I+A)^(-1), then (x,y) belongs to A precisely
when R(x+y)=x. It is a relation before nondegeneracy is imposed. -/
def negativeGenerator (T : ℝ → X →L[ℂ] X) : Graph X :=
  {p | semigroupResolventOne T (p.1 + p.2) = p.1}

example (T : ℝ → X →L[ℂ] X) (x y : X) :
    (x, y) ∈ negativeGenerator T ↔ semigroupResolventOne T (x + y) = x := Iff.rfl

example : (0 : ℂ) ∈ closedSector 0 := Or.inl rfl

example (B : Set (X →L[ℂ] X)) (S : X →L[ℂ] X) :
    S ∈ operatorCommutant B ↔ ∀ T ∈ B, S.comp T = T.comp S := Iff.rfl

/-- Finite-valued measurable symbols, with pointwise equality; reused from
the accepted measurable-calculus paper (PDF p.39). -/
abbrev MeasurableSymbol (Z : Type*) [MeasurableSpace Z] :=
  QAlgorithms.Papers.Independent.Claimed50.P05.Symbol Z ℂ

section Measurable

variable {Z H : Type*} [MeasurableSpace Z] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Strong algebraic determination for the accepted measurable-symbol
operations, without imposing an algebra instance on their subtype (PDF pp.6,40). -/
def MeasurableAlgebraicCore (Phi : MeasurableSymbol Z → Graph H)
    (E : Set (MeasurableSymbol Z)) : Prop :=
  (∀ e ∈ E, Bounded (Phi e)) ∧ ∀ f x y,
    ((x, y) ∈ Phi f ↔ ∀ e ∈ E,
      QAlgorithms.Papers.Independent.Claimed50.P05.times e f ∈ E →
      ∃ z, (x, z) ∈ Phi (QAlgorithms.Papers.Independent.Claimed50.P05.times e f) ∧ (y, z) ∈ Phi e)

/-- Formula (6.1) for the bounded measurable-symbol algebra (PDF pp.39–40).
No free unbounded evaluation is supplied as a parameter. -/
def measurableExtension (rho : MeasurableSymbol Z → Graph H)
    (E : Set (MeasurableSymbol Z)) : MeasurableSymbol Z → Graph H :=
  fun f => {p | ∀ e ∈ E, QAlgorithms.Papers.Independent.Claimed50.P05.times e f ∈ E →
    ∃ z, (p.1, z) ∈ rho (QAlgorithms.Papers.Independent.Claimed50.P05.times e f) ∧ (p.2, z) ∈ rho e}

/-- A bounded unital star representation WITH weak bp continuity. Only
bounded symbols constrain rho; values outside that algebra are immaterial.
This is the bounded input to the measurable extension construction (PDF pp.39–40). -/
def BoundedMeasurableRepresentation (rho : MeasurableSymbol Z → Graph H) : Prop :=
  rho (QAlgorithms.Papers.Independent.Claimed50.P05.constant 1) = identityGraph ∧
  (∀ f, QAlgorithms.Papers.Independent.Claimed50.P05.BoundedSymbol f →
    Bounded (rho f) ∧
    QAlgorithms.Papers.Independent.Claimed50.P05.graphAdjoint (k := ℂ) (rho f) =
      rho (QAlgorithms.Papers.Independent.Claimed50.P05.starSymbol f)) ∧
  (∀ f g, QAlgorithms.Papers.Independent.Claimed50.P05.BoundedSymbol f →
    QAlgorithms.Papers.Independent.Claimed50.P05.BoundedSymbol g →
    graphAdd (rho f) (rho g) = rho (QAlgorithms.Papers.Independent.Claimed50.P05.plus f g) ∧
    graphMul (rho f) (rho g) = rho (QAlgorithms.Papers.Independent.Claimed50.P05.times f g)) ∧
  (∀ (c : ℂ) f, QAlgorithms.Papers.Independent.Claimed50.P05.BoundedSymbol f →
    graphScale c (rho f) = rho (QAlgorithms.Papers.Independent.Claimed50.P05.scalar c f)) ∧
  (∀ fn f, QAlgorithms.Papers.Independent.Claimed50.P05.BP fn f →
    QAlgorithms.Papers.Independent.Claimed50.P05.Weak (k := ℂ) (fun n => rho (fn n)) (rho f))

/-- The common identity from p.40, indexed from n+1 so that its denominator
is strictly positive even where f=g=0. This is a constructed measurable function. -/
def measurableApproxSequence (f g : MeasurableSymbol Z) (n : ℕ) : MeasurableSymbol Z :=
  ⟨fun x => (((n + 1 : ℕ) : ℂ) /
    (((n + 1 : ℕ) : ℂ) + (‖f.val x‖ : ℂ) + (‖g.val x‖ : ℂ))), by
      have hf := f.property
      have hg := g.property
      fun_prop⟩

example : (QAlgorithms.Papers.Independent.Claimed50.P05.constant (0 : ℂ) :
    MeasurableSymbol Z).val = fun _ => 0 := rfl

example : measurableApproxSequence
    (QAlgorithms.Papers.Independent.Claimed50.P05.constant (0 : ℂ) : MeasurableSymbol Z)
    (QAlgorithms.Papers.Independent.Claimed50.P05.constant (0 : ℂ)) 0 =
      QAlgorithms.Papers.Independent.Claimed50.P05.constant (1 : ℂ) := by
  apply Subtype.ext
  funext x
  simp [measurableApproxSequence, QAlgorithms.Papers.Independent.Claimed50.P05.constant]

end Measurable

end QAlgorithms.Papers.Independent.Next46.P06


