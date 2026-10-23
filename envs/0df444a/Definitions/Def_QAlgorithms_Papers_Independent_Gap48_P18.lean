-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P18
-- name    : QAlgorithms_Papers_Independent_Gap48_P18
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T07:33:09.223987+00:00
-- url     : https://prove2.me/theorems/7a572b47-90ac-4804-bd34-9dc5101e5e52
-- title:
--   Definitions for Entropic characteristics of subsets of states
-- statement:
--   The objects the formalized statements of *Entropic characteristics of subsets of states* (arXiv:quant-ph/0510073) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `stateEntropyNats`: Normalized-state entropy in nats, PDF pp.4–5; infinity is retained.
--   - `stateRelativeEntropyNats`: Umegaki relative entropy with its support guard, PDF p.4.
--   - `distanceSquared`: Squared trace distance, PDF p.4, (1); not half trace distance.
--   - `meanCoefficients`: Coefficients of a measure's average, PDF p.5. Only probability laws are used for barycenters; scalar integrability follows from bounded state entries.
--   - `measureHolevo`: The integral definition of chi, PDF p.5. This extends the accepted probability-law functional to measures so finite mixtures can be constructed without extra normalization witnesses. Every theorem uses probability mass one.
--   - `probabilityAverage`: The actual normalized average, selected from the accepted barycenter existence theorem; PDF p.5. No new existence or continuity assumption is made.
--   - `MeasureConcentratedOn`: A law concentrated on A, PDF p.5. For closed A this is equivalent to its topological support being contained in A.
--   - `FiniteEnsembleOn`: Conventional finite ensembles whose signals lie in A, PDF pp.5,24.
--   - `setChiCapacity`: Per-signal set capacity, PDF p.24, (24), distinct from average constraints.
--   - `stateClosedConvexHull`: The trace-norm closed real convex hull, PDF p.4.
--   - `CoefficientConvexStates`: Convexity of actual operator coefficients, PDF p.4.
--   - `entropySup`: Entropy supremum in the complete extended nonnegative reals, PDF p.7.
--   - `FiniteContinuousOn`: Source continuity is finite-valued continuity, explicitly used on PDF p.18.
--   - `FiniteContinuousWithinAt`: Finite-valued relative continuity at a point, PDF p.7.
--   - `HConverges`: H-convergence has its fixed reference in the SECOND slot, PDF p.4.
--   - `RadiusCenter`: The information-radius condition defining the unique optimal average, PDF pp.24,27. Theorem 1 establishes existence and uniqueness.
--   - `optimalAverage`: Canonical choice by the source's defining radius condition, PDF p.27, Definition 1. On a nonempty finite-capacity set Theorem 1 makes this choice unique. Elsewhere this total helper has no claimed meaning as an optimal average: its fallback is an element of A, not an assumed radius minimizer.
--   - `radius`: Radius about a reference state, PDF p.25, (25); the empty supremum is zero.
--   - `RegularityOne`: First regularity alternative, PDF p.28: finite entropy at the center and entropy convergence along every H-convergent sequence in the CLOSED hull.
--   - `RegularityTwo`: Second regularity alternative, PDF p.28; no conjunction with the first.
--   - `ChiRegular`: Regular sets, PDF p.28, Definition 2, with the implicit nonempty domain.
--   - `OptimalMeasure`: Optimal generalized measure, PDF p.39, Definition 3.
--   - `extremeClosure`: Trace closure of extreme points, PDF p.40 (both overlines are essential).
--   - `StateChannel`: A concrete CPTP map packaged with its normalized state action, PDF pp.3,35. The action is tied coefficient by coefficient to the accepted full trace-class map; no finite Kraus or finite-dimensional restriction is imposed.
--   - `PreservingChannels`: Capacity-preserving channels mapping into the closed hull, PDF p.35.
--   - `CommonChannelInvariant`: Common invariant states, PDF p.35; no commutativity is assumed.
--   - `countableLaw`: Countable ensemble as its actual atomic probability law, PDF pp.39–40. Normalization of w is required at each use, and zero weights contribute zero.
--   - `jointMarginalConstraintSet`: All joint states with marginal membership, including entangled states, PDF p.61. The two marginals are identified with actual normalized states.
--   - `couplingSet`: Fixed-marginal coupling set C(rho,sigma), PDF p.62.
--   - `layer`: A layer in a CHOSEN eigenbasis, PDF p.22 and footnote 10. The theorems explicitly require sigma diagonal in these coordinates, leaving repeated eigenvalues and their basis choice visible.
--   - `Diagonal`: Chosen coordinates are an eigenbasis of sigma, PDF p.22.
--   - `InSimplex`: Finite probability simplex, PDF p.36. The equation excludes n=0.
--   - `finiteLaw`: The actual finite ensemble of specified states, PDF pp.5,36.
--   - `unionObjective`: The objective whose maximum appears in Proposition 7, PDF p.36.
--   - `tailLayer`: Layer with the first n-1 rows and columns diagonal, PDF p.59. Source indices start at one, so coordinate i corresponds to source i+1.
--   - `decreasingFamily`: The concrete decreasing family of PDF p.61, not an arbitrary family satisfying capacity conclusions: L_(n+1)(sigma) intersect V_(sigma,c).
--   - `MinimalClosedEqualCapacity`: Minimal closed equal-capacity subset, PDF p.30, footnote 19.
--   - `spectralPowerTrace`: Actual spectral-power trace by finite-compression exhaustion, PDF p.13. For positive exponents finite-compression eigenvalue interlacing gives the extended trace of sigma^t. At t=0 this is the rank of the support projection, not the ambient dimension. The scalar zero-eigenvalue branch is explicit.
--   - `decreaseCoefficient`: Decrease coefficient, PDF p.13. Extended infima avoid a real junk value when a convergence set is empty; state normalization makes t=1 admissible.
--   - `PositiveFiniteRankState`: Finite-dimensional operator support, PDF p.13. A finite positive rank-one sum characterizes positive finite rank in any coordinate basis; this does NOT require finite coordinate support.
--   - `BoundedOrthogonalProjection`: Any bounded orthogonal projection, PDF pp.71–73. Neither finite rank nor a monotone-sequence condition is built into this type.
--   - `projectionMass`: Positive compression mass Tr(P rho), PDF p.71. On states the bounded conjugation is trace class, hence the real trace series is summable.
--   - `compressedCoefficients`: The source's normalized coefficients, PDF p.71. Uses are restricted to positive mass, so inverse at zero is never asserted to produce a state.
--   - `projectionImage`: Actual positive-domain image under Theta_P, PDF pp.71–72. Output states are identified by the formula, not supplied with assumed capacity properties.
--   - `projectionSuccessInfimum`: Uniform retained mass, PDF p.72. The extended empty infimum is infinity; all theorem uses explicitly require A nonempty.
--   - `projectedAverage`: Optimal average of a compression image on the eventual valid domain, PDF p.73. An empty early image uses the original set's average only to make the sequence total; Theorem 4 concludes that this branch eventually disappears.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, https://arxiv.org/abs/quant-ph/0510073v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

/-!
Shirokov, arXiv:quant-ph/0510073v2. Statements use countable orthonormal
coordinates for arbitrary separable complex Hilbert spaces, trace-norm topology,
and natural logarithms. All entropic quantities retain positive infinity.
Deferred full nodes are recorded in HARD.md; no partial substitute is stated.
Compilation is pending the separately authorized batch handoff.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Matrix.Norms.L2Operator
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState traceSize traceClosure IsTraceClassChannel productCoeff)
open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasFiniteSupport HasAverage averageCoefficients
   extendedEntropyNats extendedRelativeEntropyNats
   finiteEnsembleCapacity pureStates)
open QAlgorithms.Papers.Independent.Frontier18.P01 (traceFirst traceSecond)

namespace QAlgorithms.Papers.Independent.Gap48.P18

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Normalized-state entropy in nats, PDF pp.4–5; infinity is retained. -/
def stateEntropyNats {I : Type} (rho : State I) : ℝ≥0∞ :=
  extendedEntropyNats rho.coefficients

/-- Umegaki relative entropy with its support guard, PDF p.4. -/
def stateRelativeEntropyNats {I : Type} (rho sigma : State I) : ℝ≥0∞ :=
  extendedRelativeEntropyNats rho.coefficients sigma.coefficients

/-- Squared trace distance, PDF p.4, (1); not half trace distance. -/
def distanceSquared {I : Type} (rho sigma : State I) : ℝ≥0∞ :=
  traceSize (rho.coefficients - sigma.coefficients) ^ 2

/-- Coefficients of a measure's average, PDF p.5. Only probability laws are
used for barycenters; scalar integrability follows from bounded state entries. -/
def meanCoefficients {I : Type} (mu : Measure (State I)) : Matrix I I ℂ :=
  fun i j => ∫ rho, rho.coefficients i j ∂mu

/-- The integral definition of chi, PDF p.5. This extends the accepted
probability-law functional to measures so finite mixtures can be constructed
without extra normalization witnesses. Every theorem uses probability mass one. -/
def measureHolevo {I : Type} (mu : Measure (State I)) : ℝ≥0∞ :=
  ∫⁻ rho, extendedRelativeEntropyNats rho.coefficients (meanCoefficients mu) ∂mu

/-- The actual normalized average, PDF p.5: the barycenter map whose existence is
the accepted theorem `Frontier18.P07.barycenter_continuous`, chosen under that
theorem's statement as a guard (a definition may import only proved theorems).
Whenever the statement holds this is the map that theorem selects; no new
existence or continuity assumption is made. -/
def probabilityAverage {I : Type} [Countable I] (mu : GeneralizedEnsemble I) : State I :=
  if h : ∃ average : GeneralizedEnsemble I → State I,
      (∀ mu, HasAverage mu (average mu)) ∧ Continuous average then
    Classical.choose h mu
  else
    Classical.choice (MeasureTheory.nonempty_of_isProbabilityMeasure (mu : Measure (State I)))

/-- A law concentrated on A, PDF p.5. For closed A this is equivalent to
its topological support being contained in A. -/
def MeasureConcentratedOn {I : Type} (mu : Measure (State I)) (A : Set (State I)) : Prop :=
  ∀ᵐ rho ∂mu, rho ∈ A

/-- Conventional finite ensembles whose signals lie in A, PDF pp.5,24. -/
def FiniteEnsembleOn {I : Type} (mu : GeneralizedEnsemble I)
    (A : Set (State I)) : Prop :=
  HasFiniteSupport mu ∧ (mu : Measure (State I)).support ⊆ A

/-- Per-signal set capacity, PDF p.24, (24), distinct from average constraints. -/
def setChiCapacity {I : Type} (A : Set (State I)) : ℝ≥0∞ :=
  ⨆ mu : {mu : GeneralizedEnsemble I // FiniteEnsembleOn mu A},
    measureHolevo (mu.val : Measure (State I))

/-- The trace-norm closed real convex hull, PDF p.4. -/
def stateClosedConvexHull {I : Type} (A : Set (State I)) : Set (State I) :=
  {rho | rho.coefficients ∈ traceClosure (convexHull ℝ (State.coefficients '' A))}

/-- Convexity of actual operator coefficients, PDF p.4. -/
def CoefficientConvexStates {I : Type} (A : Set (State I)) : Prop :=
  Convex ℝ (State.coefficients '' A)

/-- Entropy supremum in the complete extended nonnegative reals, PDF p.7. -/
def entropySup {I : Type} (A : Set (State I)) : ℝ≥0∞ :=
  ⨆ rho : A, stateEntropyNats rho.val

/-- Source continuity is finite-valued continuity, explicitly used on PDF p.18. -/
def FiniteContinuousOn {I : Type} (f : State I → ℝ≥0∞)
    (A : Set (State I)) : Prop :=
  (∀ rho ∈ A, f rho < ⊤) ∧ ContinuousOn f A

/-- Finite-valued relative continuity at a point, PDF p.7. -/
def FiniteContinuousWithinAt {I : Type} (f : State I → ℝ≥0∞)
    (A : Set (State I)) (rho : State I) : Prop :=
  f rho < ⊤ ∧ ContinuousWithinAt f A rho

/-- H-convergence has its fixed reference in the SECOND slot, PDF p.4. -/
def HConverges {I : Type} (seq : ℕ → State I) (rho : State I) : Prop :=
  Tendsto (fun n => stateRelativeEntropyNats (seq n) rho) atTop (𝓝 0)

/-- The information-radius condition defining the unique optimal average,
PDF pp.24,27. Theorem 1 establishes existence and uniqueness. -/
def RadiusCenter {I : Type} (A : Set (State I)) (omega : State I) : Prop :=
  ∀ rho ∈ A, stateRelativeEntropyNats rho omega ≤ setChiCapacity A

/-- Canonical choice by the source's defining radius condition, PDF p.27,
Definition 1. On a nonempty finite-capacity set Theorem 1 makes this choice
unique. Elsewhere this total helper has no claimed meaning as an optimal
average: its fallback is an element of A, not an assumed radius minimizer. -/
def optimalAverage {I : Type} (A : Set (State I)) (hA : A.Nonempty) : State I :=
  if h : ∃ omega, RadiusCenter A omega then Classical.choose h else hA.choose

/-- Radius about a reference state, PDF p.25, (25); the empty supremum is zero. -/
def radius {I : Type} (A : Set (State I)) (sigma : State I) : ℝ≥0∞ :=
  ⨆ rho : A, stateRelativeEntropyNats rho.val sigma

/-- First regularity alternative, PDF p.28: finite entropy at the center and
entropy convergence along every H-convergent sequence in the CLOSED hull. -/
def RegularityOne {I : Type} (A : Set (State I)) (omega : State I) : Prop :=
  stateEntropyNats omega < ⊤ ∧ ∀ seq : ℕ → State I,
    (∀ n, seq n ∈ stateClosedConvexHull A) → HConverges seq omega →
      Tendsto (fun n => stateEntropyNats (seq n)) atTop (𝓝 (stateEntropyNats omega))

/-- Second regularity alternative, PDF p.28; no conjunction with the first. -/
def RegularityTwo {I : Type} (A : Set (State I)) (omega : State I) : Prop :=
  FiniteContinuousOn (fun rho => stateRelativeEntropyNats rho omega) A

/-- Regular sets, PDF p.28, Definition 2, with the implicit nonempty domain. -/
def ChiRegular {I : Type} (A : Set (State I)) : Prop :=
  A.Nonempty ∧ setChiCapacity A < ⊤ ∧ ∃ omega,
    RadiusCenter A omega ∧ (RegularityOne A omega ∨ RegularityTwo A omega)

/-- Optimal generalized measure, PDF p.39, Definition 3. -/
def OptimalMeasure {I : Type} (A : Set (State I)) (mu : GeneralizedEnsemble I) : Prop :=
  MeasureConcentratedOn (mu : Measure (State I)) A ∧ measureHolevo (mu : Measure (State I)) = setChiCapacity A

/-- Trace closure of extreme points, PDF p.40 (both overlines are essential). -/
def extremeClosure {I : Type} (A : Set (State I)) : Set (State I) :=
  closure {rho | rho.coefficients ∈ (State.coefficients '' A).extremePoints ℝ}

/-- A concrete CPTP map packaged with its normalized state action, PDF pp.3,35.
The action is tied coefficient by coefficient to the accepted full trace-class
map; no finite Kraus or finite-dimensional restriction is imposed. -/
structure StateChannel (I J : Type) where
  map : Matrix I I ℂ → Matrix J J ℂ
  channel : IsTraceClassChannel map
  action : State I → State J
  action_eq : ∀ rho, (action rho).coefficients = map rho.coefficients

/-- Capacity-preserving channels mapping into the closed hull, PDF p.35. -/
def PreservingChannels {I : Type} (A : Set (State I)) : Set (StateChannel I I) :=
  {Phi | Phi.action '' A ⊆ stateClosedConvexHull A ∧ setChiCapacity (Phi.action '' A) = setChiCapacity A}

/-- Common invariant states, PDF p.35; no commutativity is assumed. -/
def CommonChannelInvariant {I : Type} (F : Set (StateChannel I I)) (rho : State I) : Prop :=
  ∀ Phi ∈ F, Phi.action rho = rho

/-- Countable ensemble as its actual atomic probability law, PDF pp.39–40.
Normalization of w is required at each use, and zero weights contribute zero. -/
def countableLaw {I : Type} (w : ℕ → ℝ≥0) (rho : ℕ → State I) : Measure (State I) :=
  Measure.sum (fun n => (w n : ℝ≥0∞) • Measure.dirac (rho n))

/-- All joint states with marginal membership, including entangled states,
PDF p.61. The two marginals are identified with actual normalized states. -/
def jointMarginalConstraintSet {I J : Type} (A : Set (State I)) (B : Set (State J)) :
    Set (State (I × J)) :=
  {omega | (∃ rho ∈ A, traceSecond omega.coefficients = rho.coefficients) ∧
    (∃ sigma ∈ B, traceFirst omega.coefficients = sigma.coefficients)}

/-- Fixed-marginal coupling set C(rho,sigma), PDF p.62. -/
def couplingSet {I J : Type} (rho : State I) (sigma : State J) :
    Set (State (I × J)) := jointMarginalConstraintSet {rho} {sigma}

/-- A layer in a CHOSEN eigenbasis, PDF p.22 and footnote 10. The theorems
explicitly require sigma diagonal in these coordinates, leaving repeated
eigenvalues and their basis choice visible. -/
def layer {I : Type} (sigma : State I) : Set (State I) :=
  {rho | ∀ i, rho.coefficients i i = sigma.coefficients i i}

/-- Chosen coordinates are an eigenbasis of sigma, PDF p.22. -/
def Diagonal {I : Type} (sigma : State I) : Prop :=
  ∀ i j, i ≠ j → sigma.coefficients i j = 0

/-- Finite probability simplex, PDF p.36. The equation excludes n=0. -/
def InSimplex {n : ℕ} (w : Fin n → ℝ≥0) : Prop := (∑ k, w k) = 1

/-- The actual finite ensemble of specified states, PDF pp.5,36. -/
def finiteLaw {I : Type} {n : ℕ} (w : Fin n → ℝ≥0) (rho : Fin n → State I) :
    Measure (State I) := ∑ k, (w k : ℝ≥0∞) • Measure.dirac (rho k)

/-- The objective whose maximum appears in Proposition 7, PDF p.36. -/
def unionObjective {I : Type} {n : ℕ} (A : Fin n → Set (State I))
    (hA : ∀ k, (A k).Nonempty) (w : Fin n → ℝ≥0) : ℝ≥0∞ :=
  (∑ k, (w k : ℝ≥0∞) * setChiCapacity (A k)) +
    measureHolevo (finiteLaw w (fun k => optimalAverage (A k) (hA k)))

/-- Layer with the first n-1 rows and columns diagonal, PDF p.59.
Source indices start at one, so coordinate i corresponds to source i+1. -/
def tailLayer (sigma : State ℕ) (n : ℕ) : Set (State ℕ) :=
  {rho | rho ∈ layer sigma ∧ ∀ i j, i ≠ j →
    (i + 1 < n ∨ j + 1 < n) → rho.coefficients i j = 0}

/-- The concrete decreasing family of PDF p.61, not an arbitrary family
satisfying capacity conclusions: L_(n+1)(sigma) intersect V_(sigma,c). -/
def decreasingFamily (sigma : State ℕ) (c : ℝ≥0) (n : ℕ) : Set (State ℕ) :=
  tailLayer sigma (n + 1) ∩ {rho | stateRelativeEntropyNats rho sigma ≤ (c : ℝ≥0∞)}

/-- Minimal closed equal-capacity subset, PDF p.30, footnote 19. -/
def MinimalClosedEqualCapacity {I : Type} (A B : Set (State I)) : Prop :=
  IsClosed B ∧ B ⊆ A ∧ setChiCapacity B = setChiCapacity A ∧
    ∀ C : Set (State I), IsClosed C → C ⊆ B → setChiCapacity C = setChiCapacity B → C = B

/-- Actual spectral-power trace by finite-compression exhaustion, PDF p.13.
For positive exponents finite-compression eigenvalue interlacing gives the
extended trace of sigma^t. At t=0 this is the rank of the support projection,
not the ambient dimension. The scalar zero-eigenvalue branch is explicit. -/
def spectralPowerTrace {I : Type} (sigma : State I) (t : ℝ) : ℝ≥0∞ :=
  ⨆ s : Finset I, ENNReal.ofReal
    ((cfc (fun x : ℝ => if x = 0 then 0 else x ^ t)
      (sigma.coefficients.submatrix (fun i : s => i.val) (fun i : s => i.val))).trace.re)

/-- Decrease coefficient, PDF p.13. Extended infima avoid a real junk value
when a convergence set is empty; state normalization makes t=1 admissible. -/
def decreaseCoefficient {I : Type} (sigma : State I) : ℝ≥0∞ :=
  ⨅ t : {t : ℝ // 0 < t ∧ spectralPowerTrace sigma t < ⊤}, ENNReal.ofReal t.val

/-- Finite-dimensional operator support, PDF p.13. A finite positive
rank-one sum characterizes positive finite rank in any coordinate basis;
this does NOT require finite coordinate support. -/
def PositiveFiniteRankState {I : Type} (rho : State I) : Prop :=
  ∃ (n : ℕ) (v : Fin n → QAlgorithms.RealRegisters.Hilbert I),
    ∀ i j, rho.coefficients i j = ∑ k, v k i * star (v k j)

/-- Any bounded orthogonal projection, PDF pp.71–73. Neither finite rank
nor a monotone-sequence condition is built into this type. -/
structure BoundedOrthogonalProjection (I : Type) where
  operator : QAlgorithms.RealRegisters.Hilbert I →L[ℂ] QAlgorithms.RealRegisters.Hilbert I
  idempotent : operator.comp operator = operator
  selfAdjoint : operator.adjoint = operator

/-- Positive compression mass Tr(P rho), PDF p.71. On states the bounded
conjugation is trace class, hence the real trace series is summable. -/
def projectionMass {I : Type} (P : BoundedOrthogonalProjection I) (rho : State I) : ℝ :=
  ∑' i, (QAlgorithms.Papers.Independent.Frontier18.P01.boundedConjugation
    P.operator rho.coefficients i i).re

/-- The source's normalized coefficients, PDF p.71. Uses are restricted to
positive mass, so inverse at zero is never asserted to produce a state. -/
def compressedCoefficients {I : Type} (P : BoundedOrthogonalProjection I)
    (rho : State I) : Matrix I I ℂ :=
  ((projectionMass P rho)⁻¹ : ℂ) •
    QAlgorithms.Papers.Independent.Frontier18.P01.boundedConjugation P.operator rho.coefficients

/-- Actual positive-domain image under Theta_P, PDF pp.71–72. Output states
are identified by the formula, not supplied with assumed capacity properties. -/
def projectionImage {I : Type} (P : BoundedOrthogonalProjection I) (A : Set (State I)) :
    Set (State I) :=
  {sigma | ∃ rho ∈ A, 0 < projectionMass P rho ∧
    sigma.coefficients = compressedCoefficients P rho}

/-- Uniform retained mass, PDF p.72. The extended empty infimum is infinity;
all theorem uses explicitly require A nonempty. -/
def projectionSuccessInfimum {I : Type} (P : BoundedOrthogonalProjection I)
    (A : Set (State I)) : ℝ≥0∞ :=
  ⨅ rho : A, ENNReal.ofReal (projectionMass P rho.val)

/-- Optimal average of a compression image on the eventual valid domain,
PDF p.73. An empty early image uses the original set's average only to make
the sequence total; Theorem 4 concludes that this branch eventually disappears. -/
def projectedAverage {I : Type} (P : BoundedOrthogonalProjection I) (A : Set (State I))
    (hA : A.Nonempty) : State I :=
  if h : (projectionImage P A).Nonempty then optimalAverage (projectionImage P A) h
    else optimalAverage A hA

/-! Sanity tests for the defining conventions; no source theorem is proved. -/

example {I : Type} : entropySup (∅ : Set (State I)) = 0 := by simp [entropySup]

example {I : Type} : measureHolevo (0 : Measure (State I)) = 0 := by simp [measureHolevo]

example {I : Type} (mu : Measure (State I)) :
    MeasureConcentratedOn mu Set.univ := by simp [MeasureConcentratedOn]

example {I : Type} (sigma : State I) : sigma ∈ layer sigma := by
  intro i
  rfl

example {I : Type} (X : Matrix I I ℂ) (i : I) : (Matrix.diagonal (Matrix.diag X)) i i = X i i := by
  simp

example {I : Type} (Phi : StateChannel I I) (rho : State I) :
    (Phi.action rho).coefficients = Phi.map rho.coefficients := Phi.action_eq rho

example {I J : Type} (rho : State I) (sigma : State J) (omega : State (I × J)) :
    omega ∈ couplingSet rho sigma ↔
      traceSecond omega.coefficients = rho.coefficients ∧
        traceFirst omega.coefficients = sigma.coefficients := by
  simp [couplingSet, jointMarginalConstraintSet]

example (t : ℝ) : (if (0 : ℝ) = 0 then 0 else (0 : ℝ) ^ t) = (0 : ℝ) := by
  simp

example {I : Type} (rho : PureState I) : PositiveFiniteRankState rho.val := by
  rcases rho.property with ⟨u, hu, heq⟩
  refine ⟨1, fun _ => u, ?_⟩
  intro i j
  simp [heq, QAlgorithms.Papers.Independent.Dependency50.P33.rankOne]

example (sigma : State ℕ) (hdiag : Diagonal sigma) (n : ℕ) :
    sigma ∈ tailLayer sigma n := by
  refine ⟨fun _ => rfl, ?_⟩
  intro i j hne hbelow
  exact hdiag i j hne

example {I : Type} [Countable I] (mu : GeneralizedEnsemble I)
    (hb : ∃ average : GeneralizedEnsemble I → State I,
      (∀ mu, HasAverage mu (average mu)) ∧ Continuous average) :
    HasAverage mu (probabilityAverage mu) := by
  unfold probabilityAverage
  rw [dif_pos hb]
  exact (Classical.choose_spec hb).1 mu

example {I : Type} [Countable I] (mu : GeneralizedEnsemble I)
    (hb : ∃ average : GeneralizedEnsemble I → State I,
      (∀ mu, HasAverage mu (average mu)) ∧ Continuous average) :
    meanCoefficients (mu : Measure (State I)) = (probabilityAverage mu).coefficients := by
  unfold probabilityAverage
  rw [dif_pos hb]
  funext i j
  exact ((Classical.choose_spec hb).1 mu i j).2.symm

example {I : Type} (A : Set (State I)) (hA : A.Nonempty)
    (h : ∃ omega, RadiusCenter A omega) : RadiusCenter A (optimalAverage A hA) := by
  unfold optimalAverage
  rw [dif_pos h]
  exact Classical.choose_spec h

example : ¬ InSimplex (fun _ : Fin 0 => (0 : ℝ≥0)) := by simp [InSimplex]

example : InSimplex (fun _ : Fin 1 => (1 : ℝ≥0)) := by simp [InSimplex]

example {I : Type} (rho : ℕ → State I) :
    countableLaw (fun _ => 0) rho = 0 := by simp [countableLaw]

example {I J : Type} (B : Set (State J)) :
    jointMarginalConstraintSet (∅ : Set (State I)) B = ∅ := by
  ext omega
  simp [jointMarginalConstraintSet]

/-! Source statement batch. -/

end QAlgorithms.Papers.Independent.Gap48.P18


