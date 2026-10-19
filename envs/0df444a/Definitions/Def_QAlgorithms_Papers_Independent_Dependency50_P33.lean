-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
-- name    : QAlgorithms_Papers_Independent_Dependency50_P33
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:18:34.525429+00:00
-- url     : https://prove2.me/theorems/cbb4ea36-3c31-43bb-969f-97f67e51adcd
-- title:
--   Definitions for Separability and Entanglement-Breaking in Infinite Dimensions
-- statement:
--   The objects the formalized statements of *Separability and Entanglement-Breaking in Infinite Dimensions* (arXiv:quant-ph/0504204) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `NuclearExpansion`: Nuclear representation of trace class (PDF pp.1–2). Summable products of Hilbert norms guarantee trace-norm and absolute coefficient-series convergence.
--   - `IsTraceClass`: Trace class via the equivalent Hilbert-space nuclear criterion (PDF p.1). This includes nonpositive operators.
--   - `traceSize`: Nuclear norm equals trace norm on Hilbert-space trace class (PDF pp.1–2). The extended nonnegative infimum of an empty set is infinity, avoiding the default real infimum zero on arrays without a nuclear expansion.
--   - `traceClosure`: Trace-norm closure using every positive radius (PDF p.2). Coefficientwise and weak-operator closure are not substituted.
--   - `IsDensity`: Positive trace-class operators of trace one (PDF pp.1–2). All finite quadratic forms must be real and nonnegative. The trace series is summable.
--   - `State`: Density operators; zero and unnormalized operators are excluded (PDF p.1).
--   - `rankOne`: Rank-one coefficients; a pure state also requires norm one (PDF p.3).
--   - `PureState`: Pure density operators with inherited trace-norm Borel structure (PDF p.3). No measurable choice of unit-vector representatives or global phases is made.
--   - `productCoeff`: Tensor product on completed Hilbert spaces (PDF p.2), whose coordinate space is `l²(I × J)`, including vectors of infinite Schmidt rank.
--   - `productStates`: All mixed product density operators, Definition 1 (PDF p.2).
--   - `IsSeparable`: Definition 1: trace-norm closed convex hull of all product states (PDF p.2). Equality to the pure-product version is a conclusion, not an assumption.
--   - `IsCountablyDecomposable`: Countable product decomposition, PDF p.3 following (2). Nonnegative weights are summable with sum one. Product states have trace norm one, so the series also converges in trace norm. Zero weights include finite decompositions.
--   - `IsBarycenter`: Coefficient characterization of barycenter (1), PDF p.2. For the Borel probability laws and state/product-state integrands used below, the trace-norm Bochner integral exists (the integrand has norm one). These are its coefficients. Explicit scalar integrability prevents a default-zero integral.
--   - `IsTraceClosed`: Closed subsets of the trace-norm state space (Lemma 1, PDF p.2).
--   - `tensorApply`: Apply the channel to the first factor, retaining off-diagonal blocks (Definition 2, PDF p.3). Trace-class bipartite inputs have trace-class slices.
--   - `IsTraceClassChannel`: Complex-linear, completely positive, trace-preserving map on trace class (PDF p.3, conditions 1–2). Arrays outside trace class are ignored. Complete positivity and trace preservation are equivalently expressed as preservation of states by every finite matrix amplification. Boundedness follows; no Kraus form is imposed. The accepted `QAlgorithms.IsChannel` requires finite basis sets and finite Kraus families, so it cannot express this source's infinite-dimensional map.
--   - `BreaksTraceClassEntanglement`: Definition 2 (PDF p.3): every state, with every separable complex Hilbert ancilla, has separable output. Countable bases represent all such ancillas. The accepted `QAlgorithms.Entanglement.IsEntanglementBreaking` has a fixed qubit input/output and finite ancillas, so a separate general predicate is necessary.
--   - `rotationMeasure`: Normalized Lebesgue measure on `[0,2pi)`, PDF pp.6–7, (15).
--   - `rotationCoeff`: Translation conjugation in Fourier coordinates, PDF pp.6–7, (13)–(15). Printed: positive Fourier phase, incompatible with `V_u psi(t) = psi(t-u)`. Changed: negative Fourier phase as dictated by translation (`e_1` has phase `exp(-iu)`). Reversal of the full twirl parameter leaves (15) unchanged.
--   - `correlatedTwirl`: The specific correlated rotation twirl (15), PDF p.7. `Hilbert Z` is the Fourier model of normalized circle L².
-- source:
--   Separability and Entanglement-Breaking in Infinite Dimensions, arXiv:quant-ph/0504204v1, https://arxiv.org/abs/quant-ph/0504204v1

import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters

/-!
# Separability and entanglement-breaking in infinite dimensions

Source: Holevo, Shirokov and Werner, arXiv:quant-ph/0504204v1.
Countable orthonormal coordinates model arbitrary separable complex Hilbert spaces.
Their completed Hilbert tensor product has Cartesian-product basis indices.
There is no finite-dimensional cutoff. Operator arrays require explicit nuclearity,
positivity and normalization. All state topology and convergence use the trace norm.
Results without completed interfaces are recorded in the unit's HARD.md/GAPS.json.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P33

/-! Reuse `QAlgorithms.RealRegisters.Hilbert` directly from the imported frozen
module. Mathlib `Matrix I I ℂ` is the unrestricted operator-coefficient array;
trace class and boundedness are supplied separately below. The accepted paper-local
`Information100.P19.Coeff` instead denotes finitely supported partition coefficients
and has no relation to operator arrays. -/

open QAlgorithms.RealRegisters (Hilbert)

/-- Nuclear representation of trace class (PDF pp.1–2). Summable products of
Hilbert norms guarantee trace-norm and absolute coefficient-series convergence. -/
structure NuclearExpansion {I : Type} (X : (Matrix I I ℂ)) where
  left : ℕ → Hilbert I
  right : ℕ → Hilbert I
  summable : Summable (fun n => ‖left n‖ * ‖right n‖)
  coefficients : ∀ i j, X i j = ∑' n : ℕ, left n i * star (right n j)

/-- Trace class via the equivalent Hilbert-space nuclear criterion (PDF p.1).
This includes nonpositive operators. -/
def IsTraceClass {I : Type} (X : (Matrix I I ℂ)) : Prop := Nonempty (NuclearExpansion X)

/-- Nuclear norm equals trace norm on Hilbert-space trace class (PDF pp.1–2).
The extended nonnegative infimum of an empty set is infinity, avoiding the default
real infimum zero on arrays without a nuclear expansion. -/
def traceSize {I : Type} (X : (Matrix I I ℂ)) : ℝ≥0∞ :=
  ⨅ e : NuclearExpansion X, ENNReal.ofReal (∑' n : ℕ, ‖e.left n‖ * ‖e.right n‖)

/-- Trace-norm closure using every positive radius (PDF p.2).
Coefficientwise and weak-operator closure are not substituted. -/
def traceClosure {I : Type} (S : Set ((Matrix I I ℂ))) : Set ((Matrix I I ℂ)) :=
  {X | ∀ epsilon : ℝ, 0 < epsilon →
    ∃ Y ∈ S, traceSize (X - Y) < ENNReal.ofReal epsilon}

/-- Positive trace-class operators of trace one (PDF pp.1–2). All finite
quadratic forms must be real and nonnegative. The trace series is summable. -/
def IsDensity {I : Type} (X : (Matrix I I ℂ)) : Prop :=
  IsTraceClass X ∧
  (∀ (s : Finset I) (z : I → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).re) ∧
  Summable (fun i => (X i i).re) ∧ (∑' i, (X i i).re) = 1

/-- Density operators; zero and unnormalized operators are excluded (PDF p.1). -/
structure State (I : Type) where
  coefficients : (Matrix I I ℂ)
  density : IsDensity coefficients

/-- Trace-norm topology on states (PDF p.1), generated only by trace-norm balls.
The product topology on coefficient arrays is unused. -/
instance stateTopology (I : Type) : TopologicalSpace (State I) :=
  TopologicalSpace.generateFrom {U | ∃ (rho : State I) (epsilon : ℝ),
    0 < epsilon ∧ U = {sigma | traceSize (sigma.coefficients - rho.coefficients) <
      ENNReal.ofReal epsilon}}

/-- Trace-norm Borel sigma algebra (PDF pp.1–2). -/
instance stateMeasurableSpace (I : Type) : MeasurableSpace (State I) := borel (State I)

/-- Rank-one coefficients; a pure state also requires norm one (PDF p.3). -/
def rankOne {I : Type} (u : Hilbert I) : (Matrix I I ℂ) := fun i j => u i * star (u j)

/-- Pure density operators with inherited trace-norm Borel structure (PDF p.3).
No measurable choice of unit-vector representatives or global phases is made. -/
abbrev PureState (I : Type) := {rho : State I //
  ∃ u : Hilbert I, ‖u‖ = 1 ∧ rho.coefficients = rankOne u}

/-- Tensor product on completed Hilbert spaces (PDF p.2), whose coordinate
space is `l²(I × J)`, including vectors of infinite Schmidt rank. -/
def productCoeff {I J : Type} (X : (Matrix I I ℂ)) (Y : (Matrix J J ℂ)) : (Matrix (I × J) (I × J) ℂ) :=
  fun p q => X p.1 q.1 * Y p.2 q.2

/-- All mixed product density operators, Definition 1 (PDF p.2). -/
def productStates (I J : Type) : Set ((Matrix (I × J) (I × J) ℂ)) :=
  {X | ∃ (rho : State I) (sigma : State J),
    X = productCoeff rho.coefficients sigma.coefficients}

/-- Definition 1: trace-norm closed convex hull of all product states (PDF p.2).
Equality to the pure-product version is a conclusion, not an assumption. -/
def IsSeparable {I J : Type} (X : (Matrix (I × J) (I × J) ℂ)) : Prop :=
  X ∈ traceClosure (convexHull ℝ (productStates I J))

/-- Countable product decomposition, PDF p.3 following (2). Nonnegative weights
are summable with sum one. Product states have trace norm one, so the series also
converges in trace norm. Zero weights include finite decompositions. -/
def IsCountablyDecomposable {I J : Type} (X : (Matrix (I × J) (I × J) ℂ)) : Prop :=
  ∃ (w : ℕ → ℝ) (rho : ℕ → State I) (sigma : ℕ → State J),
    (∀ n, 0 ≤ w n) ∧ Summable w ∧ (∑' n, w n) = 1 ∧
    ∀ p q, X p q = ∑' n : ℕ,
      (w n : ℂ) * productCoeff (rho n).coefficients (sigma n).coefficients p q

/-- Coefficient characterization of barycenter (1), PDF p.2. For the Borel
probability laws and state/product-state integrands used below, the trace-norm
Bochner integral exists (the integrand has norm one). These are its coefficients.
Explicit scalar integrability prevents a default-zero integral. -/
def IsBarycenter {I : Type} {X : Type} [MeasurableSpace X]
    (mu : Measure X) (f : X → (Matrix I I ℂ)) (rho : (Matrix I I ℂ)) : Prop :=
  ∀ i j, Integrable (fun x => f x i j) mu ∧ rho i j = ∫ x, f x i j ∂mu

/-- Closed subsets of the trace-norm state space (Lemma 1, PDF p.2). -/
def IsTraceClosed {I : Type} (A : Set (State I)) : Prop :=
  ∀ rho : State I, rho.coefficients ∈ traceClosure (State.coefficients '' A) → rho ∈ A

/-- Apply the channel to the first factor, retaining off-diagonal blocks
(Definition 2, PDF p.3). Trace-class bipartite inputs have trace-class slices. -/
def tensorApply {I J A : Type} (Phi : (Matrix I I ℂ) → (Matrix J J ℂ))
    (X : (Matrix (I × A) (I × A) ℂ)) : (Matrix (J × A) (J × A) ℂ) :=
  fun p q => Phi (fun i j => X (i, p.2) (j, q.2)) p.1 q.1

/-- Complex-linear, completely positive, trace-preserving map on trace class
(PDF p.3, conditions 1–2). Arrays outside trace class are ignored. Complete
positivity and trace preservation are equivalently expressed as preservation of
states by every finite matrix amplification. Boundedness follows; no Kraus form
is imposed. The accepted `QAlgorithms.IsChannel` requires finite basis sets and
finite Kraus families, so it cannot express this source's infinite-dimensional map. -/
def IsTraceClassChannel {I J : Type} (Phi : (Matrix I I ℂ) → (Matrix J J ℂ)) : Prop :=
  (∀ X, IsTraceClass X → IsTraceClass (Phi X)) ∧
  (∀ X Y, IsTraceClass X → IsTraceClass Y → Phi (X + Y) = Phi X + Phi Y) ∧
  (∀ (c : ℂ) X, IsTraceClass X → Phi (c • X) = c • Phi X) ∧
  (∀ (n : ℕ) (rho : State (I × Fin n)), IsDensity (tensorApply Phi rho.coefficients))

/-- Definition 2 (PDF p.3): every state, with every separable complex Hilbert
ancilla, has separable output. Countable bases represent all such ancillas.
The accepted `QAlgorithms.Entanglement.IsEntanglementBreaking` has a fixed qubit
input/output and finite ancillas, so a separate general predicate is necessary. -/
def BreaksTraceClassEntanglement {I J : Type} (Phi : (Matrix I I ℂ) → (Matrix J J ℂ)) : Prop :=
  ∀ (A : Type) [Countable A] (rho : State (I × A)),
    IsSeparable (tensorApply Phi rho.coefficients)

/-- Normalized Lebesgue measure on `[0,2pi)`, PDF pp.6–7, (15). -/
def rotationMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Set.Ico 0 (2 * Real.pi))

/-- Translation conjugation in Fourier coordinates, PDF pp.6–7, (13)–(15).
Printed: positive Fourier phase, incompatible with `V_u psi(t) = psi(t-u)`.
Changed: negative Fourier phase as dictated by translation (`e_1` has phase
`exp(-iu)`). Reversal of the full twirl parameter leaves (15) unchanged. -/
def rotationCoeff (x : ℝ) (X : (Matrix ℤ ℤ ℂ)) : (Matrix ℤ ℤ ℂ) :=
  fun k l => Complex.exp (-Complex.I * (x : ℂ) * ((k : ℂ) - (l : ℂ))) * X k l

/-- The specific correlated rotation twirl (15), PDF p.7.
`Hilbert Z` is the Fourier model of normalized circle L². -/
def correlatedTwirl (u v : Hilbert ℤ) : (Matrix (ℤ × ℤ) (ℤ × ℤ) ℂ) :=
  fun p q => ∫ x, productCoeff (rotationCoeff x (rankOne u))
    (rotationCoeff x (rankOne v)) p q ∂rotationMeasure

/-! Sanity examples for local definitions; no source theorem is proved here. -/

example {I : Type} : IsTraceClass (0 : (Matrix I I ℂ)) := by
  refine ⟨{
    left := fun _ => 0
    right := fun _ => 0
    summable := ?_
    coefficients := ?_
  }⟩
  · simp
  · intro i j
    simp

example {I : Type} (X : (Matrix I I ℂ)) (e : NuclearExpansion X) :
    traceSize X ≤ ENNReal.ofReal (∑' n : ℕ, ‖e.left n‖ * ‖e.right n‖) :=
  iInf_le _ e

example {I : Type} (rho : State I) : (∑' i, (rho.coefficients i i).re) = 1 :=
  rho.density.2.2.2

example {I : Type} (rho : PureState I) :
    ∃ u : Hilbert I, ‖u‖ = 1 ∧ rho.val.coefficients = rankOne u := rho.property

example {I J : Type} (rho : State I) (sigma : State J) :
    productCoeff rho.coefficients sigma.coefficients ∈ productStates I J :=
  ⟨rho, sigma, rfl⟩

example {I : Type} : ¬ IsDensity (0 : (Matrix I I ℂ)) := by
  intro h
  simpa using h.2.2.2

example {I : Type} : traceClosure (∅ : Set ((Matrix I I ℂ))) = ∅ := by
  ext X
  constructor
  · intro h
    obtain ⟨Y, hY, _⟩ := h 1 zero_lt_one
    exact hY
  · intro h
    exact False.elim h

example {I : Type} : rankOne (0 : Hilbert I) = 0 := by
  funext i j
  simp [rankOne]

example {I J : Type} (X : (Matrix I I ℂ)) : productCoeff X (0 : (Matrix J J ℂ)) = 0 := by
  funext p q
  simp [productCoeff]

example {I A : Type} (X : (Matrix (I × A) (I × A) ℂ)) : tensorApply id X = X := rfl

example (x : ℝ) (X : (Matrix ℤ ℤ ℂ)) (k : ℤ) : rotationCoeff x X k k = X k k := by
  simp [rotationCoeff]

example (X : (Matrix ℤ ℤ ℂ)) : rotationCoeff 0 X = X := by
  funext k l
  simp [rotationCoeff]

end QAlgorithms.Papers.Independent.Dependency50.P33


