-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P42
-- name    : QAlgorithms_Papers_Independent_Next46_P42
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T15:33:02.238627+00:00
-- url     : https://prove2.me/theorems/320930c6-a8fd-47af-9ea3-9723cb24c59d
-- title:
--   Definitions for On entropic quantities related to the classical capacity of infinite dimensional quantum channels
-- statement:
--   The objects the formalized statements of *On entropic quantities related to the classical capacity of infinite dimensional quantum channels* (arXiv:quant-ph/0411091) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `LabelledEnsemble`: PDF pp.3,6: a labelled ensemble of exactly m slots, with zero weights allowed.
--   - `LabelledEnsemble.average`: PDF p.3: the exact average density coefficients of a finite ensemble.
--   - `LabelledEnsemble.cost`: PDF pp.5,9: finite ensemble output-entropy cost; 0 times infinity is zero.
--   - `LabelledEnsemble.law`: PDF pp.3,10: the finite atomic law associated to a labelled ensemble.
--   - `finiteHull`: PDF pp.5,9: convex hull over finite mixed-state decompositions, with exact average.
--   - `entropyRoof`: PDF p.9: integral roof over all probability laws, with exact trace-norm barycenter. The scalar integrability in IsBarycenter rules out default-zero integrals.
--   - `ConvexOnStates`: PDF pp.12,22: extended convexity on the state space, including endpoint weights.
--   - `ConcaveOnStates`: PDF pp.5,22: extended concavity on normalized states.
--   - `closedHull`: PDF pp.22–23: greatest closed convex minorant. Restricting to nonnegative minorants loses nothing for a nonnegative entropy. Off-state values are unused.
--   - `realEpigraph`: PDF p.22: the real vertical epigraph, with empty fibers at infinite values.
--   - `RoofOptimal`: PDF p.12, Definition 2: exact average, pure support, and attained integral roof.
--   - `ChiOptimal`: PDF p.5, Definition 1: exact average, pure support, and attained chi value.
--   - `HasRank`: PDF pp.10–12: exact finite rank, avoiding default infinite-dimensional finrank.
--   - `partialLimits`: PDF p.17: partial limits mean limits of subsequences in the weak law topology.
--   - `HermitianObservable`: PDF pp.15,18: bounded Hermitian observables on the completed Hilbert space.
--   - `BoundedPositiveObservable`: PDF p.18: the bounded part of the accepted positive-observable space. A uniform quadratic-form bound excludes unbounded observables while retaining zero. The closed-form representation theorem identifies this subtype with B_+(H).
--   - `observablePair`: PDF p.15: Tr(A X), evaluated only for trace-class X. The inner coefficient series is the bounded-operator action and the outer trace series is absolutely convergent.
--   - `entropyConjugate`: PDF p.15, (13): signed extended Fenchel conjugate on bounded Hermitian operators.
--   - `entropyBiconjugate`: PDF p.15, (14): biconjugate, allowing -infinity conjugates and +infinity roofs.
--   - `minimumCost`: PDF p.18: generalized minimum with a specified nonnegative input cost.
--   - `outputPurity`: PDF p.18, (16): output purity, with the positive sign before Tr(A rho).
--   - `minimumOutputEntropy`: PDF p.18, (17): minimum output entropy as an extended infimum, not an attained minimum.
--   - `kroneckerCost`: PDF pp.18–19: expectation of A tensor I + I tensor B on a joint state. The marginal formula is exactly the Kronecker sum, including correlated inputs.
--   - `marginalConstraint`: PDF p.19, (21): all joint states with constrained marginals; no product-state restriction.
--   - `StrongSuperadditive`: PDF p.19: strong superadditivity of the integral roof, on every joint state.
--   - `PurityAdditive`: PDF p.19: additivity of the output purity for every pair of bounded positive operators.
--   - `StrongCapacityAdditive`: PDF p.19: capacity additivity for nonempty constraints of finite output entropy.
--   - `restrictedChannel`: PDF p.20: a subchannel is an input-subspace restriction along an isometric embedding.
--   - `SubchannelMinimumAdditive`: PDF pp.19–20: minimum-output additivity for all nonzero closed input subspaces.
--   - `OutputHamiltonian`: PDF p.17: a positive unbounded discrete observable in a complete eigenbasis. U sends the coordinate basis to that eigenbasis; finite sublevels mean finite multiplicities.
--   - `OutputHamiltonian.mean`: PDF p.17: extended nonnegative output energy in the Hamiltonian eigenbasis.
--   - `OutputHamiltonian.gibbs`: PDF p.17: Gibbs finiteness at every positive inverse temperature.
--   - `measureEof`: PDF p.21: measure entanglement of formation on the full bipartite state space.
--   - `PureDecomposition`: PDF p.21: actual countable decompositions into normalized pure density operators.
--   - `PureDecomposition.hasAverage`: PDF p.21: exact barycenter is convergence in trace norm of the partial operator sums.
--   - `countableEof`: PDF p.21: countable EoF roof; no finite-marginal-entropy restriction in its definition.
--   - `localPureCost`: PDF p.22: finite pure-ensemble cost with average in an open trace-norm ball. The exact target need not be the ensemble average. Empty feasible sets have infimum infinity.
--   - `regroupProduct`: Section 6 and PDF pp.21–22: product of two bipartite states regrouped as AC : BD.
--   - `GlobalEofAdditive`: Full-state tensor-additivity property for a chosen EoF convention. This is a property, not an unconditional theorem; the source leaves general additivity open.
-- source:
--   On entropic quantities related to the classical capacity of infinite dimensional quantum channels, arXiv:quant-ph/0411091v1, https://arxiv.org/abs/quant-ph/0411091v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

/-!
Shirokov, arXiv:quant-ph/0411091v1. All Hilbert spaces are nonzero separable
complex spaces, represented by countable nonempty orthonormal coordinates.
The pinned P33 state type is positive nuclear trace class of trace one, with
trace-norm topology. P07 supplies weak probability laws, integrable coefficient
barycenters, natural-log extended entropy and the finite-ensemble capacity.
Raw coefficient arguments below allow partial traces and channel outputs without
choosing proofs of normalization; all theorem inputs are actual states.
No new axioms or unfinished definitions are introduced. Compilation is pending.
-/

noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsBarycenter IsTraceClassChannel traceSize traceClosure
    productCoeff IsSeparable)
open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel IsPositive TraceOperatorLE RankAtMost SpectralPresentation spectralTruncation
    convexOperatorMixture traceSecond traceFirst channelTensorAction boundedConjugation)
open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasAverage HasFiniteSupport pureStates extendedEntropyNats
    extendedRelativeEntropyNats relativeIntegral finiteEnsembleCapacity stateChi)
open QAlgorithms.Papers.Independent.Claimed50.P13
  (PositiveObservable closedFormExpectation)

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P42

/-- PDF pp.3,6: a labelled ensemble of exactly m slots, with zero weights allowed. -/
structure LabelledEnsemble (I : Type) (m : ℕ) where
  weight : Fin m → ℝ≥0
  mass : ∑ i, weight i = 1
  state : Fin m → State I

/-- PDF p.3: the exact average density coefficients of a finite ensemble. -/
def LabelledEnsemble.average {I : Type} {m : ℕ} (e : LabelledEnsemble I m) : Matrix I I ℂ :=
  ∑ i, (((e.weight i : ℝ) : ℂ) • (e.state i).coefficients)

/-- PDF pp.5,9: finite ensemble output-entropy cost; 0 times infinity is zero. -/
def LabelledEnsemble.cost {I J : Type} {m : ℕ}
    (e : LabelledEnsemble I m) (Phi : Matrix I I ℂ → Matrix J J ℂ) : ℝ≥0∞ :=
  ∑ i, (e.weight i : ℝ≥0∞) * extendedEntropyNats (Phi (e.state i).coefficients)

/-- PDF pp.3,10: the finite atomic law associated to a labelled ensemble. -/
def LabelledEnsemble.law {I : Type} {m : ℕ} (e : LabelledEnsemble I m) : Measure (State I) :=
  ∑ i : Fin m, (e.weight i : ℝ≥0∞) • (Measure.dirac (e.state i) : Measure (State I))

/-- PDF pp.5,9: convex hull over finite mixed-state decompositions, with exact average. -/
def finiteHull {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (X : Matrix I I ℂ) : ℝ≥0∞ :=
  ⨅ m : ℕ, ⨅ e : {e : LabelledEnsemble I m // e.average = X}, e.val.cost Phi

/-- PDF p.9: integral roof over all probability laws, with exact trace-norm barycenter.
The scalar integrability in IsBarycenter rules out default-zero integrals. -/
def entropyRoof {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (X : Matrix I I ℂ) : ℝ≥0∞ :=
  ⨅ mu : {mu : GeneralizedEnsemble I //
    IsBarycenter (mu : Measure (State I)) State.coefficients X},
    ∫⁻ rho : State I, extendedEntropyNats (Phi rho.coefficients)
      ∂(mu.val : Measure (State I))

/-- PDF pp.12,22: extended convexity on the state space, including endpoint weights. -/
def ConvexOnStates {I : Type} (f : Matrix I I ℂ → ℝ≥0∞) : Prop :=
  ∀ (rho sigma tau : State I) (t : ℝ), t ∈ Set.Icc 0 1 →
    tau.coefficients = convexOperatorMixture t rho.coefficients sigma.coefficients →
    f tau.coefficients ≤ ENNReal.ofReal t * f rho.coefficients +
      ENNReal.ofReal (1-t) * f sigma.coefficients

/-- PDF pp.5,22: extended concavity on normalized states. -/
def ConcaveOnStates {I : Type} (f : Matrix I I ℂ → ℝ≥0∞) : Prop :=
  ∀ (rho sigma tau : State I) (t : ℝ), t ∈ Set.Icc 0 1 →
    tau.coefficients = convexOperatorMixture t rho.coefficients sigma.coefficients →
    ENNReal.ofReal t * f rho.coefficients +
      ENNReal.ofReal (1-t) * f sigma.coefficients ≤ f tau.coefficients

/-- PDF pp.22–23: greatest closed convex minorant. Restricting to nonnegative
minorants loses nothing for a nonnegative entropy. Off-state values are unused. -/
def closedHull {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (X : Matrix I I ℂ) : ℝ≥0∞ :=
  ⨆ f : {f : Matrix I I ℂ → ℝ≥0∞ // ConvexOnStates f ∧
      LowerSemicontinuous (fun rho : State I => f rho.coefficients) ∧
      ∀ rho : State I, f rho.coefficients ≤ extendedEntropyNats (Phi rho.coefficients)},
    f.val X

/-- PDF p.22: the real vertical epigraph, with empty fibers at infinite values. -/
def realEpigraph {I : Type} (f : Matrix I I ℂ → ℝ≥0∞) : Set (State I × ℝ) :=
  {p | (f p.1.coefficients).toEReal ≤ (p.2 : EReal)}

/-- PDF p.12, Definition 2: exact average, pure support, and attained integral roof. -/
def RoofOptimal {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (X : Matrix I I ℂ) (mu : GeneralizedEnsemble I) : Prop :=
  IsBarycenter (mu : Measure (State I)) State.coefficients X ∧
    (mu : Measure (State I)).support ⊆ pureStates I ∧
    (∫⁻ rho : State I, extendedEntropyNats (Phi rho.coefficients)
      ∂(mu : Measure (State I))) = entropyRoof Phi X

/-- PDF p.5, Definition 1: exact average, pure support, and attained chi value. -/
def ChiOptimal {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (X : Matrix I I ℂ) (mu : GeneralizedEnsemble I) : Prop :=
  IsBarycenter (mu : Measure (State I)) State.coefficients X ∧
    (mu : Measure (State I)).support ⊆ pureStates I ∧
    relativeIntegral Phi mu X =
      finiteEnsembleCapacity Phi {rho : State I | rho.coefficients = X}

/-- PDF pp.10–12: exact finite rank, avoiding default infinite-dimensional finrank. -/
def HasRank {I : Type} (X : Matrix I I ℂ) (n : ℕ) : Prop :=
  RankAtMost X n ∧ ∀ k, RankAtMost X k → n ≤ k

/-- PDF p.17: partial limits mean limits of subsequences in the weak law topology. -/
def partialLimits {I : Type} (mu : ℕ → GeneralizedEnsemble I) : Set (GeneralizedEnsemble I) :=
  {nu | ∃ k : ℕ → ℕ, StrictMono k ∧ Tendsto (fun n => mu (k n)) atTop (nhds nu)}

/-- PDF pp.15,18: bounded Hermitian observables on the completed Hilbert space. -/
abbrev HermitianObservable (I : Type) :=
  {A : Hilbert I →L[ℂ] Hilbert I // A.adjoint = A}

/-- PDF p.18: the bounded part of the accepted positive-observable space.
A uniform quadratic-form bound excludes unbounded observables while retaining zero.
The closed-form representation theorem identifies this subtype with B_+(H). -/
abbrev BoundedPositiveObservable (I : Type) :=
  {A : PositiveObservable I // ∃ C : ℝ, 0 ≤ C ∧
    ∀ u : Hilbert I, A.form u ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)}

/-- PDF p.15: Tr(A X), evaluated only for trace-class X. The inner coefficient
series is the bounded-operator action and the outer trace series is absolutely convergent. -/
def observablePair {I : Type} (A : Hilbert I →L[ℂ] Hilbert I)
    (X : Matrix I I ℂ) : ℝ :=
  (∑' i : I, ∑' j : I, (A (lp.single 2 j 1)) i * X j i).re

/-- PDF p.15, (13): signed extended Fenchel conjugate on bounded Hermitian operators. -/
def entropyConjugate {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (A : HermitianObservable I) : EReal :=
  ⨆ rho : State I, (observablePair A.val rho.coefficients : EReal) -
    (extendedEntropyNats (Phi rho.coefficients)).toEReal

/-- PDF p.15, (14): biconjugate, allowing -infinity conjugates and +infinity roofs. -/
def entropyBiconjugate {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (X : Matrix I I ℂ) : EReal :=
  ⨆ A : HermitianObservable I, (observablePair A.val X : EReal) - entropyConjugate Phi A

/-- PDF p.18: generalized minimum with a specified nonnegative input cost. -/
def minimumCost {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (cost : Matrix I I ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ rho : State I, extendedEntropyNats (Phi rho.coefficients) + cost rho.coefficients

/-- PDF p.18, (16): output purity, with the positive sign before Tr(A rho). -/
def outputPurity {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (A : BoundedPositiveObservable I) : ℝ≥0∞ :=
  minimumCost Phi (closedFormExpectation A.val)

/-- PDF p.18, (17): minimum output entropy as an extended infimum, not an attained minimum. -/
def minimumOutputEntropy {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) : ℝ≥0∞ :=
  ⨅ rho : State I, extendedEntropyNats (Phi rho.coefficients)

/-- PDF pp.18–19: expectation of A tensor I + I tensor B on a joint state.
The marginal formula is exactly the Kronecker sum, including correlated inputs. -/
def kroneckerCost {I K : Type} (A : BoundedPositiveObservable I) (B : BoundedPositiveObservable K)
    (X : Matrix (I × K) (I × K) ℂ) : ℝ≥0∞ :=
  closedFormExpectation A.val (traceSecond X) +
    closedFormExpectation B.val (traceFirst X)

/-- PDF p.19, (21): all joint states with constrained marginals; no product-state restriction. -/
def marginalConstraint {I K : Type} (A : Set (State I)) (B : Set (State K)) :
    Set (State (I × K)) :=
  {omega | (∃ rho ∈ A, rho.coefficients = traceSecond omega.coefficients) ∧
    (∃ sigma ∈ B, sigma.coefficients = traceFirst omega.coefficients)}

/-- PDF p.19: strong superadditivity of the integral roof, on every joint state. -/
def StrongSuperadditive {I J K L : Type}
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (Psi : Matrix K K ℂ → Matrix L L ℂ) : Prop :=
  ∀ omega : State (I × K), entropyRoof Phi (traceSecond omega.coefficients) +
    entropyRoof Psi (traceFirst omega.coefficients) ≤
      entropyRoof (channelTensorAction Phi Psi) omega.coefficients

/-- PDF p.19: additivity of the output purity for every pair of bounded positive operators. -/
def PurityAdditive {I J K L : Type}
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (Psi : Matrix K K ℂ → Matrix L L ℂ) : Prop :=
  ∀ (A : BoundedPositiveObservable I) (B : BoundedPositiveObservable K),
    minimumCost (channelTensorAction Phi Psi) (kroneckerCost A B) =
      outputPurity Phi A + outputPurity Psi B

/-- PDF p.19: capacity additivity for nonempty constraints of finite output entropy. -/
def StrongCapacityAdditive {I J K L : Type}
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (Psi : Matrix K K ℂ → Matrix L L ℂ) : Prop :=
  ∀ (A : Set (State I)) (B : Set (State K)), A.Nonempty → B.Nonempty →
    (∀ rho ∈ A, extendedEntropyNats (Phi rho.coefficients) < ⊤) →
    (∀ sigma ∈ B, extendedEntropyNats (Psi sigma.coefficients) < ⊤) →
    finiteEnsembleCapacity (channelTensorAction Phi Psi) (marginalConstraint A B) =
      finiteEnsembleCapacity Phi A + finiteEnsembleCapacity Psi B

/-- PDF p.20: a subchannel is an input-subspace restriction along an isometric embedding. -/
def restrictedChannel {I J S : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (V : Hilbert S →ₗᵢ[ℂ] Hilbert I) : Matrix S S ℂ → Matrix J J ℂ :=
  fun X => Phi (boundedConjugation V.toContinuousLinearMap X)

/-- PDF pp.19–20: minimum-output additivity for all nonzero closed input subspaces. -/
def SubchannelMinimumAdditive {I J K L : Type}
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (Psi : Matrix K K ℂ → Matrix L L ℂ) : Prop :=
  ∀ (S T : Type) [Countable S] [Countable T] [Nonempty S] [Nonempty T]
    (V : Hilbert S →ₗᵢ[ℂ] Hilbert I) (W : Hilbert T →ₗᵢ[ℂ] Hilbert K),
    minimumOutputEntropy (channelTensorAction (restrictedChannel Phi V) (restrictedChannel Psi W)) =
      minimumOutputEntropy (restrictedChannel Phi V) + minimumOutputEntropy (restrictedChannel Psi W)

/-- PDF p.17: a positive unbounded discrete observable in a complete eigenbasis.
U sends the coordinate basis to that eigenbasis; finite sublevels mean finite multiplicities. -/
structure OutputHamiltonian (I : Type) where
  eigenbasis : Hilbert I ≃ₗᵢ[ℂ] Hilbert I
  energy : I → ℝ≥0
  finiteSublevels : ∀ E : ℝ, {i | (energy i : ℝ) ≤ E}.Finite
  unbounded : ∀ E : ℝ, ∃ i, E < (energy i : ℝ)

/-- PDF p.17: extended nonnegative output energy in the Hamiltonian eigenbasis. -/
def OutputHamiltonian.mean {I : Type} (G : OutputHamiltonian I)
    (X : Matrix I I ℂ) : ℝ≥0∞ :=
  ∑' i, (G.energy i : ℝ≥0∞) * ENNReal.ofReal
    ((boundedConjugation G.eigenbasis.symm.toLinearIsometry.toContinuousLinearMap X i i).re)

/-- PDF p.17: Gibbs finiteness at every positive inverse temperature. -/
def OutputHamiltonian.gibbs {I : Type} (G : OutputHamiltonian I) : Prop :=
  ∀ beta : ℝ, 0 < beta →
    (∑' i, ENNReal.ofReal (Real.exp (-beta * (G.energy i : ℝ)))) < ⊤

/-- PDF p.21: measure entanglement of formation on the full bipartite state space. -/
def measureEof {I K : Type} (X : Matrix (I × K) (I × K) ℂ) : ℝ≥0∞ :=
  entropyRoof (@traceSecond I K) X

/-- PDF p.21: actual countable decompositions into normalized pure density operators. -/
structure PureDecomposition (I : Type) where
  weight : ℕ → ℝ≥0
  summable : Summable (fun n => (weight n : ℝ))
  mass : (∑' n, (weight n : ℝ)) = 1
  state : ℕ → PureState I

/-- PDF p.21: exact barycenter is convergence in trace norm of the partial operator sums. -/
def PureDecomposition.hasAverage {I : Type} (e : PureDecomposition I)
    (X : Matrix I I ℂ) : Prop :=
  Tendsto (fun N => traceSize (X -
    ∑ n ∈ Finset.range N, (((e.weight n : ℝ) : ℂ) • (e.state n).val.coefficients)))
    atTop (nhds 0)

/-- PDF p.21: countable EoF roof; no finite-marginal-entropy restriction in its definition. -/
def countableEof {I K : Type} (X : Matrix (I × K) (I × K) ℂ) : ℝ≥0∞ :=
  ⨅ e : {e : PureDecomposition (I × K) // e.hasAverage X},
    ∑' n, (e.val.weight n : ℝ≥0∞) *
      extendedEntropyNats (traceSecond (e.val.state n).val.coefficients)

/-- PDF p.22: finite pure-ensemble cost with average in an open trace-norm ball.
The exact target need not be the ensemble average. Empty feasible sets have infimum infinity. -/
def localPureCost {I K : Type} (X : Matrix (I × K) (I × K) ℂ) (epsilon : ℝ) : ℝ≥0∞ :=
  ⨅ m : ℕ, ⨅ e : {e : LabelledEnsemble (I × K) m //
    (∀ i, e.state i ∈ pureStates (I × K)) ∧
    traceSize (e.average - X) < ENNReal.ofReal epsilon}, e.val.cost (@traceSecond I K)

/-- Section 6 and PDF pp.21–22: product of two bipartite states regrouped as AC : BD. -/
def regroupProduct {I J K L : Type} (X : Matrix (I × J) (I × J) ℂ)
    (Y : Matrix (K × L) (K × L) ℂ) : Matrix ((I × K) × (J × L)) ((I × K) × (J × L)) ℂ :=
  fun p q => X (p.1.1, p.2.1) (q.1.1, q.2.1) * Y (p.1.2, p.2.2) (q.1.2, q.2.2)

/-- Full-state tensor-additivity property for a chosen EoF convention. This is a
property, not an unconditional theorem; the source leaves general additivity open. -/
def GlobalEofAdditive (useCountable : Bool) : Prop :=
  ∀ (I J K L : Type) [Countable I] [Countable J] [Countable K] [Countable L]
    [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L]
    (rho : State (I × J)) (sigma : State (K × L)),
    (if useCountable then countableEof (regroupProduct rho.coefficients sigma.coefficients)
      else measureEof (regroupProduct rho.coefficients sigma.coefficients)) =
    (if useCountable then countableEof rho.coefficients else measureEof rho.coefficients) +
    (if useCountable then countableEof sigma.coefficients else measureEof sigma.coefficients)

/-! Sanity examples for the new definitions, without proving source theorems. -/

example {I : Type} (rho : State I) :
    (LabelledEnsemble.average (⟨fun _ => 1, by simp, fun _ => rho⟩ : LabelledEnsemble I 1)) =
      rho.coefficients := by
  simp [LabelledEnsemble.average]

example {I : Type} (e : LabelledEnsemble I 0) : False := by
  have h := e.mass
  simpa using h

example {I : Type} (f : Matrix I I ℂ → ℝ≥0∞) (rho : State I)
    (h : f rho.coefficients = ⊤) : ∀ r : ℝ, (rho, r) ∉ realEpigraph f := by
  intro r
  simp [realEpigraph, h]

example {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (X : Matrix I I ℂ) (mu : GeneralizedEnsemble I) (h : RoofOptimal Phi X mu) :
    IsBarycenter (mu : Measure (State I)) State.coefficients X := h.1

example {I K : Type} (X : Matrix (I × K) (I × K) ℂ) :
    measureEof X = entropyRoof (@traceSecond I K) X := rfl

example {I J K L : Type} (X : Matrix (I × J) (I × J) ℂ)
    (Y : Matrix (K × L) (K × L) ℂ) (i i2 : I) (j j2 : J) (k k2 : K) (l l2 : L) :
    regroupProduct X Y ((i,k),(j,l)) ((i2,k2),(j2,l2)) =
      X (i,j) (i2,j2) * Y (k,l) (k2,l2) := rfl

example (I : Type) :
    ∃ A : BoundedPositiveObservable I,
      A.val = QAlgorithms.Papers.Independent.Claimed50.P13.zeroObservable I := by
  refine ⟨⟨QAlgorithms.Papers.Independent.Claimed50.P13.zeroObservable I, ?_⟩, rfl⟩
  refine ⟨0, le_rfl, ?_⟩
  intro u
  simp [QAlgorithms.Papers.Independent.Claimed50.P13.zeroObservable]

example {I : Type} (X : Matrix I I ℂ) :
    observablePair (0 : Hilbert I →L[ℂ] Hilbert I) X = 0 := by
  simp [observablePair]

example {I K : Type} (X : Matrix (I × K) (I × K) ℂ) :
    localPureCost X 0 = ⊤ := by
  simp [localPureCost]

variable {I J K L : Type}

end QAlgorithms.Papers.Independent.Next46.P42


