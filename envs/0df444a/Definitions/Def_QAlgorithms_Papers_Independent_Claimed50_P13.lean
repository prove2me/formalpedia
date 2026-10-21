-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13
-- name    : QAlgorithms_Papers_Independent_Claimed50_P13
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T09:25:30.78581+00:00
-- url     : https://prove2.me/theorems/6c1847db-1c18-49dc-b151-53df292acb79
-- title:
--   Definitions for On the entanglement-assisted classical capacity of infinite-dimensional quantum channels
-- statement:
--   The objects the formalized statements of *On the entanglement-assisted classical capacity of infinite-dimensional quantum channels* (arXiv:1210.6926) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PositiveObservable`: PDF pp.2,4: the densely defined closed nonnegative quadratic form of F. Infinity denotes vectors outside the form domain dom(sqrt F). The closed-form representation theorem identifies these with the source's positive self-adjoint operators, including continuous spectrum.
--   - `zeroObservable`: The zero observable, PDF p.4.
--   - `closedFormExpectation`: PDF p.4: extended Tr(rho F). The closed-form trace formula is the supremum over finite rank-one suboperators of rho. It equals the spectral-cutoff formula also when F has continuous spectrum. The empty family is permitted.
--   - `feasibleStates`: PDF p.4: input constraint, allowing an empty feasible set.
--   - `FiniteEntropyConstraint`: Section 4 assumption (28), PDF p.12.
--   - `GibbsCondition`: PDF pp.15,17: Gibbs trace finite at every positive inverse temperature. Exactly in this regime a discrete spectral representation exists. This condition is not imposed on Theorem 1 or lower semicontinuity.
--   - `FiniteLaw`: PDF pp.4,6: finite probability alphabet, necessarily nonempty.
--   - `finiteAverage`: PDF pp.4,6: average coefficients; all signal uses below are density operators.
--   - `finiteHolevo`: First relative-entropy formula for finite chi, PDF p.4.
--   - `TensorBlockIndex`: Completed n-fold tensor register; n=0 has dimension one.
--   - `blockAction`: PDF pp.4--6: tensor powers, keeping all entangled input blocks.
--   - `blockEnergy`: PDF p.4, (5): expectation of the SUM of the n single-use observables.
--   - `AssistedProtocol`: PDF p.6, (11): one fixed pure shared state and message-dependent encoding channels. The unrestricted countable reference includes every separable reference by isometric embedding. No finite-dimensional reference cutoff is imposed.
--   - `AssistedProtocol.signal`: PDF p.6: signals constructed from the shared state and encoders.
--   - `assistedBlockCapacity`: PDF p.6, (13): average-message energy constraint only; the signal states need not individually satisfy the energy bound.
--   - `operationalAssistedCapacity`: PDF p.6, (12): regularized protocol capacity, independent of formula (14). The source establishes existence of the limit, so liminf gives its value. Empty protocol suprema give zero; n=0 does not affect the limit.
--   - `unconstrainedAssistedCapacity`: PDF p.7: independently regularized unconstrained protocols.
--   - `informationSupremum`: Right side of (14), PDF p.7: extended supremum, zero on the empty set.
--   - `chiCapacity`: PDF p.4: single-use constrained chi capacity over finite ensembles.
--   - `regularizedUnassistedCapacity`: PDF p.5: classical capacity via its separately given regularization.
--   - `pureReplacer`: PDF p.13: pure-replacer complement of the noiseless channel.
--   - `diagonalWeight`: PDF p.14, (32): vector expectation in the channel's classical basis.
--   - `DiscreteCQRepresentation`: PDF p.14, (32): discrete c-q representation in a COMPLETE basis. Repeated output states and one-dimensional input spaces are permitted.
--   - `IsDiscreteCQ`: PDF pp.14--16: c-q of discrete type, not merely c-q.
--   - `stateSupport`: PDF p.15: closed support is the orthogonal complement of the kernel.
--   - `DiscreteCQOnSupport`: PDF p.15: restriction to the CONSTRUCTED support, including lines.
--   - `FormDiagonal`: PDF p.16: F diagonal in the SAME basis as (32).
--   - `HasFiniteKrausRepresentation`: PDF p.15: finite Kraus rank; the Hilbert spaces remain unrestricted.
--   - `OutputEntropyCondition`: PDF p.17, condition 1, finite-entropy reading used by the p.19 proof. Printed: entropy limit has no explicit finiteness qualifier. Changed: finite limit entropy, since extended continuity at constant infinity is insufficient. Every feasible state sequence and its separate feasible limit are quantified. Independent correction review pending.
--   - `Subnormalized`: PDF p.20: T_1(H), including zero.
--   - `subnormalizedAverage`: PDF p.20: barycenter coefficients; integrands on T_1(H) are bounded.
--   - `subnormalizedHolevo`: PDF pp.20--21: extended relative entropy includes the correction Tr(B-A).
--   - `subnormalizedS`: PDF p.20: S(A)=-Tr A log A, distinguished from homogeneous H(A). For trace in [0,1] the added term is nonnegative; its zero endpoint is zero.
--   - `TraceDecreasingOperation`: PDF p.21: complex-linear CP trace-nonincreasing maps on the FULL trace class.
--   - `crossConjugation`: PDF p.18: V rho W*, retaining the complement's off-diagonal entries.
--   - `krausComplementAction`: PDF p.18: complementary output on the countable Kraus index space.
--   - `ComplementaryMaps`: PDF pp.3,18: two partial traces of one and the SAME isometry.
--   - `ExhaustingProjections`: PDF p.21: increasing finite-rank orthogonal projections exhausting the output.
--   - `compressedAction`: PDF p.21: trace-decreasing compression, without a replacer term.
--   - `compressedComplement`: PDF p.21, (38): complement using the SAME compressed dilation. Positive two-sided compression equals the printed one-sided partial-trace formula.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, https://arxiv.org/abs/1210.6926v2

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

/-!
Holevo--Shirokov, arXiv:1210.6926v2. Natural logarithms and extended capacities.
Countable nonempty orthonormal coordinates model nonzero separable systems.
Local positive observables are closed quadratic forms, allowing continuous spectrum.
Assisted capacity is independently defined by block protocols (11)--(13).
Six source/interface deferrals are documented in the assigned unit's HARD/GAPS.
Draft stage only: compilation and independent moderation remain pending.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

/-! Accepted-library comparison for the repair: identically spelled names do not
identify the same mathematical objects. Frontier18.P01.Hamiltonian.meanEnergy
uses a diagonal spectral Hamiltonian; closedFormExpectation below also permits
continuous spectrum. Information100.P59/P62.Block are respectively a Bloch matrix
and finite algebra labels, whereas TensorBlockIndex labels tensor powers.
Information100.P62.assistedCapacity/classicalCapacity are finite-dimensional
zero-error capacities in bits, not the natural-log regularized constrained rates
here. These distinct concepts therefore keep distinct paper-local names.
Frontier30.P14.Operation is reused as the ambient map type of the CP
trace-nonincreasing subtype TraceDecreasingOperation. No frozen body is edited.
The complete countable bases below are HilbertBasis, with no Fintype premise. -/

namespace MI

export QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel mutualInformation homogeneousEntropy generalizedRelativeEntropy traceFirst traceSecond
   boundedConjugation channelTensorAction Complementary operatorKernel SupportWithin
   KrausFamily countableKrausAction finiteInputCoherentInfo)

end MI

namespace Ens

export QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients HasAverage HasFiniteSupport constrainedEnsembles
   ensembleHolevo finiteEnsembleCapacity stateChi IsCapacityAttaining pureStates)

end Ens

namespace Op

export QAlgorithms.Papers.Independent.Frontier18.P08
  (PositiveTraceClass operatorTrace IsQuantumOperation StronglyConverges)

end Op

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2,4: the densely defined closed nonnegative quadratic form of F.
Infinity denotes vectors outside the form domain dom(sqrt F). The closed-form
representation theorem identifies these with the source's positive self-adjoint
operators, including continuous spectrum. -/
structure PositiveObservable (I : Type) where
  form : Hilbert I → ℝ≥0∞
  zero : form 0 = 0
  homogeneous : ∀ (c : ℂ) u, form (c • u) = ENNReal.ofReal (‖c‖ ^ 2) * form u
  parallelogram : ∀ u v, form (u + v) + form (u - v) = 2 * form u + 2 * form v
  closed : LowerSemicontinuous form
  dense : Dense {u | form u < ⊤}

/-- The zero observable, PDF p.4. -/
def zeroObservable (I : Type) : PositiveObservable I where
  form := fun _ => 0
  zero := rfl
  homogeneous := by intros; simp
  parallelogram := by intros; simp
  closed := lowerSemicontinuous_const
  dense := by simpa using (dense_univ : Dense (Set.univ : Set (Hilbert I)))

/-- PDF p.4: extended Tr(rho F). The closed-form trace formula is the supremum
over finite rank-one suboperators of rho. It equals the spectral-cutoff formula
also when F has continuous spectrum. The empty family is permitted. -/
def closedFormExpectation {I : Type} (F : PositiveObservable I) (rho : Matrix I I ℂ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ u : {v : Fin n → Hilbert I //
    QAlgorithms.Papers.Independent.Frontier18.P01.IsPositive
      (rho - ∑ k, rankOne (v k))}, ∑ k, F.form (u.val k)

/-- PDF p.4: input constraint, allowing an empty feasible set. -/
def feasibleStates {I : Type} (F : PositiveObservable I) (E : ℝ) : Set (State I) :=
  {rho | closedFormExpectation F rho.coefficients ≤ ENNReal.ofReal E}

/-- Section 4 assumption (28), PDF p.12. -/
def FiniteEntropyConstraint {I : Type} (F : PositiveObservable I) (E : ℝ) : Prop :=
  ∀ rho ∈ feasibleStates F E, MI.homogeneousEntropy rho.coefficients < ⊤

/-- PDF pp.15,17: Gibbs trace finite at every positive inverse temperature.
Exactly in this regime a discrete spectral representation exists. This
condition is not imposed on Theorem 1 or lower semicontinuity. -/
def GibbsCondition {I : Type} (F : PositiveObservable I) : Prop :=
  ∃ (b : HilbertBasis I ℂ (Hilbert I)) (energy : I → ℝ),
    (∀ k, 0 ≤ energy k) ∧
    (∀ u, F.form u = ∑' k, ENNReal.ofReal (energy k * ‖inner ℂ (b k) u‖ ^ 2)) ∧
    ∀ beta : ℝ, 0 < beta → (∑' k, ENNReal.ofReal (Real.exp (-beta * energy k))) < ⊤

/-- PDF pp.4,6: finite probability alphabet, necessarily nonempty. -/
structure FiniteLaw (m : ℕ) where
  weight : Fin m → ℝ≥0∞
  mass : ∑ i, weight i = 1

/-- PDF pp.4,6: average coefficients; all signal uses below are density operators. -/
def finiteAverage {I : Type} {m : ℕ} (p : FiniteLaw m)
    (signal : Fin m → Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ i, ((p.weight i).toReal : ℂ) • signal i

/-- First relative-entropy formula for finite chi, PDF p.4. -/
def finiteHolevo {I J : Type} {m : ℕ} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (p : FiniteLaw m) (signal : Fin m → Matrix I I ℂ) : ℝ≥0∞ :=
  ∑ i, p.weight i * MI.generalizedRelativeEntropy
    (Phi (signal i)) (Phi (finiteAverage p signal))

/-- Completed n-fold tensor register; n=0 has dimension one. -/
def TensorBlockIndex (I : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => I × TensorBlockIndex I n

/-- PDF pp.4--6: tensor powers, keeping all entangled input blocks. -/
def blockAction {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) :
    (n : ℕ) → Matrix (TensorBlockIndex I n) (TensorBlockIndex I n) ℂ → Matrix (TensorBlockIndex J n) (TensorBlockIndex J n) ℂ
  | 0 => id
  | n + 1 => MI.channelTensorAction Phi (blockAction Phi n)

/-- PDF p.4, (5): expectation of the SUM of the n single-use observables. -/
def blockEnergy {I : Type} (F : PositiveObservable I) :
    (n : ℕ) → Matrix (TensorBlockIndex I n) (TensorBlockIndex I n) ℂ → ℝ≥0∞
  | 0, _ => 0
  | n + 1, rho => closedFormExpectation F (MI.traceSecond rho) + blockEnergy F n (MI.traceFirst rho)

/-- PDF p.6, (11): one fixed pure shared state and message-dependent encoding
channels. The unrestricted countable reference includes every separable reference
by isometric embedding. No finite-dimensional reference cutoff is imposed. -/
structure AssistedProtocol (I : Type) (n m : ℕ) where
  law : FiniteLaw m
  shared : PureState (TensorBlockIndex I n × ℕ)
  encode : Fin m → MI.Channel (TensorBlockIndex I n) (TensorBlockIndex I n)

/-- PDF p.6: signals constructed from the shared state and encoders. -/
def AssistedProtocol.signal {I : Type} {n m : ℕ} (p : AssistedProtocol I n m)
    (i : Fin m) : Matrix (TensorBlockIndex I n × ℕ) (TensorBlockIndex I n × ℕ) ℂ :=
  tensorApply (p.encode i).val p.shared.val.coefficients

/-- PDF p.6, (13): average-message energy constraint only; the signal states
need not individually satisfy the energy bound. -/
def assistedBlockCapacity {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (F : PositiveObservable I) (E : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨆ m : ℕ, ⨆ p : {p : AssistedProtocol I n m //
    blockEnergy F n (MI.traceSecond (finiteAverage p.law p.signal)) ≤
      (n : ℝ≥0∞) * ENNReal.ofReal E},
    finiteHolevo (tensorApply (blockAction Phi n)) p.val.law p.val.signal

/-- PDF p.6, (12): regularized protocol capacity, independent of formula (14).
The source establishes existence of the limit, so liminf gives its value.
Empty protocol suprema give zero; n=0 does not affect the limit. -/
def operationalAssistedCapacity {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (F : PositiveObservable I) (E : ℝ) : ℝ≥0∞ :=
  Filter.liminf (fun n : ℕ => (n : ℝ≥0∞)⁻¹ * assistedBlockCapacity Phi F E n) atTop

/-- PDF p.7: independently regularized unconstrained protocols. -/
def unconstrainedAssistedCapacity {I J : Type}
    (Phi : Matrix I I ℂ → Matrix J J ℂ) : ℝ≥0∞ :=
  Filter.liminf (fun n : ℕ => (n : ℝ≥0∞)⁻¹ *
    (⨆ m : ℕ, ⨆ p : AssistedProtocol I n m,
      finiteHolevo (tensorApply (blockAction Phi n)) p.law p.signal)) atTop

/-- Right side of (14), PDF p.7: extended supremum, zero on the empty set. -/
def informationSupremum {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (F : PositiveObservable I) (E : ℝ) : ℝ≥0∞ :=
  ⨆ rho : {rho : State I // rho ∈ feasibleStates F E},
    MI.mutualInformation rho.val.coefficients Phi

/-- PDF p.4: single-use constrained chi capacity over finite ensembles. -/
def chiCapacity {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (F : PositiveObservable I) (E : ℝ) : ℝ≥0∞ :=
  Ens.finiteEnsembleCapacity Phi (feasibleStates F E)

/-- PDF p.5: classical capacity via its separately given regularization. -/
def regularizedUnassistedCapacity {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (F : PositiveObservable I) (E : ℝ) : ℝ≥0∞ :=
  Filter.liminf (fun n : ℕ => (n : ℝ≥0∞)⁻¹ *
    Ens.finiteEnsembleCapacity (blockAction Phi n)
      {rho | blockEnergy F n rho.coefficients ≤ (n : ℝ≥0∞) * ENNReal.ofReal E}) atTop

/-- PDF p.13: pure-replacer complement of the noiseless channel. -/
def pureReplacer {I : Type} (tau : PureState Unit) (rho : Matrix I I ℂ) :
    Matrix Unit Unit ℂ := (∑' i, rho i i) • tau.val.coefficients

/-- PDF p.14, (32): vector expectation in the channel's classical basis. -/
def diagonalWeight {I : Type} (rho : Matrix I I ℂ) (u : Hilbert I) : ℝ :=
  (∑' i, ∑' j, star (u i) * rho i j * u j).re

/-- PDF p.14, (32): discrete c-q representation in a COMPLETE basis.
Repeated output states and one-dimensional input spaces are permitted. -/
def DiscreteCQRepresentation {I J : Type}
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (b : HilbertBasis I ℂ (Hilbert I)) : Prop :=
  ∃ sigma : I → State J, ∀ rho : State I, ∀ i j,
    Phi rho.coefficients i j = ∑' k,
      (diagonalWeight rho.coefficients (b k) : ℂ) * (sigma k).coefficients i j

/-- PDF pp.14--16: c-q of discrete type, not merely c-q. -/
def IsDiscreteCQ {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) : Prop :=
  ∃ b : HilbertBasis I ℂ (Hilbert I), DiscreteCQRepresentation Phi b

/-- PDF p.15: closed support is the orthogonal complement of the kernel. -/
def stateSupport {I : Type} (rho : Matrix I I ℂ) : Set (Hilbert I) :=
  {u | ∀ v ∈ MI.operatorKernel rho, inner ℂ v u = 0}

/-- PDF p.15: restriction to the CONSTRUCTED support, including lines. -/
def DiscreteCQOnSupport {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (rho : Matrix I I ℂ) : Prop :=
  ∃ (K : Type) (_ : Countable K) (_ : Nonempty K)
    (U : Hilbert K →ₗᵢ[ℂ] Hilbert I),
    Set.range U = stateSupport rho ∧
      IsDiscreteCQ (fun X => Phi (MI.boundedConjugation U.toContinuousLinearMap X))

/-- PDF p.16: F diagonal in the SAME basis as (32). -/
def FormDiagonal {I : Type} (F : PositiveObservable I)
    (b : HilbertBasis I ℂ (Hilbert I)) : Prop :=
  ∃ energy : I → ℝ≥0, ∀ u,
    F.form u = ∑' k, (energy k : ℝ≥0∞) * ENNReal.ofReal (‖inner ℂ (b k) u‖ ^ 2)

/-- PDF p.15: finite Kraus rank; the Hilbert spaces remain unrestricted. -/
def HasFiniteKrausRepresentation {I J : Type}
    (Phi : Matrix I I ℂ → Matrix J J ℂ) : Prop :=
  ∃ V : MI.KrausFamily I J, ∃ N : ℕ,
    (∀ k ≥ N, V.val k = 0) ∧ ∀ rho : State I,
      Phi rho.coefficients = MI.countableKrausAction V rho.coefficients

/-- PDF p.17, condition 1, finite-entropy reading used by the p.19 proof.
Printed: entropy limit has no explicit finiteness qualifier. Changed: finite
limit entropy, since extended continuity at constant infinity is insufficient.
Every feasible state sequence and its separate feasible limit are quantified.
Independent correction review pending. -/
def OutputEntropyCondition {I J : Type}
    (Phi : ℕ → MI.Channel I J) (Phi0 : MI.Channel I J)
    (F : PositiveObservable I) (E : ℝ) : Prop :=
  ∀ (rho : ℕ → State I) (rho0 : State I),
    (∀ n, rho n ∈ feasibleStates F E) → rho0 ∈ feasibleStates F E →
    Tendsto rho atTop (𝓝 rho0) →
    MI.homogeneousEntropy (Phi0.val rho0.coefficients) < ⊤ ∧
    Tendsto (fun n => MI.homogeneousEntropy ((Phi n).val (rho n).coefficients))
      atTop (𝓝 (MI.homogeneousEntropy (Phi0.val rho0.coefficients)))

/-- PDF p.20: T_1(H), including zero. -/
abbrev Subnormalized (I : Type) :=
  {X : Matrix I I ℂ // Op.PositiveTraceClass X ∧ Op.operatorTrace X ≤ 1}

/-- PDF p.20: trace-norm, not entrywise, topology. -/
instance subnormalizedTopology (I : Type) : TopologicalSpace (Subnormalized I) :=
  TopologicalSpace.generateFrom {U | ∃ (X : Subnormalized I) (eps : ℝ),
    0 < eps ∧ U = {Y | traceSize (Y.val - X.val) < ENNReal.ofReal eps}}

instance subnormalizedMeasurableSpace (I : Type) : MeasurableSpace (Subnormalized I) :=
  borel (Subnormalized I)

instance subnormalizedBorelSpace (I : Type) : BorelSpace (Subnormalized I) := ⟨rfl⟩

/-- PDF p.20: barycenter coefficients; integrands on T_1(H) are bounded. -/
def subnormalizedAverage {I : Type} (mu : ProbabilityMeasure (Subnormalized I)) :
    Matrix I I ℂ := fun i j => ∫ X, X.val i j ∂(mu : Measure (Subnormalized I))

/-- PDF pp.20--21: extended relative entropy includes the correction Tr(B-A). -/
def subnormalizedHolevo {I : Type} (mu : ProbabilityMeasure (Subnormalized I)) : ℝ≥0∞ :=
  ∫⁻ X, MI.generalizedRelativeEntropy X.val (subnormalizedAverage mu)
    ∂(mu : Measure (Subnormalized I))

/-- PDF p.20: S(A)=-Tr A log A, distinguished from homogeneous H(A).
For trace in [0,1] the added term is nonnegative; its zero endpoint is zero. -/
def subnormalizedS {I : Type} (A : Matrix I I ℂ) : ℝ≥0∞ :=
  MI.homogeneousEntropy A + ENNReal.ofReal (-Op.operatorTrace A * Real.log (Op.operatorTrace A))

/-- PDF p.21: complex-linear CP trace-nonincreasing maps on the FULL trace class. -/
abbrev TraceDecreasingOperation (I J : Type) :=
  {Phi : QAlgorithms.Papers.Independent.Frontier30.P14.Operation I J //
    Op.IsQuantumOperation Phi}

/-- PDF p.21: strong operation topology uses trace norm at every input state. -/
instance operationTopology (I J : Type) : TopologicalSpace (TraceDecreasingOperation I J) :=
  TopologicalSpace.generateFrom {U | ∃ (Phi : TraceDecreasingOperation I J) (rho : State I) (eps : ℝ),
    0 < eps ∧ U = {Psi | traceSize (Psi.val rho.coefficients - Phi.val rho.coefficients) <
      ENNReal.ofReal eps}}

/-- PDF p.18: V rho W*, retaining the complement's off-diagonal entries. -/
def crossConjugation {I J : Type} (V W : Hilbert I →L[ℂ] Hilbert J)
    (X : Matrix I I ℂ) : Matrix J J ℂ :=
  fun p q => ∑' i, ∑' j, (V (lp.single 2 i 1)) p * X i j * star ((W (lp.single 2 j 1)) q)

/-- PDF p.18: complementary output on the countable Kraus index space. -/
def krausComplementAction {I J : Type} (V : MI.KrausFamily I J)
    (X : Matrix I I ℂ) : Matrix ℕ ℕ ℂ :=
  fun i j => ∑' a, crossConjugation (V.val i) (V.val j) X a a

/-- PDF pp.3,18: two partial traces of one and the SAME isometry. -/
def ComplementaryMaps {I J K : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (Psi : Matrix I I ℂ → Matrix K K ℂ) : Prop :=
  ∃ V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × K), ∀ rho : State I,
    Phi rho.coefficients = MI.traceSecond (MI.boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
    Psi rho.coefficients = MI.traceFirst (MI.boundedConjugation V.toContinuousLinearMap rho.coefficients)

/-- PDF p.21: increasing finite-rank orthogonal projections exhausting the output. -/
structure ExhaustingProjections (J : Type) where
  proj : ℕ → (Hilbert J →L[ℂ] Hilbert J)
  idempotent : ∀ n u, proj n (proj n u) = proj n u
  selfAdjoint : ∀ n u v, inner ℂ (proj n u) v = inner ℂ u (proj n v)
  finiteRank : ∀ n, FiniteDimensional ℂ (LinearMap.range (proj n).toLinearMap)
  increasing : ∀ n m, n ≤ m → ∀ u, proj m (proj n u) = proj n u
  exhaustive : ∀ u, Tendsto (fun n => proj n u) atTop (𝓝 u)

/-- PDF p.21: trace-decreasing compression, without a replacer term. -/
def compressedAction {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (P : Hilbert J →L[ℂ] Hilbert J) (X : Matrix I I ℂ) : Matrix J J ℂ :=
  MI.boundedConjugation P (Phi X)

/-- PDF p.21, (38): complement using the SAME compressed dilation. Positive
two-sided compression equals the printed one-sided partial-trace formula. -/
def compressedComplement {I J K : Type} (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × K))
    (P : Hilbert J →L[ℂ] Hilbert J) (X : Matrix I I ℂ) : Matrix K K ℂ :=
  MI.traceFirst (tensorApply (MI.boundedConjugation P)
    (MI.boundedConjugation V.toContinuousLinearMap X))

/-! Sanity examples for local interfaces; paper theorem proofs are omitted. -/

example {I : Type} (rho : Matrix I I ℂ) : closedFormExpectation (zeroObservable I) rho = 0 := by
  simp [closedFormExpectation, zeroObservable]

example {I : Type} (F : PositiveObservable I) (X : Matrix Unit Unit ℂ) :
    blockEnergy F 0 X = 0 := rfl

example {I : Type} (F : PositiveObservable I) (E : ℝ) (rho : State I) :
    rho ∈ feasibleStates F E ↔ closedFormExpectation F rho.coefficients ≤ ENNReal.ofReal E := Iff.rfl

example {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) :
    blockAction Phi 0 = id := rfl

example {I : Type} (rho : Matrix I I ℂ) (u : Hilbert I) :
    u ∈ stateSupport rho ↔ ∀ v ∈ MI.operatorKernel rho, inner ℂ v u = 0 := Iff.rfl

example {I : Type} : subnormalizedS (0 : Matrix I I ℂ) = 0 := by
  have hcompression (s : Finset I) :
      QAlgorithms.Papers.Independent.Frontier18.P01.coordinateCompression s
        (0 : Matrix I I ℂ) = 0 := rfl
  have hentropy : MI.homogeneousEntropy (0 : Matrix I I ℂ) = 0 := by
    simp only [QAlgorithms.Papers.Independent.Frontier18.P01.homogeneousEntropy,
      hcompression]
    simp [QAlgorithms.Papers.Independent.Frontier18.P01.finiteEntropy]
  simp [subnormalizedS, hentropy, Op.operatorTrace]

end QAlgorithms.Papers.Independent.Claimed50.P13


