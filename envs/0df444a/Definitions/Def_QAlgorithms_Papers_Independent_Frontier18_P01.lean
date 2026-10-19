-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
-- name    : QAlgorithms_Papers_Independent_Frontier18_P01
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:40:11.983055+00:00
-- url     : https://prove2.me/theorems/1743b236-0145-4aff-9224-5bcb1ef65370
-- title:
--   Definitions for Mutual and coherent informations for infinite-dimensional quantum channels
-- statement:
--   The objects the formalized statements of *Mutual and coherent informations for infinite-dimensional quantum channels* (arXiv:1004.2495) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsPositive`: Positive coefficient operators, including zero; source p.5, T_+(H).
--   - `TraceOperatorLE`: Loewner order, also for real multiples with negative coefficients (p.12).
--   - `coordinateCompression`: Finite-coordinate compression; source p.5, Lemma 1.
--   - `finiteEntropy`: Finite-dimensional homogeneous entropy (11), including H(0)=0; p.5.
--   - `finiteRelativeEntropy`: Finite-dimensional Definition 2, including trace correction and support failure (p.5).
--   - `homogeneousEntropy`: Definition 1 via its equivalent compression limit, Lemma 1, p.5. The directed extended supremum permits genuinely infinite entropy.
--   - `generalizedRelativeEntropy`: Definition 2 via Lemma 1, p.5. Valid for arbitrary positive trace-class operators; H(0||B)=Tr B, and nonzero mass outside supp B gives infinity.
--   - `traceSecond`: Trace over the second completed tensor factor; pp.3,6.
--   - `traceFirst`: Trace over the first completed tensor factor; pp.3,6.
--   - `Purifies`: Purification is a pure normalized density operator with prescribed marginal; no phase or purification vector is preselected (p.6, footnote 2).
--   - `Channel`: Genuine CPTP trace-class maps (Definition 3, p.6); values off trace class are irrelevant. The pinned predicate includes complex linearity and all finite matrix amplifications, equivalently complete positivity of the dual.
--   - `mutualInformation`: Definition 4, p.6. Take the extended infimum over all purifications in the canonical reference copy. For every state this set is nonempty (spectral purification (15)); Remark 1 asserts that each of its values, and each value from any other reference space, equals this number. No purification-invariance or entropy identity is assumed in this definition.
--   - `finiteInputCoherentInfo`: Definition 5, p.15. Used only on finite-input-entropy states, where (22) ensures both real conversions are finite. There is no receiver-entropy premise.
--   - `convexOperatorMixture`: Binary convex combination, pp.7,24.
--   - `channelTensorAction`: Tensor product of channel maps, on all blocks of entangled inputs (p.7).
--   - `boundedConjugation`: Conjugation by a bounded map, in completed Hilbert coordinates (pp.3,13). On trace class the nested coefficient series converge; no algebraic tensor product or entrywise multiplication of infinite matrices is used.
--   - `Complementary`: Complementary channels from the SAME isometry, equation (2), pp.3,13. No minimality assumption is imposed.
--   - `operatorKernel`: Kernel in the completed Hilbert space; p.17 support convention.
--   - `SupportWithin`: Closed support inclusion for positive operators is reverse kernel inclusion. Equality is allowed, as in Definition 6 and its p.26 proof.
--   - `PerfectlyReversible`: One decoder recovers ALL states supported on the support code (p.17, Definition 6).
--   - `RankAtMost`: Rank at most k for positive operators, via a sum of k rank-one terms (p.20). This includes infinite-dimensional supports only when they actually have rank ≤ k; Mathlib's default-valued infinite finrank is never used.
--   - `CountableStateEnsemble`: Countable ensembles, allowing finite ensembles by zero weights (p.20 footnote 4). Coefficient barycenters equal trace-norm barycenters since the weights sum to one and every constituent has trace norm one.
--   - `Barycenter`: Prescribed barycenter, with no optimization over different input states (pp.16,20).
--   - `barycentricChi`: The chi function at rho, NOT the chi capacity; p.16, Remark 2.
--   - `RankedEnsemble`: Rank-constrained ensembles of prescribed barycenter, equation (28), p.20.
--   - `mutualApprox`: Equation (28), p.20. The extended supremum has no real unbounded-set default.
--   - `entropyApprox`: Entropy approximators specified after (29), p.21.
--   - `UniformApprox`: Epsilon form of finite-valued uniform convergence from below, p.21 (30). Empty sets impose no condition. The index k is positive eventually.
--   - `deficit`: The approximation deficit, p.21. Subtraction is only by finite I_k for k≥1.
--   - `ensembleDeficit`: Relative-entropy bracket from p.21, with zero-weight components omitted. For positive weights each relative entropy here is finite by domination; the bracket is nonnegative. Thus no infinity-minus-infinity or default real tsum occurs.
--   - `KrausFamily`: Countable Kraus families normalized in the strong operator sense, pp.13,22. The topology defined below is coordinatewise strong, never adjoint-strong.
--   - `countableKrausAction`: The channel generated by a normalized countable Kraus family (p.22).
--   - `posteriorEntropy`: Homogeneous mean posterior entropy, equation (27), p.18.
--   - `normalizedPosteriorEntropy`: The normalized posterior term is zero at zero probability; (27), p.18. No trace-zero operator is called a normalized state.
--   - `OrthogonalRanges`: Orthogonality of entire Kraus ranges, p.18.
--   - `SpectralPresentation`: Spectral representation of a state, pp.10–11. Only positive-mass entries must be unit orthogonal eigenvectors; zero padding includes finite-dimensional and finite-rank states. Putting one nonzero eigenvalue first is always possible.
--   - `spectralTruncation`: Explicit normalized partial spectral sum (18), p.10. Index n means the first n+1 entries, so the denominator is strictly positive even at n=0.
--   - `Hamiltonian`: A semibounded spectral Hamiltonian. For Gibbs-trace Hamiltonians the spectrum is discrete, so choosing its orthonormal eigenbasis loses no generality (p.20). Its operator domain is recorded separately below.
--   - `Hamiltonian.domain`: Dense maximal domain of the spectral self-adjoint observable (p.20). Finite-support vectors belong to it; multiplication by the real energies is therefore a densely defined self-adjoint operator on the completed space.
--   - `Hamiltonian.apply`: The actual self-adjoint spectral observable on its maximal dense domain; coordinate action for the Hamiltonian of Example 1, p.20.
--   - `Hamiltonian.meanEnergy`: Extended mean energy, computed by increasing spectral cutoffs (p.20). The lower-bound shift keeps the series nonnegative, and is added back exactly.
--   - `Hamiltonian.gibbs`: Gibbs trace condition at EVERY positive inverse temperature (p.20).
--   - `Hamiltonian.ball`: The energy ball of p.20, with the original, unshifted threshold.
--   - `binaryEntropy`: Binary entropy including endpoints, Appendix Lemma 6, p.24.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, https://arxiv.org/abs/1004.2495v2

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy

/-!
Holevo–Shirokov, arXiv:1004.2495v2. Natural logarithms throughout.
Countable orthonormal coordinates represent arbitrary complex separable Hilbert spaces;
product coordinates represent the completed Hilbert tensor product. The pinned accepted
P33 library supplies nuclear trace class, normalized states, their trace-norm topology,
and the completely positive trace-preserving channel predicate. No finite-dimensional
restriction is imposed on the system indices. Paper-local generalizations use distinct names from finite-dimensional or unrelated
accepted concepts; exact source comparisons are recorded in ASSESSMENT.json.
Finite compressions below are the directed
limits of source Lemma 1 (p.5), not finite-dimensional replacements for the systems.
All source theorem proofs are deliberately omitted.
-/

noncomputable section

open Filter
open scoped ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

/-- Positive coefficient operators, including zero; source p.5, T_+(H). -/
def IsPositive {I : Type} (X : Matrix I I ℂ) : Prop :=
  ∀ (s : Finset I) (z : I → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).re

/-- Loewner order, also for real multiples with negative coefficients (p.12). -/
def TraceOperatorLE {I : Type} (X Y : Matrix I I ℂ) : Prop := IsPositive (Y - X)

/-- Finite-coordinate compression; source p.5, Lemma 1. -/
def coordinateCompression {I : Type} (s : Finset I) (X : Matrix I I ℂ) : Matrix s s ℂ :=
  fun i j => X i j

/-- Finite-dimensional homogeneous entropy (11), including H(0)=0; p.5. -/
def finiteEntropy {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (-(cfc (fun x : ℝ => x * Real.log x) X).trace.re +
    X.trace.re * Real.log X.trace.re)

/-- Finite-dimensional Definition 2, including trace correction and support failure (p.5). -/
def finiteRelativeEntropy {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) : ℝ≥0∞ :=
  if LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin then
    ENNReal.ofReal ((cfc (fun x : ℝ => x * Real.log x) X -
      X * cfc Real.log Y + Y - X).trace.re)
  else ⊤

/-- Definition 1 via its equivalent compression limit, Lemma 1, p.5.
The directed extended supremum permits genuinely infinite entropy. -/
def homogeneousEntropy {I : Type} (X : Matrix I I ℂ) : ℝ≥0∞ :=
  ⨆ s : Finset I, finiteEntropy (coordinateCompression s X)

/-- Definition 2 via Lemma 1, p.5. Valid for arbitrary positive trace-class
operators; H(0||B)=Tr B, and nonzero mass outside supp B gives infinity. -/
def generalizedRelativeEntropy {I : Type} (X Y : Matrix I I ℂ) : ℝ≥0∞ :=
  ⨆ s : Finset I, finiteRelativeEntropy (coordinateCompression s X) (coordinateCompression s Y)

/-- Trace over the second completed tensor factor; pp.3,6. -/
def traceSecond {I J : Type} (X : Matrix (I × J) (I × J) ℂ) : Matrix I I ℂ :=
  fun i j => ∑' r : J, X (i, r) (j, r)

/-- Trace over the first completed tensor factor; pp.3,6. -/
def traceFirst {I J : Type} (X : Matrix (I × J) (I × J) ℂ) : Matrix J J ℂ :=
  fun i j => ∑' r : I, X (r, i) (r, j)

/-- Purification is a pure normalized density operator with prescribed marginal;
no phase or purification vector is preselected (p.6, footnote 2). -/
def Purifies {I R : Type} (psi : PureState (I × R)) (rho : Matrix I I ℂ) : Prop :=
  traceSecond psi.val.coefficients = rho

/-- Genuine CPTP trace-class maps (Definition 3, p.6); values off trace class
are irrelevant. The pinned predicate includes complex linearity and all finite
matrix amplifications, equivalently complete positivity of the dual. -/
abbrev Channel (I J : Type) :=
  {Phi : Matrix I I ℂ → Matrix J J ℂ // IsTraceClassChannel Phi}

/-- Pointwise trace-norm channel topology, p.7. This uses every input state. -/
instance channelTopology (I J : Type) : TopologicalSpace (Channel I J) :=
  TopologicalSpace.generateFrom {U | ∃ (Phi : Channel I J) (rho : State I) (eps : ℝ),
    0 < eps ∧ U = {Psi | traceSize (Psi.val rho.coefficients - Phi.val rho.coefficients) <
      ENNReal.ofReal eps}}

/-- Definition 4, p.6. Take the extended infimum over all purifications in the
canonical reference copy. For every state this set is nonempty (spectral
purification (15)); Remark 1 asserts that each of its values, and each value
from any other reference space, equals this number. No purification-invariance
or entropy identity is assumed in this definition. -/
def mutualInformation {I J : Type} (rho : Matrix I I ℂ)
    (Phi : Matrix I I ℂ → Matrix J J ℂ) : ℝ≥0∞ :=
  ⨅ psi : {p : PureState (I × I) // Purifies p rho},
    generalizedRelativeEntropy (tensorApply Phi psi.val.val.coefficients)
      (productCoeff (Phi rho) (traceFirst psi.val.val.coefficients))

/-- Definition 5, p.15. Used only on finite-input-entropy states, where (22)
ensures both real conversions are finite. There is no receiver-entropy premise. -/
def finiteInputCoherentInfo {I J : Type} (rho : Matrix I I ℂ)
    (Phi : Matrix I I ℂ → Matrix J J ℂ) : ℝ :=
  (mutualInformation rho Phi).toReal - (homogeneousEntropy rho).toReal

/-- Binary convex combination, pp.7,24. -/
def convexOperatorMixture {I : Type} (t : ℝ) (X Y : Matrix I I ℂ) : Matrix I I ℂ :=
  (t : ℂ) • X + ((1 - t : ℝ) : ℂ) • Y

/-- Tensor product of channel maps, on all blocks of entangled inputs (p.7). -/
def channelTensorAction {I J K L : Type}
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (Psi : Matrix K K ℂ → Matrix L L ℂ)
    (X : Matrix (I × K) (I × K) ℂ) : Matrix (J × L) (J × L) ℂ :=
  fun p q => Psi (fun c d => Phi (fun a b => X (a, c) (b, d)) p.1 q.1) p.2 q.2

/-- Conjugation by a bounded map, in completed Hilbert coordinates (pp.3,13).
On trace class the nested coefficient series converge; no algebraic tensor
product or entrywise multiplication of infinite matrices is used. -/
def boundedConjugation {I J : Type} (V : Hilbert I →L[ℂ] Hilbert J)
    (X : Matrix I I ℂ) : Matrix J J ℂ :=
  fun p q => ∑' i : I, ∑' j : I,
    (V (lp.single 2 i 1)) p * X i j * star ((V (lp.single 2 j 1)) q)

/-- Complementary channels from the SAME isometry, equation (2), pp.3,13.
No minimality assumption is imposed. -/
def Complementary {I J E : Type} (Phi : Channel I J) (Psi : Channel I E) : Prop :=
  ∃ V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E), ∀ rho : State I,
    Phi.val rho.coefficients = traceSecond (boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
    Psi.val rho.coefficients = traceFirst (boundedConjugation V.toContinuousLinearMap rho.coefficients)

/-- Kernel in the completed Hilbert space; p.17 support convention. -/
def operatorKernel {I : Type} (X : Matrix I I ℂ) : Set (Hilbert I) :=
  {u | ∀ i, (∑' j : I, X i j * u j) = 0}

/-- Closed support inclusion for positive operators is reverse kernel inclusion.
Equality is allowed, as in Definition 6 and its p.26 proof. -/
def SupportWithin {I : Type} (X Y : Matrix I I ℂ) : Prop :=
  operatorKernel Y ⊆ operatorKernel X

/-- One decoder recovers ALL states supported on the support code (p.17, Definition 6). -/
def PerfectlyReversible {I J : Type} (rho : State I) (Phi : Channel I J) : Prop :=
  ∃ D : Channel J I, ∀ sigma : State I,
    SupportWithin sigma.coefficients rho.coefficients →
      D.val (Phi.val sigma.coefficients) = sigma.coefficients

/-- Rank at most k for positive operators, via a sum of k rank-one terms (p.20).
This includes infinite-dimensional supports only when they actually have rank ≤ k;
Mathlib's default-valued infinite finrank is never used. -/
def RankAtMost {I : Type} (X : Matrix I I ℂ) (k : ℕ) : Prop :=
  ∃ v : Fin k → Hilbert I, ∀ i j, X i j = ∑ a, v a i * star (v a j)

/-- Countable ensembles, allowing finite ensembles by zero weights (p.20 footnote 4).
Coefficient barycenters equal trace-norm barycenters since the weights sum to one
and every constituent has trace norm one. -/
structure CountableStateEnsemble (I : Type) where
  weight : ℕ → ℝ≥0∞
  weight_sum : (∑' n, weight n) = 1
  state : ℕ → State I

/-- Prescribed barycenter, with no optimization over different input states (pp.16,20). -/
def Barycenter {I : Type} (e : CountableStateEnsemble I) (rho : Matrix I I ℂ) : Prop :=
  ∀ i j, rho i j = ∑' n, ((e.weight n).toReal : ℂ) * (e.state n).coefficients i j

/-- The chi function at rho, NOT the chi capacity; p.16, Remark 2. -/
def barycentricChi {I J : Type} (rho : Matrix I I ℂ)
    (Phi : Matrix I I ℂ → Matrix J J ℂ) : ℝ≥0∞ :=
  ⨆ e : {e : CountableStateEnsemble I // Barycenter e rho},
    ∑' n, e.val.weight n * generalizedRelativeEntropy
      (Phi (e.val.state n).coefficients) (Phi rho)

/-- Rank-constrained ensembles of prescribed barycenter, equation (28), p.20. -/
abbrev RankedEnsemble {I : Type} (rho : Matrix I I ℂ) (k : ℕ) :=
  {e : CountableStateEnsemble I // Barycenter e rho ∧ ∀ n, RankAtMost (e.state n).coefficients k}

/-- Equation (28), p.20. The extended supremum has no real unbounded-set default. -/
def mutualApprox {I J : Type} (k : ℕ) (rho : Matrix I I ℂ)
    (Phi : Matrix I I ℂ → Matrix J J ℂ) : ℝ≥0∞ :=
  ⨆ e : RankedEnsemble rho k, ∑' n, e.val.weight n * mutualInformation (e.val.state n).coefficients Phi

/-- Entropy approximators specified after (29), p.21. -/
def entropyApprox {I : Type} (k : ℕ) (rho : Matrix I I ℂ) : ℝ≥0∞ :=
  ⨆ e : RankedEnsemble rho k, ∑' n, e.val.weight n * homogeneousEntropy (e.val.state n).coefficients

/-- Epsilon form of finite-valued uniform convergence from below, p.21 (30).
Empty sets impose no condition. The index k is positive eventually. -/
def UniformApprox {X : Type} (A : Set X) (f : X → ℝ≥0∞)
    (approx : ℕ → X → ℝ≥0∞) : Prop :=
  (∀ x ∈ A, f x < ⊤) ∧ ∀ eps : ℝ, 0 < eps →
    ∃ K : ℕ, 1 ≤ K ∧ ∀ k ≥ K, ∀ x ∈ A, f x ≤ approx k x + ENNReal.ofReal eps

/-- The approximation deficit, p.21. Subtraction is only by finite I_k for k≥1. -/
def deficit {I J : Type} (k : ℕ) (rho : Matrix I I ℂ)
    (Phi : Matrix I I ℂ → Matrix J J ℂ) : ℝ≥0∞ := mutualInformation rho Phi - mutualApprox k rho Phi

/-- Relative-entropy bracket from p.21, with zero-weight components omitted.
For positive weights each relative entropy here is finite by domination; the
bracket is nonnegative. Thus no infinity-minus-infinity or default real tsum occurs. -/
def ensembleDeficit {I J E : Type} (rho : Matrix I I ℂ)
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (Psi : Matrix I I ℂ → Matrix E E ℂ)
    (e : CountableStateEnsemble I) : ℝ≥0∞ :=
  ∑' n, if e.weight n = 0 then 0 else e.weight n * ENNReal.ofReal
    ((generalizedRelativeEntropy (e.state n).coefficients rho).toReal +
      (generalizedRelativeEntropy (Phi (e.state n).coefficients) (Phi rho)).toReal -
      (generalizedRelativeEntropy (Psi (e.state n).coefficients) (Psi rho)).toReal)

/-- Countable Kraus families normalized in the strong operator sense, pp.13,22.
The topology defined below is coordinatewise strong, never adjoint-strong. -/
abbrev KrausFamily (I J : Type) :=
  {V : ℕ → (Hilbert I →L[ℂ] Hilbert J) //
    ∀ u : Hilbert I, HasSum (fun n => ‖V n u‖ ^ 2) (‖u‖ ^ 2)}

/-- Coordinatewise strong-operator topology, pp.22–24. -/
instance krausTopology (I J : Type) : TopologicalSpace (KrausFamily I J) :=
  TopologicalSpace.induced (fun V => fun n u => V.val n u) inferInstance

/-- The channel generated by a normalized countable Kraus family (p.22). -/
def countableKrausAction {I J : Type} (V : KrausFamily I J) (X : Matrix I I ℂ) : Matrix J J ℂ :=
  fun i j => ∑' n, boundedConjugation (V.val n) X i j

/-- Homogeneous mean posterior entropy, equation (27), p.18. -/
def posteriorEntropy {I J : Type} (rho : Matrix I I ℂ) (V : KrausFamily I J) : ℝ≥0∞ :=
  ∑' n, homogeneousEntropy (boundedConjugation (V.val n) rho)

/-- The normalized posterior term is zero at zero probability; (27), p.18.
No trace-zero operator is called a normalized state. -/
def normalizedPosteriorEntropy {I J : Type} (rho : Matrix I I ℂ)
    (V : KrausFamily I J) : ℝ≥0∞ :=
  ∑' n, let X := boundedConjugation (V.val n) rho
    let p := ∑' i : J, (X i i).re
    if p = 0 then 0 else ENNReal.ofReal p * homogeneousEntropy ((p⁻¹ : ℂ) • X)

/-- Orthogonality of entire Kraus ranges, p.18. -/
def OrthogonalRanges {I J : Type} (V : KrausFamily I J) : Prop :=
  ∀ m n, m ≠ n → ∀ u v : Hilbert I, inner ℂ (V.val m u) (V.val n v) = 0

/-- Spectral representation of a state, pp.10–11. Only positive-mass entries
must be unit orthogonal eigenvectors; zero padding includes finite-dimensional
and finite-rank states. Putting one nonzero eigenvalue first is always possible. -/
structure SpectralPresentation {I : Type} (rho : State I) where
  weight : ℕ → ℝ
  vector : ℕ → Hilbert I
  nonnegative : ∀ n, 0 ≤ weight n
  summable : Summable weight
  mass : (∑' n, weight n) = 1
  first_positive : 0 < weight 0
  normalized : ∀ n, 0 < weight n → ‖vector n‖ = 1
  orthogonal : ∀ m n, m ≠ n → 0 < weight m → 0 < weight n →
    inner ℂ (vector m) (vector n) = 0
  coefficients : ∀ i j, rho.coefficients i j =
    ∑' n, (weight n : ℂ) * vector n i * star (vector n j)

/-- Explicit normalized partial spectral sum (18), p.10. Index n means the
first n+1 entries, so the denominator is strictly positive even at n=0. -/
def spectralTruncation {I : Type} {rho : State I} (s : SpectralPresentation rho)
    (n : ℕ) : Matrix I I ℂ :=
  ((∑ a ∈ Finset.range (n + 1), s.weight a)⁻¹ : ℂ) •
    (fun i j => ∑ a ∈ Finset.range (n + 1),
      (s.weight a : ℂ) * s.vector a i * star (s.vector a j))

/-- A semibounded spectral Hamiltonian. For Gibbs-trace Hamiltonians the
spectrum is discrete, so choosing its orthonormal eigenbasis loses no generality
(p.20). Its operator domain is recorded separately below. -/
structure Hamiltonian (I : Type) where
  energy : I → ℝ
  lower : ℝ
  bounded_below : ∀ i, lower ≤ energy i

/-- Dense maximal domain of the spectral self-adjoint observable (p.20).
Finite-support vectors belong to it; multiplication by the real energies is
therefore a densely defined self-adjoint operator on the completed space. -/
def Hamiltonian.domain {I : Type} (H : Hamiltonian I) : Set (Hilbert I) :=
  {u | Memℓp (fun i => (H.energy i : ℂ) * u i) 2}

/-- The actual self-adjoint spectral observable on its maximal dense domain;
coordinate action for the Hamiltonian of Example 1, p.20. -/
def Hamiltonian.apply {I : Type} (H : Hamiltonian I) (u : H.domain) : Hilbert I :=
  ⟨fun i => (H.energy i : ℂ) * u.val i, u.property⟩

/-- Extended mean energy, computed by increasing spectral cutoffs (p.20).
The lower-bound shift keeps the series nonnegative, and is added back exactly. -/
def Hamiltonian.meanEnergy {I : Type} (H : Hamiltonian I) (rho : State I) : EReal :=
  (H.lower : EReal) + ((∑' i, ENNReal.ofReal
    ((H.energy i - H.lower) * (rho.coefficients i i).re)) : ℝ≥0∞).toEReal

/-- Gibbs trace condition at EVERY positive inverse temperature (p.20). -/
def Hamiltonian.gibbs {I : Type} (H : Hamiltonian I) : Prop :=
  ∀ beta : ℝ, 0 < beta → (∑' i, ENNReal.ofReal (Real.exp (-beta * H.energy i))) < ⊤

/-- The energy ball of p.20, with the original, unshifted threshold. -/
def Hamiltonian.ball {I : Type} (H : Hamiltonian I) (h : ℝ) : Set (State I) :=
  {rho | H.meanEnergy rho ≤ (h : EReal)}

/-- Binary entropy including endpoints, Appendix Lemma 6, p.24. -/
def binaryEntropy (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (-t * Real.log t - (1 - t) * Real.log (1 - t))

/-! Definition sanity checks. The source results themselves remain unproved. -/

example {I : Type} : IsPositive (0 : Matrix I I ℂ) := by
  intro s z
  simp

example {I J : Type} :
    traceSecond (0 : Matrix (I × J) (I × J) ℂ) = 0 := by
  funext i j
  simp [traceSecond]

example {I : Type} (X : Matrix I I ℂ) : convexOperatorMixture 0 X X = X := by
  simp [convexOperatorMixture]

example {I : Type} (X : Matrix I I ℂ) : SupportWithin X X := Set.Subset.rfl

example : binaryEntropy 0 = 0 ∧ binaryEntropy 1 = 0 := by
  simp [binaryEntropy]

example {I : Type} : RankAtMost (0 : Matrix I I ℂ) 0 := by
  refine ⟨fun _ => 0, ?_⟩
  intro i j
  simp

example : finiteEntropy (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
  simp [finiteEntropy, cfc_one]

example : finiteRelativeEntropy (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 = 0 := by
  simp [finiteRelativeEntropy, cfc_one]

example {I J : Type} (V : Hilbert I →L[ℂ] Hilbert J) :
    boundedConjugation V (0 : Matrix I I ℂ) = 0 := by
  funext i j
  simp [boundedConjugation]

example {I : Type} (H : Hamiltonian I) (u : H.domain) (i : I) :
    H.apply u i = (H.energy i : ℂ) * u.val i := rfl

example {X : Type} (f : X → ℝ≥0∞) (approx : ℕ → X → ℝ≥0∞) :
    UniformApprox (∅ : Set X) f approx := by
  constructor
  · simp
  · intro eps heps
    exact ⟨1, le_rfl, by simp⟩

variable {I J K L E R : Type}

end QAlgorithms.Papers.Independent.Frontier18.P01


