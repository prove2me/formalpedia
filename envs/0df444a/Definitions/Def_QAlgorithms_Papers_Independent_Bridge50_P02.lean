-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P02
-- name    : QAlgorithms_Papers_Independent_Bridge50_P02
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T11:38:22.425+00:00
-- url     : https://prove2.me/theorems/683e2204-0d00-49f8-99ee-63f18071138a
-- title:
--   Definitions for Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more
-- statement:
--   The objects the formalized statements of *Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more* (arXiv:1510.04682) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `finitePairRelativeEntropyNats`: PDF p.6, (2.4): positive Umegaki entropy in nats, converting the accepted nonpositive relative-entropy convention. Used only with support inclusion.
--   - `pairInformationVarianceNats`: PDF p.6, (2.5): PAIR information variance, in nats squared. Distinct from the accepted single-density spectral informationVariance in bits squared.
--   - `realPetzLogOverlap`: PDF pp.6,9: real analytic representative of the Petz logarithm. Kernel powers vanish; all uses have common support or support inclusion near s=1.
--   - `optimalTestingExponentNats`: PDF pp.8--10: testing exponent in natural logarithms, on the stated valid inputs.
--   - `symmetricError`: PDF p.12, (3.9): infimum of the SUM of the errors, with no prior factor 1/2.
--   - `spectralIntegral`: PDF p.7, (2.11): integration against the FINITE spectral measure of -log Delta in Omega_B. Its mass is Tr B, with no implicit normalization.
--   - `spectralTail`: PDF p.13, (3.13): finite spectral mass of (-infinity,nu].
--   - `modularLowProjector`: PDF p.14: spectral projector of Delta_(rho|sigma) on the STRICT interval [0,L).
--   - `eigenvalueSet`: PDF p.13: distinct eigenvalues, for the explicit spectral-sum identity.
--   - `eigenprojector`: PDF p.5: spectral projection of a Hermitian matrix at lambda.
--   - `TestingSequence`: PDF pp.8--9: a pair of finite spaces at each positive sequence index. No density, support, or analytic conclusions are built into this data structure.
--   - `StatePairs`: PDF pp.5--9: nonzero spaces, trace-one PSD pairs, and finite relative entropy domain.
--   - `FaithfulPairs`: PDF pp.6--9: the standing faithful-state restriction.
--   - `AnalyticCumulants`: PDF pp.9,11: analytic extensions of real log-Laplace germs, a common disc, finite pointwise real limits, and one bound uniform in the index and the whole disc. No variance limit or central limit theorem is assumed here.
--   - `ConditionOne`: PDF pp.8--9, Condition 1, with nondecreasing positive divergent weights. Repeated weights are permitted. The support-inclusion version is used in Remark 1.
--   - `relativeEntropyRate`: PDF p.9, (3.1): constructed limit, rather than a free entropy-rate parameter. The rates-exist theorem establishes that this topological limit exists under Condition 1.
--   - `varianceRate`: PDF p.9, (3.2): constructed variance-rate limit; its value may be zero.
--   - `relativeEntropyCorrection`: PDF p.10, (3.5): signed entropy correction.
--   - `secondOrderCoefficient`: PDF p.9: second-order coefficient, including the zero-variance case.
--   - `SecondOrderBounds`: PDF pp.9--10: both quantified clauses, with an all-index upper bound and eventual lower bound. The remainders are actual real FUNCTIONS of the weight, not free sequence errors.
--   - `iidSequence`: PDF p.16: slot k is tensor power k+1; no source n=0 is introduced.
--   - `iidWeight`: PDF p.16: IID weights at positive source indices.
--   - `RandomVariable`: PDF p.11: a measurable real random variable on a probability space, varying with k.
--   - `logLaplace`: PDF p.11: real log-Laplace transform; exponential integrability is a theorem hypothesis.
--   - `BrycWeakLimit`: PDF p.11: weak convergence, tested against every bounded continuous real function. This also describes a Dirac Gaussian limit when the limiting variance is zero.
--   - `Site`: PDF p.17: sites of the integer lattice.
--   - `manhattan`: PDF p.17: Manhattan distance between sites.
--   - `SpinInteraction`: PDF p.17: local observables on a common q-dimensional one-site space.
--   - `translateSupport`: PDF p.17: translate a finite support.
--   - `translatedSite`: PDF p.17: site identification under translation, with no basis change.
--   - `TranslationInvariant`: PDF p.17: covariance of the actual local matrices under every translation.
--   - `FiniteRange`: PDF p.18: some positive R kills all terms with Manhattan diameter at least R. For finite nonempty sets the diameter is attained; empty terms already vanish.
--   - `latticeIncludeLocal`: PDF p.17: inclusion A -> A tensor I on Z^d, in the named site bases. The accepted Next46.P28.includeLocal is restricted to subsets of Z.
--   - `localHamiltonian`: PDF p.18, (4.4): interaction Hamiltonian, constructed by summing all contained terms.
--   - `spinBox`: PDF p.18: Lambda_n={-n,...,n}^d, with n=k+1.
--   - `spinSequence`: PDF p.18, (4.5): the two actual finite-volume Gibbs matrices.
--   - `spinVolumeWeight`: PDF p.18: lattice volume (2n+1)^d; unrelated to the accepted angular-momentum spinWeight.
--   - `normalizedPartition`: PDF p.19, (4.8): partition function normalized by the completely mixed state.
--   - `clusterGerm`: PDF p.19, (4.8)--(4.10): the canonical cluster-coefficient germ. Subset Mobius inversion of the finite-volume normalized partition logarithms. Complex.log is used only near zero, where every partition value is near 1. Analytic continuation to the full polydisc is a conclusion, never an assumption.
--   - `ClusterSmallness`: PDF p.19, (4.11): nonnegative extended sum, so divergence is infinity, never zero.
--   - `torusMeasure`: PDF p.22: normalized Lebesgue measure on the Fourier cube [0,2pi)^d.
--   - `torusAverage`: PDF p.22: normalized integral of a real symbol on the Fourier cube.
--   - `symbolCompression`: PDF pp.22--23: compression of the Fourier multiplier to {0,...,n-1}^d. The sign is exp(-i <j-k,x>), as in the source. Finite enumeration changes basis only.
--   - `fermionSequence`: PDF p.23, (4.16): finite Fock densities, using the accepted exterior-power construction. The occupation basis includes the vacuum and all particle-number sectors.
--   - `fermionWeight`: PDF p.23: volume n^d, with positive source index n=k+1.
--   - `symbolEntropy`: PDF p.23, (4.20): relative entropy density of the commuting Fourier symbols.
--   - `symbolPressure`: PDF p.23, (4.21): limiting real Petz log-overlap density.
-- source:
--   Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more, arXiv:1510.04682v4, https://arxiv.org/abs/1510.04682v4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

/-! Statements from Datta--Pautrat--Rouze, arXiv:1510.04682v4.
All logarithms are natural. A sequence slot k represents the positive source index k+1.
All new definitions are confined to this paper. Compilation is pending.
Theorem 4 is recorded as accepted-library reuse; source-defective clauses are in HARD.md. -/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate positiveMatrixRpow modularMatrix modularQuadratic resolventOverlap petzOverlap
    finiteRelativeEntropyNats)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower testingBeta)
open QAlgorithms.Papers.Independent.Information100.P58 (normalQuantile)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- PDF p.6, (2.4): positive Umegaki entropy in nats, converting the accepted
nonpositive relative-entropy convention. Used only with support inclusion. -/
def finitePairRelativeEntropyNats (rho sigma : Mat I) : ℝ :=
  -finiteRelativeEntropyNats rho sigma

/-- PDF p.6, (2.5): PAIR information variance, in nats squared. Distinct from the
accepted single-density spectral informationVariance in bits squared. -/
def pairInformationVarianceNats (rho sigma : Mat I) : ℝ :=
  evaluate rho ((cfc Real.log rho - cfc Real.log sigma) ^ 2) -
    finitePairRelativeEntropyNats rho sigma ^ 2

/-- PDF pp.6,9: real analytic representative of the Petz logarithm.
Kernel powers vanish; all uses have common support or support inclusion near s=1. -/
def realPetzLogOverlap (rho sigma : Mat I) (s : ℝ) : ℝ :=
  Real.log ((supportPower rho s * supportPower sigma (1-s)).trace.re)

/-- PDF pp.8--10: testing exponent in natural logarithms, on the stated valid inputs. -/
def optimalTestingExponentNats (rho sigma : Mat I) (epsilon : ℝ) : ℝ :=
  -Real.log (testingBeta epsilon rho sigma)

/-- PDF p.12, (3.9): infimum of the SUM of the errors, with no prior factor 1/2. -/
def symmetricError (A B : Mat I) : ℝ :=
  sInf {e : ℝ | ∃ T : Mat I, QAlgorithms.IsEffect T ∧
    e = evaluate A (1-T) + evaluate B T}

/-- PDF p.7, (2.11): integration against the FINITE spectral measure of -log Delta
in Omega_B. Its mass is Tr B, with no implicit normalization. -/
def spectralIntegral (A B : Mat I) (f : ℝ → ℝ) : ℝ :=
  modularQuadratic B (cfc (fun t : ℝ => f (-Real.log t)) (modularMatrix A B))

/-- PDF p.13, (3.13): finite spectral mass of (-infinity,nu]. -/
def spectralTail (A B : Mat I) (nu : ℝ) : ℝ :=
  spectralIntegral A B (fun x => if x ≤ nu then 1 else 0)

/-- PDF p.14: spectral projector of Delta_(rho|sigma) on the STRICT interval [0,L). -/
def modularLowProjector (rho sigma : Mat I) (L : ℝ) : Mat (I × I) :=
  cfc (fun t : ℝ => if 0 ≤ t ∧ t < L then 1 else 0) (modularMatrix rho sigma)

/-- PDF p.13: distinct eigenvalues, for the explicit spectral-sum identity. -/
def eigenvalueSet (A : Mat I) (hA : A.IsHermitian) : Finset ℝ :=
  Finset.univ.image hA.eigenvalues

/-- PDF p.5: spectral projection of a Hermitian matrix at lambda. -/
def eigenprojector (A : Mat I) (lambda : ℝ) : Mat I :=
  cfc (fun x : ℝ => if x = lambda then 1 else 0) A

/-- PDF pp.8--9: a pair of finite spaces at each positive sequence index.
No density, support, or analytic conclusions are built into this data structure. -/
structure TestingSequence where
  Index : ℕ → Type
  finite : ∀ k, Fintype (Index k)
  decidable : ∀ k, DecidableEq (Index k)
  rho : ∀ k, Mat (Index k)
  sigma : ∀ k, Mat (Index k)

attribute [instance] TestingSequence.finite TestingSequence.decidable

/-- PDF pp.5--9: nonzero spaces, trace-one PSD pairs, and finite relative entropy domain. -/
def StatePairs (S : TestingSequence) : Prop :=
  ∀ k, Nonempty (S.Index k) ∧ QAlgorithms.IsDensityMatrix (S.rho k) ∧
    QAlgorithms.IsDensityMatrix (S.sigma k) ∧ SupportIncluded (S.rho k) (S.sigma k)

/-- PDF pp.6--9: the standing faithful-state restriction. -/
def FaithfulPairs (S : TestingSequence) : Prop :=
  ∀ k, (S.rho k).PosDef ∧ (S.sigma k).PosDef

/-- PDF pp.9,11: analytic extensions of real log-Laplace germs, a common disc,
finite pointwise real limits, and one bound uniform in the index and the whole disc.
No variance limit or central limit theorem is assumed here. -/
def AnalyticCumulants (w : ℕ → ℝ) (h : ℕ → ℝ → ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ H : ℕ → ℂ → ℂ,
    (∀ k, AnalyticOnNhd ℂ (H k) (Metric.ball 0 r)) ∧
    (∀ k x, |x| < r → H k (x : ℂ) = (h k x : ℂ)) ∧
    (∀ x : ℝ, |x| < r → ∃ l : ℂ,
      Tendsto (fun k => H k (x : ℂ) / (w k : ℂ)) atTop (nhds l)) ∧
    (∃ C : ℝ, ∀ k z, ‖z‖ < r → ‖H k z‖ ≤ C * w k)

/-- PDF pp.8--9, Condition 1, with nondecreasing positive divergent weights.
Repeated weights are permitted. The support-inclusion version is used in Remark 1. -/
def ConditionOne (S : TestingSequence) (w : ℕ → ℝ) : Prop :=
  StatePairs S ∧ (∀ k, 0 < w k) ∧ Monotone w ∧ Tendsto w atTop atTop ∧
    AnalyticCumulants w (fun k x => realPetzLogOverlap (S.rho k) (S.sigma k) (1-x))

/-- PDF p.9, (3.1): constructed limit, rather than a free entropy-rate parameter.
The rates-exist theorem establishes that this topological limit exists under Condition 1. -/
def relativeEntropyRate (S : TestingSequence) (w : ℕ → ℝ) : ℝ :=
  limUnder atTop (fun k => finitePairRelativeEntropyNats (S.rho k) (S.sigma k) / w k)

/-- PDF p.9, (3.2): constructed variance-rate limit; its value may be zero. -/
def varianceRate (S : TestingSequence) (w : ℕ → ℝ) : ℝ :=
  limUnder atTop (fun k => pairInformationVarianceNats (S.rho k) (S.sigma k) / w k)

/-- PDF p.10, (3.5): signed entropy correction. -/
def relativeEntropyCorrection (S : TestingSequence) (w : ℕ → ℝ) (k : ℕ) : ℝ :=
  finitePairRelativeEntropyNats (S.rho k) (S.sigma k) - w k * relativeEntropyRate S w

/-- PDF p.9: second-order coefficient, including the zero-variance case. -/
def secondOrderCoefficient (S : TestingSequence) (w : ℕ → ℝ) (epsilon : ℝ) : ℝ :=
  Real.sqrt (varianceRate S w) * normalQuantile epsilon

/-- PDF pp.9--10: both quantified clauses, with an all-index upper bound and eventual lower
bound. The remainders are actual real FUNCTIONS of the weight, not free sequence errors. -/
def SecondOrderBounds (S : TestingSequence) (w center : ℕ → ℝ) (epsilon : ℝ) : Prop :=
  (∀ t : ℝ, secondOrderCoefficient S w epsilon < t →
    ∃ f : ℝ → ℝ, Asymptotics.IsLittleO atTop f Real.sqrt ∧
      ∀ k, optimalTestingExponentNats (S.rho k) (S.sigma k) epsilon ≤
        center k + Real.sqrt (w k) * t + f (w k)) ∧
  (∀ t : ℝ, t < secondOrderCoefficient S w epsilon →
    ∀ f : ℝ → ℝ, Asymptotics.IsLittleO atTop f Real.sqrt →
      ∀ᶠ k in atTop, center k + Real.sqrt (w k) * t + f (w k) ≤
        optimalTestingExponentNats (S.rho k) (S.sigma k) epsilon)

/-- PDF p.16: slot k is tensor power k+1; no source n=0 is introduced. -/
def iidSequence (rho sigma : Mat I) : TestingSequence where
  Index k := Fin (k+1) → I
  finite _ := inferInstance
  decidable _ := Classical.decEq _
  rho k := tensorPower (k+1) rho
  sigma k := tensorPower (k+1) sigma

/-- PDF p.16: IID weights at positive source indices. -/
def iidWeight (k : ℕ) : ℝ := (k+1 : ℕ)

/-- PDF p.11: a measurable real random variable on a probability space, varying with k. -/
structure RandomVariable where
  Space : Type
  measurableSpace : MeasurableSpace Space
  measure : @Measure Space measurableSpace
  probability : @IsProbabilityMeasure Space measurableSpace measure
  value : Space → ℝ
  measurable_value : @Measurable Space ℝ measurableSpace inferInstance value

attribute [instance] RandomVariable.measurableSpace RandomVariable.probability

/-- PDF p.11: real log-Laplace transform; exponential integrability is a theorem hypothesis. -/
def logLaplace (X : RandomVariable) (x : ℝ) : ℝ :=
  Real.log (∫ a, Real.exp (-x * X.value a) ∂X.measure)

/-- PDF p.11: weak convergence, tested against every bounded continuous real function.
This also describes a Dirac Gaussian limit when the limiting variance is zero. -/
def BrycWeakLimit (X : ℕ → RandomVariable) (w : ℕ → ℝ) (v : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Tendsto (fun k => ∫ a, f (((X k).value a + deriv (logLaplace (X k)) 0) / Real.sqrt (w k)) ∂(X k).measure) atTop
      (nhds (∫ y, f y ∂ProbabilityTheory.gaussianReal 0 (Real.toNNReal v)))

example (rho sigma : Mat I) : finitePairRelativeEntropyNats rho sigma =
    -finiteRelativeEntropyNats rho sigma := rfl

set_option maxHeartbeats 2000000 in
example (rho sigma : Mat I) : relativeEntropyCorrection (iidSequence rho sigma) iidWeight 0 =
    finitePairRelativeEntropyNats (tensorPower 1 rho) (tensorPower 1 sigma) -
      relativeEntropyRate (iidSequence rho sigma) iidWeight := by
  unfold relativeEntropyCorrection
  rw [show iidWeight 0 = (1 : ℝ) by norm_num [iidWeight], one_mul]
  rw [show (iidSequence rho sigma).decidable 0 =
    (inferInstance : DecidableEq (Fin 1 → I)) from Subsingleton.elim _ _] <;> rfl

example (rho sigma : Mat I) : tensorPower 0 rho = tensorPower 0 sigma := by
  funext a b
  simp [QAlgorithms.Papers.Independent.Information100.P63.tensorPower]

/-- PDF p.17: sites of the integer lattice. -/
abbrev Site (d : ℕ) := Fin d → ℤ

/-- PDF p.17: Manhattan distance between sites. -/
def manhattan {d : ℕ} (x y : Site d) : ℝ := ∑ j, |((x j - y j : ℤ) : ℝ)|

/-- PDF p.17: local observables on a common q-dimensional one-site space. -/
structure SpinInteraction (d q : ℕ) where
  term : ∀ X : Finset (Site d), Mat (X → Fin q)
  hermitian : ∀ X, (term X).IsHermitian
  empty_zero : term ∅ = 0

/-- PDF p.17: translate a finite support. -/
def translateSupport {d : ℕ} (X : Finset (Site d)) (t : Site d) : Finset (Site d) :=
  X.image (fun x => x+t)

/-- PDF p.17: site identification under translation, with no basis change. -/
def translatedSite {d : ℕ} (X : Finset (Site d)) (t : Site d) (x : X) :
    translateSupport X t :=
  ⟨x.val+t, Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩

/-- PDF p.17: covariance of the actual local matrices under every translation. -/
def TranslationInvariant {d q : ℕ} (Phi : SpinInteraction d q) : Prop :=
  ∀ (X : Finset (Site d)) (t : Site d) (a b : translateSupport X t → Fin q),
    Phi.term (translateSupport X t) a b =
      Phi.term X (fun x => a (translatedSite X t x)) (fun x => b (translatedSite X t x))

/-- PDF p.18: some positive R kills all terms with Manhattan diameter at least R.
For finite nonempty sets the diameter is attained; empty terms already vanish. -/
def FiniteRange {d q : ℕ} (Phi : SpinInteraction d q) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ X : Finset (Site d),
    (∃ x ∈ X, ∃ y ∈ X, R ≤ manhattan x y) → Phi.term X = 0

/-- PDF p.17: inclusion A -> A tensor I on Z^d, in the named site bases.
The accepted Next46.P28.includeLocal is restricted to subsets of Z. -/
def latticeIncludeLocal {d q : ℕ} (Y X : Finset (Site d)) (hYX : Y ⊆ X)
    (A : Mat (Y → Fin q)) : Mat (X → Fin q) :=
  fun a b => if ∀ x : X, x.val ∉ Y → a x = b x then
    A (fun y => a ⟨y.val, hYX y.property⟩) (fun y => b ⟨y.val, hYX y.property⟩)
  else 0

/-- PDF p.18, (4.4): interaction Hamiltonian, constructed by summing all contained terms. -/
def localHamiltonian {d q : ℕ} (Phi : SpinInteraction d q) (X : Finset (Site d)) :
    Mat (X → Fin q) :=
  ∑ Y ∈ X.powerset, if hYX : Y ⊆ X then latticeIncludeLocal Y X hYX (Phi.term Y) else 0

/-- PDF p.18: Lambda_n={-n,...,n}^d, with n=k+1. -/
def spinBox (d k : ℕ) : Finset (Site d) :=
  Finset.univ.image (fun a : Fin d → Fin (2*(k+1)+1) =>
    fun j => ((a j).val : ℤ) - (k+1 : ℤ))

/-- PDF p.18, (4.5): the two actual finite-volume Gibbs matrices. -/
def spinSequence {d q : ℕ} (Phi Psi : SpinInteraction d q) (beta1 beta2 : ℝ) :
    TestingSequence where
  Index k := spinBox d k → Fin q
  finite _ := inferInstance
  decidable _ := Classical.decEq _
  rho k := QAlgorithms.gibbsState ((-beta1 : ℂ) • localHamiltonian Phi (spinBox d k))
  sigma k := QAlgorithms.gibbsState ((-beta2 : ℂ) • localHamiltonian Psi (spinBox d k))

/-- PDF p.18: lattice volume (2n+1)^d; unrelated to the accepted angular-momentum spinWeight. -/
def spinVolumeWeight (d k : ℕ) : ℝ := ((2*(k+1)+1 : ℕ) : ℝ)^d

/-- PDF p.19, (4.8): partition function normalized by the completely mixed state. -/
def normalizedPartition {d q : ℕ} (Phi Psi : SpinInteraction d q)
    (beta1 beta2 : ℝ) (X : Finset (Site d)) (z : ℂ × ℂ) : ℂ :=
  ((q : ℂ)^X.card)⁻¹ *
    (NormedSpace.exp ((z.1 * (beta1 : ℂ)) • localHamiltonian Phi X) *
      NormedSpace.exp ((z.2 * (beta2 : ℂ)) • localHamiltonian Psi X)).trace

/-- PDF p.19, (4.8)--(4.10): the canonical cluster-coefficient germ.
Subset Mobius inversion of the finite-volume normalized partition logarithms.
Complex.log is used only near zero, where every partition value is near 1.
Analytic continuation to the full polydisc is a conclusion, never an assumption. -/
def clusterGerm {d q : ℕ} (Phi Psi : SpinInteraction d q) (beta1 beta2 : ℝ)
    (X : Finset (Site d)) (z : ℂ × ℂ) : ℂ :=
  ∑ Y ∈ X.powerset, (-1 : ℂ)^(X.card-Y.card) *
    Complex.log (normalizedPartition Phi Psi beta1 beta2 Y z)

/-- PDF p.19, (4.11): nonnegative extended sum, so divergence is infinity, never zero. -/
def ClusterSmallness {d q : ℕ} (Phi Psi : SpinInteraction d q)
    (beta1 beta2 a delta : ℝ) : Prop :=
  (∑' X : {X : Finset (Site d) // (0 : Site d) ∈ X},
    ENNReal.ofReal (Real.exp (2*a*(X.val.card : ℝ)) *
      (Real.exp (delta*(beta1*‖Phi.term X.val‖ + beta2*‖Psi.term X.val‖))-1))) ≤
    ENNReal.ofReal a

/-- PDF p.22: normalized Lebesgue measure on the Fourier cube [0,2pi)^d. -/
def torusMeasure (d : ℕ) : Measure (Fin d → ℝ) :=
  (ENNReal.ofReal ((2*Real.pi)^d))⁻¹ •
    volume.restrict (Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) (2*Real.pi)))

/-- PDF p.22: normalized integral of a real symbol on the Fourier cube. -/
def torusAverage {d : ℕ} (f : (Fin d → ℝ) → ℝ) : ℝ := ∫ x, f x ∂torusMeasure d

/-- PDF pp.22--23: compression of the Fourier multiplier to {0,...,n-1}^d.
The sign is exp(-i <j-k,x>), as in the source. Finite enumeration changes basis only. -/
def symbolCompression {d : ℕ} (qhat : (Fin d → ℝ) → ℝ) (n : ℕ) :
    Mat (Fin (Fintype.card (Fin d → Fin n))) :=
  let e := Fintype.equivFin (Fin d → Fin n)
  fun j k => ∫ x : Fin d → ℝ,
    Complex.exp (-Complex.I * ((∑ l,
      (((e.symm j l).val : ℝ)-((e.symm k l).val : ℝ))*x l) : ℂ)) * (qhat x : ℂ)
      ∂torusMeasure d

/-- PDF p.23, (4.16): finite Fock densities, using the accepted exterior-power construction.
The occupation basis includes the vacuum and all particle-number sectors. -/
def fermionSequence {d : ℕ} (qhat rhat : (Fin d → ℝ) → ℝ) : TestingSequence where
  Index k := Finset (Fin (Fintype.card (Fin d → Fin (k+1))))
  finite _ := inferInstance
  decidable _ := Classical.decEq _
  rho k := QAlgorithms.Papers.Independent.Next46.P23.quasiFree (symbolCompression qhat (k+1))
  sigma k := QAlgorithms.Papers.Independent.Next46.P23.quasiFree (symbolCompression rhat (k+1))

/-- PDF p.23: volume n^d, with positive source index n=k+1. -/
def fermionWeight (d k : ℕ) : ℝ := ((k+1 : ℕ) : ℝ)^d

/-- PDF p.23, (4.20): relative entropy density of the commuting Fourier symbols. -/
def symbolEntropy {d : ℕ} (qhat rhat : (Fin d → ℝ) → ℝ) : ℝ :=
  torusAverage (fun x => qhat x * Real.log (qhat x / rhat x) +
    (1-qhat x)*Real.log ((1-qhat x)/(1-rhat x)))

/-- PDF p.23, (4.21): limiting real Petz log-overlap density. -/
def symbolPressure {d : ℕ} (qhat rhat : (Fin d → ℝ) → ℝ) (s : ℝ) : ℝ :=
  torusAverage (fun x => Real.log ((qhat x)^s * (rhat x)^(1-s) +
    (1-qhat x)^s * (1-rhat x)^(1-s)))

example (k : ℕ) : spinVolumeWeight 1 k = (2*(k+1)+1 : ℕ) := by simp [spinVolumeWeight]

example (k : ℕ) : fermionWeight 1 k = (k+1 : ℕ) := by simp [fermionWeight]

example (d k : ℕ) : fermionWeight d k = ((k+1 : ℕ) : ℝ)^d := rfl

example (H : Mat I) (beta : ℝ) : QAlgorithms.gibbsState ((-beta : ℂ) • H) =
    (NormedSpace.exp ((-beta : ℂ) • H)).trace⁻¹ • NormedSpace.exp ((-beta : ℂ) • H) := rfl

example {d q : ℕ} (Phi Psi : SpinInteraction d q) (b1 b2 : ℝ) (X : Finset (Site d)) :
    clusterGerm Phi Psi b1 b2 X =
      fun z => ∑ Y ∈ X.powerset, (-1 : ℂ)^(X.card-Y.card) *
        Complex.log (normalizedPartition Phi Psi b1 b2 Y z) := rfl

end QAlgorithms.Papers.Independent.Bridge50.P02


