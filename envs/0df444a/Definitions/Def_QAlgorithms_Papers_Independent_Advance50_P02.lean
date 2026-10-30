-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P02
-- name    : QAlgorithms_Papers_Independent_Advance50_P02
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T15:10:48.084985+00:00
-- url     : https://prove2.me/theorems/93da2a36-2dee-46ea-8f27-bb4403042b9c
-- title:
--   Definitions for A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks
-- statement:
--   The objects the formalized statements of *A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks* (arXiv:1208.1478) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PositiveTraceSubnormalized`: PDF pp.6--7: the source's strictly positive-trace subnormalized states.
--   - `negLog`: PDF p.8, Definition 4: -log_2, explicitly extended at zero.
--   - `extendedTestingDivergence`: PDF p.8, Definition 4. Reuses the accepted extended testing entropy, adapting its argument order. The beta optimization is nonempty/bounded on the theorem domains.
--   - `smoothedMaxRelativeEntropy`: PDF pp.7--8, Definition 2: nearby strictly positive-trace subnormalized states, with positive scale t=2^lambda. Includes Lemma 2's subnormalized centers.
--   - `lowProjector`: PDF p.14, Definition 8: weak spectral projector, including zero eigenvalues.
--   - `spectrumMass`: PDF p.14: actual quantum threshold mass, without logarithms at zero.
--   - `spectrumEntropy`: PDF p.14, Definition 8: empty/unbounded sets give negative/positive infinity.
--   - `classicalThresholdMass`: PDF p.2, (2): classical threshold mass, permitting Q=0 at positive P.
--   - `classicalSpectrumDivergence`: PDF p.2, (2): extended-real classical information spectrum.
--   - `relativeMean`: PDF pp.7,19: finite relative entropy in bits, used only on the support domain. Kernel log values are irrelevant after weighting by rho.
--   - `centeredRelativeVariance`: PDF p.19, correcting Definition 1 p.7: accepted centered pair variance in bits.
--   - `PositiveSpectralPresentation`: PDF p.14: arbitrary finite index, nonnegative eigenvalues, and full unitary reconstruction of this PSD matrix. Unlike Information100.P53.SpectralData, no ordering or Fin-index presentation is imposed.
--   - `eigenbasisOverlapSquared`: PDF p.14: overlap squared of the two eigenvectors.
--   - `nsSpectralPresentation`: PDF p.14: adapt column eigenvectors to the accepted NS row-vector presentation.
--   - `nsProbability`: PDF p.14: Nussbaum--Szkola P, including zero-probability entries.
--   - `nsReferenceWeight`: PDF p.14: Nussbaum--Szkola Q; need not have total mass one.
--   - `classicalMean`: PDF p.19: classical mean, used only on the finite-likelihood domain.
--   - `classicalVariance`: PDF p.19: centered classical information variance.
--   - `classicalThirdCentralMoment`: PDF p.19: third absolute central moment (the cube of the printed T).
--   - `weightPower`: PDF pp.2,18: products of classical weights, including the empty product.
--   - `empiricalMeanMass`: Eq.(31), PDF p.18: CDF of the empirical mean of n independent log likelihoods. Used with n>0 and support inclusion; zero-P atoms carry zero mass.
--   - `distinctEigenvalueSet`: PDF p.14: distinct spectral values, counting the kernel once.
--   - `distinctCount`: PDF pp.13--14: number of distinct eigenvalues, not dimension or rank.
--   - `eigenspaceProjector`: PDF p.14: projection onto one whole eigenspace.
--   - `spectralSpread`: PDF p.17: spread for an invertible PSD operator; only used there.
--   - `positiveSpectralFactor`: PDF pp.17--18: corrected positive bin count. Printed 2*ceil(lambda)=0 for flat spectra. The proof requires l>0; use l=max(1,ceil(lambda)). For singular sigma use the separately proved nu branch, without evaluating log(0).
--   - `identityTensor`: PDF p.7: identity on A tensored with the reference on B.
--   - `positiveTraceSmoothedMinEntropy`: PDF p.8, Definition 3: normalized reference optimization on B.
--   - `conditionalTesting`: PDF p.8, Definition 5: optimized conditional testing entropy.
--   - `cqBlockMatrix`: PDF pp.7--8: unnormalized positive classical blocks, allowing zero labels.
--   - `processBlocks`: PDF pp.7--8: arbitrary many-to-one processing, constructed from input.
--   - `NormalizedBlocks`: PDF p.7: normalized CQ states expressed as positive blocks.
--   - `cqMarginal`: PDF p.7: the actual B marginal.
--   - `conditionOnClassical`: PDF p.9, Proposition 7: reorder XAB to A(XB).
--   - `joinClassical`: PDF p.9, Proposition 7: reorder XAB to (XA)B.
--   - `labelCount`: PDF p.9: positive-probability support size.
--   - `PublicRandomSeed`: PDF pp.10--12: independent public seed of arbitrary finite size.
--   - `Extractor`: PDF p.10: arbitrary seeded hashes to a finite output alphabet.
--   - `extractionOutput`: PDF p.10: output retaining the public seed.
--   - `extractionIdeal`: PDF p.10: same seed cqMarginal, uniform output, one common reference.
--   - `extractionSecurity`: PDF p.10, Definition 6: extractionSecurity optimized over one normalized sigma_B.
--   - `extractionLength`: PDF p.10, Definition 6: maximal INTEGER length; arbitrary output cardinality. The set is nonempty/bounded on normalized CQ sources with e<1.
--   - `Compressor`: PDF pp.11--12: seeded encoder and seed/message-dependent decoder POVM.
--   - `compressionError`: PDF p.12, Definition 7: actual source/seed average error.
--   - `compressionLength`: PDF p.12, Definition 7: minimal INTEGER length.
--   - `blocksPower`: PDF p.20: independent CQ copies in the product classical basis.
--   - `conditionalMean`: PDF pp.7,20: conditional entropy, actual marginal.
--   - `cqConditionalVariance`: PDF pp.19--20: centered conditional pair variance.
--   - `gaussianCenter`: PDF p.19: Gaussian approximation, including V=0.
--   - `LogarithmicRemainder`: PDF p.19: two-sided O(log n), constants before blocklength.
--   - `ConstantRemainder`: PDF p.19, (33): two-sided O(1).
--   - `liftIsometry`: PDF p.8: the actual isometry U tensor identity_B.
--   - `nsTensorP`: PDF p.14: NS P for product eigenbases, independently computed from the product eigenvalues and the eigenbasisOverlapSquared of product eigenvectors.
--   - `nsTensorQ`: PDF p.14: NS Q for the same product eigenbases.
--   - `supportedSpread`: PDF p.21: spread after restricting a marginal to its positive support.
--   - `finiteBins`: PDF p.21: positive-bin correction, including a flat nonzero marginal.
--   - `intervalSup`: PDF p.21: lower/upper optimization over a half-open real interval, in EReal.
--   - `intervalInf`: PDF p.21: infimum counterpart, retaining infinite limiting values.
--   - `monotoneInverse`: Lemma 18, PDF p.22: generalized inverse with extended endpoints.
--   - `inverseRate`: PDF p.22: optimization over ALL real threshold sequences.
--   - `thresholdRate`: PDF p.22: threshold spectrum with its exact limsup/non-strict or liminf/strict constraint.
--   - `pauliP`: Appendix A, PDF pp.24--25: explicit NS probabilities, total P=1.
--   - `pauliQ`: Appendix A, PDF pp.24--25: reference weights, total Q=2(p^2+(1-p)^2) on the nontrivial NS support. Remaining zero-P entries are irrelevant to Ds.
--   - `binomialBelow`: Appendix A, PDF p.25: F(k-1;n,p), with F(-1)=0 at k=0.
--   - `binomialCutoff`: Appendix A, PDF p.25: maximum k in 0,...,n with F(k-1)<=epsilon. For 0<=epsilon<1 the set contains 0 and larger k>n never qualify.
--   - `PairSequence`: PDF pp.21--23: arbitrary finite pairs; slot k is source blocklength k+1. Dimensions can vary and no iid, support or variance property is built in.
--   - `StateSequence`: PDF p.22: both sequences consist of normalized quantum states.
--   - `ErrorConstraint`: PDF pp.22--23: the two different asymptotic error constraints.
--   - `quantumSpectrumRate`: PDF p.22: source thresholds are 2^((k+1)R), in bits.
--   - `optimizedEntropySequenceRate`: PDF pp.22--23: one-shot rates, optimizing all [0,1]-valued error sequences.
--   - `VaryingRegisterTests`: PDF p.23: one genuine effect at each blocklength, without a free rate variable.
--   - `testError`: PDF p.23: actual type-I error of an effect.
--   - `testRate`: PDF p.23: actual type-II exponent, including zero type-II error.
--   - `operationalTestingRate`: PDF p.23: operational B and the strict-error sup form of B-dagger.
--   - `testingConverseRate`: PDF p.23: universal converse threshold defining B-dagger.
--   - `SpectralControl`: PDF p.23: the source's sufficient polynomial spectral condition. The positive-eigenvalue alternative is on the supported restriction and explicitly retains support inclusion. Constants and thresholds precede k.
--   - `nsSequence`: PDF p.23: classical NS distributions as diagonal matrices; testing arbitrary effects on diagonal states equals randomized classical testing.
--   - `smoothMaxEndpoint`: PDF p.23: explicit endpoint continuation for smoothing parameter one, by its monotone left limit, rather than a finite real default.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, https://arxiv.org/abs/1208.1478v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P50

/-! Tomamichel--Hayashi, arXiv:1208.1478v3. Binary logarithms throughout.
Extended-real optimizations preserve empty sets and infinite values. Matching accepted
primitives are imported; source-specific interfaces have distinct names. Local definitions
have complete bodies. Source corrections/deferrals are recorded with this unit.
Compilation and independent moderation are pending the batch handoff. -/

noncomputable section

open Filter
open scoped BigOperators Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Advance50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63
  (Mat tensorPower logTwo normalQuantile testingBeta)
open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded supportPower)
open QAlgorithms (effectProb)
open QAlgorithms.Papers.Independent.Information100.P06 (Below)
open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)
open QAlgorithms.Papers.Independent.Information100.P67 (purifiedDistance)
open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)
open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

variable {I J A B X Z : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X]
  [Fintype Z] [DecidableEq Z]

/-- PDF pp.6--7: the source's strictly positive-trace subnormalized states. -/
def PositiveTraceSubnormalized (a : Mat I) : Prop :=
  QAlgorithms.Papers.Independent.Information100.P67.IsSubnormalized a ∧ 0 < a.trace.re

/-- PDF p.8, Definition 4: -log_2, explicitly extended at zero. -/
def negLog (x : ℝ) : EReal := if x = 0 then ⊤ else (-logTwo x : ℝ)

/-- PDF p.8, Definition 4. Reuses the accepted extended testing entropy, adapting its argument order.
The beta optimization is nonempty/bounded on the theorem domains. -/
def extendedTestingDivergence (e : ℝ) (rho sigma : Mat I) : EReal :=
  QAlgorithms.Papers.Independent.Dependency50.P36.testingEntropy rho sigma e

/-- PDF pp.7--8, Definition 2: nearby strictly positive-trace subnormalized
states, with positive scale t=2^lambda. Includes Lemma 2's subnormalized centers. -/
def smoothedMaxRelativeEntropy (e : ℝ) (rho sigma : Mat I) : EReal :=
  sInf {d : EReal | ∃ tau : Mat I, PositiveTraceSubnormalized tau ∧ purifiedDistance rho tau ≤ e ∧
    ∃ t : ℝ, 0 < t ∧ Below tau ((t : ℂ) • sigma) ∧ d = (logTwo t : ℝ)}

/-- PDF p.14, Definition 8: weak spectral projector, including zero eigenvalues. -/
def lowProjector (rho sigma : Mat I) (R : ℝ) : Mat I :=
  cfc (fun x : ℝ => if x ≤ 0 then (1 : ℝ) else 0)
    (rho - ((Real.rpow 2 R : ℝ) : ℂ) • sigma)

/-- PDF p.14: actual quantum threshold mass, without logarithms at zero. -/
def spectrumMass (rho sigma : Mat I) (R : ℝ) : ℝ :=
  effectProb rho (lowProjector rho sigma R)

/-- PDF p.14, Definition 8: empty/unbounded sets give negative/positive infinity. -/
def spectrumEntropy (e : ℝ) (rho sigma : Mat I) : EReal :=
  sSup {r : EReal | ∃ R : ℝ, spectrumMass rho sigma R ≤ e ∧ r = (R : EReal)}

/-- PDF p.2, (2): classical threshold mass, permitting Q=0 at positive P. -/
def classicalThresholdMass {K : Type} [Fintype K] (P Q : K → ℝ) (R : ℝ) : ℝ :=
  ∑ z, if P z ≤ Real.rpow 2 R * Q z then P z else 0

/-- PDF p.2, (2): extended-real classical information spectrum. -/
def classicalSpectrumDivergence {K : Type} [Fintype K] (e : ℝ) (P Q : K → ℝ) : EReal :=
  sSup {r : EReal | ∃ R : ℝ, classicalThresholdMass P Q R ≤ e ∧ r = (R : EReal)}

/-- PDF pp.7,19: finite relative entropy in bits, used only on the support domain.
Kernel log values are irrelevant after weighting by rho. -/
def relativeMean (rho sigma : Mat I) : ℝ :=
  effectProb rho (cfc logTwo rho - cfc logTwo sigma)

/-- PDF p.19, correcting Definition 1 p.7: accepted centered pair variance in bits. -/
def centeredRelativeVariance (rho sigma : Mat I) : ℝ :=
  QAlgorithms.Papers.Independent.Dependency50.P36.pairInformationVariance rho sigma

/-- PDF p.14: arbitrary finite index, nonnegative eigenvalues, and full unitary
reconstruction of this PSD matrix. Unlike Information100.P53.SpectralData, no
ordering or Fin-index presentation is imposed. -/
structure PositiveSpectralPresentation (rho : Mat I) where
  value : I → ℝ
  nonnegative : ∀ i, 0 ≤ value i
  vectors : Mat I
  unitary : vectorsᴴ * vectors = 1
  decomposition : rho = vectors * Matrix.diagonal (fun i => (value i : ℂ)) * vectorsᴴ

/-- PDF p.14: overlap squared of the two eigenvectors. -/
def eigenbasisOverlapSquared {rho sigma : Mat I} (r : PositiveSpectralPresentation rho) (s : PositiveSpectralPresentation sigma)
    (x y : I) : ℝ :=
  Complex.normSq (∑ i, conj (r.vectors i x) * s.vectors i y)

/-- PDF p.14: adapt column eigenvectors to the accepted NS row-vector presentation. -/
def nsSpectralPresentation {rho : Mat I} (r : PositiveSpectralPresentation rho) :
    QAlgorithms.Papers.Independent.Bridge50.P50.NSSpectralData I :=
  ⟨r.value, fun x i => r.vectors i x⟩

/-- PDF p.14: Nussbaum--Szkola P, including zero-probability entries. -/
def nsProbability {rho sigma : Mat I} (r : PositiveSpectralPresentation rho) (s : PositiveSpectralPresentation sigma) : I × I → ℝ :=
  QAlgorithms.Papers.Independent.Bridge50.P50.nsP (nsSpectralPresentation r) (nsSpectralPresentation s)

/-- PDF p.14: Nussbaum--Szkola Q; need not have total mass one. -/
def nsReferenceWeight {rho sigma : Mat I} (r : PositiveSpectralPresentation rho) (s : PositiveSpectralPresentation sigma) : I × I → ℝ :=
  QAlgorithms.Papers.Independent.Bridge50.P50.nsQ (nsSpectralPresentation r) (nsSpectralPresentation s)

/-- PDF p.19: classical mean, used only on the finite-likelihood domain. -/
def classicalMean {K : Type} [Fintype K] (P Q : K → ℝ) : ℝ :=
  ∑ z, P z * (logTwo (P z) - logTwo (Q z))

/-- PDF p.19: centered classical information variance. -/
def classicalVariance {K : Type} [Fintype K] (P Q : K → ℝ) : ℝ :=
  ∑ z, P z * (logTwo (P z) - logTwo (Q z) - classicalMean P Q) ^ 2

/-- PDF p.19: third absolute central moment (the cube of the printed T). -/
def classicalThirdCentralMoment {K : Type} [Fintype K] (P Q : K → ℝ) : ℝ :=
  ∑ z, P z * |logTwo (P z) - logTwo (Q z) - classicalMean P Q| ^ 3

/-- PDF pp.2,18: products of classical weights, including the empty product. -/
def weightPower {K : Type} (n : ℕ) (P : K → ℝ) : (Fin n → K) → ℝ :=
  fun z => ∏ i, P (z i)

/-- Eq.(31), PDF p.18: CDF of the empirical mean of n independent log
likelihoods. Used with n>0 and support inclusion; zero-P atoms carry zero mass. -/
def empiricalMeanMass {K : Type} [Fintype K] (n : ℕ) (P Q : K → ℝ) (R : ℝ) : ℝ :=
  ∑ z : Fin n → K, if (∑ i : Fin n, (logTwo (P (z i)) - logTwo (Q (z i)))) / n ≤ R
    then weightPower n P z else 0

/-- PDF p.14: distinct spectral values, counting the kernel once. -/
def distinctEigenvalueSet (sigma : Mat I) : Finset ℝ :=
  if h : sigma.IsHermitian then Finset.univ.image h.eigenvalues else ∅

/-- PDF pp.13--14: number of distinct eigenvalues, not dimension or rank. -/
def distinctCount (sigma : Mat I) : ℕ := (distinctEigenvalueSet sigma).card

/-- PDF p.14: projection onto one whole eigenspace. -/
def eigenspaceProjector (sigma : Mat I) (v : ℝ) : Mat I :=
  cfc (fun x : ℝ => if x = v then (1 : ℝ) else 0) sigma

/-- PDF p.17: spread for an invertible PSD operator; only used there. -/
def spectralSpread (sigma : Mat I) : ℝ :=
  logTwo (sSup (distinctEigenvalueSet sigma : Set ℝ)) - logTwo (sInf (distinctEigenvalueSet sigma : Set ℝ))

/-- PDF pp.17--18: corrected positive bin count. Printed 2*ceil(lambda)=0 for
flat spectra. The proof requires l>0; use l=max(1,ceil(lambda)). For singular
sigma use the separately proved nu branch, without evaluating log(0). -/
def positiveSpectralFactor (sigma : Mat I) : ℕ :=
  if sigma.PosDef then min (2 * max 1 (Nat.ceil (spectralSpread sigma))) (distinctCount sigma)
  else distinctCount sigma

/-- PDF p.7: identity on A tensored with the reference on B. -/
def identityTensor (A : Type) [DecidableEq A] (sigma : Mat B) : Mat (A × B) :=
  fun i j => if i.1 = j.1 then sigma i.2 j.2 else 0

/-- PDF p.8, Definition 3: normalized reference optimization on B. -/
def positiveTraceSmoothedMinEntropy (e : ℝ) (rho : Mat (A × B)) : EReal :=
  sSup {h : EReal | ∃ sigma : Mat B, QAlgorithms.IsDensityMatrix sigma ∧
    h = -smoothedMaxRelativeEntropy e rho (identityTensor A sigma)}

/-- PDF p.8, Definition 5: optimized conditional testing entropy. -/
def conditionalTesting (e : ℝ) (rho : Mat (A × B)) : EReal :=
  sSup {h : EReal | ∃ sigma : Mat B, QAlgorithms.IsDensityMatrix sigma ∧
    h = -extendedTestingDivergence e rho (identityTensor A sigma)}

/-- PDF pp.7--8: unnormalized positive classical blocks, allowing zero labels. -/
def cqBlockMatrix (blocks : X → Mat B) : Mat (X × B) :=
  fun i j => if i.1 = j.1 then blocks i.1 i.2 j.2 else 0

/-- PDF pp.7--8: arbitrary many-to-one processing, constructed from input. -/
def processBlocks (f : X → Z) (blocks : X → Mat B) : Z → Mat B :=
  fun z => ∑ x, if f x = z then blocks x else 0

/-- PDF p.7: normalized CQ states expressed as positive blocks. -/
def NormalizedBlocks (blocks : X → Mat B) : Prop :=
  (∀ x, (blocks x).PosSemidef) ∧ (∑ x, (blocks x).trace.re) = 1

/-- PDF p.7: the actual B marginal. -/
def cqMarginal (blocks : X → Mat B) : Mat B := ∑ x, blocks x

/-- PDF p.9, Proposition 7: reorder XAB to A(XB). -/
def conditionOnClassical (blocks : X → Mat (A × B)) : Mat (A × (X × B)) :=
  fun i j => if i.2.1 = j.2.1 then blocks i.2.1 (i.1,i.2.2) (j.1,j.2.2) else 0

/-- PDF p.9, Proposition 7: reorder XAB to (XA)B. -/
def joinClassical (blocks : X → Mat (A × B)) : Mat ((X × A) × B) :=
  fun i j => if i.1.1 = j.1.1 then blocks i.1.1 (i.1.2,i.2) (j.1.2,j.2) else 0

/-- PDF p.9: positive-probability support size. -/
def labelCount (blocks : X → Mat B) : ℕ :=
  (Finset.univ.filter fun x => 0 < (blocks x).trace.re).card

/-- PDF pp.10--12: independent public seed of arbitrary finite size. -/
structure PublicRandomSeed where
  size : ℕ
  probability : Fin size → ℝ
  nonnegative : ∀ s, 0 ≤ probability s
  total : ∑ s, probability s = 1

/-- PDF p.10: arbitrary seeded hashes to a finite output alphabet. -/
structure Extractor (X : Type) where
  seed : PublicRandomSeed
  outputs : ℕ
  outputs_positive : 0 < outputs
  hash : Fin seed.size → X → Fin outputs

/-- PDF p.10: output retaining the public seed. -/
def extractionOutput (P : Extractor X) (blocks : X → Mat B) :
    Mat (Fin P.seed.size × (Fin P.outputs × B)) :=
  fun i j => if i.1 = j.1 ∧ i.2.1 = j.2.1 then
    (P.seed.probability i.1 : ℂ) *
      (∑ x, if P.hash i.1 x = i.2.1 then blocks x i.2.2 j.2.2 else 0) else 0

/-- PDF p.10: same seed cqMarginal, uniform output, one common reference. -/
def extractionIdeal (P : Extractor X) (sigma : Mat B) :
    Mat (Fin P.seed.size × (Fin P.outputs × B)) :=
  fun i j => if i.1 = j.1 ∧ i.2.1 = j.2.1 then
    ((P.seed.probability i.1 / P.outputs : ℝ) : ℂ) * sigma i.2.2 j.2.2 else 0

/-- PDF p.10, Definition 6: extractionSecurity optimized over one normalized sigma_B. -/
def extractionSecurity (P : Extractor X) (blocks : X → Mat B) : ℝ :=
  sInf {d : ℝ | ∃ sigma : Mat B, QAlgorithms.IsDensityMatrix sigma ∧
    d = purifiedDistance (extractionOutput P blocks) (extractionIdeal P sigma)}

/-- PDF p.10, Definition 6: maximal INTEGER length; arbitrary output cardinality.
The set is nonempty/bounded on normalized CQ sources with e<1. -/
def extractionLength (e : ℝ) (blocks : X → Mat B) : ℕ :=
  sSup {l : ℕ | ∃ P : Extractor X, (l : ℝ) ≤ logTwo P.outputs ∧ extractionSecurity P blocks ≤ e}

/-- PDF pp.11--12: seeded encoder and seed/message-dependent decoder POVM. -/
structure Compressor (X B : Type) [Fintype X] [Fintype B] [DecidableEq B] where
  seed : PublicRandomSeed
  messages : ℕ
  messages_positive : 0 < messages
  encode : Fin seed.size → X → Fin messages
  decode : Fin seed.size → Fin messages → X → Mat B
  positive : ∀ s m x, (decode s m x).PosSemidef
  complete : ∀ s m, ∑ x, decode s m x = 1

/-- PDF p.12, Definition 7: actual source/seed average error. -/
def compressionError (P : Compressor X B) (blocks : X → Mat B) : ℝ :=
  1 - ∑ s, P.seed.probability s * ∑ x, effectProb (blocks x) (P.decode s (P.encode s x) x)

/-- PDF p.12, Definition 7: minimal INTEGER length. -/
def compressionLength (e : ℝ) (blocks : X → Mat B) : ℕ :=
  sInf {m : ℕ | ∃ P : Compressor X B, logTwo P.messages ≤ (m : ℝ) ∧
    compressionError P blocks ≤ e}

/-- PDF p.20: independent CQ copies in the product classical basis. -/
def blocksPower (n : ℕ) (blocks : X → Mat B) : (Fin n → X) → Mat (Fin n → B) :=
  fun x i j => ∏ k, blocks (x k) (i k) (j k)

/-- PDF pp.7,20: conditional entropy, actual marginal. -/
def conditionalMean (blocks : X → Mat B) : ℝ :=
  -relativeMean (cqBlockMatrix blocks) (identityTensor X (cqMarginal blocks))

/-- PDF pp.19--20: centered conditional pair variance. -/
def cqConditionalVariance (blocks : X → Mat B) : ℝ :=
  centeredRelativeVariance (cqBlockMatrix blocks) (identityTensor X (cqMarginal blocks))

/-- PDF p.19: Gaussian approximation, including V=0. -/
def gaussianCenter (n : ℕ) (D V e : ℝ) : ℝ :=
  n * D + Real.sqrt ((n : ℝ) * V) * normalQuantile e

/-- PDF p.19: two-sided O(log n), constants before blocklength. -/
def LogarithmicRemainder (f : ℕ → EReal) (center : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0,
    ((center n - C * logTwo n : ℝ) : EReal) ≤ f n ∧
    f n ≤ ((center n + C * logTwo n : ℝ) : EReal)

/-- PDF p.19, (33): two-sided O(1). -/
def ConstantRemainder (f : ℕ → EReal) (center : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n ≥ n0,
    ((center n - C : ℝ) : EReal) ≤ f n ∧ f n ≤ ((center n + C : ℝ) : EReal)

example : negLog 0 = ⊤ := by simp [negLog]

example : logTwo 1 = 0 := by simp [logTwo]

example (P : I → ℝ) (x : Fin 0 → I) : weightPower 0 P x = 1 := by simp [weightPower]

example (rho sigma : Mat I) : centeredRelativeVariance rho sigma =
    QAlgorithms.Papers.Independent.Dependency50.P36.pairInformationVariance rho sigma := by
  rfl

example (blocks : X → Mat B) (i j : B) (x : X) :
    cqBlockMatrix blocks (x,i) (x,j) = blocks x i j := by simp [cqBlockMatrix]

example (blocks : X → Mat B) (a b : Fin 0 → B) (x : Fin 0 → X) :
    blocksPower 0 blocks x a b = 1 := by simp [blocksPower]

/-- PDF p.8: the actual isometry U tensor identity_B. -/
def liftIsometry (U : Matrix I A ℂ) : Matrix (I × B) (A × B) ℂ :=
  fun i j => U i.1 j.1 * (if i.2 = j.2 then (1 : ℂ) else 0)

/-- PDF p.14: NS P for product eigenbases, independently computed from the
product eigenvalues and the eigenbasisOverlapSquared of product eigenvectors. -/
def nsTensorP {rho sigma : Mat I} (r : PositiveSpectralPresentation rho) (s : PositiveSpectralPresentation sigma)
    (n : ℕ) (z : Fin n → I × I) : ℝ :=
  (∏ k, r.value (z k).1) * Complex.normSq
    (∑ a : Fin n → I, conj (∏ k, r.vectors (a k) (z k).1) *
      (∏ k, s.vectors (a k) (z k).2))

/-- PDF p.14: NS Q for the same product eigenbases. -/
def nsTensorQ {rho sigma : Mat I} (r : PositiveSpectralPresentation rho) (s : PositiveSpectralPresentation sigma)
    (n : ℕ) (z : Fin n → I × I) : ℝ :=
  (∏ k, s.value (z k).2) * Complex.normSq
    (∑ a : Fin n → I, conj (∏ k, r.vectors (a k) (z k).1) *
      (∏ k, s.vectors (a k) (z k).2))

/-- PDF p.21: spread after restricting a marginal to its positive support. -/
def supportedSpread (sigma : Mat I) : ℝ :=
  logTwo (sSup (distinctEigenvalueSet sigma : Set ℝ)) - logTwo (QAlgorithms.minPositiveEigenvalue sigma)

/-- PDF p.21: positive-bin correction, including a flat nonzero marginal. -/
def finiteBins (n : ℕ) (sigma : Mat I) : ℕ :=
  max 1 (Nat.ceil ((n : ℝ) * supportedSpread sigma))

/-- PDF p.21: lower/upper optimization over a half-open real interval, in EReal. -/
def intervalSup (a b : ℝ) (f : ℝ → ℝ) : EReal :=
  sSup {v : EReal | ∃ x : ℝ, a ≤ x ∧ x < b ∧ v = (f x : EReal)}

/-- PDF p.21: infimum counterpart, retaining infinite limiting values. -/
def intervalInf (a b : ℝ) (f : ℝ → ℝ) : EReal :=
  sInf {v : EReal | ∃ x : ℝ, a ≤ x ∧ x < b ∧ v = (f x : EReal)}

/-- Lemma 18, PDF p.22: generalized inverse with extended endpoints. -/
def monotoneInverse (g : ℝ → ℝ) (e : ℝ) : EReal :=
  sSup {r : EReal | ∃ R : ℝ, g R ≤ e ∧ r = (R : EReal)}

/-- PDF p.22: optimization over ALL real threshold sequences. -/
def inverseRate (g : ℕ → ℝ → ℝ) (e : ℝ) (strict : Bool) : EReal :=
  sSup {v : EReal | ∃ a : ℕ → ℝ,
    (if strict then liminf (fun n => (a n : EReal)) atTop < (e : EReal)
     else limsup (fun n => (a n : EReal)) atTop ≤ (e : EReal)) ∧
    v = liminf (fun n => monotoneInverse (g n) (a n)) atTop}

/-- PDF p.22: threshold spectrum with its exact limsup/non-strict or liminf/strict constraint. -/
def thresholdRate (g : ℕ → ℝ → ℝ) (e : ℝ) (strict : Bool) : EReal :=
  sSup {r : EReal | ∃ R : ℝ,
    (if strict then liminf (fun n => (g n R : EReal)) atTop < (e : EReal)
     else limsup (fun n => (g n R : EReal)) atTop ≤ (e : EReal)) ∧ r = (R : EReal)}

/-- Appendix A, PDF pp.24--25: explicit NS probabilities, total P=1. -/
def pauliP (p : ℝ) : Fin 4 → ℝ := ![p/2, p/2, (1-p)/2, (1-p)/2]

/-- Appendix A, PDF pp.24--25: reference weights, total Q=2(p^2+(1-p)^2)
on the nontrivial NS support. Remaining zero-P entries are irrelevant to Ds. -/
def pauliQ (p : ℝ) : Fin 4 → ℝ := ![p^2, p^2, (1-p)^2, (1-p)^2]

/-- Appendix A, PDF p.25: F(k-1;n,p), with F(-1)=0 at k=0. -/
def binomialBelow (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, if j ≤ n then (Nat.choose n j : ℝ) * p^j * (1-p)^(n-j) else 0

/-- Appendix A, PDF p.25: maximum k in 0,...,n with F(k-1)<=epsilon.
For 0<=epsilon<1 the set contains 0 and larger k>n never qualify. -/
def binomialCutoff (n : ℕ) (p e : ℝ) : ℕ :=
  ((Finset.range (n+1)).filter fun k => binomialBelow n p k ≤ e).sup id

/-- PDF pp.21--23: arbitrary finite pairs; slot k is source blocklength k+1.
Dimensions can vary and no iid, support or variance property is built in. -/
structure PairSequence where
  Index : ℕ → Type
  finite : ∀ k, Fintype (Index k)
  decidable : ∀ k, DecidableEq (Index k)
  rho : ∀ k, Mat (Index k)
  sigma : ∀ k, Mat (Index k)

attribute [instance] PairSequence.finite PairSequence.decidable

/-- PDF p.22: both sequences consist of normalized quantum states. -/
def StateSequence (S : PairSequence) : Prop :=
  ∀ k, QAlgorithms.IsDensityMatrix (S.rho k) ∧ QAlgorithms.IsDensityMatrix (S.sigma k)

/-- PDF pp.22--23: the two different asymptotic error constraints. -/
def ErrorConstraint (a : ℕ → ℝ) (e : ℝ) (strict : Bool) : Prop :=
  if strict then liminf (fun n => (a n : EReal)) atTop < (e : EReal)
  else limsup (fun n => (a n : EReal)) atTop ≤ (e : EReal)

/-- PDF p.22: source thresholds are 2^((k+1)R), in bits. -/
def quantumSpectrumRate (S : PairSequence) (e : ℝ) (strict : Bool) : EReal :=
  thresholdRate (fun k R => spectrumMass (S.rho k) (S.sigma k) ((k+1 : ℕ)*R)) e strict

/-- PDF pp.22--23: one-shot rates, optimizing all [0,1]-valued error sequences. -/
def optimizedEntropySequenceRate (H : ℕ → ℝ → EReal) (e : ℝ) (strict : Bool) : EReal :=
  sSup {v : EReal | ∃ a : ℕ → ℝ, (∀ k, 0 ≤ a k ∧ a k ≤ 1) ∧
    ErrorConstraint a e strict ∧
    v = liminf (fun k => (((1 : ℝ)/(k+1 : ℕ) : ℝ) : EReal) * H k (a k)) atTop}

/-- PDF p.23: one genuine effect at each blocklength, without a free rate variable. -/
def VaryingRegisterTests (S : PairSequence) :=
  {Q : ∀ k, Mat (S.Index k) // ∀ k, QAlgorithms.IsEffect (Q k)}

/-- PDF p.23: actual type-I error of an effect. -/
def testError (S : PairSequence) (Q : VaryingRegisterTests S) (k : ℕ) : ℝ :=
  effectProb (S.rho k) (1 - Q.val k)

/-- PDF p.23: actual type-II exponent, including zero type-II error. -/
def testRate (S : PairSequence) (Q : VaryingRegisterTests S) : EReal :=
  liminf (fun k => (((1 : ℝ)/(k+1 : ℕ) : ℝ) : EReal) *
    negLog (effectProb (S.sigma k) (Q.val k))) atTop

/-- PDF p.23: operational B and the strict-error sup form of B-dagger. -/
def operationalTestingRate (S : PairSequence) (e : ℝ) (strict : Bool) : EReal :=
  sSup {v : EReal | ∃ Q : VaryingRegisterTests S,
    ErrorConstraint (testError S Q) e strict ∧ v = testRate S Q}

/-- PDF p.23: universal converse threshold defining B-dagger. -/
def testingConverseRate (S : PairSequence) (e : ℝ) : EReal :=
  sInf {r : EReal | ∃ R : ℝ, r = (R : EReal) ∧
    ∀ Q : VaryingRegisterTests S, (R : EReal) ≤ testRate S Q →
      (e : EReal) ≤ liminf (fun k => (testError S Q k : EReal)) atTop}

/-- PDF p.23: the source's sufficient polynomial spectral condition. The
positive-eigenvalue alternative is on the supported restriction and explicitly
retains support inclusion. Constants and thresholds precede k. -/
def SpectralControl (S : PairSequence) : Prop :=
  (∃ C : ℝ, 0 < C ∧ ∃ d k0 : ℕ, ∀ k ≥ k0,
    (distinctCount (S.sigma k) : ℝ) ≤ C * (k+1 : ℕ)^d) ∨
  (∃ C : ℝ, 0 < C ∧ ∃ d k0 : ℕ, ∀ k ≥ k0,
    SupportIncluded (S.rho k) (S.sigma k) ∧
    0 < QAlgorithms.minPositiveEigenvalue (S.sigma k) ∧
    -logTwo (QAlgorithms.minPositiveEigenvalue (S.sigma k)) ≤ C * (k+1 : ℕ)^d)

/-- PDF p.23: classical NS distributions as diagonal matrices; testing arbitrary
effects on diagonal states equals randomized classical testing. -/
def nsSequence (S : PairSequence) (r : ∀ k, PositiveSpectralPresentation (S.rho k))
    (s : ∀ k, PositiveSpectralPresentation (S.sigma k)) : PairSequence where
  Index k := S.Index k × S.Index k
  finite _ := inferInstance
  decidable _ := Classical.decEq _
  rho k := Matrix.diagonal (fun z => (nsProbability (r k) (s k) z : ℂ))
  sigma k := Matrix.diagonal (fun z => (nsReferenceWeight (r k) (s k) z : ℂ))

/-- PDF p.23: explicit endpoint continuation for smoothing parameter one,
by its monotone left limit, rather than a finite real default. -/
def smoothMaxEndpoint (a : ℝ) (rho sigma : Mat I) : EReal :=
  if a < 1 then smoothedMaxRelativeEntropy a rho sigma
  else sInf {v : EReal | ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧ v = smoothedMaxRelativeEntropy b rho sigma}

/-- Sanity: no seed-dependent choice of the reference in the ideal state. -/
example (P : Extractor X) (sigma : Mat B) (s : Fin P.seed.size)
    (z : Fin P.outputs) (i j : B) :
    extractionIdeal P sigma (s,(z,i)) (s,(z,j)) =
      ((P.seed.probability s / P.outputs : ℝ) : ℂ) * sigma i j := by
  simp [extractionIdeal]

example (n : ℕ) (p : ℝ) : binomialBelow n p 0 = 0 := by simp [binomialBelow]

example (g : ℕ → ℝ → ℝ) (e : ℝ) :
    ErrorConstraint (fun n => g n 0) e false =
      (limsup (fun n => (g n 0 : EReal)) atTop ≤ (e : EReal)) := rfl

/-- Sanity: the NS adapter preserves the specified column eigenvector. -/
example {rho : Mat I} (r : PositiveSpectralPresentation rho) (x i : I) :
    (nsSpectralPresentation r).vector x i = r.vectors i x := by
  rfl

end QAlgorithms.Papers.Independent.Advance50.P02


