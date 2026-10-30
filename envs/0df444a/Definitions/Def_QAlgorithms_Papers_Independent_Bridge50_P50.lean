-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P50
-- name    : QAlgorithms_Papers_Independent_Bridge50_P50
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T09:22:22.527568+00:00
-- url     : https://prove2.me/theorems/8828a153-da36-4057-9e6c-ca89f66acbd9
-- title:
--   Definitions for Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels
-- statement:
--   The objects the formalized statements of *Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels* (arXiv:1308.6503) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `normalizedTestingDivergence`: PDF p.5, (15): NORMALIZED testing divergence, with infinity at zero type-II error. Only e in (0,1) and states are used; there the feasible set is nonempty and bounded.
--   - `ClosedStateSet`: PDF pp.3–4,6: nonempty closed sets of states. Nonemptiness is the source's tacit optimization convention and is needed for peripheral decompositions.
--   - `radiusAt`: PDF p.6: extended radius about sigma. Empty suprema have their extended-order meaning.
--   - `divergenceRadius`: PDF p.6, (16): infimum over comparison STATES, before the codeword supremum.
--   - `centers`: PDF p.12: the SET of all minimizers, without assuming existence or uniqueness.
--   - `divergenceCenter`: PDF pp.6,13: select the unique center when it exists. The fallback zero is unused under ClosedStateSet; its exclusion is a theorem conclusion, not an assumed optimizer.
--   - `peripheralAt`: PDF p.12: peripheral points relative to ANY minimizing state, before uniqueness.
--   - `peripheralStates`: PDF p.6, (17): peripheral set for the selected center.
--   - `measuresOn`: PDF pp.3–4: Borel probability measures carried by S, represented on the ambient matrix space. On closed S this is equivalent to measures on the subtype S.
--   - `stateBarycenter`: PDF p.4, (7): actual Bochner barycenter; integrable on the compact state space.
--   - `borelHolevoInformation`: PDF pp.6,14, (18),(50): extended integral avoids a default real integral at infinity.
--   - `peripheralMeasures`: PDF p.7, (19): probability measures carried by Gamma whose barycenter IS the center.
--   - `MeasureConvex`: PDF p.7: convexity in the space of probability measures, expressed by normalized nonnegative mixtures. This avoids pretending that ProbabilityMeasure is a real vector space.
--   - `FiniteSupport`: PDF pp.7–8: a discrete probability measure supported by at most k points of A.
--   - `conditionalVariance`: PDF pp.7–8, (20): conditional variance. The center dominates every state in S; on peripheral measures this is a bounded continuous, hence integrable, function.
--   - `vMin`: PDF p.8, (21): minimum peripheral variance. Relevant sets are nonempty and compact.
--   - `vMax`: PDF p.8, (22): maximum peripheral variance.
--   - `vEpsilon`: PDF p.8, (25): epsilon=1/2 belongs to the minimum branch.
--   - `capacityBits`: PDF p.8: finite divergence radius in bits. Its finiteness on the stated domain follows by comparison with the maximally mixed state; no arbitrary extended value is silently optimized.
--   - `PeripheralEnsemble`: PDF p.7, (19), discrete specialization: exactly Pi membership, including the barycenter condition. Zero-weight labels are immaterial.
--   - `cqJointState`: PDF p.15: classical-quantum joint block state, with a genuine finite classical register.
--   - `referenceState`: PDF p.15: block-diagonal product of the classical marginal and quantum barycenter.
--   - `tensorWord`: PDF p.4: tensor product with the indicated ordered factors.
--   - `productSet`: PDF p.5: all product outputs with factors in S.
--   - `testingRadius`: PDF p.9, (27): hypothesis-testing radius; comparison state chosen first.
--   - `CqTransmissionCode`: PDF pp.4–5: a physical classical-quantum code, uniform nonempty messages and joint POVM.
--   - `cqAverageError`: PDF p.4, (10): average error, not maximum message error.
--   - `cqOptimalMessages`: PDF p.5, (12): all actual codes. On a nonempty state-valued channel and 0≤e<1, the feasible message sizes are nonempty and bounded by dim(output)/(1-e).
--   - `cqBlockChannel`: PDF p.5: actual n memoryless c-q channel uses.
--   - `blockLog`: PDF p.5: logarithm of optimal block message size.
--   - `cqOperationalCapacity`: PDF p.1, (1): operational capacity via lower limits. Theorem 4 supplies genuine convergence, so both lower limits are actual limits on the stated channel domain.
--   - `secondOrder`: PDF p.8: the actual second-order expression, evaluated on the closure of the image.
--   - `cqRemainder`: PDF p.8: K is the actual difference, not a supplied remainder parameter.
--   - `ErrorEnvelope`: PDF pp.8–24: positive blocklength error envelope. Early terms need not be in (0,1).
--   - `empiricalInformation`: PDF p.17: conditional empirical relative entropy.
--   - `empiricalVariance`: PDF p.17: conditional empirical variance.
--   - `empiricalBarycenter`: PDF p.19: empirical barycenter. Only positive n is asserted below.
--   - `peripheralDistance`: PDF p.19, (79): distance to Gamma. Relevant Gamma is nonempty compact.
--   - `OmegaOne`: PDF p.19, (79): first closeness condition.
--   - `OmegaTwo`: PDF p.19, (80): second closeness condition. The good set is their INTERSECTION.
--   - `NetConditions`: PDF p.18, (76)–(77): all THREE net requirements on the same witness tau.
--   - `auxiliaryState`: PDF p.19, (78): the constructed auxiliary state, fixed before the input sequence.
--   - `NSSpectralData`: PDF p.25, (B1): chosen spectral data. Raw data allow forming a product basis explicitly; validity is separately pinned by IsSpectral, never by arbitrary laws.
--   - `IsSpectral`: PDF p.25: an orthonormal eigenbasis and the actual spectral reconstruction.
--   - `nsP`: PDF p.25, (B1): first NS distribution in the specified bases.
--   - `nsQ`: PDF p.25, (B1): second NS distribution.
--   - `productSpectral`: PDF p.26, (B3): product eigenvalues AND product eigenvectors, not an independently chosen basis in a degenerate tensor eigenspace.
--   - `nsClassicalD`: PDF p.25: classical D with infinite support-violation value.
--   - `classicalV`: PDF p.25: classical variance, on the support-dominated domain.
--   - `classicalT`: PDF p.26, (B8): the classical centered absolute third moment.
--   - `canonicalSpectral`: PDF pp.25–26: a canonical choice of eigenbasis, used only for basis-invariant moments.
--   - `thirdMoment`: PDF p.26, (B8): NS third moment. This is NOT a noncommutative absolute cube.
--   - `ensembleVariance`: PDF p.28: weighted variance at the actual barycenter; zero-weight summands contribute zero.
--   - `ensembleThird`: PDF p.28: weighted centered NS third moment at the actual barycenter.
--   - `finiteHolevoInformation`: PDF p.14: finite information I(P), with zero-probability blocks omitted by their weights.
--   - `restrictedInf`: PDF p.22: infimum on a subset of Theta_1, so no global extension of f is assumed.
--   - `pauliFamily`: Example 1, PDF p.10: Pauli matrices in the accepted Bool computational basis.
--   - `pauliMap`: Example 1, PDF p.10: the actual Pauli channel, not an unconstrained invariant tuple.
--   - `pauliImage`: Example 1, PDF p.10: image of all qubit input states.
--   - `pauliContractions`: Example 1, PDF p.10: the three Bloch contraction factors of the Pauli map.
--   - `bscCrossover`: Example 1, PDF p.10: comparison BSC is constructed from the longest Bloch semiaxis.
--   - `bscVariance`: Example 1, PDF p.10: classical BSC variance, zero at deterministic endpoints.
--   - `ensembleSize`: Example 1, PDF p.10: support cardinality of a finite ensemble, ignoring repeated labels and zero-weight entries as a probability measure does.
--   - `EnsembleOn`: Example 1, PDF p.10: all positive-weight states belong to the stated channel image.
--   - `MinimalAchieving`: Example 1, PDF p.10: minimality among ALL capacity-achieving ensembles in the image.
--   - `pauliQuantumBlockLog`: Example 1, PDF p.10: unrestricted n-use quantum code, including entangled inputs. The block channel is the accepted actual matrix-unit tensor extension.
--   - `pauliQuantumCapacity`: Example 1, PDF p.10, and (1), PDF p.1: unrestricted operational classical capacity.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, https://arxiv.org/abs/1308.6503v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36

/-! Paper-local interfaces for arXiv:1308.6503v3. All logarithms below are in bits. Exact primitives are imported from the pinned accepted library.
Matrix topology is the usual finite-dimensional topology, equal to the trace-distance topology.
Theorems concern normalized density matrices. No frozen declaration is modified. -/

noncomputable section

open scoped Topology BigOperators ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator
open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P50

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; these names do not create local declarations.
open QAlgorithms.Papers.Independent.Information100.P63 (Mat logTwo testingBeta normalCDF normalQuantile)
open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage)
open QAlgorithms.Papers.Independent.Information100.P69 (entropy)
open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)
open QAlgorithms.Papers.Independent.Dependency50.P36 (pairInformationVariance)
open QAlgorithms (vnEntropy traceDistance minEigenvalue)

/-- PDF pp.3–4: the Borel sigma-algebra for the usual finite-dimensional matrix topology,
which agrees with the source trace-distance topology on Hermitian matrices. -/
local instance matrixBorelMeasurable (I : Type*) : MeasurableSpace (Mat I) := borel _

/-- PDF pp.3–4: the measurable matrix structure above is exactly Borel. -/
local instance matrixBorelSpace (I : Type*) : BorelSpace (Mat I) := ⟨rfl⟩

/-- PDF p.5, (15): NORMALIZED testing divergence, with infinity at zero type-II error.
Only e in (0,1) and states are used; there the feasible set is nonempty and bounded. -/
def normalizedTestingDivergence {I : Type*} [Fintype I] [DecidableEq I]
    (e : ℝ) (rho sigma : Mat I) : ℝ≥0∞ :=
  let b := testingBeta e rho sigma
  if b = 0 then ⊤ else ENNReal.ofReal (-logTwo (b / (1-e)))

/-- PDF pp.3–4,6: nonempty closed sets of states. Nonemptiness is the source's tacit
optimization convention and is needed for peripheral decompositions. -/
def ClosedStateSet {I : Type*} [Fintype I] (S : Set (Mat I)) : Prop :=
  S.Nonempty ∧ IsClosed S ∧ ∀ rho ∈ S, QAlgorithms.IsDensityMatrix rho

/-- PDF p.6: extended radius about sigma. Empty suprema have their extended-order meaning. -/
def radiusAt {I : Type*} [Fintype I] [DecidableEq I]
    (S : Set (Mat I)) (sigma : Mat I) : ℝ≥0∞ :=
  ⨆ rho : S, entropy rho.val sigma

/-- PDF p.6, (16): infimum over comparison STATES, before the codeword supremum. -/
def divergenceRadius {I : Type*} [Fintype I] [DecidableEq I] (S : Set (Mat I)) : ℝ≥0∞ :=
  ⨅ sigma : {A : Mat I // QAlgorithms.IsDensityMatrix A}, radiusAt S sigma.val

/-- PDF p.12: the SET of all minimizers, without assuming existence or uniqueness. -/
def centers {I : Type*} [Fintype I] [DecidableEq I] (S : Set (Mat I)) : Set (Mat I) :=
  {sigma | QAlgorithms.IsDensityMatrix sigma ∧ radiusAt S sigma = divergenceRadius S}

/-- PDF pp.6,13: select the unique center when it exists. The fallback zero is unused
under ClosedStateSet; its exclusion is a theorem conclusion, not an assumed optimizer. -/
def divergenceCenter {I : Type*} [Fintype I] [DecidableEq I] (S : Set (Mat I)) : Mat I :=
  if h : (centers S).Nonempty then h.choose else 0

/-- PDF p.12: peripheral points relative to ANY minimizing state, before uniqueness. -/
def peripheralAt {I : Type*} [Fintype I] [DecidableEq I]
    (S : Set (Mat I)) (sigma : Mat I) : Set (Mat I) :=
  {rho | rho ∈ S ∧ entropy rho sigma = radiusAt S sigma}

/-- PDF p.6, (17): peripheral set for the selected center. -/
def peripheralStates {I : Type*} [Fintype I] [DecidableEq I] (S : Set (Mat I)) : Set (Mat I) :=
  peripheralAt S (divergenceCenter S)

/-- PDF pp.3–4: Borel probability measures carried by S, represented on the ambient
matrix space. On closed S this is equivalent to measures on the subtype S. -/
def measuresOn {I : Type*} [Fintype I] (S : Set (Mat I)) : Set (ProbabilityMeasure (Mat I)) :=
  {P | (P : Measure (Mat I)) S = 1}

/-- PDF p.4, (7): actual Bochner barycenter; integrable on the compact state space. -/
def stateBarycenter {I : Type*} [Fintype I] (P : ProbabilityMeasure (Mat I)) : Mat I :=
  ∫ rho, rho ∂(P : Measure (Mat I))

/-- PDF pp.6,14, (18),(50): extended integral avoids a default real integral at infinity. -/
def borelHolevoInformation {I : Type*} [Fintype I] [DecidableEq I]
    (P : ProbabilityMeasure (Mat I)) : ℝ≥0∞ :=
  ∫⁻ rho, entropy rho (stateBarycenter P) ∂(P : Measure (Mat I))

/-- PDF p.7, (19): probability measures carried by Gamma whose barycenter IS the center. -/
def peripheralMeasures {I : Type*} [Fintype I] [DecidableEq I]
    (S : Set (Mat I)) : Set (ProbabilityMeasure (Mat I)) :=
  {P | P ∈ measuresOn (peripheralStates S) ∧ stateBarycenter P = divergenceCenter S}

/-- PDF p.7: convexity in the space of probability measures, expressed by normalized
nonnegative mixtures. This avoids pretending that ProbabilityMeasure is a real vector space. -/
def MeasureConvex {X : Type*} [MeasurableSpace X]
    (A : Set (ProbabilityMeasure X)) : Prop :=
  ∀ P ∈ A, ∀ Q ∈ A, ∀ a b : ℝ≥0∞, a+b=1 →
    ∃ R ∈ A, (R : Measure X) = a • (P : Measure X) + b • (Q : Measure X)

/-- PDF pp.7–8: a discrete probability measure supported by at most k points of A. -/
def FiniteSupport {I : Type*} [Fintype I] (P : ProbabilityMeasure (Mat I))
    (k : ℕ) (A : Set (Mat I)) : Prop :=
  ∃ F : Finset (Mat I), F.card ≤ k ∧ (↑F : Set (Mat I)) ⊆ A ∧
    (P : Measure (Mat I)) (↑F : Set (Mat I)) = 1

/-- PDF pp.7–8, (20): conditional variance. The center dominates every state in S;
on peripheral measures this is a bounded continuous, hence integrable, function. -/
def conditionalVariance {I : Type*} [Fintype I] [DecidableEq I]
    (P : ProbabilityMeasure (Mat I)) (sigma : Mat I) : ℝ :=
  ∫ rho, pairInformationVariance rho sigma ∂(P : Measure (Mat I))

/-- PDF p.8, (21): minimum peripheral variance. Relevant sets are nonempty and compact. -/
def vMin {I : Type*} [Fintype I] [DecidableEq I] (S : Set (Mat I)) : ℝ :=
  sInf {v | ∃ P ∈ peripheralMeasures S, v = conditionalVariance P (divergenceCenter S)}

/-- PDF p.8, (22): maximum peripheral variance. -/
def vMax {I : Type*} [Fintype I] [DecidableEq I] (S : Set (Mat I)) : ℝ :=
  sSup {v | ∃ P ∈ peripheralMeasures S, v = conditionalVariance P (divergenceCenter S)}

/-- PDF p.8, (25): epsilon=1/2 belongs to the minimum branch. -/
def vEpsilon {I : Type*} [Fintype I] [DecidableEq I] (S : Set (Mat I)) (e : ℝ) : ℝ :=
  if e ≤ 1/2 then vMin S else vMax S

/-- PDF p.8: finite divergence radius in bits. Its finiteness on the stated domain follows
by comparison with the maximally mixed state; no arbitrary extended value is silently optimized. -/
def capacityBits {I : Type*} [Fintype I] [DecidableEq I] (S : Set (Mat I)) : ℝ :=
  (divergenceRadius S).toReal

/-- PDF p.7, (19), discrete specialization: exactly Pi membership, including the barycenter
condition. Zero-weight labels are immaterial. -/
def PeripheralEnsemble {I : Type} [Fintype I] [DecidableEq I]
    (S : Set (Mat I)) (E : Ensemble I) : Prop :=
  ensembleAverage E = divergenceCenter S ∧ ∀ i, 0 < E.prob i → E.state i ∈ peripheralStates S

/-- PDF p.15: classical-quantum joint block state, with a genuine finite classical register. -/
def cqJointState {I : Type} [Fintype I] (E : Ensemble I) : Mat (Fin E.size × I) :=
  fun a b => if a.1 = b.1 then (E.prob a.1 : ℂ) * E.state a.1 a.2 b.2 else 0

/-- PDF p.15: block-diagonal product of the classical marginal and quantum barycenter. -/
def referenceState {I : Type} [Fintype I] (E : Ensemble I) : Mat (Fin E.size × I) :=
  fun a b => if a.1 = b.1 then (E.prob a.1 : ℂ) * ensembleAverage E a.2 b.2 else 0

/-- PDF p.4: tensor product with the indicated ordered factors. -/
def tensorWord {I : Type*} {n : ℕ} (rho : Fin n → Mat I) : Mat (Fin n → I) :=
  fun a b => ∏ i, rho i (a i) (b i)

/-- PDF p.5: all product outputs with factors in S. -/
def productSet {I : Type*} (S : Set (Mat I)) (n : ℕ) : Set (Mat (Fin n → I)) :=
  {A | ∃ rho : Fin n → Mat I, (∀ i, rho i ∈ S) ∧ A = tensorWord rho}

/-- PDF p.9, (27): hypothesis-testing radius; comparison state chosen first. -/
def testingRadius {I : Type*} [Fintype I] [DecidableEq I]
    (S : Set (Mat I)) (e : ℝ) : ℝ≥0∞ :=
  ⨅ sigma : {A : Mat I // QAlgorithms.IsDensityMatrix A},
    ⨆ rho : S, normalizedTestingDivergence e rho.val sigma.val

/-- PDF pp.4–5: a physical classical-quantum code, uniform nonempty messages and joint POVM. -/
structure CqTransmissionCode (X I : Type*) [Fintype I] [DecidableEq I] (M : ℕ) where
  positive : 0 < M
  encode : Fin M → X
  decode : Fin M → Mat I
  positiveDecode : ∀ m, (decode m).PosSemidef
  complete : ∑ m, decode m = 1

/-- PDF p.4, (10): average error, not maximum message error. -/
def cqAverageError {X I : Type*} [Fintype I] [DecidableEq I] {M : ℕ}
    (W : X → Mat I) (C : CqTransmissionCode X I M) : ℝ :=
  1 - (M : ℝ)⁻¹ * ∑ m, QAlgorithms.effectProb (C.decode m) (W (C.encode m))

/-- PDF p.5, (12): all actual codes. On a nonempty state-valued channel and 0≤e<1,
the feasible message sizes are nonempty and bounded by dim(output)/(1-e). -/
def cqOptimalMessages {X I : Type*} [Fintype I] [DecidableEq I]
    (W : X → Mat I) (e : ℝ) : ℕ := sSup {M | ∃ C : CqTransmissionCode X I M, cqAverageError W C ≤ e}

/-- PDF p.5: actual n memoryless c-q channel uses. -/
def cqBlockChannel {X I : Type*} (W : X → Mat I) (n : ℕ) : (Fin n → X) → Mat (Fin n → I) :=
  fun x => tensorWord (fun i => W (x i))

/-- PDF p.5: logarithm of optimal block message size. -/
def blockLog {X I : Type*} [Fintype I] [DecidableEq I]
    (W : X → Mat I) (e : ℝ) (n : ℕ) : ℝ := logTwo (cqOptimalMessages (cqBlockChannel W n) e)

/-- PDF p.1, (1): operational capacity via lower limits. Theorem 4 supplies genuine
convergence, so both lower limits are actual limits on the stated channel domain. -/
def cqOperationalCapacity {X I : Type*} [Fintype I] [DecidableEq I] (W : X → Mat I) : ℝ :=
  Filter.liminf (fun e : ℝ => Filter.liminf (fun n : ℕ => blockLog W e n / n) atTop)
    (nhdsWithin 0 (Set.Ioi 0))

/-- PDF p.8: the actual second-order expression, evaluated on the closure of the image. -/
def secondOrder {I : Type*} [Fintype I] [DecidableEq I]
    (S : Set (Mat I)) (e : ℝ) (n : ℕ) : ℝ :=
  n * capacityBits S + Real.sqrt (n * vEpsilon S e) * normalQuantile e

/-- PDF p.8: K is the actual difference, not a supplied remainder parameter. -/
def cqRemainder {X I : Type*} [Fintype I] [DecidableEq I]
    (W : X → Mat I) (e : ℝ) (n : ℕ) : ℝ :=
  blockLog W e n - secondOrder (closure (Set.range W)) e n

/-- PDF pp.8–24: positive blocklength error envelope. Early terms need not be in (0,1). -/
def ErrorEnvelope (e : ℝ) (es : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → |es n-e| ≤ 1 / Real.sqrt n

/-- PDF p.17: conditional empirical relative entropy. -/
def empiricalInformation {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (rho : Fin n → Mat I) (sigma : Mat I) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, (entropy (rho i) sigma).toReal

/-- PDF p.17: conditional empirical variance. -/
def empiricalVariance {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (rho : Fin n → Mat I) (sigma : Mat I) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, pairInformationVariance (rho i) sigma

/-- PDF p.19: empirical barycenter. Only positive n is asserted below. -/
def empiricalBarycenter {I : Type*} [Fintype I] {n : ℕ} (rho : Fin n → Mat I) : Mat I :=
  (n : ℝ)⁻¹ • ∑ i, rho i

/-- PDF p.19, (79): distance to Gamma. Relevant Gamma is nonempty compact. -/
def peripheralDistance {I : Type*} [Fintype I] [DecidableEq I]
    (S : Set (Mat I)) (rho : Mat I) : ℝ :=
  sInf {r | ∃ tau ∈ peripheralStates S, r = traceDistance rho tau}

/-- PDF p.19, (79): first closeness condition. -/
def OmegaOne {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (S : Set (Mat I)) (nu : ℝ) (rho : Fin n → Mat I) : Prop :=
  (n : ℝ)⁻¹ * ∑ i, peripheralDistance S (rho i) ≤ nu

/-- PDF p.19, (80): second closeness condition. The good set is their INTERSECTION. -/
def OmegaTwo {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (S : Set (Mat I)) (nu : ℝ) (rho : Fin n → Mat I) : Prop :=
  traceDistance (empiricalBarycenter rho) (divergenceCenter S) ≤ nu

/-- PDF p.18, (76)–(77): all THREE net requirements on the same witness tau. -/
def NetConditions {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (g : ℝ) (G : Finset (Mat I)) : Prop :=
  (∀ tau ∈ G, QAlgorithms.IsDensityMatrix tau) ∧
  (G.card : ℝ) ≤ (5/g)^(2*(Fintype.card I)^2) * (2*(Fintype.card I : ℝ)/g+2)^(Fintype.card I-1) ∧
  ∀ rho : Mat I, QAlgorithms.IsDensityMatrix rho → ∃ tau ∈ G,
    traceDistance rho tau ≤ g ∧
    entropy rho tau ≤ ENNReal.ofReal (g*4*(2*(Fintype.card I : ℝ)+1)) ∧
    g/(2*(Fintype.card I : ℝ)+g) ≤ minEigenvalue tau

/-- PDF p.19, (78): the constructed auxiliary state, fixed before the input sequence. -/
def auxiliaryState {I : Type*} [Fintype I] [DecidableEq I]
    (S : Set (Mat I)) (G : Finset (Mat I)) (n : ℕ) : Mat (Fin n → I) :=
  (1/2 : ℝ) • tensorWord (fun _ => divergenceCenter S) +
    (1/(2*(G.card : ℝ))) • ∑ tau ∈ G, tensorWord (fun _ => tau)

/-- PDF p.25, (B1): chosen spectral data. Raw data allow forming a product basis
explicitly; validity is separately pinned by IsSpectral, never by arbitrary laws. -/
structure NSSpectralData (I : Type*) where
  value : I → ℝ
  vector : I → I → ℂ

/-- PDF p.25: an orthonormal eigenbasis and the actual spectral reconstruction. -/
def IsSpectral {I : Type*} [Fintype I] [DecidableEq I]
    (A : Mat I) (s : NSSpectralData I) : Prop :=
  (∀ i, 0 ≤ s.value i) ∧
  (∀ i j, (∑ k, conj (s.vector i k) * s.vector j k) = if i=j then 1 else 0) ∧
  A = fun k l => ∑ i, (s.value i : ℂ) * s.vector i k * conj (s.vector i l)

/-- PDF p.25, (B1): first NS distribution in the specified bases. -/
def nsP {I : Type*} [Fintype I] (r s : NSSpectralData I) (a : I × I) : ℝ :=
  r.value a.1 * Complex.normSq (∑ k, conj (r.vector a.1 k) * s.vector a.2 k)

/-- PDF p.25, (B1): second NS distribution. -/
def nsQ {I : Type*} [Fintype I] (r s : NSSpectralData I) (a : I × I) : ℝ :=
  s.value a.2 * Complex.normSq (∑ k, conj (r.vector a.1 k) * s.vector a.2 k)

/-- PDF p.26, (B3): product eigenvalues AND product eigenvectors, not an independently
chosen basis in a degenerate tensor eigenspace. -/
def productSpectral {I J : Type*} (r : NSSpectralData I) (s : NSSpectralData J) : NSSpectralData (I × J) :=
  ⟨fun a => r.value a.1 * s.value a.2,
   fun a b => r.vector a.1 b.1 * s.vector a.2 b.2⟩

/-- PDF p.25: classical D with infinite support-violation value. -/
def nsClassicalD {A : Type*} [Fintype A] (P Q : A → ℝ) : ℝ≥0∞ :=
  if ∀ a, Q a = 0 → P a = 0 then ENNReal.ofReal (∑ a, P a * logTwo (P a / Q a)) else ⊤

/-- PDF p.25: classical variance, on the support-dominated domain. -/
def classicalV {A : Type*} [Fintype A] (P Q : A → ℝ) : ℝ :=
  ∑ a, P a * (logTwo (P a/Q a) - (nsClassicalD P Q).toReal)^2

/-- PDF p.26, (B8): the classical centered absolute third moment. -/
def classicalT {A : Type*} [Fintype A] (P Q : A → ℝ) : ℝ :=
  ∑ a, P a * |logTwo (P a/Q a) - (nsClassicalD P Q).toReal|^3

/-- PDF pp.25–26: a canonical choice of eigenbasis, used only for basis-invariant moments. -/
def canonicalSpectral {I : Type*} [Fintype I] [DecidableEq I] (A : Mat I) : NSSpectralData I :=
  if h : A.IsHermitian then
    ⟨h.eigenvalues, fun i j => h.eigenvectorBasis i j⟩
  else ⟨fun _ => 0, fun _ _ => 0⟩

/-- PDF p.26, (B8): NS third moment. This is NOT a noncommutative absolute cube. -/
def thirdMoment {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Mat I) : ℝ :=
  classicalT (nsP (canonicalSpectral rho) (canonicalSpectral sigma))
    (nsQ (canonicalSpectral rho) (canonicalSpectral sigma))

/-- PDF p.28: weighted variance at the actual barycenter; zero-weight summands contribute zero. -/
def ensembleVariance {I : Type} [Fintype I] [DecidableEq I] (E : Ensemble I) : ℝ :=
  ∑ i, E.prob i * pairInformationVariance (E.state i) (ensembleAverage E)

/-- PDF p.28: weighted centered NS third moment at the actual barycenter. -/
def ensembleThird {I : Type} [Fintype I] [DecidableEq I] (E : Ensemble I) : ℝ :=
  ∑ i, E.prob i * thirdMoment (E.state i) (ensembleAverage E)

/-- PDF p.14: finite information I(P), with zero-probability blocks omitted by their weights. -/
def finiteHolevoInformation {I : Type} [Fintype I] [DecidableEq I] (E : Ensemble I) : ℝ :=
  ∑ i, E.prob i * (entropy (E.state i) (ensembleAverage E)).toReal

/-- PDF p.22: infimum on a subset of Theta_1, so no global extension of f is assumed. -/
def restrictedInf {X : Type*} (Theta : ℕ → Set X) (f : Theta 0 → ℝ) (A : Set X) : ℝ :=
  sInf {r | ∃ x : Theta 0, x.val ∈ A ∧ r = f x}

example (I : Type*) : (inferInstance : MeasurableSpace (Mat I)) = borel (Mat I) := by rfl

example : logTwo 1 = 0 := by simp [logTwo]

example {I : Type*} (rho : Fin 0 → Mat I) (a b : Fin 0 → I) : tensorWord rho a b = 1 := by
  simp [tensorWord]

example {I : Type*} [Fintype I] [DecidableEq I] (rho : Mat I) :
    traceDistance rho rho = 0 := by simp [QAlgorithms.traceDistance, QAlgorithms.traceNorm, cfc_zero]

example {I : Type*} [Fintype I] [DecidableEq I] (S : Set (Mat I)) :
    vEpsilon S (1/2) = vMin S := by simp [vEpsilon]

/-- Example 1, PDF p.10: Pauli matrices in the accepted Bool computational basis. -/
def pauliFamily : Fin 4 → Mat Bool :=
  ![1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ]

/-- Example 1, PDF p.10: the actual Pauli channel, not an unconstrained invariant tuple. -/
def pauliMap (p : Fin 4 → ℝ) (A : Mat Bool) : Mat Bool :=
  ∑ k, p k • (pauliFamily k * A * Matrix.conjTranspose (pauliFamily k))

/-- Example 1, PDF p.10: image of all qubit input states. -/
def pauliImage (p : Fin 4 → ℝ) : Set (Mat Bool) :=
  {B | ∃ A : Mat Bool, QAlgorithms.IsDensityMatrix A ∧ B = pauliMap p A}

/-- Example 1, PDF p.10: the three Bloch contraction factors of the Pauli map. -/
def pauliContractions (p : Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![p 0+p 1-p 2-p 3, p 0-p 1+p 2-p 3, p 0-p 1-p 2+p 3]

/-- Example 1, PDF p.10: comparison BSC is constructed from the longest Bloch semiaxis. -/
def bscCrossover (p : Fin 4 → ℝ) : ℝ :=
  (1 - max |pauliContractions p 0| (max |pauliContractions p 1| |pauliContractions p 2|))/2

/-- Example 1, PDF p.10: classical BSC variance, zero at deterministic endpoints. -/
def bscVariance (q : ℝ) : ℝ :=
  if q = 0 ∨ q = 1 then 0 else q*(1-q)*(logTwo ((1-q)/q))^2

/-- Example 1, PDF p.10: support cardinality of a finite ensemble, ignoring repeated
labels and zero-weight entries as a probability measure does. -/
def ensembleSize {I : Type} [Fintype I] (E : Ensemble I) : ℕ :=
  ((Finset.univ.filter fun i => 0 < E.prob i).image E.state).card

/-- Example 1, PDF p.10: all positive-weight states belong to the stated channel image. -/
def EnsembleOn {I : Type} [Fintype I] (S : Set (Mat I)) (E : Ensemble I) : Prop :=
  ∀ i, 0 < E.prob i → E.state i ∈ S

/-- Example 1, PDF p.10: minimality among ALL capacity-achieving ensembles in the image. -/
def MinimalAchieving {I : Type} [Fintype I] [DecidableEq I]
    (S : Set (Mat I)) (E : Ensemble I) : Prop :=
  EnsembleOn S E ∧ finiteHolevoInformation E = capacityBits S ∧
  ∀ F : Ensemble I, EnsembleOn S F → finiteHolevoInformation F = capacityBits S →
    ensembleSize E ≤ ensembleSize F

/-- Example 1, PDF p.10: unrestricted n-use quantum code, including entangled inputs.
The block channel is the accepted actual matrix-unit tensor extension. -/
def pauliQuantumBlockLog (p : Fin 4 → ℝ) (e : ℝ) (n : ℕ) : ℝ :=
  logTwo (cqOptimalMessages (fun rho : {A : Mat (Fin n → Bool) // QAlgorithms.IsDensityMatrix A} =>
    QAlgorithms.piSuperop (fun _ : Fin n => pauliMap p) rho.val) e)

/-- Example 1, PDF p.10, and (1), PDF p.1: unrestricted operational classical capacity. -/
def pauliQuantumCapacity (p : Fin 4 → ℝ) : ℝ :=
  Filter.liminf (fun e : ℝ => Filter.liminf
    (fun n : ℕ => pauliQuantumBlockLog p e n / n) atTop) (nhdsWithin 0 (Set.Ioi 0))

example : pauliFamily 0 = 1 := by rfl

example : bscVariance 0 = 0 := by simp [bscVariance]

example {I : Type*} [Fintype I] (s : NSSpectralData I) (a : I × I) :
    nsP (⟨fun _ => 0, fun _ _ => 0⟩ : NSSpectralData I) s a = 0 := by simp [nsP]

end QAlgorithms.Papers.Independent.Bridge50.P50


